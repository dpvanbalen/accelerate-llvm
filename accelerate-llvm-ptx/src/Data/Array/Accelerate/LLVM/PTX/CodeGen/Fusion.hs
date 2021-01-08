{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
module Data.Array.Accelerate.LLVM.PTX.CodeGen.Fusion where

import Data.Array.Accelerate.LLVM.CodeGen.Monad         (return_,  CodeGen )
import Data.Array.Accelerate.LLVM.PTX.Target            ( PTX )
import Data.Array.Accelerate.LLVM.PTX.CodeGen.FusionAST
import Data.Array.Accelerate.LLVM.PTX.CodeGen.Tree
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Type.Equality

----- codegen ----

codegenFused :: Fused t aenv i o -> i -> CodeGen PTX ()
codegenFused f i = compile f i $ const return_


compile :: Fused t aenv i o -> i -> (o -> CodeGen PTX ()) -> CodeGen PTX ()
compile (Sequence one two)  i c = compile one i $ flip (compile two) c
compile (EndOfFused w)      i c = case (mkProof w, mkProof' w) of (P Refl, P Refl) -> c (w $:> i)
compile (BaseToken token) i c =                  token i >>= c . (i,)
compile (TreeToken token) i c = compileTreeToken token i >>= c 

----- /codegen ----


---- fusion of `Fused` ----

---- horizontal ----


horizontal :: FusedAcc aenv a b -> FusedAcc aenv a c -> HorizontalOutput aenv a b c
horizontal (EndOfFused wb) (EndOfFused wc) = case wb &:> wc of
  Union tot b c ->                           HorizontalOutput (EndOfFused tot) b c

horizontal (Sequence x xs) (Sequence y ys) = case horizontalToken x y of                        -- fuse   the heads
  HorizontalTokenOutput one two wone wtwo -> case (weakenFused wone xs, weakenFused wtwo ys) of -- weaken the tails
      (WO xs' wxs, WO ys' wys)            -> case horizontal xs' ys' of                         -- fuse   the tails
              HorizontalOutput xys db dc  -> HorizontalOutput (Sequence one
                                                                        (Sequence two 
                                                                                  xys)) 
                                                              (wxs .:> db) 
                                                              (wys .:> dc)

horizontal (EndOfFused weof) (Sequence x xs) = case x                                      of

  BaseToken f                               -> case horizontal (EndOfFused (Keep weof)) xs of
    HorizontalOutput xs'' left right        -> case mkProof' weof                          of
      P Refl                                -> HorizontalOutput (Sequence (BaseToken f) 
                                                                          xs'') 
                                                                (Toss identityW .:> left) 
                                                                right

  TreeToken tree -> let wtree  = weakenFromTree tree 
                    in  case horizontal (EndOfFused (weof .:> wtree)) xs of
    HorizontalOutput xs'' left right -> HorizontalOutput (Sequence (TreeToken tree) 
                                                                   xs'') 
                                                         left 
                                                         right
-- calling the cases above
horizontal (Sequence x xs) (EndOfFused w) = case horizontal (EndOfFused w) (Sequence x xs) of 
  HorizontalOutput res a b -> HorizontalOutput res b a

data HorizontalOutput aenv a b c = forall d. HorizontalOutput (FusedAcc aenv a d) (d :> b) (d :> c)



-- Because we can't sequence two TOKENs, nor return both results from one token, we return two tokens that match
horizontalToken :: Fused TOKEN aenv a b -> Fused TOKEN aenv a c -> HorizontalTokenOutput aenv a b c
horizontalToken (BaseToken  xb) (BaseToken  xc) = HorizontalTokenOutput (BaseToken  xb)
                                                                        (BaseToken (xc . (Toss identityW  $:>)))
                                                                        (Toss        identityW)
                                                                        (Keep $ Toss identityW)
horizontalToken (BaseToken  x) (TreeToken  t) = case mkProofT' t of 
  P Refl                               -> HorizontalTokenOutput (BaseToken x)
                                                                          (TreeToken $ Skip t)
                                                                          (Keep $ weakenFromTree t) 
                                                                          (Toss   identityW)
horizontalToken (TreeToken  t) (BaseToken  x) = case mkProofT' t of 
  P Refl                               -> HorizontalTokenOutput (BaseToken x)
                                                                          (TreeToken (Skip t))
                                                                          (Toss   identityW)
                                                                          (Keep $ weakenFromTree t) 
-- In the case of two TreeTokens, we perform loop fusion with `horizontalTree`. Because we have to return
-- two tokens, we add a dummy BaseToken that puts () on the environment (and weaken it away later).
horizontalToken (TreeToken  l) (TreeToken  r) = case horizontalTree l r of
  HorizontalTreeOutput tree db dc                -> case (mkProofT tree, mkProofT' tree) of
    (P Refl, P Refl)                             -> HorizontalTokenOutput (BaseToken (const return_))
                                                                          (TreeToken $ Skip tree)
                                                                          (Toss db)
                                                                          (Toss dc)


-- | `d` is the resulting environment containing `b` and `c`, `t` is just a temporary environment between the two tokens
data HorizontalTokenOutput aenv a b c = forall d t. HorizontalTokenOutput (Fused TOKEN aenv a t) (Fused TOKEN aenv t d) (d :> b) (d :> c)


horizontalTree :: TreeTokenContent aenv i a -> TreeTokenContent aenv i b -> HorizontalTreeOutput aenv i a b
horizontalTree Leaf Leaf           = HorizontalTreeOutput Leaf                 End       End

horizontalTree (Skip l) (Skip r)   = case horizontalTree l r of
  HorizontalTreeOutput tree ca cb -> HorizontalTreeOutput (Skip          tree) (Keep ca) (Keep cb) 

horizontalTree (ScanT a b c d l) r = case horizontalTree l r of
  HorizontalTreeOutput tree ca cb -> HorizontalTreeOutput (ScanT a b c d tree) (Keep ca) (Toss cb)

horizontalTree l (ScanT a b c d r) = case horizontalTree l r of
  HorizontalTreeOutput tree ca cb -> HorizontalTreeOutput (ScanT a b c d tree) (Toss ca) (Keep cb)

horizontalTree (FoldT a b c l) r   = case horizontalTree l r of
  HorizontalTreeOutput tree ca cb -> HorizontalTreeOutput (FoldT a b c   tree) (Keep ca) (Toss cb)

horizontalTree l (FoldT a b c r)   = case horizontalTree l r of
  HorizontalTreeOutput tree ca cb -> HorizontalTreeOutput (FoldT a b c   tree) (Toss ca) (Keep cb)
  
data HorizontalTreeOutput aenv i a b = forall c. HorizontalTreeOutput (TreeTokenContent aenv i c) (c :> a) (c :> b)


---- /horizontal ----

{- todo: vertical, diagonal -}

---- utilities for fusion ----

-- | A TreeTokenContent strictly adds to the environment, so we can derive the reverse weakening
weakenFromTree :: TreeTokenContent aenv a b -> b :> a
weakenFromTree Leaf              = End
weakenFromTree (Skip          t) = Keep $ weakenFromTree t
weakenFromTree (ScanT _ _ _ _ t) = Toss $ weakenFromTree t
weakenFromTree (FoldT _ _ _   t) = Toss $ weakenFromTree t



-- not possible anymore:
-- weakenFused :: i' :> i -> Fused t aenv i o -> Fused t aenv i' o
-- weakenTreeToken :: i' :> i -> TreeTokenContent aenv i o -> TreeTokenContent aenv i' o
data WeakenOutput t aenv i o = forall o'. WO (Fused t aenv i o') (o' :> o)

weakenFused :: i' :> i -> Fused t aenv i o -> WeakenOutput t aenv i' o
weakenFused w (Sequence x y)  = case weakenFused w x of 
                    WO x' oo -> case weakenFused oo y of
                      WO y' oo' ->                            WO (Sequence x' y')          oo'
weakenFused w (EndOfFused w') = case mkProof' w' of P Refl -> WO (EndOfFused (w' .:> w))   identityW 
weakenFused w (BaseToken   t) = case mkProof  w  of P Refl -> WO (BaseToken (t . (w $:>))) (Keep w) 
weakenFused w (TreeToken   t) = case weakenTreeToken w t of
                                                 WTO t' oo -> WO (TreeToken t') oo


data WeakenTreeOutput aenv i o = forall o'. WTO (TreeTokenContent aenv i o') (o' :> o)

weakenTreeToken :: i' :> i -> TreeTokenContent aenv i o -> WeakenTreeOutput aenv i' o
weakenTreeToken End      Leaf              =                                                 WTO Leaf               End
weakenTreeToken (Toss w)                t  = case weakenTreeToken       w  t of WTO t' w' -> WTO (Skip          t') (Toss w')
weakenTreeToken (Keep w) (Skip          t) = case weakenTreeToken       w  t of WTO t' w' -> WTO (Skip          t') (Keep w')
weakenTreeToken (Keep w) (ScanT a b c d t) = case weakenTreeToken (Keep w) t of WTO t' w' -> WTO (ScanT a b c d t') (Keep w')
weakenTreeToken (Keep w) (FoldT a b c   t) = case weakenTreeToken (Keep w) t of WTO t' w' -> WTO (FoldT a b c   t') (Keep w')

-- | could also make this work on Fused TOKENs
weakenFused' :: o :> o' -> FusedAcc aenv i o -> FusedAcc aenv i o'
weakenFused' w (Sequence x xs) = Sequence x $ weakenFused' w xs
weakenFused' w (EndOfFused w') = EndOfFused $ w .:> w'

---- /utilities for fusion ----

---- /fusion of `Fused` ----



---- utilities for weakenings ----





-- | Vertical fusion for weakenings
(|:>) :: (a :> b) -> (b :> c) -> a :> c
(|:>) = flip (.:>)

-- TODO Diagonal fusion for weakenings
-- ... or does that not make sense? 


-- | Composition for weakenings
(.:>) :: b :> c -> a :> b -> a :> c
x         .:> End      = x
x         .:> (Toss w) = Toss (x .:> w)
(Toss w') .:> (Keep w) = Toss (w' .:> w)
(Keep w') .:> (Keep w) = Keep (w' .:> w)


-- | Applying a weakening on a tuplist
-- (could just as easily write an equivalent for `Data.Array.Accelerate.AST.Environment.Val`)
($:>) :: (IsTupList a, IsTupList b) => (a :> b) -> (a -> b)
End      $:> ()     = ()
(Toss w) $:> (y, _) = case (mkProof w, mkProof' w) of (P Refl, P Refl) ->  w $:> y
(Keep w) $:> (y, x) = case (mkProof w, mkProof' w) of (P Refl, P Refl) -> (w $:> y, x)


-- -- | If `isJust $ isIdentity (a &:> b)`, this constructs the union. 
-- -- No type-level proof that this only fails when isIdentity fails, but it's true.
-- (?:>) :: (big :> left) -> (big :> right) -> Maybe (left -> right -> big)
-- End      ?:> End      = Just $ \() () -> ()
-- (Toss _) ?:> (Toss _) = Nothing 
-- (Keep a) ?:> (Toss b) = (\f (l, x)     r  -> (f l r, x)) <$> a ?:> b
-- (Toss a) ?:> (Keep b) = (\f     l  (r, x) -> (f l r, x)) <$> a ?:> b
-- (Keep a) ?:> (Keep b) = (\f (l, x) (r, _) -> (f l r, x)) <$> a ?:> b

data Foo a b = forall union. Foo (a -> b -> union)

(?:>) :: (big :> left) -> (big :> right) -> Foo left right
End      ?:> End      = Foo $ \() () -> ()
(Toss a) ?:> (Toss b) = case a ?:> b of Foo f -> Foo $ \ l      r     ->  f l r 
(Keep a) ?:> (Toss b) = case a ?:> b of Foo f -> Foo $ \(l, x)  r     -> (f l r, x)
(Toss a) ?:> (Keep b) = case a ?:> b of Foo f -> Foo $ \ l     (r, x) -> (f l r, x)
(Keep a) ?:> (Keep b) = case a ?:> b of Foo f -> Foo $ \(l, x) (r, _) -> (f l r, x)

-- | Horizontal fusion for weakenings --- the union of the subsets
(-:>) :: (a :> b) -> (a :> c) -> Exists ((:>) a)
x -:> y = case x &:> y of Union result _ _ -> Exists result

data Union all a b = forall union. Union (all :> union) (union :> a) (union :> b)

(&:>) :: (x :> a) -> (x :> b) -> Union x a b
End      &:> End      =                                   Union End       End       End
(Toss a) &:> (Toss b) = case a &:> b of Union xu ua ub -> Union (Toss xu)       ua        ub
(Keep a) &:> (Toss b) = case a &:> b of Union xu ua ub -> Union (Keep xu) (Keep ua) (Toss ub)
(Toss a) &:> (Keep b) = case a &:> b of Union xu ua ub -> Union (Keep xu) (Toss ua) (Keep ub)
(Keep a) &:> (Keep b) = case a &:> b of Union xu ua ub -> Union (Keep xu) (Keep ua) (Keep ub)

isIdentity :: a :> b -> Maybe (a :~: b)
isIdentity End      = Just Refl
isIdentity (Keep x) = (\Refl -> Refl) <$> isIdentity x
isIdentity (Toss _) = Nothing 

---- /utilities for manipulating weakenings ----


