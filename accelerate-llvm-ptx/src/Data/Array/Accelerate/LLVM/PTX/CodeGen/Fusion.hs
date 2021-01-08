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
compile (EndOfFused w)      i c = c (w $:> i)
compile (BaseToken w token) i c =                  token i >>= c . (w $:> i, )
compile (TreeToken w token) i c = compileTreeToken token i >>= c . (w $:>)

----- /codegen ----


---- fusion of `Fused` ----

---- horizontal ----


horizontal :: FusedAcc aenv a b -> FusedAcc aenv a c -> Exists (HorizontalOutput aenv a b c) 
horizontal (EndOfFused wb) (EndOfFused wc) = case wb &:> wc of
  Exists (Union tot b c) ->  Exists $ HorizontalOutput (EndOfFused tot) b c

horizontal (Sequence x xs) (Sequence y ys) =           case horizontalToken x y of                        -- fuse   the heads
  Exists2 (HorizontalTokenOutput one two wone wtwo) -> case (weakenFused wone xs, weakenFused wtwo ys) of -- weaken the tails
      (Exists (WO xs' wxs), Exists (WO ys' wys))    -> case horizontal xs' ys' of                         -- fuse   the tails
              Exists (HorizontalOutput xys db dc)   -> Exists $ HorizontalOutput (Sequence one
                                                                                           (Sequence two 
                                                                                                     xys)) 
                                                                                 (wxs .:> db) 
                                                                                 (wys .:> dc)

horizontal (EndOfFused weof) (Sequence x xs) = case x of
  BaseToken wtok f -> case weof &:> wtok of
    Exists (Union union ueof utok) -> case weakenFused (Keep utok) xs of
      Exists (WO xs' wxs) -> case horizontal (EndOfFused (Keep ueof)) xs' of
        Exists (HorizontalOutput xs'' left right) -> case (mkProof wtok, mkProof' ueof) of
          (Exists (P Refl), Exists (P Refl)) -> Exists $ HorizontalOutput (Sequence (BaseToken union f) 
                                                                                    xs'') 
                                                                          (Toss identityW .:> left) 
                                                                          (wxs .:> right)

  TreeToken wtok tree -> let wtree  = weakenFromTree tree in case wtok &:> (weof .:> wtree) of
    Exists (Union union utok ueof) -> case weakenFused utok xs of
      Exists (WO xs' wxs) -> case horizontal (EndOfFused ueof) xs' of
        Exists (HorizontalOutput x'' left right) -> 
                  Exists $ HorizontalOutput (Sequence (TreeToken union tree) 
                                                      x'') 
                                            left 
                                            (wxs .:> right)

  -- calling the code above
horizontal (Sequence x xs) (EndOfFused w) = case horizontal (EndOfFused w) (Sequence x xs) of 
  Exists (HorizontalOutput res a b) -> Exists $ HorizontalOutput res b a

data HorizontalOutput aenv a b c d = HorizontalOutput (FusedAcc aenv a d) (d :> b) (d :> c)



-- Because we can't sequence two TOKENs, nor return both results from one token, we return two tokens that match
horizontalToken :: Fused TOKEN aenv a b -> Fused TOKEN aenv a c -> Exists2 (HorizontalTokenOutput aenv a b c)
horizontalToken (BaseToken wb xb) (BaseToken wc xc) = case wb &:> wc of
  Exists (Union ad db dc) -> case mkProof ad of
    Exists (P Refl) -> Exists2 $ HorizontalTokenOutput (BaseToken identityW  xb)
                                                       (BaseToken (Keep ad) (xc . (Toss identityW  $:>)))
                                                       (Toss $ Keep db)
                                                       (Keep $ Toss dc)
horizontalToken (BaseToken wx x) (TreeToken wt t) = case (mkProof wx, mkProofT' t) of 
  (Exists (P Refl), Exists (P Refl)) -> Exists2 $ HorizontalTokenOutput (BaseToken identityW x)
                                                                        (TreeToken identityW (Skip t))
                                                                        (Keep $ wx .:> weakenFromTree t) 
                                                                        (Toss   wt)
horizontalToken (TreeToken wt t) (BaseToken wx x) = case (mkProof wx, mkProofT' t) of 
  (Exists (P Refl), Exists (P Refl)) -> Exists2 $ HorizontalTokenOutput (BaseToken identityW x)
                                                                        (TreeToken identityW (Skip t))
                                                                        (Toss   wt)
                                                                        (Keep $ wx .:> weakenFromTree t) 
-- In the case of two TreeTokens, we perform loop fusion with `horizontalTree`. Because we have to return
-- two tokens, we add a dummy BaseToken that puts () on the environment (and weaken it away later).
horizontalToken (TreeToken wl l) (TreeToken wr r) = case horizontalTree l r of
  Exists (HorizontalTreeOutput tree db dc) -> case (mkProofT tree, mkProofT' tree) of
    (Exists (P Refl), Exists (P Refl)) -> Exists2 $ HorizontalTokenOutput (BaseToken identityW (const return_))
                                                                          (TreeToken identityW $ Skip tree)
                                                                          (Toss $ wl .:> db)
                                                                          (Toss $ wr .:> dc)


-- | `d` is the resulting environment containing `b` and `c`, `t` is just a temporary environment between the two tokens
data HorizontalTokenOutput aenv a b c d t = HorizontalTokenOutput (Fused TOKEN aenv a t) (Fused TOKEN aenv t d) (d :> b) (d :> c)


horizontalTree :: TreeTokenContent aenv i a -> TreeTokenContent aenv i b -> Exists (HorizontalTreeOutput aenv i a b)
horizontalTree Leaf Leaf           =          Exists $ HorizontalTreeOutput Leaf                 End       End

horizontalTree (Skip l) (Skip r)   = case horizontalTree l r of
  Exists (HorizontalTreeOutput tree ca cb) -> Exists $ HorizontalTreeOutput (Skip          tree) (Keep ca) (Keep cb) 

horizontalTree (ScanT a b c d l) r = case horizontalTree l r of
  Exists (HorizontalTreeOutput tree ca cb) -> Exists $ HorizontalTreeOutput (ScanT a b c d tree) (Keep ca) (Toss cb)

horizontalTree l (ScanT a b c d r) = case horizontalTree l r of
  Exists (HorizontalTreeOutput tree ca cb) -> Exists $ HorizontalTreeOutput (ScanT a b c d tree) (Toss ca) (Keep cb)

horizontalTree (FoldT a b c l) r   = case horizontalTree l r of
  Exists (HorizontalTreeOutput tree ca cb) -> Exists $ HorizontalTreeOutput (FoldT a b c   tree) (Keep ca) (Toss cb)

horizontalTree l (FoldT a b c r)   = case horizontalTree l r of
  Exists (HorizontalTreeOutput tree ca cb) -> Exists $ HorizontalTreeOutput (FoldT a b c   tree) (Toss ca) (Keep cb)
  
data HorizontalTreeOutput aenv i a b c = HorizontalTreeOutput (TreeTokenContent aenv i c) (c :> a) (c :> b)


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
data WeakenOutput t aenv i o o' = WO (Fused t aenv i o') (o' :> o)

weakenFused :: i' :> i -> Fused t aenv i o -> Exists (WeakenOutput t aenv i' o)
weakenFused w (Sequence x y)    = case weakenFused w x of 
  Exists (WO x' oo) -> case weakenFused oo y of
    Exists (WO y' oo') -> Exists $ WO (Sequence x' y') oo'
weakenFused w (EndOfFused w')   = case mkProof' w' of Exists (P Refl) -> Exists $ WO (EndOfFused (w' .:> w))               identityW 
weakenFused w (BaseToken  w' t) = case mkProof' w' of Exists (P Refl) -> Exists $ WO (BaseToken  (w' .:> w) (t . (w $:>))) identityW 
weakenFused w (TreeToken  w' t) = case weakenTreeToken w t of
  Exists (WTO t' oo) -> Exists $ WO (TreeToken oo t') w'


data WeakenTreeOutput aenv i o o' = WTO (TreeTokenContent aenv i o') (o' :> o)

weakenTreeToken :: i' :> i -> TreeTokenContent aenv i o -> Exists (WeakenTreeOutput aenv i' o)
weakenTreeToken End      Leaf              = Exists $ WTO Leaf End
weakenTreeToken (Toss w)                 t = case weakenTreeToken       w  t of Exists (WTO t' w') -> Exists $ WTO (Skip          t') (Toss w')
weakenTreeToken (Keep w) (Skip          t) = case weakenTreeToken       w  t of Exists (WTO t' w') -> Exists $ WTO (Skip          t') (Keep w')
weakenTreeToken (Keep w) (ScanT a b c d t) = case weakenTreeToken (Keep w) t of Exists (WTO t' w') -> Exists $ WTO (ScanT a b c d t') (Keep w')
weakenTreeToken (Keep w) (FoldT a b c   t) = case weakenTreeToken (Keep w) t of Exists (WTO t' w') -> Exists $ WTO (FoldT a b c   t') (Keep w')

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
x .:> End = x
x .:> (Toss w) = Toss (x .:> w)
x .:> (Keep w) = case x of
                (Toss w') -> Toss (w' .:> w)
                (Keep w') -> Keep (w' .:> w)


-- | Applying a weakening on a tuplist
-- (could just as easily write an equivalent for `Data.Array.Accelerate.AST.Environment.Val`)
($:>) :: (a :> b) -> (a -> b)
End      $:> ()     = ()
(Toss w) $:> (y, _) =  w $:> y
(Keep w) $:> (y, x) = (w $:> y, x)


-- -- | If `isJust $ isIdentity (a &:> b)`, this constructs the union. 
-- -- No type-level proof that this only fails when isIdentity fails, but it's true.
-- (?:>) :: (big :> left) -> (big :> right) -> Maybe (left -> right -> big)
-- End      ?:> End      = Just $ \() () -> ()
-- (Toss _) ?:> (Toss _) = Nothing 
-- (Keep a) ?:> (Toss b) = (\f (l, x)     r  -> (f l r, x)) <$> a ?:> b
-- (Toss a) ?:> (Keep b) = (\f     l  (r, x) -> (f l r, x)) <$> a ?:> b
-- (Keep a) ?:> (Keep b) = (\f (l, x) (r, _) -> (f l r, x)) <$> a ?:> b

newtype Foo a b union = Foo (a -> b -> union)

(?:>) :: (big :> left) -> (big :> right) -> Exists (Foo left right)
End      ?:> End      = Exists $ Foo $ \() () -> ()
(Toss a) ?:> (Toss b) = case a ?:> b of Exists (Foo f) -> Exists $ Foo $ \ l      r     -> f l r 
(Keep a) ?:> (Toss b) = case a ?:> b of Exists (Foo f) -> Exists $ Foo $ \(l, x)  r     -> (f l r, x)
(Toss a) ?:> (Keep b) = case a ?:> b of Exists (Foo f) -> Exists $ Foo $ \ l     (r, x) -> (f l r, x)
(Keep a) ?:> (Keep b) = case a ?:> b of Exists (Foo f) -> Exists $ Foo $ \(l, x) (r, _) -> (f l r, x)

-- | Horizontal fusion for weakenings --- the union of the subsets
(-:>) :: (a :> b) -> (a :> c) -> Exists ((:>) a)
x -:> y = case x &:> y of
  Exists (Union result _ _) -> Exists result

data Union all a b union = Union (all :> union) (union :> a) (union :> b)

(&:>) :: (x :> a) -> (x :> b) -> Exists (Union x a b)
End      &:> End      =                                            Exists $ Union End       End       End
(Toss a) &:> (Toss b) = case a &:> b of Exists (Union xu ua ub) -> Exists $ Union (Toss xu)       ua        ub
(Keep a) &:> (Toss b) = case a &:> b of Exists (Union xu ua ub) -> Exists $ Union (Keep xu) (Keep ua) (Toss ub)
(Toss a) &:> (Keep b) = case a &:> b of Exists (Union xu ua ub) -> Exists $ Union (Keep xu) (Toss ua) (Keep ub)
(Keep a) &:> (Keep b) = case a &:> b of Exists (Union xu ua ub) -> Exists $ Union (Keep xu) (Keep ua) (Keep ub)

isIdentity :: a :> b -> Maybe (a :~: b)
isIdentity End = Just Refl
isIdentity (Keep x) = (\Refl -> Refl) <$> isIdentity x
isIdentity (Toss _) = Nothing 

---- /utilities for manipulating weakenings ----


