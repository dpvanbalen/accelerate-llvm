{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GADTs #-}
module Data.Array.Accelerate.LLVM.PTX.CodeGen.Fusion
  ( codegenFused
  , horizontal
  , vertical
  , diagonal
  ) where

import Data.Array.Accelerate.LLVM.CodeGen.Monad
import Data.Array.Accelerate.LLVM.PTX.Target
import Data.Array.Accelerate.LLVM.PTX.CodeGen.FusionAST
import Data.Array.Accelerate.LLVM.PTX.CodeGen.Tree
import Data.Type.Equality
import Data.Array.Accelerate.LLVM.PTX.CodeGen.Base (makeKernel)
import qualified Foreign.CUDA.Analysis as CUDA
import Foreign.CUDA.Analysis.Device
import Data.Array.Accelerate.LLVM.CodeGen.Environment
import Data.Array.Accelerate.LLVM.PTX.Analysis.Launch
import Data.Array.Accelerate.LLVM.CodeGen.Module
import Data.Array.Accelerate.LLVM.CodeGen.Base
import Data.Array.Accelerate.Representation.Elt (bytesElt)
import Prelude as P


-- test --
-- import Data.Array.Accelerate.LLVM.CodeGen.IR (Operands)
-- import Data.Array.Accelerate.Type
-- import Data.Array.Accelerate.Representation.Type
-- import Data.Array.Accelerate.LLVM.CodeGen.Sugar
-- import qualified Data.Array.Accelerate.LLVM.CodeGen.Arithmetic as A
-- import Data.Array.Accelerate.AST (Direction(..))

-- test = case testinput of
--   HorizontalOutput fused wFold wScan ->
--     let x = codegenFused _ mempty fused _ in _

-- testinput :: HorizontalOutput () ((), Operands Int32) ((), Operands Int32) ((), Operands Int32)
-- testinput = case horizontal (toList aFold) (toList aScan) of
--   HorizontalOutput fused wFold wScan -> 
--     HorizontalOutput (vertical (toList aMap) fused) wFold wScan


-- toList :: IsTupList o => Fused TOKEN () i (o, x) -> FusedAcc () i ((), x)
-- toList token = Sequence token $ EndOfFused (Keep emptyW)

-- aFold :: Fused TOKEN () ((), Operands Int32) (((), Operands Int32), Operands Int32) 
-- aFold = TreeToken $ FoldT (TupRsingle scalarType) 
--                           (IRFun2 $ A.add numType) (Just $ A.liftInt32 10) (Skip Leaf)


-- aScan :: Fused TOKEN () ((), Operands Int32) (((), Operands Int32), Operands Int32) 
-- aScan = TreeToken $ ScanT (TupRsingle scalarType) 
--                           (IRFun2 $ A.mul numType) (Just $ A.liftInt32 3) LeftToRight (Skip Leaf)

-- aMap ::  Fused TOKEN () ((), Operands Int32) (((), Operands Int32), Operands Int32) 
-- aMap = BaseToken $ \((), x) -> A.mul numType (A.liftInt32 5) x

-- /test --






----- codegen ----

-- some conversion between array types, maybe?
data Foo i

codegenFused :: DeviceProperties -> Gamma aenv -> Fused t aenv i o -> Foo i -> CodeGen PTX (Kernel PTX aenv o)
codegenFused dev aenv fused i = 
  let (params, arrs) = undefined i -- TODO: see what kind of input this function should have, match 'Foo' and this undefined to it.
      paramEnv = envParam aenv

      config = launchConfig dev (CUDA.incWarp dev) smem 
                _ _ -- no idea: some functions use 'const', others 'multipleOf', others "\_ _ -> 1"
                    -- all functions seem to put the same in the Q version as in the normal version
                    -- \arraySize threadBlockSize -> gridSize
                    -- I think gridSize = number of threadblocks.. so `const` just makes very many of them?
                    -- Is that not super inefficient?
                    -- 'multipleOf' makes sense, and \_ _ -> 1 is for ones that need to be done by 1 threadblock.
                    -- if this is all correct, then we'd want a variation on multipleOf which takes a list of input
                    -- sizes, computes the max, then does 'multipleOf' with that and the threadblocksize.
        where
          -- required shared memory (in bytes) as a function of threadblock size: only for tree aggregates
          smem :: Int -> Int
          smem n = (n `P.quot` CUDA.warpSize dev) * go fused
          -- big version of `bytesElt`: we only need 1 treetoken in memory at a time
          go :: forall t env a b. Fused t env a b -> Int
          go (Sequence x y) = max (go x) (go y) -- they can alias
          go (EndOfFused _) = 0
          
          go (BaseToken _) = 0 -- does not require shared memory

          go (TreeToken Leaf) = 0
          go (TreeToken (Skip           t)) =               go (TreeToken t)
          go (TreeToken (ScanT tp _ _ _ t)) = bytesElt tp + go (TreeToken t)
          go (TreeToken (FoldT tp _ _   t)) = bytesElt tp + go (TreeToken t)
  in  
  makeKernel config "fusedKernelName" (params ++ paramEnv) $ do
  compile fused arrs _ -- TODO write the results into the output arrays: quite important



compile :: Fused t aenv i o -> i -> (o -> CodeGen PTX ()) -> CodeGen PTX ()
compile (Sequence one two)  i c = compile one i $ flip (compile two) c
compile (EndOfFused w)      i c = case (mkProof w, mkProof' w) of (P Refl, P Refl) -> c (w $:> i)
compile (BaseToken token) i c =                  token i >>= c . (i,)
compile (TreeToken token) i c = compileTreeToken token i >>= c

----- /codegen ----


---- fusion of `Fused` ----


---- vertical, diagonal ----

vertical :: FusedAcc aenv a b -> FusedAcc aenv b c -> FusedAcc aenv a c
vertical (EndOfFused w)  acc = weakenFused w acc
vertical (Sequence x xs) acc = Sequence x (vertical xs acc)

data DiagOutput aenv a b c = forall d. DiagOutput (FusedAcc aenv a d) (d :> b) (d :> c)

diagonal :: forall aenv a b c. FusedAcc aenv a b -> FusedAcc aenv b c -> DiagOutput aenv a b c
diagonal (EndOfFused w) (EndOfFused w') = case mkProof w' of
  P Refl ->                   DiagOutput (EndOfFused w) identityW w'

diagonal (EndOfFused w) (Sequence y ys) = case mkProof w of
  P Refl -> case y of
    BaseToken f -> case diagonal (EndOfFused (Keep w)) ys of
        DiagOutput ys' db dc -> DiagOutput (Sequence (BaseToken (f . (w $:>))) ys')
                                           (Toss identityW .:> db)
                                           dc
    TreeToken t -> let wtree = weakenFromTree t
                   in case weakenTreeToken w t of
      WTO t' oo    -> case diagonal (EndOfFused oo) ys of
        DiagOutput ys' db dc -> DiagOutput (Sequence (TreeToken t') ys')
                                           (wtree .:> db)
                                           dc

diagonal (Sequence x xs) acc = case diagonal xs acc of
  DiagOutput xsacc db dc -> DiagOutput (Sequence x xsacc) db dc


---- /vertical, diagonal ----


---- horizontal ----

-- |Here we take care to fuse efficiently: we consume `BaseToken`s on both sides until
-- we encounter an EOF or two `TreeToken`s, which we can perform loop fusion on.
-- This greedy method is good enough to guarantee we never increase the number of
-- `TreeToken`s, which is the best we can do.
horizontal :: FusedAcc aenv a b -> FusedAcc aenv a c -> HorizontalOutput aenv a b c
horizontal (EndOfFused wb) (EndOfFused wc) = case wb -:> wc of
  Union tot b c ->                           HorizontalOutput (EndOfFused tot) b c
horizontal (EndOfFused w) (Sequence y ys) = case y of
  BaseToken f -> case horizontal (EndOfFused (Toss w)) ys of
    HorizontalOutput ys' wleft wright -> HorizontalOutput (Sequence (BaseToken f) ys') wleft wright
  TreeToken t -> let wtree = weakenFromTree t
                 in case horizontal (EndOfFused (w .:> wtree)) ys of
    HorizontalOutput ys' wleft wright -> HorizontalOutput (Sequence (TreeToken t) ys') wleft wright
horizontal (Sequence (TreeToken x) xs) (Sequence (TreeToken y) ys) = case horizontalTree x y of
  HorizontalTreeOutput tree wleft wright -> let xs' = weakenFused wleft  xs
                                                ys' = weakenFused wright ys
                                            in case horizontal xs' ys' of
    HorizontalOutput hor wleft' wright' -> HorizontalOutput (Sequence (TreeToken tree) hor) wleft' wright'
horizontal (Sequence (BaseToken x) xs) ys = let ys' = weakenFused (Toss identityW) ys
                                            in case horizontal xs ys' of
  HorizontalOutput hor wleft wright -> HorizontalOutput (Sequence (BaseToken x) hor) wleft wright
-- The remaining symmetrical cases: (TreeToken, BaseToken) and (TreeToken, EOF).
horizontal tree baseOrEOF = case horizontal baseOrEOF tree of
  HorizontalOutput a b c -> HorizontalOutput a c b

data HorizontalOutput aenv a b c = forall d. HorizontalOutput (FusedAcc aenv a d) (d :> b) (d :> c)


horizontalTree :: TreeToken aenv i a -> TreeToken aenv i b -> HorizontalTreeOutput aenv i a b
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

data HorizontalTreeOutput aenv i a b = forall c. HorizontalTreeOutput (TreeToken aenv i c) (c :> a) (c :> b)


---- /horizontal ----


---- /fusion of `Fused` ----



---- utilities for fusion ----

-- | A TreeToken strictly adds to the environment, so we can derive the reverse weakening
weakenFromTree :: TreeToken aenv a b -> b :> a
weakenFromTree Leaf              = End
weakenFromTree (Skip          t) = Keep $ weakenFromTree t
weakenFromTree (ScanT _ _ _ _ t) = Toss $ weakenFromTree t
weakenFromTree (FoldT _ _ _   t) = Toss $ weakenFromTree t


weakenFused :: i' :> i -> FusedAcc aenv i o -> FusedAcc aenv i' o
weakenFused ii (Sequence x y) = case weakenFusedT ii x of
                    WO x' oo' -> Sequence x' $ weakenFused oo' y
weakenFused ii (EndOfFused w) = EndOfFused $ w .:> ii

data WeakenOutput aenv i o = forall o'. WO (Fused TOKEN aenv i o') (o' :> o)
weakenFusedT :: i' :> i -> Fused TOKEN aenv i o -> WeakenOutput aenv i' o
weakenFusedT w (BaseToken   t) = case mkProof  w  of P Refl -> WO (BaseToken (t . (w $:>))) (Keep w)
weakenFusedT w (TreeToken   t) = case weakenTreeToken w t of
                                                 WTO t' oo -> WO (TreeToken t') oo


data WeakenTreeOutput aenv i o = forall o'. WTO (TreeToken aenv i o') (o' :> o)

weakenTreeToken :: i' :> i -> TreeToken aenv i o -> WeakenTreeOutput aenv i' o
weakenTreeToken End      Leaf              =                                                 WTO Leaf               End
weakenTreeToken (Toss w)                t  = case weakenTreeToken       w  t of WTO t' w' -> WTO (Skip          t') (Toss w')
weakenTreeToken (Keep w) (Skip          t) = case weakenTreeToken       w  t of WTO t' w' -> WTO (Skip          t') (Keep w')
weakenTreeToken (Keep w) (ScanT a b c d t) = case weakenTreeToken (Keep w) t of WTO t' w' -> WTO (ScanT a b c d t') (Keep w')
weakenTreeToken (Keep w) (FoldT a b c   t) = case weakenTreeToken (Keep w) t of WTO t' w' -> WTO (FoldT a b c   t') (Keep w')


---- /utilities for fusion ----



---- utilities for weakenings ----


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






data Union all a b = forall union. Union (all :> union) (union :> a) (union :> b)
-- |Horizontal fusion for weakenings: Conjures a `union` type variable and produces the
-- relevant weakenings. Note that the type does not quite capture the full specification:
--    `x -:> y = Union identityW x y`
-- would also typecheck. To ensure correctness, we could fuse this function with (?:>).
(-:>) :: (all :> a) -> (all :> b) -> Union all a b
End      -:> End      =                                   Union End       End       End
(Toss a) -:> (Toss b) = case a -:> b of Union xu ua ub -> Union (Toss xu)       ua        ub
(Keep a) -:> (Toss b) = case a -:> b of Union xu ua ub -> Union (Keep xu) (Keep ua) (Toss ub)
(Toss a) -:> (Keep b) = case a -:> b of Union xu ua ub -> Union (Keep xu) (Toss ua) (Keep ub)
(Keep a) -:> (Keep b) = case a -:> b of Union xu ua ub -> Union (Keep xu) (Keep ua) (Keep ub)


---- /utilities for manipulating weakenings ----


---- Utilities that I felt like writing but didn't end up using (yet) ----

-- -- | Vertical fusion for weakenings
-- (|:>) :: (a :> b) -> (b :> c) -> a :> c
-- (|:>) = flip (.:>)

-- -- | Diagonal fusion for weakenings
-- (/:>) :: (a :> b) -> (b :> c) -> (a :> c, b :> c)
-- x /:> y = (x |:> y, y)

-- -- | could also make this work on Fused TOKENs
-- weakenFused' :: o :> o' -> FusedAcc aenv i o -> FusedAcc aenv i o'
-- weakenFused' w (Sequence x xs) = Sequence x $ weakenFused' w xs
-- weakenFused' w (EndOfFused w') = EndOfFused $ w .:> w'


-- -- |Given two weakenings, produces a function that can construct the union environment.
-- -- Is probably of little use without any kind of proof that it does what it says,
-- -- you'd like to be able to give this two weakenings whose union is `big` but can't
-- -- express that on the type level yet. Better would be to fuse this function with (-:>).
-- data Foo a b = forall union. Foo (a -> b -> union)
-- (?:>) :: (big :> left) -> (big :> right) -> Foo left right
-- End      ?:> End      = Foo $ \() () -> ()
-- (Toss a) ?:> (Toss b) = case a ?:> b of Foo f -> Foo $ \ l      r     ->  f l r
-- (Keep a) ?:> (Toss b) = case a ?:> b of Foo f -> Foo $ \(l, x)  r     -> (f l r, x)
-- (Toss a) ?:> (Keep b) = case a ?:> b of Foo f -> Foo $ \ l     (r, x) -> (f l r, x)
-- (Keep a) ?:> (Keep b) = case a ?:> b of Foo f -> Foo $ \(l, x) (r, _) -> (f l r, x)


-- isIdentityW :: a :> b -> Maybe (a :~: b)
-- isIdentityW End      = Just Refl
-- isIdentityW (Keep x) = (\Refl -> Refl) <$> isIdentityW x
-- isIdentityW (Toss _) = Nothing
--