{-# LANGUAGE TupleSections #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE RebindableSyntax    #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}

-- | Code generation for fused scans and folds

module Data.Array.Accelerate.LLVM.PTX.CodeGen.Tree where

import Data.Array.Accelerate.LLVM.PTX.CodeGen.FusionAST



import Data.Array.Accelerate.AST

import Data.Array.Accelerate.LLVM.CodeGen.Arithmetic                as A
import Data.Array.Accelerate.LLVM.CodeGen.IR
import Data.Array.Accelerate.LLVM.CodeGen.Monad
import Data.Array.Accelerate.LLVM.CodeGen.Sugar

import Data.Array.Accelerate.LLVM.PTX.Analysis.Launch
import Data.Array.Accelerate.LLVM.PTX.CodeGen.Base
import Data.Array.Accelerate.LLVM.PTX.Target

import LLVM.AST.Type.Representation

import qualified Foreign.CUDA.Analysis                              as CUDA

import Data.Bits                                                    as P
import Prelude                                                      as P
import Data.Type.Equality
import Control.Monad ( (>=>) )
import Data.Array.Accelerate.LLVM.CodeGen.Array
import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Representation.Elt
import Data.Array.Accelerate.LLVM.CodeGen.Loop
import Control.Monad.State (gets)




compileTreeToken :: TreeToken aenv i o -> i -> CodeGen PTX o
compileTreeToken token x = do
  dev <- liftCodeGen $ gets ptxDeviceProperties
  treeBlock dev token (Left x)





-- |Perform block-level scans and folds.
treeBlock
    :: forall aenv i o.
       DeviceProperties
    -> TreeToken aenv i o
    -> Either i o
    -> CodeGen PTX o
treeBlock dev token = warpTree >=> warpAggregates
  where
    warpTree :: Either i o -> CodeGen PTX o
    warpTree = treeWarp dev token 


    -- |Scan and fold over the warp-wide aggregates. Here it's done sequentially
    -- by thread 0, as in CUB and in previous acc-llvm backends, but it could be
    -- done cooperatively (either by limiting threadblocksize to warpsize^2, or
    -- by recursing). 
    warpAggregates :: o -> CodeGen PTX o
    warpAggregates input = do
      -- Allocate #warps elements of shared memory for each scan/fold
      bd       <- blockDim
      warps    <- A.quot integralType bd (int32 (CUDA.warpSize dev))
      treesmem <- goAllocate warps token 

      -- Share aggregates
      wid   <- warpId
      lane  <- laneId
      goWriteAggregates wid lane token input treesmem

      -- Wait for each warp to finish its local fold/scan and share the aggregate
      __syncthreads

      -- Final step
      tid <- threadIdx
      goFinish tid wid warps token input treesmem


    goAllocate :: Operands Int32 -> TreeToken aenv i o -> CodeGen PTX (TreeSmem o)
    goAllocate warps =   -- We can start with 0 here, because it's okay to alias shared
        go (liftInt32 0) -- memory with TreeTokens that get evaluated before or after this one.
      where go :: forall env a b. Operands Int32 -> TreeToken env a b -> CodeGen PTX (TreeSmem b)
            go _ Leaf = return EmptySmem
            go skip (Skip t) = NothingSmem <$> go skip t
            go skip (ScanT tp _ _ _ t) = do
              deltaskip <- A.mul numType warps (liftInt32 $ P.fromIntegral $ bytesElt tp)
              newskip <- A.add numType skip deltaskip
              subtree <- go newskip t
              smem <- dynamicSharedMem tp TypeInt32 warps skip
              return $ ConsSmem smem subtree 
            go skip (FoldT tp _ _   t) = do
              deltaskip <- A.mul numType warps (liftInt32 $ P.fromIntegral $ bytesElt tp)
              newskip <- A.add numType skip deltaskip
              subtree <- go newskip t
              smem <- dynamicSharedMem tp TypeInt32 warps skip
              return $ ConsSmem smem subtree 
 

    -- for scans shares the highest index in the warp, for folds lane 0 in each warp, share their value.
    goWriteAggregates :: Operands Int32 -> Operands Int32 -> TreeToken aenv i o -> o -> TreeSmem o -> CodeGen PTX ()
    goWriteAggregates wid lane = go
      where go :: forall env a b. TreeToken env a b -> b -> TreeSmem b -> CodeGen PTX ()
            go Leaf () EmptySmem = return_
            go (Skip t) (env, _) (NothingSmem tree) = go t env tree
            go (ScanT _ _ _ _ t) (env, x) (ConsSmem smem tree) = do
              when (A.eq singleType lane (int32 (CUDA.warpSize dev - 1))) $ do
                writeArray TypeInt32 smem wid x
              go t env tree
            go (FoldT   _ _ _ t) (env, x) (ConsSmem smem tree) = do
              when (A.eq singleType lane (liftInt32 0)) $ do
                writeArray TypeInt32 smem wid x
              go t env tree
            -- These cases should never occur, see 'goAllocate' above.
            go (Skip _) _ (ConsSmem _ _) = error "goWriteAggregates:    shared memory allocated for Skipped node"
            go _ _ (NothingSmem _)       = error "goWriteAggregates: no shared memory allocated for Scan/Fold node"


    -- Performs the scans and folds on the aggregates.
    -- TODO: use the initial elements! 
    goFinish :: Operands Int32 -> Operands Int32 -> Operands Int32 -> TreeToken aenv i o -> o -> TreeSmem o -> CodeGen PTX o
    goFinish tid wid warps = go
      where go :: forall env a b. TreeToken env  a b -> b -> TreeSmem b -> CodeGen PTX b
            go Leaf     ()       EmptySmem          = return_
            go (Skip t) (env, x) (NothingSmem tree) = (,x) <$> go t env tree

            go (ScanT tp combine _ dir t) (env, input) (ConsSmem smem tree) = do
              let nelem = Nothing -- TODO this is not correct, deal with small arrays somehow.
              output <- if (tp, A.eq singleType wid (liftInt32 0))
                then return input
                else do
                  -- Every thread sequentially scans the warp aggregates to compute
                  -- their prefix value. 
                  steps <- case nelem of
                              Nothing -> return wid
                              Just n  -> A.min singleType wid =<< A.quot integralType n (int32 (CUDA.warpSize dev))

                  p0     <- readArray TypeInt32 smem (liftInt32 0)
                  prefix <- iterFromStepTo tp (liftInt32 1) (liftInt32 1) steps p0 $ \step x -> do
                              y <- readArray TypeInt32 smem step
                              case dir of
                                LeftToRight -> app2 combine x y
                                RightToLeft -> app2 combine y x

                  case dir of
                    LeftToRight -> app2 combine prefix input
                    RightToLeft -> app2 combine input prefix
              (,output) <$> go t env tree

            go (FoldT tp combine _ t) (env, input) (ConsSmem smem tree) = do
              let size = Nothing -- TODO this is not correct, deal with small arrays somehow.

              -- Update the total aggregate. Thread 0 just does this sequentially (as is
              -- done in CUB), but we could also do this cooperatively (better for
              -- larger thread blocks?)
              output <- if (tp, A.eq singleType tid (liftInt32 0))
                then do
                  steps <- case size of
                            Nothing -> return warps
                            Just n  -> do
                              a <- A.add numType n (int32 (CUDA.warpSize dev - 1))
                              A.quot integralType a (int32 (CUDA.warpSize dev))
                  iterFromStepTo tp (liftInt32 1) (liftInt32 1) steps input $ \step x ->
                    app2 combine x =<< readArray TypeInt32 smem step
                else
                  return input
              (,output) <$> go t env tree

            -- These cases should never occur, see 'goAllocate' above.
            go (Skip _) _ (ConsSmem _ _) = error "goWriteAggregates:    shared memory allocated for Skipped node"
            go _ _ (NothingSmem _)       = error "goWriteAggregates: no shared memory allocated for Scan/Fold node"


-- |Perform warp-level scans and folds, using `shfl` instructions.
-- TODO: make shared memory-based twin version for older GPUs
treeWarpShfl
    :: forall aenv i o.
       DeviceProperties
    -> TreeToken aenv i o
    -> Either i o
    -> CodeGen PTX o
treeWarpShfl dev token eitherio = case eitherio of
    -- First call  -> read the input arrays
          Left i -> gather i >>= tree 0

    -- Later calls -> reducing/scanning intermediate results, i.e. block-wide aggregates
          Right o -> tree 0 o
  where
    log2 = P.logBase 2 :: Double -> Double

    steps = P.floor . log2 . P.fromIntegral . CUDA.warpSize $ dev

    tree :: Int -> o -> CodeGen PTX o
    tree step x
      | step >= steps = return x -- TODO (>=) vs (>)
      | otherwise     = do
        let offset = liftWord32 (1 `P.shiftL` step)

        -- Fusing 'shuffles' and 'combines' is possible,
        -- and would use `n+1` memory at once instead of `2n`.
        -- I don't know if that would be noticable, and if it even
        -- matters without `free`ing the variables in between.
        -- How does memory management work in CUDA?
        -- If this would have any performance benefit, it would
        -- surely be worth the effort! 
        -- Probably worth trying regardless: TODO
        y  <- shuffles offset x
        x' <- combines x y
        tree (step + 1) x'


    -- | Separated from the loop, as it changes the size (and thus type)
    -- of the variables we're looking at (as a result of horizontal fusion).
    gather :: i -> CodeGen PTX o
    gather = go token
      -- TODO: future micro-optimisation: fusing this with the first call to
      -- `shuffles` (and possibly `combines`) would let us save on a couple
      -- instructions (because, for multiple scans or multiple folds over the same
      -- array, we only need 1 shfl_up or shfl_down). This obviously doesn't work
      -- for later calls to `shuffle`: Even though it would be typecorrect, you'd
      -- get the wrong values. (Horizontally fused scans/folds neccesarily have the 
      -- exact same type.)
      where
        go :: TreeToken aenv a b -> a -> CodeGen PTX b
        go Leaf () = return ()
        go (Skip t) (a, b) = (,b) <$> go t a
        go (ScanT _ _ _ _ t) a = case mkRefl t of
          TreeRefl Refl -> (\(x, y) -> ((x, y), y)) <$> go t a
        go (FoldT _ _ _ t) a = case mkRefl t of
          TreeRefl Refl -> (\(x, y) -> ((x, y), y)) <$> go t a

    shuffles :: Operands Word32 -> o -> CodeGen PTX o
    shuffles offset = go token
      where
        go :: TreeToken aenv a b -> b -> CodeGen PTX b
        go Leaf              ()     = return ()
        go (Skip  t)         (a, b) = (,b) <$> go t a
        go (ScanT r _ _ _ t) (a, b) = (,)  <$> go t a <*> shfl_up   r b offset
        go (FoldT r _ _ t)   (a, b) = (,)  <$> go t a <*> shfl_down r b offset

    combines :: o -> o -> CodeGen PTX o
    combines = go token
      where
        go :: forall a b. TreeToken aenv a b -> b -> b -> CodeGen PTX b
        go Leaf              ()     ()     = return ()
        go (Skip t)          (x, a) (y, _) = (,a) <$> go t x y
        go (ScanT _ c _ d t) (x, a) (y, b) = (,)  <$> go t x y <*> case d of
          LeftToRight ->                                           app2 c a b
          RightToLeft ->                                           app2 c b a
        go (FoldT _ c _ t)   (x, a) (y, b) = (,)  <$> go t x y <*> app2 c a b



-- |TODO
treeWarp, treeWarpSmem
    :: forall aenv i o.
       DeviceProperties
    -> TreeToken aenv i o
    -> Either i o
    -> CodeGen PTX o
treeWarp dev
  | useShfl dev = treeWarpShfl dev
  | otherwise   = treeWarpSmem dev

treeWarpSmem = undefined 


-- |Stores pointers to shared memory segments belonging to the scan/fold nodes of a treetoken.
-- TODO: currently, this represents a layout where all elements of a single scan/fold are adjacent.
-- We'd maybe get a decent performance boost if instead, all elements belonging to a single warp
-- are adjacent? Tough to say though, and probably depends on how they are accessed (e.g. currently,
-- scan aggregates are read sequentially by each thread, which actually profits from this layout. 
-- If/when we switch to cooperatively scanning/reducing aggregates too, this suggested change
-- might have more impact than it currently would).
data TreeSmem a where
  EmptySmem :: TreeSmem ()
  ConsSmem :: IRArray (Vector e) -> TreeSmem a -> TreeSmem (a, Operands e)
  NothingSmem :: TreeSmem a -> TreeSmem (a, b)




int32 :: Integral a => a -> Operands Int32
int32 = liftInt32 . P.fromIntegral