{-# LANGUAGE TupleSections #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RebindableSyntax    #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE ViewPatterns        #-}

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

import Control.Monad                                                ( (>=>) )
import Data.Bits                                                    as P
import Prelude                                                      as P








compileTreeToken :: TreeTokenContent aenv ins outs -> ins -> CodeGen PTX outs
compileTreeToken = undefined 



treeWarpShfl
    :: forall aenv i o.
       DeviceProperties 
    -> TreeTokenContent aenv i o
    -> i                          -- tuplist of Operands
    -> CodeGen PTX o
treeWarpShfl dev token = initialStep >=> tree 1
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
        -- I don't know if that is noticable, and if it even 
        -- matters without `free`ing the variables in between. 
        -- How does memory management work in CUDA?
        y  <- shuffles x offset
        x' <- combines x y
        tree (step + 1) x'


    -- | Separated from the rest of the loop, as it changes the size (and thus type)
    --   of the variables we're looking at (as a result of horizontal fusion).
    initialStep :: i -> CodeGen PTX o
    initialStep = undefined 
    -- case d == dir of -- quick check
    --         False -> error "oops" 
    --         True -> case t of
    --           ScanT _ _ _ _ -> case thing of
    --             (first, rest) -> return (first, (first, rest))
    --           FoldT _ _ _   -> case thing of
    --             (first, rest) -> return (first, (first, rest))
    --           _               -> do
    --             res <- shfl_down _ _ offset
    --             (res,) <$> go t b

    shuffles :: o -> Operands Word32 -> CodeGen PTX o
    shuffles x offset = go token x
      where
        go :: forall a b. TreeTokenContent aenv a b -> b -> CodeGen PTX b
        go Leaf              ()     = return ()
        go (Skip  t)         (a, b) = (,b) <$> go t a
        go (ScanT r _ _ _ t) (a, b) = (,)
                  <$> go t a <*> shfl_up   r b offset
        go (FoldT r _ _ t)   (a, b) = (,)
                  <$> go t a <*> shfl_down r b offset 

    combines :: o -> o -> CodeGen PTX o
    combines = go token
      where
        go :: forall a b. TreeTokenContent aenv a b -> b -> b -> CodeGen PTX b
        go Leaf              ()     ()     = return ()
        go (Skip t)          (x, a) (y, _) = (,a) <$> go t x y
        go (ScanT _ c _ d t) (x, a) (y, b) = (,)  <$> go t x y <*> case d of
          LeftToRight ->                                           app2 c a b
          RightToLeft ->                                           app2 c b a
        go (FoldT _ c _ t)   (x, a) (y, b) = (,)  <$> go t x y <*> app2 c a b
