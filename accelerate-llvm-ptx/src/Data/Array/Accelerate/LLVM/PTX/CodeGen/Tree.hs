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
import Data.Type.Equality








compileTreeToken :: TreeTokenContent aenv ins outs -> ins -> CodeGen PTX outs
compileTreeToken = undefined 




treeWarpShfl
    :: forall aenv i o.
       DeviceProperties 
    -> TreeTokenContent aenv i o
    -> Either i o
    -> CodeGen PTX o
treeWarpShfl dev token eitherio = case eitherio of
              -- First call
              Left i -> gather i >>= tree 0
              
              -- Later calls
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
        -- I don't know if that is noticable, and if it even 
        -- matters without `free`ing the variables in between. 
        -- How does memory management work in CUDA?
        -- If this would have any performance benefit, it would
        -- surely be worth the effort!
        y  <- shuffles x offset
        x' <- combines x y
        tree (step + 1) x'


    -- | Separated from the loop, as it changes the size (and thus type)
    -- of the variables we're looking at (as a result of horizontal fusion).
    gather :: i -> CodeGen PTX o
    gather = go token
      where
        go :: TreeTokenContent aenv a b -> a -> CodeGen PTX b
        go Leaf () = return ()
        go (Skip t) (a, b) = (,b) <$> go t a
        go (ScanT _ _ _ _ t) a = case mkRefl t of
          TreeRefl Refl -> (\(x, y) -> ((x, y), y)) <$> go t a
        go (FoldT _ _ _ t) a = case mkRefl t of
          TreeRefl Refl -> (\(x, y) -> ((x, y), y)) <$> go t a

    shuffles :: Operands Word32 -> o -> CodeGen PTX o
    shuffles offset = go token
      where
        go :: TreeTokenContent aenv a b -> b -> CodeGen PTX b
        go Leaf              ()     = return ()
        go (Skip  t)         (a, b) = (,b) <$> go t a
        go (ScanT r _ _ _ t) (a, b) = (,)  <$> go t a <*> shfl_up   r b offset
        go (FoldT r _ _ t)   (a, b) = (,)  <$> go t a <*> shfl_down r b offset 

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


