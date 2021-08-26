{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GADTs #-}
module Data.Array.Accelerate.LLVM.PTX.Fusion.FusionCodeGen
  ( compile
  ) where

import Data.Array.Accelerate.LLVM.CodeGen.Monad
import Data.Array.Accelerate.LLVM.PTX.Target
import Data.Array.Accelerate.LLVM.PTX.Fusion.FusionAST
-- import Data.Array.Accelerate.LLVM.PTX.Fusion.TreeCodeGen



-- | This makes the 'body' of a kernel: still need to read all inputs from the arrays and write all outputs to them.
-- 'inplace updates' are performed by simply assigning one array to be both input and output.
-- Within a kernel, we don't perform any loop-fusion anymore: this simply uses the 'leftI, rightI, totalO' combinators
-- to thread the CodeGen state through the sub-branches.
-- TODO: not doing loop fusion means we do some excess synchronisations (between warp-level and block-level scans/folds).
-- A middleground would be to split each fold/scan into two 'black boxes' (before and after sync), and interleave those
-- where possible (i.e. if there is no vertical dependancy)
compile :: ClusterAST op i o -> i -> CodeGen PTX o
compile None i = return i
compile (Bind lhs op c) i = compileBody op (getIn lhs i) >>= compile c . genOut lhs i
  where
    compileBody :: op body -> ToIn body -> CodeGen PTX (ToOut body)
    compileBody = _

