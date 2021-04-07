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
compile :: FusedAcc aenv i o -> i -> CodeGen PTX o
compile (Leaf f) i = f i

compile (Branch c l r) totalIn = do
  -- Within a kernel, we don't perform any loop-fusion anymore: this simply uses the 'leftI, rightI, totalO' combinators
  -- to thread the CodeGen state through the sub-branches.
  let leftIn = leftI c $:> totalIn
  leftOut <- compile l leftIn
  let rightIn = rightI c leftOut totalIn
  rightOut <- compile r rightIn
  return $ totalO c leftOut rightOut


-- | Applying a weakening on a tuplist
-- (could just as easily write an equivalent for `Data.Array.Accelerate.AST.Environment.Val`)
($:>) :: (a :> b) -> (a -> b)
End      $:> ()     = ()
(Toss w) $:> (y, _) =  w $:> y
(Keep w) $:> (y, x) = (w $:> y, x)


