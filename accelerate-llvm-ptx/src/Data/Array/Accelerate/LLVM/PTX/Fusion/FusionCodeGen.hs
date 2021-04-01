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



-- | This produces output elements, doesn't write them to output arrays yet!
compile :: FusedAcc aenv i o -> i -> CodeGen PTX o
compile (Leaf f) i = f i

compile (Branch c l r) totalIn = do
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


