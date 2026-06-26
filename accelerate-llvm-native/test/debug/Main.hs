-- |
-- Module      : nofib-llvm-native
-- Copyright   : [2017..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
--
-- Portability : non-portable (GHC extensions)
{-# LANGUAGE TypeApplications #-}
module Main where

import Data.Array.Accelerate
import qualified Data.Array.Accelerate.LLVM.Native as CPU
import Prelude (print)
main = print $ CPU.runN p2 as -- bs

p1 :: Acc (Scalar Int)
p1 = fold (+) 0 $ map (+1) $ generate (Z_ ::. 30) (\(I1 x) -> x)

p2 = zipWith max xs -- ys
xs = generate (Z_ ::. 30 ::. 10) (\(I2 x _) -> x)
ys = generate (Z_ ::. 30 ::. 10) (\(I2 _ x) -> x+2)
as = fromList (Z :. 30 :. 10) [1..]
bs = fromList (Z :. 30 :. 10) [3 :: Int ..]
