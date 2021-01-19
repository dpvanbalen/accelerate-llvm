module Data.Array.Accelerate.LLVM.PTX.Fusion where


-- |A datatype representing `unfused kernels`: Parts of Accelerate AST terms that can be evaluated in a single kernel.
-- for example: folds/scans get split into 2/3 pieces, whilst `Map` does not need to change.
data SeparatedAcc a


-- |Describes how to translate Named.Acc into SeparatedAcc
-- instance DesugarAcc SeparatedAcc


-- instance ILP SeparatedAcc

