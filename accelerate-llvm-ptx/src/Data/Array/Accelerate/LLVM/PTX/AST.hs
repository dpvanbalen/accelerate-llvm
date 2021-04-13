{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE GADTs #-}
module Data.Array.Accelerate.LLVM.PTX.AST where
import Data.Array.Accelerate.LLVM.PTX.StuffFromAccNewPipeline



data PTXAST args where
  -- might delete Map and Backpermute, if they end up with no advantage over Transform. Perhaps Map fuses better than Transform?
  Map :: Arg env (Fun' (a -> b))
      -> Arg env (In  sh a)
      -> Arg env (Out sh b)
      -> PTXAST ( Fun' (a -> b)
               -> In  sh a
               -> Out sh b
               -> ())

  Backpermute :: Arg env (Fun' (sh2 -> sh1))
              -> Arg env (In  sh1 a)
              -> Arg env (Out sh2 a)
              -> PTXAST ( Fun' (sh2 -> sh1)
                       -> In  sh1 a
                       -> Out sh2 a
                       -> ())

  Transform :: PTXAST ()
  Generate :: PTXAST ()
  Shrink :: PTXAST () -- like 'Map', the main advantage I can see this having is retaining more information for the ILP. Either toss it now, or desugar later (e.g. at codegen time)
  -- Copy?
  ZipWith :: PTXAST ()
  Replicate :: PTXAST () -- as Shrink
  Slice :: PTXAST () -- as Shrink
  Permute :: PTXAST ()
  Stencil :: PTXAST ()
  Stencil2 :: PTXAST ()

  -- fold variants
  FoldDim :: PTXAST () -- Reduce along the innermost dimension of a higher-dimensional array. Old pipeline always does this in 1 kernel, with a threadblock per resulting element. Can be done better, depending on exact dimensions.
  FoldAllWarp :: PTXAST () -- 1-dimensional array reduction. For small arrays, this will be done in a single kernel. Larger ones will need repeated invocations until it fits in 1 threadblock
  FoldAllBlock :: PTXAST ()

  -- scan variants
  ScanDim :: PTXAST () -- Scan along the innermost dimension. As FoldDim.

  -- TODO: Determine exactly what the responsibilities of 1 and 2 are. Is upsweep only warp-level, or also within blocks? etc
  -- TODO: Do we want Tijns single-pass version instead?
  ScanAll1 :: PTXAST () -- First step of scanning a 1-dimensional array: upsweep
  ScanAll2 :: PTXAST () -- Step 2 of scanall: compute carry-in (Recursive? Or forced single-block size?)
  ScanAllMap :: PTXAST () -- Final step of scanning a 1-dimensional array: apply the carry-in.


instance DesugarAcc PTXAST where
  mkMap         f i o = Exec (Map         f i o) $ f :>: i :>: o :>: ArgsNil
  mkBackpermute f i o = Exec (Backpermute f i o) $ f :>: i :>: o :>: ArgsNil


instance MakesILP PTXAST where
  type BackendVar PTXAST = () -- choose a nice variable type to make fusion constraints
  mkGraph :: op args -> LabelArgs args -> Label -> Information ilp op
  mkGraph = undefined
