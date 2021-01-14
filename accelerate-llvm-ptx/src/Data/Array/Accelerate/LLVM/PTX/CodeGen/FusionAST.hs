{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
module Data.Array.Accelerate.LLVM.PTX.CodeGen.FusionAST where


import Data.Array.Accelerate.LLVM.CodeGen.Monad
import Data.Array.Accelerate.LLVM.PTX.Target
import Data.Array.Accelerate.AST (Direction)
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.LLVM.CodeGen.IR
import Data.Array.Accelerate.LLVM.CodeGen.Sugar
import Data.Type.Equality


data Fused t aenv i o where
  -- | Semicolon or cons: puts a single token in front of the list.
  Sequence   :: Fused TOKEN aenv a b -> Fused FUSED aenv b c -> Fused FUSED aenv a c

  -- | Empty program, end of the list.
  EndOfFused :: o :> o'                                      -> Fused FUSED aenv o o'

  -- | Some LLVM, representing non-tree things. Produces a single result on top of the tuplist.
  -- These don't use shared memory, so we can compose them easily.
  BaseToken  :: IsTupList i => (i -> CodeGen PTX o)          -> Fused TOKEN aenv i (i, o)

  -- | Any number of folds and scans that get loop-fused (horizontally).
  -- Produces many results, and TreeToken innately has weakening.
  TreeToken  :: TreeToken aenv i o                           -> Fused TOKEN aenv i o

data TOKEN
data FUSED
type FusedAcc = Fused FUSED



-- | Defunctionalised weakening for tuplists.
data (:>) big small where
  End  ::           ()     :> ()
  Toss :: b :> s -> (b, x) :>  s
  Keep :: b :> s -> (b, x) :> (s, x)



-- | Gathers a bunch of tree-like traversals to be horizontally fused.
-- The scans and folds are at the block-level: Compiling this takes
-- care of the warp- and block-level but doesn't scan/fold the entire
-- array, as we're generating a single kernel.
--
--   vertical loop fusion of trees is not possible,
--   vertical kernel fusion is done by sequencing tree tokens

-- TODO perhaps, we should remove the initial elements from the trees
-- and instead make separate `kernels` (which will compile to BaseTokens
-- that are fusible with the corresponding treetokens) that (add an element
-- and) map the combination with the treetoken over the result
data TreeToken aenv i o where
  Leaf  :: TreeToken aenv ()      ()

  -- TODO rename?
  Skip  :: TreeToken aenv  x       y
        -> TreeToken aenv (x, a)  (y, a)

  ScanT :: TypeR a -> IRFun2 PTX aenv (a -> a -> a) -> Maybe (Operands a)
        -> Direction -- It's possible that the entire TreeToken should have
        -- just one direction, or at least all scans/folds over the same input.
        -> TreeToken aenv (x, Operands a)  y
        -> TreeToken aenv (x, Operands a) (y, Operands a)

  FoldT :: TypeR a -> IRFun2 PTX aenv (a -> a -> a) -> Maybe (Operands a)
        -> TreeToken aenv (x, Operands a)  y
        -> TreeToken aenv (x, Operands a) (y, Operands a)


-- | Utility for TreeToken: Gives proof that
-- allows you to recursively consume scan/fold much
-- easier.
data TreeRefl b c = forall d. TreeRefl (c :~: (d, b))
mkRefl :: TreeToken aenv (a, b) c -> TreeRefl b c
mkRefl Skip {} = TreeRefl Refl
mkRefl ScanT{} = TreeRefl Refl
mkRefl FoldT{} = TreeRefl Refl




-- | Describes tuplists. Avoid adding `IsTupList` constraints to everything,
-- instead use `mkProof` and `mkProof'`.
class IsTupList a where
  tupListProof :: Either (a :~: ()) (TupListProof a)

  identityW :: a :> a
  emptyW    :: a :> ()

instance IsTupList () where
  tupListProof = Left Refl
  identityW = End
  emptyW = End

instance IsTupList y => IsTupList (y, x) where
  tupListProof = Right $ TupListProof Refl
  identityW = Keep identityW
  emptyW = Toss emptyW


data TupListProof a = forall b x. TupListProof (IsTupList b => (a :~: (b, x)))




data IsTupListProof a = forall b. IsTupList b => P (a :~: b)

mkProof :: a :> b -> IsTupListProof a
mkProof End      = P Refl
mkProof (Keep w) = case mkProof w of P Refl -> P Refl
mkProof (Toss w) = case mkProof w of P Refl -> P Refl

mkProof' :: a :> b -> IsTupListProof b
mkProof' End      = P Refl
mkProof' (Keep w) = case mkProof' w of P Refl -> P Refl
mkProof' (Toss w) = case mkProof' w of P Refl -> P Refl


---- not currently needed ----

mkProofT :: TreeToken aenv a b -> IsTupListProof a
mkProofT Leaf             = P Refl
mkProofT (Skip          t) = case mkProofT t of P Refl -> P Refl
mkProofT (ScanT _ _ _ _ t) = case mkProofT t of P Refl -> P Refl
mkProofT (FoldT _ _ _   t) = case mkProofT t of P Refl -> P Refl

mkProofT' :: TreeToken aenv a b -> IsTupListProof b
mkProofT' Leaf              = P Refl
mkProofT' (Skip          t) = case mkProofT' t of P Refl -> P Refl
mkProofT' (ScanT _ _ _ _ t) = case mkProofT' t of P Refl -> P Refl
mkProofT' (FoldT _ _ _   t) = case mkProofT' t of P Refl -> P Refl
