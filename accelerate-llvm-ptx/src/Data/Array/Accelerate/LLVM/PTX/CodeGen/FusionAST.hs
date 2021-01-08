{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
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
  -- | Semicolon or cons: puts a single token in front of the list
  Sequence   :: Fused TOKEN aenv a b -> Fused FUSED aenv b c -> Fused FUSED aenv a c

  -- | Empty program, end of the list
  EndOfFused :: o :> o'                                      -> Fused FUSED aenv o o'

  -- | Some LLVM, representing non-tree things. Produces a single result on top of the tuplist.
  BaseToken  :: IsTupList i => (i -> CodeGen PTX o)          -> Fused TOKEN aenv i (i, o)

  -- | Any number of folds and scans that get loop-fused (horizontally).
  -- Produces many results, and TreeTokenContent innately has weakening.
  TreeToken  :: TreeTokenContent aenv i o                    -> Fused TOKEN aenv i o

data TOKEN
data FUSED
type FusedAcc = Fused FUSED



-- | Gathers a bunch of tree-like traversals to be horizontally fused.
-- The scans and folds are at the block-level: Compiling this takes
-- care of the warp- and block-level but doesn't scan/fold the entire
-- array, as we're generating a single kernel.
--
--   vertical loop fusion of trees is not possible,
--   vertical kernel fusion is done by sequencing tree tokens

data TreeTokenContent aenv i o where
  Leaf  :: TreeTokenContent aenv ()      ()

  -- TODO rename?
  Skip  :: TreeTokenContent aenv  x       y  
        -> TreeTokenContent aenv (x, a)  (y, a)

  ScanT :: TypeR a -> IRFun2 PTX aenv (a -> a -> a) -> Maybe (Operands a) -> Direction
        -> TreeTokenContent aenv (x, Operands a)  y
        -> TreeTokenContent aenv (x, Operands a) (y, Operands a) 
  
  FoldT :: TypeR a -> IRFun2 PTX aenv (a -> a -> a) -> Maybe (Operands a) 
        -> TreeTokenContent aenv (x, Operands a)  y
        -> TreeTokenContent aenv (x, Operands a) (y, Operands a)



-- | Defunctionalised weakening for tuplists.
data (:>) big small where
  End  ::           ()     :> ()
  Toss :: b :> s -> (b, x) :>  s
  Keep :: b :> s -> (b, x) :> (s, x)


-- | Describes tuplists. Avoid adding `IsTupList` constraints to everything,
-- instead use `mkProof` and `mkProof'`.
class IsTupList a where
  tupListProof :: Either (a :~: ()) (TupListProof a)
  
  identityW :: a :> a
  emptyW :: a :> ()

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

mkProofT :: TreeTokenContent aenv a b -> IsTupListProof a
mkProofT Leaf             = P Refl
mkProofT (Skip          t) = case mkProofT t of P Refl -> P Refl
mkProofT (ScanT _ _ _ _ t) = case mkProofT t of P Refl -> P Refl
mkProofT (FoldT _ _ _   t) = case mkProofT t of P Refl -> P Refl

mkProofT' :: TreeTokenContent aenv a b -> IsTupListProof b
mkProofT' Leaf              = P Refl
mkProofT' (Skip          t) = case mkProofT' t of P Refl -> P Refl
mkProofT' (ScanT _ _ _ _ t) = case mkProofT' t of P Refl -> P Refl
mkProofT' (FoldT _ _ _   t) = case mkProofT' t of P Refl -> P Refl
