{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE GADTs #-}
module Data.Array.Accelerate.LLVM.PTX.Fusion.FusionAST where


import Data.Array.Accelerate.LLVM.CodeGen.Monad
import Data.Array.Accelerate.LLVM.PTX.Target


data FusedAcc aenv i o where
  Leaf :: (i -> CodeGen PTX o) -> FusedAcc aenv i o

  Branch :: Combine'       li lo ri ro ti to
         -> FusedAcc aenv li lo
         -> FusedAcc aenv       ri ro
         -> FusedAcc aenv             ti to

-- | Defunctionalised weakening for tuplists.
data (:>) big small where
  End  ::           ()     :> ()
  Toss :: b :> s -> (b, x) :>  s
  Keep :: b :> s -> (b, x) :> (s, x)


-- `a` is always an "Operands x" here
data Combine' leftI leftO rightI rightO totalI totalO where
  Combine' :: Combine' () () () () () ()

  Vertical'   :: Combine' li  lo     ri    ro ti to
              -> Combine' li (lo,a) (ri,a) ro ti to

  Diagonal'   :: Combine' li  lo     ri    ro ti  to
              -> Combine' li (lo,a) (ri,a) ro ti (to,a)

  Horizontal' :: Combine'  li    lo  ri    ro  ti    to
              -> Combine' (li,a) lo (ri,a) ro (ti,a) to

  -- this one is weird: do you pick the left or the right output? 
  -- probably change Combine' in acc/new-pipeline to exclude it
  -- HorizontalO :: Combine' li  lo    ri  ro    ti  to
  --             -> Combine' li (lo,a) ri (ro,a) ti (to,a)

  WeakRightI :: Combine'  li    lo ri ro  ti    to
             -> Combine' (li,a) lo ri ro (ti,a) to
  WeakRightO :: Combine' li  lo    ri ro ti  to
             -> Combine' li (lo,a) ri ro ti (to,a)

  WeakLeftI :: Combine' li lo  ri    ro  ti    to
            -> Combine' li lo (ri,a) ro (ti,a) to
  WeakLeftO :: Combine' li lo ri  ro    ti  to
            -> Combine' li lo ri (ro,a) ti (to,a)

-- the left input is a subset of the total input
leftI :: Combine' li a b c ti d -> ti :> li
leftI Combine'        = End
leftI (Vertical'   c) =        leftI c
leftI (Diagonal'   c) =        leftI c
leftI (Horizontal' c) = Keep $ leftI c
leftI (WeakRightI  c) = Keep $ leftI c
leftI (WeakRightO  c) =        leftI c
leftI (WeakLeftI   c) = Toss $ leftI c
leftI (WeakLeftO   c) =        leftI c

-- the right output is a subset of the total output
rightO :: Combine' a b c ro d to -> to :> ro
rightO Combine'        = End
rightO (Vertical'   c) =        rightO c
rightO (Diagonal'   c) = Toss $ rightO c
rightO (Horizontal' c) =        rightO c
rightO (WeakRightI  c) =        rightO c
rightO (WeakRightO  c) = Toss $ rightO c
rightO (WeakLeftI   c) =        rightO c
rightO (WeakLeftO   c) = Keep $ rightO c

-- the right input can be constructed from the total input and left output
rightI :: Combine' a lo ri b ti c -> (lo -> ti -> ri)
rightI Combine'        = \() ()      -> ()
rightI (Vertical'   c) = \(lo, a) ti -> (rightI c lo ti, a)
rightI (Diagonal'   c) = \(lo, a) ti -> (rightI c lo ti, a)
rightI (Horizontal' c) = \lo (ti, a) -> (rightI c lo ti, a)
rightI (WeakRightI  c) = \lo (ti, _) ->  rightI c lo ti
rightI (WeakRightO  c) = \(lo, _) ti ->  rightI c lo ti
rightI (WeakLeftI   c) = \lo (ti, a) -> (rightI c lo ti, a)
rightI (WeakLeftO   c) = \lo ti      ->  rightI c lo ti

-- the total output can be constructed from the other outputs
totalO :: Combine' a lo b ro c to -> (lo -> ro -> to)
totalO Combine'        = \() ()      -> ()
totalO (Vertical'   c) = \(lo, _) ro ->  totalO c lo ro
totalO (Diagonal'   c) = \(lo, a) ro -> (totalO c lo ro, a)
totalO (Horizontal' c) = \lo ro      ->  totalO c lo ro
totalO (WeakRightI  c) = \lo ro      ->  totalO c lo ro
totalO (WeakRightO  c) = \(lo, a) ro -> (totalO c lo ro, a)
totalO (WeakLeftI   c) = \lo ro      ->  totalO c lo ro
totalO (WeakLeftO   c) = \lo (ro, a) -> (totalO c lo ro, a)


lowerCombine :: Combine left right result -> Combine' (ToIn left)   (ToOut left)
                                                      (ToIn right)  (ToOut right)
                                                      (ToIn result) (ToOut result)
lowerCombine Combine        = Combine'
lowerCombine (Vertical   c) = Vertical'   $ lowerCombine c
lowerCombine (Diagonal   c) = Diagonal'   $ lowerCombine c
lowerCombine (Horizontal c) = Horizontal' $ lowerCombine c
lowerCombine (WeakLeft   c) = _
lowerCombine (WeakRight  c) = _

type family ToIn  a where
  ToIn ()              = ()
  ToIn (In sh e  -> x) = (ToIn x, e)
  ToIn (Out sh e -> x) =  ToIn x
type family ToOut a where
  ToOut ()              = ()
  ToOut (In sh e  -> x) =  ToOut x
  ToOut (Out sh e -> x) = (ToOut x, e)

-----------
-- from acc/new-pipeline

data Combine left right result where
  Combine :: Combine () () ()
  -- An array is produced and consumed, fusing it away.
  -- NOTE: this means that the array does not appear in the environment, and
  -- it does not have an accompanying `Arg` constructor: Its scope is now
  -- bound by this `Node` constructor in `Cluster`.
  Vertical  :: Combine              a              b               c
            -> Combine (Out sh e -> a) (In sh e -> b)              c

  -- Like vertical, but the arg is stored for later use
  Diagonal  :: Combine              a              b               c
            -> Combine (Out sh e -> a) (In sh e -> b) (Out sh e -> c)

  -- Both computations use the argument in the same fashion.
  -- Note that you can't recreate this type using WeakLeft and WeakRight,
  -- as that would duplicate the argument in the resulting type.
  -- Note also that it doesn't make too much sense to horizontally fuse output arguments.
  Horizontal :: Combine       a        b        c
             -> Combine (In sh e -> a) (In sh e -> b) (In sh e -> c)

  -- Only the right computation uses x, so this 'weakens' the left computation
  WeakLeft  :: Combine       a       b        c
            -> Combine       a (x -> b) (x -> c)
  -- Mirror of WeakLeft
  WeakRight :: Combine       a       b        c
            -> Combine (x -> a)      b  (x -> c)

data Out sh e
data In sh e