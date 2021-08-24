{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}
module Data.Array.Accelerate.LLVM.PTX.Fusion.FusionAST where


import Data.Array.Accelerate.LLVM.CodeGen.Monad
import Data.Array.Accelerate.LLVM.PTX.Target
import Prelude hiding (take)
import Data.Bifunctor
import Data.Array.Accelerate.LLVM.PTX.StuffFromAccNewPipeline

data FusedAcc i o where
  Leaf :: (i -> CodeGen PTX o) -> FusedAcc i o

  Branch :: Combine' li lo ri ro ti to
         -> FusedAcc li lo
         -> FusedAcc       ri ro
         -> FusedAcc             ti to

-- | Defunctionalised weakening for tuplists.
data (:>) big small where
  End  ::           ()     :> ()
  Toss :: b :> s -> (b, x) :>  s
  Keep :: b :> s -> (b, x) :> (s, x)


-- `a` is always an "Operands x" here
data Combine' leftI leftO rightI rightO totalI totalO where
  Combine' :: Combine' () () () () () ()

  Vertical'   :: Take a loa lo -> Take a ria ri
              -> Combine' li  lo  ri  ro  ti  to
              -> Combine' li  loa ria ro  ti  to

  Diagonal'   :: Take a loa lo -> Take a ria ri -> Take a toa to
              -> Combine' li  lo  ri  ro  ti  to
              -> Combine' li  loa ria ro  ti  toa

  Horizontal' :: Take a lia li -> Take a ria ri -> Take a tia ti
              -> Combine' li  lo  ri  ro  ti  to
              -> Combine' lia lo  ria ro  tia to

  -- this one is weird: do you pick the left or the right output? 
  -- probably change Combine' in acc/new-pipeline to exclude it
  -- HorizontalO :: Combine' li  lo    ri  ro    ti  to
  --             -> Combine' li (lo,a) ri (ro,a) ti (to,a)

  WeakRightI :: Take a lia li -> Take a tia ti
             -> Combine' li  lo  ri  ro  ti  to
             -> Combine' lia lo  ri  ro  tia to
  WeakRightO :: Take a loa lo -> Take a toa to
             -> Combine' li  lo  ri  ro  ti  to
             -> Combine' li  loa ri  ro  ti  toa

  WeakLeftI :: Take a ria ri -> Take a tia ti
            -> Combine' li  lo ri  ro  ti  to
            -> Combine' li  lo ria ro  tia to
  WeakLeftO :: Take a roa ro -> Take a toa to
            -> Combine' li  lo ri  ro  ti  to
            -> Combine' li  lo ri  roa ti  toa

-- the left input is a subset of the total input
leftI :: Combine' li a b c ti d -> ti :> li
leftI Combine'                 = End
leftI (Vertical'   t1 t2    c) =                  leftI c
leftI (Diagonal'   t1 t2 t3 c) =                  leftI c
leftI (Horizontal' t1 t2 t3 c) = twoTakes t3 t1 $ leftI c
leftI (WeakRightI  t1 t2    c) = twoTakes t2 t1 $ leftI c
leftI (WeakRightO  t1 t2    c) =                  leftI c
leftI (WeakLeftI   t1 t2    c) = fromTake t2    $ leftI c
leftI (WeakLeftO   t1 t2    c) =                  leftI c

-- the right output is a subset of the total output
rightO :: Combine' a b c ro d to -> to :> ro
rightO Combine'                 = End
rightO (Vertical'   t1 t2    c) =                  rightO c
rightO (Diagonal'   t1 t2 t3 c) = fromTake t3    $ rightO c
rightO (Horizontal' t1 t2 t3 c) =                  rightO c
rightO (WeakRightI  t1 t2    c) =                  rightO c
rightO (WeakRightO  t1 t2    c) = fromTake t2    $ rightO c
rightO (WeakLeftI   t1 t2    c) =                  rightO c
rightO (WeakLeftO   t1 t2    c) = twoTakes t2 t1 $ rightO c

-- the right input can be constructed from the total input and left output
rightI :: Combine' a lo ri b ti c -> (lo -> ti -> ri)
rightI Combine'                 = \() ()                   -> ()
rightI (Vertical'   t1 t2    c) = \(take t1 -> (a, lo)) ti -> put t2 a (rightI c lo ti)
rightI (Diagonal'   t1 t2 t3 c) = \(take t1 -> (a, lo)) ti -> put t2 a (rightI c lo ti)
rightI (Horizontal' t1 t2 t3 c) = \lo (take t3 -> (a, ti)) -> put t2 a (rightI c lo ti)
rightI (WeakRightI  t1 t2    c) = \lo (take t2 -> (_, ti)) ->           rightI c lo ti
rightI (WeakRightO  t1 t2    c) = \(take t1 -> (_, lo)) ti ->           rightI c lo ti
rightI (WeakLeftI   t1 t2    c) = \lo (take t2 -> (a, ti)) -> put t1 a (rightI c lo ti)
rightI (WeakLeftO   t1 t2    c) = \lo ti                   ->           rightI c lo ti

-- the total output can be constructed from the other outputs
totalO :: Combine' a lo b ro c to -> (lo -> ro -> to)
totalO Combine'                 = \() ()      -> ()
totalO (Vertical'   t1 t2    c) = \(take t1 -> (_, lo)) ro ->           totalO c lo ro
totalO (Diagonal'   t1 t2 t3 c) = \(take t1 -> (a, lo)) ro -> put t3 a (totalO c lo ro)
totalO (Horizontal' t1 t2 t3 c) = \lo ro                   ->           totalO c lo ro
totalO (WeakRightI  t1 t2    c) = \lo ro                   ->           totalO c lo ro
totalO (WeakRightO  t1 t2    c) = \(take t1 -> (a, lo)) ro -> put t2 a (totalO c lo ro)
totalO (WeakLeftI   t1 t2    c) = \lo ro                   ->           totalO c lo ro
totalO (WeakLeftO   t1 t2    c) = \lo (take t1 -> (a, ro)) -> put t2 a (totalO c lo ro)

take :: Take a ab b -> ab -> (a, b)
take Here (b, a) = (a, b)
take (There t) (ab', c) = second (,c) $ take t ab'

put :: Take a ab b -> a -> b -> ab
put Here a b = (b, a)
put (There t) a (b, c) = (put t a b, c)

fromTake :: Take a ab b -> b :> x -> ab :> x
fromTake Here bx = Toss bx
fromTake (There t) (Toss bx) = Toss (fromTake t bx)
fromTake (There t) (Keep bx) = Keep (fromTake t bx)

fromTake' :: Take a ab b -> x :> ab -> x :> b
fromTake' t         (Toss x) = Toss (fromTake' t x)
fromTake' Here      (Keep x) = Toss x
fromTake' (There t) (Keep x) = Keep (fromTake' t x)

-- Can't really write this function, because the :> datatype encodes that not only is
-- c 'contained' in b, but also in the same order. The `Take`s don't respect this order.
-- despite being impossible, this seems like a very minor hurdle and just a sign of friction
-- between multiple attempts. A rewrite of one or two datatypes should fix this,
-- perhaps we simply put Take in :>'s constructors (making this function trivial).
twoTakes :: Take a ab b -> Take a ac c -> b :> c -> ab :> ac
twoTakes = undefined


makeCombine :: LeftHandSideArgs body i scope
            -> Combine' (ToIn body) (ToOut body) scope o i o
makeCombine Base = _ -- bunch of WeakLeftO's on top of the base case, can't implement without a typeclass of 'tuples on top of unit'
makeCombine (Reqr ta ta' lhsa) = Horizontal' Here ta' ta (makeCombine lhsa)
makeCombine (Make ta lhsa) = Vertical' Here ta (makeCombine lhsa)
makeCombine (Adju ta ta' lhsa) = undefined -- TODO mut
makeCombine (EArg lhsa) = WeakLeftI Here Here (makeCombine lhsa)
makeCombine (Ignr lhsa) = WeakLeftI Here Here (makeCombine lhsa)


compile' :: ClusterAST op i o -> FusedAcc i o
compile' None = Leaf pure
compile' (Bind lhs op ast) = Branch (makeCombine lhs) (compileOp op) (compile' ast)

compileOp :: op body -> FusedAcc (ToIn body) (ToOut body)
compileOp = undefined -- implement all primitives

type family ToIn  a where
  ToIn  ()              = ()
  ToIn  (In sh e  -> x) = (ToIn x, e)
  ToIn  (Mut sh e -> x) = (ToIn x, e)
  ToIn  (_ -> x)        =  ToIn x
type family ToOut a where
  ToOut ()              = ()
  ToOut (Out sh e -> x) = (ToOut x, e)
  ToOut (Mut sh e -> x) = (ToOut x, e)
  ToOut (_  -> x)       =  ToOut x

-----------
-- from acc/new-pipeline


-- | A cluster of operations, in total having `args` as signature
data Cluster op args where
  Cluster :: ClusterIO args input output
          -> ClusterAST op  input output
          -> Cluster op args

-- | Internal AST of `Cluster`, simply a list of let-bindings.
-- Note that all environments hold scalar values, not arrays!
data ClusterAST op env result where
  None :: ClusterAST op env env
  -- `Bind _ x y` reads as `do x; in the resulting environment, do y`
  Bind :: LeftHandSideArgs body env scope
       -> op body
       -> ClusterAST op scope result
       -> ClusterAST op env   result

-- | A version of `LeftHandSide` that works on the function-separated environments: 
-- Given environment `env`, we can execute `body`, yielding environment `scope`.
data LeftHandSideArgs body env scope where
  -- Because of `Ignr`, we could also give this the type `LeftHandSideArgs () () ()`.
  Base :: LeftHandSideArgs () () ()
  -- The body has an input array
  Reqr :: Take e eenv env -> Take e escope scope
       -> LeftHandSideArgs              body   env      scope
       -> LeftHandSideArgs (In  sh e -> body) eenv     escope
  -- The body creates an array
  Make :: Take e escope scope
       -> LeftHandSideArgs              body   env      scope
       -> LeftHandSideArgs (Out sh e -> body)  env     escope
  -- One array that is both input and output
  Adju :: Take e eenv env -> Take e escope scope
       -> LeftHandSideArgs              body   env      scope
       -> LeftHandSideArgs (Mut sh e -> body) eenv     escope
  -- Holds `Var' e`, `Exp' e`, `Fun' e`: The non-array Arg options.
  -- Behaves like `In` arguments.
  EArg :: LeftHandSideArgs              body   env      scope
       -> LeftHandSideArgs (Exp    e -> body) (env, e) (scope, e)
  -- Does nothing to this part of the environment
  Ignr :: LeftHandSideArgs              body   env      scope
       -> LeftHandSideArgs              body  (env, e) (scope, e)

data ClusterIO args input output where
  Empty  :: ClusterIO () () output
  Input  :: ClusterIO              args   input      output
         -> ClusterIO (In  sh e -> args) (input, e) (output, e)
  Output :: Take e eoutput output
         -> ClusterIO              args   input      output
         -> ClusterIO (Out sh e -> args)  input     eoutput
  MutPut :: Take e eoutput output
         -> ClusterIO              args   input      output
         -> ClusterIO (Mut sh e -> args) (input, e) eoutput
  -- Contract: Only use this for `Var`, `Exp`, `Fun` args;
  -- don't abuse as backdoor with in/out/mut
  ExpPut :: ClusterIO              args   input      output
         -> ClusterIO (Exp    e -> args) (input, e) (output, e)

-- | `xargs` is a type-level list which contains `x`. 
-- Removing `x` from `xargs` yields `args`.
data Take x xargs args where
  Here  :: Take x ( args, x)  args
  There :: Take x  xargs      args
        -> Take x (xargs, y) (args, y)


-- data Combine left right result where
--   Combine :: Combine () () ()
--   -- An array is produced and consumed, fusing it away.
--   -- NOTE: this means that the array does not appear in the environment, and
--   -- it does not have an accompanying `Arg` constructor: Its scope is now
--   -- bound by this `Node` constructor in `Cluster`.
--   Vertical  :: Combine              a              b               c
--             -> Combine (Out sh e -> a) (In sh e -> b)              c

--   -- Like vertical, but the arg is stored for later use
--   Diagonal  :: Combine              a              b               c
--             -> Combine (Out sh e -> a) (In sh e -> b) (Out sh e -> c)

--   -- Both computations use the argument in the same fashion.
--   -- Note that you can't recreate this type using WeakLeft and WeakRight,
--   -- as that would duplicate the argument in the resulting type.
--   -- Note also that it doesn't make too much sense to horizontally fuse output arguments.
--   Horizontal :: Combine       a        b        c
--              -> Combine (In sh e -> a) (In sh e -> b) (In sh e -> c)

--   -- Only the right computation uses x, so this 'weakens' the left computation
--   WeakLeft  :: Combine       a       b        c
--             -> Combine       a (x -> b) (x -> c)
--   -- Mirror of WeakLeft
--   WeakRight :: Combine       a       b        c
--             -> Combine (x -> a)      b  (x -> c)

data Exp e
