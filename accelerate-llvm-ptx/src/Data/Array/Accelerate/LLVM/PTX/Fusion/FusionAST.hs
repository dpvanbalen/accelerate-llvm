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


take :: Take a ab b -> ab -> (a, b)
take Here (b, a) = (a, b)
take (There t) (ab', c) = second (,c) $ take t ab'

put :: Take a ab b -> a -> b -> ab
put Here a b = (b, a)
put (There t) a (b, c) = (put t a b, c)

type family ToIn  a where
  ToIn  ()              = ()
  ToIn  (In sh e  -> x) = (ToIn x, e)
  ToIn  (Mut sh e -> x) = (ToIn x, e)
  ToIn  (Exp    e -> x) = (ToIn x, e)
  ToIn  (_ -> x)        =  ToIn x
type family ToOut a where
  ToOut ()              = ()
  ToOut (Out sh e -> x) = (ToOut x, e)
  ToOut (Mut sh e -> x) = (ToOut x, e)
  ToOut (_  -> x)       =  ToOut x

getIn :: LeftHandSideArgs body i o -> i -> ToIn body
getIn Base () = ()
getIn (Reqr t1 t2 lhs) i = let (x, i') = take t1 i in (getIn lhs i', x)
getIn (Make t lhs) i = getIn lhs i
getIn (Adju t1 t2 lhs) i = let (x, i') = take t1 i in (getIn lhs i', x)
getIn (EArg lhs) (i, x) = (getIn lhs i, x)
getIn (Ignr lhs) (i, x) =  getIn lhs i

genOut :: LeftHandSideArgs body i o -> i -> ToOut body -> o
genOut Base             ()    o     = 
  ()
genOut (Reqr t1 t2 lhs) i     o     = 
  let (x, i') = take t1 i 
  in put t2 x (genOut lhs i' o)
genOut (Make t lhs)     i    (o, x) = 
  put t x (genOut lhs i o)
genOut (Adju t1 t2 lhs) i    (o, x) = 
  let (y, i') = take t1 i 
  in put t2 x (genOut lhs i' o)
genOut (EArg lhs)      (i, x) o     =
  (genOut lhs i o, x)
genOut (Ignr lhs)      (i, x) o     =
  (genOut lhs i o, x)


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
