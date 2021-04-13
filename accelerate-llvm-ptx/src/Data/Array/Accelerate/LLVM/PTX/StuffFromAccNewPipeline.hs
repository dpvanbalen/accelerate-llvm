{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
module Data.Array.Accelerate.LLVM.PTX.StuffFromAccNewPipeline where

-- once accelerate/new-pipeline compiles, delete this and do good imports




import qualified Data.Array.Accelerate.AST.Var as Var
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Array.Unique
import Data.Array.Accelerate.Array.Data
import Data.Array.Accelerate.Analysis.Match
import Data.Array.Accelerate.AST hiding (PreOpenAcc)
import Data.Array.Accelerate.Representation.Array
import Data.Kind ( Type )
import Data.Array.Accelerate.Sugar.Foreign
import Data.Array.Accelerate.Representation.Shape
import Data.Array.Accelerate.Representation.Stencil
import Data.Array.Accelerate.Representation.Slice
import qualified Data.Set as S
import Data.Set (Set)
import qualified Data.Map as M

infixr :>:
data PreArgs a t where
  ArgsNil :: PreArgs a ()
  (:>:)   :: a s -> PreArgs a t -> PreArgs a (s -> t)

-- | A single argument to an operation.
--
data Arg env t where
  ArgVar      :: ExpVars env e         -> Arg env (Var' e)

  ArgExp      :: Exp env e             -> Arg env (Exp' e)

  ArgFun      :: Fun env e             -> Arg env (Fun' e)

  -- | An array is represented as scalar variables denoting the size and buffer variables.
  -- We assume that all the buffer variables stored in 'ArgBuffers' have the same size,
  -- as specified by the scalar variables of the size.
  --
  ArgArray    :: Modifier m
              -> ArrayR (Array sh e)
              -> GroundVars env sh
              -> GroundVars env (Buffers e)
              -> Arg env (m sh e)

-- | The arguments to be passed to an operation, in some environment.
--
type Args env = PreArgs (Arg env)

-- | Array arguments are annotated with an access modifier
--
data Modifier m where
  -- | The operation only reads from this array
  In  :: Modifier In
  -- | The operation only writes to the array. The initial content of the array is thus irrelevant
  Out :: Modifier Out
  -- | The operation both reads and writes to the array.
  Mut :: Modifier Mut

-- Empty data types, which are only used for the types of 'Arg'.
data Var' e   where
data Exp' e   where
data Fun' t   where
data In  sh e where
data Out sh e where
data Mut sh e where


-- | Ground values are buffers or scalars.
--
data GroundR a where
  GroundRbuffer :: ScalarType e -> GroundR (Buffer e)
  GroundRscalar :: ScalarType e -> GroundR e

-- | Tuples of ground values
--
type GroundsR = TupR GroundR

-- | Types for local bindings
--
type GLeftHandSide = LeftHandSide GroundR
type GroundVar      = Var.Var  GroundR
type GroundVars env = Var.Vars GroundR env


newtype Buffer e = Buffer (UniqueArray (ScalarArrayDataR e))
type Buffers e = Distribute Buffer e

type family Distribute f a = b where
  Distribute f () = ()
  Distribute f (a, b) = (Distribute f a, Distribute f b)
  Distribute f a = f a

class Distributes s where
  -- Shows that a single element isn't unit or a pair
  reprIsSingle :: s t -> Distribute f t :~: f t


class DesugarAcc (op :: Type -> Type) where
  mkMap         :: Arg env (Fun' (s -> t))
                -> Arg env (In sh s)
                -> Arg env (Out sh t)
                -> OperationAcc op env ()

  mkBackpermute :: Arg env (Fun' (sh' -> sh))
                -> Arg env (In sh t)
                -> Arg env (Out sh' t)
                -> OperationAcc op env ()

  mkTransform   :: Arg env (Fun' (sh' -> sh))
                -> Arg env (Fun' (s -> t))
                -> Arg env (In sh s)
                -> Arg env (Out sh' t)
                -> OperationAcc op env ()

  mkGenerate    :: Arg env (Fun' (sh -> t))
                -> Arg env (Out sh t)
                -> OperationAcc op env ()

  -- Copies the contents of the (prefix of the) input to the output.
  -- The size of the input array is smaller than or equal to the size output.
  mkShrink      :: Arg env (In  sh t)
                -> Arg env (Out sh t)
                -> OperationAcc op env ()
 
  -- Copies a buffer. This is used before passing a buffer to a 'Mut' argument,
  -- to make sure it is unique. This may be removed during fusion to facilitate
  -- in-place updates
  -- TODO: Perform one map per buffer, instead of one for the whole array?
  mkCopy        :: Arg env (In  sh t)
                -> Arg env (Out sh t)
                -> OperationAcc op env ()
 
  mkZipWith     :: Arg env (Fun' (e1 -> e2 -> e3))
                -> Arg env (In  sh e1)
                -> Arg env (In  sh e2)
                -> Arg env (Out sh e3)
                -> OperationAcc op env ()

  mkReplicate   :: SliceIndex slix sl co sh
                -> Arg env (Var' slix)
                -> Arg env (In  sl e)
                -> Arg env (Out sh e)
                -> OperationAcc op env ()

  mkSlice       :: SliceIndex slix sl co sh
                -> Arg env (Var' slix)
                -> Arg env (In  sh e)
                -> Arg env (Out sl e)
                -> OperationAcc op env ()

  mkPermute     :: Arg env (Fun' (e -> e -> e))
                -> Arg env (Mut sh' e)
                -> Arg env (Fun' (sh -> PrimMaybe sh'))
                -> Arg env (In sh e)
                -> OperationAcc op env ()

  mkStencil     :: StencilR sh e stencil
                -> Arg env (Fun' (stencil -> e'))
                -> Boundary env (Array sh e)
                -> Arg env (In sh e)
                -> Arg env (Out sh e')
                -> OperationAcc op env ()
  -- Default implementation for mkStencil uses 'generate'. It includes the conditional code for the boundary on all elements, making it less efficient
  -- than a specialized implementation.
  --

  mkStencil2    :: StencilR sh a stencil1
                -> StencilR sh b stencil2
                -> Arg env (Fun' (stencil1 -> stencil2 -> c))
                -> Boundary env (Array sh a)
                -> Arg env (In sh a)
                -> Boundary env (Array sh b)
                -> Arg env (In sh b)
                -> Arg env (Out sh c)
                -> OperationAcc op env ()
  -- Default implementation for mkStencil uses 'generate'. It includes the conditional code for the boundary on all elements, making it less efficient
  -- than a specialized implementation.
  -- XXX: Could we define this in terms of mkStencil and a zip? Maybe only if the sizes of the two input arrays are equal?
  --

  mkFold        :: Arg env (Fun' (e -> e -> e))
                -> Maybe (Arg env (Exp' e))
                -> Arg env (In  (sh, Int) e)
                -> Arg env (Out sh        e)
                -> OperationAcc op env ()

  mkFoldSeg     :: IntegralType i
                -> Arg env (Fun' (e -> e -> e))
                -> Maybe (Arg env (Exp' e))
                -> Arg env (In  (sh, Int) e)
                -> Arg env (In  DIM1      i)
                -> Arg env (Out (sh, Int) e)
                -> OperationAcc op env ()
  -- Default implementation using generate. It is sequential per segment, which is inefficient for some backends.
 
  mkScan        :: Direction
                -> Arg env (Fun' (e -> e -> e))
                -> Maybe (Arg env (Exp' e))
                -> Arg env (In  (sh, Int) e)
                -> Arg env (Out (sh, Int) e)
                -> OperationAcc op env ()

  mkScan'       :: Direction
                -> Arg env (Fun' (e -> e -> e))
                -> Arg env (Exp' e)
                -> Arg env (In  (sh, Int) e)
                -> Arg env (Out (sh, Int) e)
                -> Arg env (Out sh        e)
                -> OperationAcc op env ()


  mkForeign     :: Foreign asm
                => ArraysR bs
                -> asm (as -> bs)
                -> GroundVars env (DesugaredArrays as)
                -> Maybe (OperationAcc op env (DesugaredArrays bs))


type OperationAcc op = PreOpenAcc op


type family DesugaredArrays a where
  DesugaredArrays ()           = ()
  DesugaredArrays (a, b)       = (DesugaredArrays a, DesugaredArrays b)
  DesugaredArrays (Array sh e) = (sh, Buffers e)

type family DesugaredAfun a where
  DesugaredAfun (a -> b) = DesugaredArrays a -> DesugaredAfun b
  DesugaredAfun a        = DesugaredArrays a




data PreOpenAcc (op :: Type -> Type) env a where
  -- | Executes an executable operation. Such execution does not return a
  -- value, the effects of the execution are only visible by the mutation of
  -- buffers which were annotated with either 'Mut' or 'Out'.
  -- Provides the operation arguments from the environment.
  --
  Exec    :: op args
          -> Args env args
          -> PreOpenAcc op env ()

  -- | Returns the values of the given variables.
  --
  Return  :: GroundVars env a
          -> PreOpenAcc op env a

  -- | Evaluates the expression and returns its value.
  --
  Compute :: Exp env t
          -> PreOpenAcc op env t

  -- | Local binding of ground values.
  -- As it is common in this intermediate representation to evaluate some program
  -- resulting in unit, for instance when execution some operation, and then
  -- and then do some other code, we write 'a; b' to denote 'let () = a in b'.
  Alet    :: GLeftHandSide bnd env env'
          -> Uniquenesses bnd
          -> PreOpenAcc op env  bnd
          -> PreOpenAcc op env' t
          -> PreOpenAcc op env  t

  -- | Allocates a new buffer of the given size.
  --
  Alloc   :: ShapeR sh
          -> ScalarType e
          -> ExpVars env sh
          -> PreOpenAcc op env (Buffer e)

  -- | Buffer inlet. To pass an array constant in this data type, one may need
  -- multiple 'Use' constructs because of the explicit Structure-of-Arrays.
  -- Triggers (possibly) asynchronous host->device transfer if necessary.
  --
  Use     :: ScalarType e
          -> Buffer e
          -> PreOpenAcc op env (Buffer e)

  -- | Capture a scalar in a singleton buffer
  --
  Unit    :: ExpVar env e
          -> PreOpenAcc op env (Buffer e)

  -- | If-then-else for array-level computations
  --
  Acond   :: ExpVar env PrimBool
          -> PreOpenAcc op env a
          -> PreOpenAcc op env a
          -> PreOpenAcc op env a





data Uniqueness t where
  Unique :: Uniqueness (Buffer t)
  Shared :: Uniqueness t

type Uniquenesses = TupR Uniqueness



-- | Directed edge (a,b): `b` depends on `a`.
type Edge = (Label, Label)

-- This module (especially mkFullGraph) could be a lot more elegant with e.g. lenses.
-- To keep it simple and avoid depending on them, we instead play around with records
-- and Monoid instances:
--  `i <> mempty{graphI = mempty{graphNodes = x}}`
-- is a way to write
--  `i.graphI.graphNodes <>= x`
-- (add x to the nodes of the graph in i), without having to write tons of getters and setters.
-- next iteration: use lenses, I just realised we already depend on them...

data Graph = Graph
  { graphNodes     :: Set Label
  , fusibleEdges   :: Set Edge  -- Can   be fused over, otherwise `a` before `b`.
  , infusibleEdges :: Set Edge  -- Can't be fused over, always    `a` before `b`.
  }
instance Semigroup Graph where
  Graph n f i <> Graph n' f' i' = Graph (n <> n') (f <> f') (i <> i')
instance Monoid Graph where
  mempty = Graph mempty mempty mempty

-- The graph is the 'common part' of the ILP,
-- each backend has to encode their own constraints
-- describing the fusion rules. The bounds is a [] instead of Set
-- for practical reasons (no Ord instance, LIMP expects a list) only.
data Information ilp op = Info 
  { graphI :: Graph
  , constr :: Constraint ilp op
  , bounds :: Bounds ilp op
  }
instance ILPSolver ilp op => Semigroup (Information ilp op) where
  Info g c b <> Info g' c' b' = Info (g <> g') (c <> c') (b <> b')
instance ILPSolver ilp op => Monoid (Information ilp op) where
  mempty = Info mempty mempty mempty



data Var (op :: Type -> Type)
  = Pi    Label                     -- For acyclic ordering of clusters
  | Fused Label Label               -- 0 is fused (same cluster), 1 is unfused. We do *not* have one of these for all pairs!
  | BackendSpecific (BackendVar op) -- Vars needed to express backend-specific fusion rules.

-- convenience synonyms
pi :: ILPSolver ilp op => Label -> Expression ilp op
pi l = 1 .*. Pi l
fused :: ILPSolver ilp op => Label -> Label -> Expression ilp op
fused x y = 1 .*. Fused x y


class MakesILP op where
  -- Vars needed to express backend-specific fusion rules.
  type BackendVar op

  -- | This function only needs to do the backend-specific things, that is, things which depend on the definition of @op@.
  -- That includes "BackendVar op's" and all their constraints/bounds, but also some (in)fusible edges.
  -- As a conveniece, fusible edges have already been made from all (incoming) labels in the LabelArgs to the current label. 
  -- These can be 'strengthened' by adding a corresponding infusible edge, in which case the fusible edge will later be optimised away.
  mkGraph :: op args -> LabelArgs args -> Label -> Information ilp op



data OptDir = Maximise | Minimise

data ILP      ilp op = ILP OptDir (Expression ilp op) (Constraint ilp op) (Bounds ilp op)
type Solution ilp op = M.Map (Var op) Int

-- Has an instance for LIMP, could add more. The MIP library binds to many solvers,
-- and I enjoyed using that for a different project.
-- -David
class ( Monoid (Bounds     ilp op)
      , Monoid (Constraint ilp op)) 
    => ILPSolver ilp (op :: Type -> Type) where

  -- The functional dependencies aid type inference
  type Bounds     ilp op = a | a -> ilp op
  type Constraint ilp op = a | a -> ilp op
  type Expression ilp op = a | a -> ilp op

  (.+.)  :: Expression ilp op -> Expression ilp op -> Expression ilp op
  (.-.)  :: Expression ilp op -> Expression ilp op -> Expression ilp op
  (.*.)  :: Int               -> Var            op -> Expression ilp op 
  -- ^ Note: Asymmetric!
  
  (.>=.) :: Expression ilp op -> Expression ilp op -> Constraint ilp op
  (.<=.) :: Expression ilp op -> Expression ilp op -> Constraint ilp op
  (.==.) :: Expression ilp op -> Expression ilp op -> Constraint ilp op
  (.>.)  :: Expression ilp op -> Expression ilp op -> Constraint ilp op
  (.<.)  :: Expression ilp op -> Expression ilp op -> Constraint ilp op
  -- Has a default implementation, but Limp has a (perhaps faster?) specialisation (or it's just convenience...)
  between :: Expression ilp op -> Expression ilp op -> Expression ilp op -> Constraint ilp op
  between x y z = x .<=. y <> y .<=. z

  int :: Int -> Expression ilp op
  
  binary :: Var op -> Bounds ilp op
  lowerUpper :: Int -> Var op -> Int -> Bounds ilp op

  solve :: ILP ilp op -> IO (Maybe (Solution ilp op))


-- identifies nodes with unique Ints. and tracks their dependencies
type Label =  Int
type Labels = S.Set Label

-- identifies elements of the environment with unique Ints.
-- newtype'd to avoid confusing them with Label (above).
newtype ELabel = ELabel Int
  deriving (Show, Eq, Ord, Num)


-- | Keeps track of which argument belongs to which labels
data LabelArgs args where
  LabelArgsNil :: LabelArgs ()
  (:>>:)       :: Labels -> LabelArgs t -> LabelArgs (s -> t)

-- | Keeps track of which array in the environment belongs to which label
data LabelEnv env where
  LabelEnvNil  :: LabelEnv ()
  (:>>>:)      :: (ELabel, Labels) -> LabelEnv t -> LabelEnv (t, s)




