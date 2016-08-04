{-# LANGUAGE GADTs               #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RebindableSyntax    #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE ViewPatterns        #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.CodeGen.Arithmetic
-- Copyright   : [2015..2016] Trevor L. McDonell
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.CodeGen.Arithmetic
  where

-- standard/external libraries
import Prelude                                                  ( Eq, Num, ($), (++), (==), undefined, otherwise, flip, fromInteger )
import Control.Applicative
import Control.Monad
import Data.Bits                                                ( finiteBitSize )
import Data.String
import Foreign.Storable                                         ( sizeOf )
import qualified Prelude                                        as P
import qualified Data.Ord                                       as Ord

-- accelerate
import Data.Array.Accelerate.Error
import Data.Array.Accelerate.Array.Sugar

-- accelerate-llvm
import LLVM.General.AST.Type.Constant
import LLVM.General.AST.Type.Global
import LLVM.General.AST.Type.Instruction
import LLVM.General.AST.Type.Name
import LLVM.General.AST.Type.Operand
import LLVM.General.AST.Type.Representation

import Data.Array.Accelerate.LLVM.CodeGen.Base
import Data.Array.Accelerate.LLVM.CodeGen.Constant
import Data.Array.Accelerate.LLVM.CodeGen.IR
import Data.Array.Accelerate.LLVM.CodeGen.Monad
import Data.Array.Accelerate.LLVM.CodeGen.Type


-- Operations from Num
-- -------------------

add :: NumType a -> IR a -> IR a -> CodeGen (IR a)
add = binop Add

sub :: NumType a -> IR a -> IR a -> CodeGen (IR a)
sub = binop Sub

mul :: NumType a -> IR a -> IR a -> CodeGen (IR a)
mul = binop Mul

negate :: NumType a -> IR a -> CodeGen (IR a)
negate t x =
  case t of
    IntegralNumType i | IntegralDict <- integralDict i -> mul t x (ir t (num t (P.negate 1)))
    FloatingNumType f | FloatingDict <- floatingDict f -> mul t x (ir t (num t (P.negate 1)))

abs :: forall a. NumType a -> IR a -> CodeGen (IR a)
abs n x =
  case n of
    FloatingNumType f                  -> mathf "fabs" f x
    IntegralNumType i
      | unsigned i                     -> return x
      | IntegralDict <- integralDict i ->
          let p = ScalarPrimType (NumScalarType n)
              t = PrimType p
          in
          case finiteBitSize (undefined :: a) of
            64 -> call (Lam p (op n x) (Body t "llabs")) [NoUnwind, ReadNone]
            _  -> call (Lam p (op n x) (Body t "abs"))   [NoUnwind, ReadNone]

signum :: forall a. NumType a -> IR a -> CodeGen (IR a)
signum t x =
  case t of
    IntegralNumType i
      | IntegralDict <- integralDict i
      , unsigned i
      -> do z <- neq (NumScalarType t) x (ir t (num t 0))
            s <- instr (Ext boundedType (IntegralBoundedType i) (op scalarType z))
            return s
      --
      | IntegralDict <- integralDict i
      -> do let wsib = finiteBitSize (undefined::a)
            y <- negate t x
            l <- shiftRA i x (ir integralType (integral integralType (wsib P.- 1)))
            r <- shiftRL i y (ir integralType (integral integralType (wsib P.- 1)))
            s <- bor i l r
            return s
    --
    FloatingNumType f
      | FloatingDict <- floatingDict f
      , EltDict      <- numElt t
      -> if gt (NumScalarType t) x (ir f (floating f 0))
            then return $ ir f (floating f 1)
            else if lt (NumScalarType t) x (ir f (floating f 0))
                    then return $ ir f (floating f (P.negate 1))
                    else return $ ir f (floating f 0)


-- Operations from Integral and Bits
-- ---------------------------------

quot :: IntegralType a -> IR a -> IR a -> CodeGen (IR a)
quot = binop Quot

rem :: IntegralType a -> IR a -> IR a -> CodeGen (IR a)
rem = binop Rem

quotRem :: IntegralType a -> IR a -> IR a -> CodeGen (IR (a,a))
quotRem t x y = do
  q <- quot t x y
  z <- mul (IntegralNumType t) y q
  r <- sub (IntegralNumType t) x z
  return $ pair q r

idiv :: IntegralType a -> IR a -> IR a -> CodeGen (IR a)
idiv i x y
  | unsigned i
  = quot i x y
  --
  | IntegralDict <- integralDict i
  , EltDict      <- integralElt i
  , zero         <- ir i (integral i 0)
  , one          <- ir i (integral i 1)
  , n            <- IntegralNumType i
  , s            <- NumScalarType n
  = if gt s x zero `land` lt s y zero
       then do
         a <- sub n x one
         b <- quot i a y
         c <- sub n b one
         return c
       else
    if lt s x zero `land` gt s y zero
       then do
         a <- add n x one
         b <- quot i a y
         c <- sub n b one
         return c
    else
         quot i x y

mod :: IntegralType a -> IR a -> IR a -> CodeGen (IR a)
mod i x y
  | unsigned i
  = rem i x y
  --
  | IntegralDict <- integralDict i
  , EltDict      <- integralElt i
  , zero         <- ir i (integral i 0)
  , n            <- IntegralNumType i
  , s            <- NumScalarType n
  = do r <- rem i x y
       if (gt s x zero `land` lt s y zero) `lor` (lt s x zero `land` gt s y zero)
          then if neq s r zero
                  then add n r y
                  else return zero
          else return r

divMod :: IntegralType a -> IR a -> IR a -> CodeGen (IR (a,a))
divMod i x y
  | unsigned i
  = quotRem i x y
  --
  | IntegralDict <- integralDict i
  , EltDict      <- integralElt i
  , zero         <- ir i (integral i 0)
  , one          <- ir i (integral i 1)
  , n            <- IntegralNumType i
  , s            <- NumScalarType n
  = if gt s x zero `land` lt s y zero
       then do
         a <- sub n x one
         b <- quotRem i a y
         c <- sub n (fst b) one
         d <- add n (snd b) y
         e <- add n d one
         return $ pair c e
       else
    if lt s x zero `land` gt s y zero
       then do
         a <- add n x one
         b <- quotRem i a y
         c <- sub n (fst b) one
         d <- add n (snd b) y
         e <- sub n d one
         return $ pair c e
    else
         quotRem i x y


band :: IntegralType a -> IR a -> IR a -> CodeGen (IR a)
band = binop BAnd

bor :: IntegralType a -> IR a -> IR a -> CodeGen (IR a)
bor = binop BOr

xor :: IntegralType a -> IR a -> IR a -> CodeGen (IR a)
xor = binop BXor

complement :: IntegralType a -> IR a -> CodeGen (IR a)
complement t x | IntegralDict <- integralDict t = xor t x (ir t (integral t (P.negate 1)))

shiftL :: IntegralType a -> IR a -> IR Int -> CodeGen (IR a)
shiftL t x i = do
  i' <- fromIntegral integralType (IntegralNumType t) i
  binop ShiftL t x i'

shiftR :: IntegralType a -> IR a -> IR Int -> CodeGen (IR a)
shiftR t
  | signed t  = shiftRA t
  | otherwise = shiftRL t

shiftRL :: IntegralType a -> IR a -> IR Int -> CodeGen (IR a)
shiftRL t x i = do
  i' <- fromIntegral integralType (IntegralNumType t) i
  r  <- binop ShiftRL t x i'
  return r

shiftRA :: IntegralType a -> IR a -> IR Int -> CodeGen (IR a)
shiftRA t x i = do
  i' <- fromIntegral integralType (IntegralNumType t) i
  r  <- binop ShiftRA t x i'
  return r

rotateL :: forall a. IntegralType a -> IR a -> IR Int -> CodeGen (IR a)
rotateL t x i
  | IntegralDict <- integralDict t
  = do let wsib = finiteBitSize (undefined::a)
       i1 <- band integralType i (ir integralType (integral integralType (wsib P.- 1)))
       i2 <- sub numType (ir numType (integral integralType wsib)) i1
       --
       a  <- shiftL t x i1
       b  <- shiftRL t x i2
       c  <- bor t a b
       return c

rotateR :: forall a. IntegralType a -> IR a -> IR Int -> CodeGen (IR a)
rotateR t x i = do
  i' <- negate numType i
  r  <- rotateL t x i'
  return r


-- Operators from Fractional and Floating
-- --------------------------------------

fdiv :: FloatingType a -> IR a -> IR a -> CodeGen (IR a)
fdiv = binop Div

recip :: FloatingType a -> IR a -> CodeGen (IR a)
recip t x | FloatingDict <- floatingDict t = fdiv t (ir t (floating t 1)) x

sin :: FloatingType a -> IR a -> CodeGen (IR a)
sin = mathf "sin"

cos :: FloatingType a -> IR a -> CodeGen (IR a)
cos = mathf "cos"

tan :: FloatingType a -> IR a -> CodeGen (IR a)
tan = mathf "tan"

sinh :: FloatingType a -> IR a -> CodeGen (IR a)
sinh = mathf "sinh"

cosh :: FloatingType a -> IR a -> CodeGen (IR a)
cosh = mathf "cosh"

tanh :: FloatingType a -> IR a -> CodeGen (IR a)
tanh = mathf "tanh"

asin :: FloatingType a -> IR a -> CodeGen (IR a)
asin = mathf "asin"

acos :: FloatingType a -> IR a -> CodeGen (IR a)
acos = mathf "acos"

atan :: FloatingType a -> IR a -> CodeGen (IR a)
atan = mathf "atan"

asinh :: FloatingType a -> IR a -> CodeGen (IR a)
asinh = mathf "asinh"

acosh :: FloatingType a -> IR a -> CodeGen (IR a)
acosh = mathf "acosh"

atanh :: FloatingType a -> IR a -> CodeGen (IR a)
atanh = mathf "atanh"

atan2 :: FloatingType a -> IR a -> IR a -> CodeGen (IR a)
atan2 = mathf2 "atan2"

exp :: FloatingType a -> IR a -> CodeGen (IR a)
exp = mathf "exp"

fpow :: FloatingType a -> IR a -> IR a -> CodeGen (IR a)
fpow = mathf2 "pow"

sqrt :: FloatingType a -> IR a -> CodeGen (IR a)
sqrt = mathf "sqrt"

log :: FloatingType a -> IR a -> CodeGen (IR a)
log = mathf "log"

logBase :: forall a. FloatingType a -> IR a -> IR a -> CodeGen (IR a)
logBase t x@(op t -> base) y | FloatingDict <- floatingDict t = logBase'
  where
    match :: Eq t => Operand t -> Operand t -> Bool
    match (ConstantOperand (ScalarConstant _ u))
          (ConstantOperand (ScalarConstant _ v)) = u == v
    match _ _                                    = False

    logBase' :: (Num a, Eq a) => CodeGen (IR a)
    logBase' | match base (floating t 2)  = mathf "log2"  t y
             | match base (floating t 10) = mathf "log10" t y
             | otherwise
             = do x' <- log t x
                  y' <- log t y
                  fdiv t y' x'


-- Operators from RealFloat
-- ------------------------

isNaN :: FloatingType a -> IR a -> CodeGen (IR Bool)
isNaN f (op f -> x) = do
  let p = ScalarPrimType (NumScalarType (FloatingNumType f))
      t = type'
  name <- intrinsic "isnan"
  r    <- call (Lam p x (Body t name)) [NoUnwind, ReadOnly]
  return r


-- Operators from RealFrac
-- -----------------------

truncate :: FloatingType a -> IntegralType b -> IR a -> CodeGen (IR b)
truncate tf ti (op tf -> x) = instr (FPToInt tf ti x)

round :: FloatingType a -> IntegralType b -> IR a -> CodeGen (IR b)
round tf ti x = do
  i <- mathf "round" tf x
  truncate tf ti i

floor :: FloatingType a -> IntegralType b -> IR a -> CodeGen (IR b)
floor tf ti x = do
  i <- mathf "floor" tf x
  truncate tf ti i

ceiling :: FloatingType a -> IntegralType b -> IR a -> CodeGen (IR b)
ceiling tf ti x = do
  i <- mathf "ceil" tf x
  truncate tf ti i


-- Relational and Equality operators
-- ---------------------------------

cmp :: Predicate -> ScalarType a -> IR a -> IR a -> CodeGen (IR Bool)
cmp p dict (op dict -> x) (op dict -> y) = instr (Cmp dict p x y)

lt :: ScalarType a -> IR a -> IR a -> CodeGen (IR Bool)
lt = cmp LT

gt :: ScalarType a -> IR a -> IR a -> CodeGen (IR Bool)
gt = cmp GT

lte :: ScalarType a -> IR a -> IR a -> CodeGen (IR Bool)
lte = cmp LE

gte :: ScalarType a -> IR a -> IR a -> CodeGen (IR Bool)
gte = cmp GE

eq :: ScalarType a -> IR a -> IR a -> CodeGen (IR Bool)
eq = cmp EQ

neq :: ScalarType a -> IR a -> IR a -> CodeGen (IR Bool)
neq = cmp NE

max :: ScalarType a -> IR a -> IR a -> CodeGen (IR a)
max ty x y
  | NumScalarType (FloatingNumType f) <- ty = mathf2 "fmax" f x y
  | otherwise                               = do c <- op scalarType <$> gte ty x y
                                                 binop (flip Select c) ty x y

min :: ScalarType a -> IR a -> IR a -> CodeGen (IR a)
min ty x y
  | NumScalarType (FloatingNumType f) <- ty = mathf2 "fmin" f x y
  | otherwise                               = do c <- op scalarType <$> lte ty x y
                                                 binop (flip Select c) ty x y


-- Logical operators
-- -----------------

land :: CodeGen (IR Bool) -> CodeGen (IR Bool) -> CodeGen (IR Bool)
land x y =
  if x
    then y
    else return $ ir scalarType (scalar scalarType False)

lor :: CodeGen (IR Bool) -> CodeGen (IR Bool) -> CodeGen (IR Bool)
lor x y =
  if x
    then return $ ir scalarType (scalar scalarType True)
    else y

-- These implementations are strict in both arguments.
_land :: IR Bool -> IR Bool -> CodeGen (IR Bool)
_land (op scalarType -> x) (op scalarType -> y)
  = instr (LAnd x y)

_lor  :: IR Bool -> IR Bool -> CodeGen (IR Bool)
_lor (op scalarType -> x) (op scalarType -> y)
  = instr (LOr x y)

lnot :: IR Bool -> CodeGen (IR Bool)
lnot (op scalarType -> x) = instr (LNot x)


-- Type conversions
-- ----------------

ord :: IR Char -> CodeGen (IR Int)
ord (op scalarType -> x) =
  case finiteBitSize (undefined :: Int) of
    32 -> instr (BitCast scalarType x)
    64 -> instr (Trunc boundedType boundedType x)
    _  -> $internalError "ord" "I don't know what architecture I am"

chr :: IR Int -> CodeGen (IR Char)
chr (op integralType -> x) =
  case finiteBitSize (undefined :: Int) of
    32 -> instr (BitCast scalarType x)
    64 -> instr (Ext boundedType boundedType x)
    _  -> $internalError "chr" "I don't know what architecture I am"

boolToInt :: IR Bool -> CodeGen (IR Int)
boolToInt x = instr (Ext boundedType boundedType (op scalarType x))

fromIntegral :: forall a b. IntegralType a -> NumType b -> IR a -> CodeGen (IR b)
fromIntegral i1 n (op i1 -> x) =
  case n of
    FloatingNumType f
      -> instr (IntToFP i1 f x)

    IntegralNumType (i2 :: IntegralType b)
      | IntegralDict <- integralDict i1
      , IntegralDict <- integralDict i2
      -> let
             bits_a = finiteBitSize (undefined::a)
             bits_b = finiteBitSize (undefined::b)
         in
         case Ord.compare bits_a bits_b of
           Ord.EQ -> instr (BitCast (NumScalarType n) x)
           Ord.GT -> instr (Trunc (IntegralBoundedType i1) (IntegralBoundedType i2) x)
           Ord.LT -> instr (Ext   (IntegralBoundedType i1) (IntegralBoundedType i2) x)

toFloating :: forall a b. NumType a -> FloatingType b -> IR a -> CodeGen (IR b)
toFloating n1 f2 (op n1 -> x) =
  case n1 of
    IntegralNumType i1
      -> instr (IntToFP i1 f2 x)

    FloatingNumType (f1 :: FloatingType a)
      | FloatingDict <- floatingDict f1
      , FloatingDict <- floatingDict f2
      -> let
             bytes_a = sizeOf (undefined::a)
             bytes_b = sizeOf (undefined::b)
         in
         case Ord.compare bytes_a bytes_b of
           Ord.EQ -> instr (BitCast (NumScalarType (FloatingNumType f2)) x)
           Ord.GT -> instr (FTrunc f1 f2 x)
           Ord.LT -> instr (FExt   f1 f2 x)

coerce :: forall a b. ScalarType a -> ScalarType b -> IR a -> CodeGen (IR b)
coerce ta tb (op ta -> x) = instr (BitCast tb x)


-- Utility functions
-- -----------------

fst :: IR (a, b) -> IR a
fst (IR (OP_Pair (OP_Pair OP_Unit x) _)) = IR x

snd :: IR (a, b) -> IR b
snd (IR (OP_Pair _ y)) = IR y

pair :: IR a -> IR b -> IR (a, b)
pair (IR x) (IR y) = IR $ OP_Pair (OP_Pair OP_Unit x) y

unpair :: IR (a, b) -> (IR a, IR b)
unpair x = (fst x, snd x)

uncurry :: (IR a -> IR b -> c) -> IR (a, b) -> c
uncurry f (unpair -> (x,y)) = f x y


binop :: IROP dict => (dict a -> Operand a -> Operand a -> Instruction a) -> dict a -> IR a -> IR a -> CodeGen (IR a)
binop f dict (op dict -> x) (op dict -> y) = instr (f dict x y)


fst3 :: IR (a, b, c) -> IR a
fst3 (IR (OP_Pair (OP_Pair (OP_Pair OP_Unit x) _) _)) = IR x

snd3 :: IR (a, b, c) -> IR b
snd3 (IR (OP_Pair (OP_Pair _ y) _)) = IR y

thd3 :: IR (a, b, c) -> IR c
thd3 (IR (OP_Pair _ z)) = IR z

trip :: IR a -> IR b -> IR c -> IR (a, b, c)
trip (IR x) (IR y) (IR z) = IR $ OP_Pair (OP_Pair (OP_Pair OP_Unit x) y) z

untrip :: IR (a, b, c) -> (IR a, IR b, IR c)
untrip t = (fst3 t, snd3 t, thd3 t)


-- | Lift a constant value into an constant in the intermediate representation.
--
lift :: IsScalar a => a -> IR a
lift x = ir scalarType (scalar scalarType x)


-- | Standard if-then-else expression
--
ifThenElse
    :: Elt a
    => CodeGen (IR Bool)
    -> CodeGen (IR a)
    -> CodeGen (IR a)
    -> CodeGen (IR a)
ifThenElse test yes no = do
  ifThen <- newBlock "if.then"
  ifElse <- newBlock "if.else"
  ifExit <- newBlock "if.exit"

  _  <- beginBlock "if.entry"
  p  <- test
  _  <- cbr p ifThen ifElse

  setBlock ifThen
  tv <- yes
  tb <- br ifExit

  setBlock ifElse
  fv <- no
  fb <- br ifExit

  setBlock ifExit
  phi [(tv, tb), (fv, fb)]


-- Execute the body only if the first argument evaluates to True
--
when :: CodeGen (IR Bool) -> CodeGen () -> CodeGen ()
when test doit = do
  body <- newBlock "when.body"
  exit <- newBlock "when.exit"

  p <- test
  _ <- cbr p body exit

  setBlock body
  doit
  _ <- br exit

  setBlock exit


-- Execute the body only if the first argument evaluates to False
--
unless :: CodeGen (IR Bool) -> CodeGen () -> CodeGen ()
unless test doit = do
  body <- newBlock "unless.body"
  exit <- newBlock "unless.exit"

  p <- test
  _ <- cbr p exit body

  setBlock body
  doit
  _ <- br exit

  setBlock exit


-- Call a function from the standard C math library. This is a wrapper around
-- the 'call' function from CodeGen.Base since:
--
--   (1) The parameter and return types are all the same; and
--   (2) We check if there is an intrinsic implementation of this function
--
-- TLM: We should really be able to construct functions of any arity.
--
mathf :: String -> FloatingType t -> IR t -> CodeGen (IR t)
mathf n f (op f -> x) = do
  let s = ScalarPrimType (NumScalarType (FloatingNumType f))
      t = PrimType s
  --
  name <- lm f n
  r    <- call (Lam s x (Body t name)) [NoUnwind, ReadOnly]
  return r


mathf2 :: String -> FloatingType t -> IR t -> IR t -> CodeGen (IR t)
mathf2 n f (op f -> x) (op f -> y) = do
  let s = ScalarPrimType (NumScalarType (FloatingNumType f))
      t = PrimType s
  --
  name <- lm f n
  r    <- call (Lam s x (Lam s y (Body t name))) [NoUnwind, ReadOnly]
  return r

lm :: FloatingType t -> String -> CodeGen Label
lm t n
  = intrinsic
  $ case t of
      TypeFloat{}   -> n++"f"
      TypeCFloat{}  -> n++"f"
      TypeDouble{}  -> n
      TypeCDouble{} -> n

