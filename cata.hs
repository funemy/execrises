{-# LANGUAGE ScopedTypeVariables #-}

module Morphism where

import Data.Bifunctor (Bifunctor, bimap)
import Prelude hiding (succ)

newtype Fix f = In {unIn :: f (Fix f)}

type Mu f = Fix f

cata :: (Functor f) => (f a -> a) -> Mu f -> a
cata alg = alg . fmap (cata alg) . unIn

delta :: (a -> b) -> (a -> c) -> a -> (b, c)
delta f g x = (f x, g x)

data NatF x = Zero | Succ x

type Nat = Mu NatF

instance Functor NatF where
  fmap f Zero = Zero
  fmap f (Succ x) = Succ (f x)

algToInt :: NatF Int -> Int
algToInt Zero = 0
algToInt (Succ n) = n + 1

-- convert Nat to Int for testing
toInt :: Nat -> Int
toInt = cata algToInt

-- now we can print out the fixpoint definition of nat
instance Show Nat where
  show = show . toInt

algAdd :: Nat -> NatF Nat -> Nat
algAdd n Zero = n
algAdd _ (Succ m) = In (Succ m)

-- natural number addition
add :: Nat -> Nat -> Nat
add n = cata (algAdd n)

zero :: Nat
zero = In Zero

one :: Nat
one = In (Succ (In Zero))

succ :: Nat -> Nat
succ n = In (Succ n)

two :: Nat
two = succ one

five :: Nat
five = one `add` one `add` one `add` one `add` one

algMul :: Nat -> NatF Nat -> Nat
algMul n Zero = zero
algMul n (Succ m) = n `add` m

mul :: Nat -> Nat -> Nat
mul n = cata (algMul n)

ten :: Nat
ten = two `mul` five

para :: (Functor f) => (f (Mu f, a) -> a) -> Mu f -> a
para alg = snd . cata ((In . fmap fst) `delta` alg)

-- fact zero
-- para alg n = snd $ ((In . fmap fst) `delta` alg) $ fmap (cata ((In . fmap fst) `delta` alg)) (unIn n)
-- para alg n = snd $ ((In . fmap fst) `delta` alg) $ fmap (cata ((In . fmap fst) `delta` alg)) Zero
-- para alg n = snd $ ((In . fmap fst) `delta` alg) Zero
-- para alg n = snd $ ((In . fmap fst) Zero, alg Zero)
-- para alg n = snd $ ((In Zero), one)
--
-- fact one
-- para alg n = snd $ ((In . fmap fst) `delta` alg) $ fmap (cata ((In . fmap fst) `delta` alg)) (unIn n)
-- para alg n = snd $ ((In . fmap fst) `delta` alg) $ fmap (cata ((In . fmap fst) `delta` alg)) (Succ (In Zero))
-- para alg n = snd $ ((In . fmap fst) `delta` alg) $ Succ (cata ((In . fmap fst) `delta` alg) $ In Zero)
-- para alg n = snd $ ((In . fmap fst) (Succ (In Zero, one)), alg (Succ (In Zero, one)))
-- para alg n = snd $ ((In . fmap fst) (Succ (In Zero, one)), one)
-- para alg n = snd $ ((In $ Succ (fst (In Zero, one))) , one)
-- para alg n = snd $ ((In (Succ (In Zero)) , one)
-- para alg n = snd $ (one , one)

algFact :: NatF (Nat, Nat) -> Nat
algFact Zero = one
algFact (Succ (prev, b)) = succ prev `mul` b

-- factorial using paramorphism
fact :: Nat -> Nat
fact = para algFact

algFact' :: NatF (Nat, Nat) -> (Nat, Nat)
algFact' Zero = (one, one)
algFact' (Succ (prev, b)) = (succ prev, prev `mul` b)

-- factorial using catamorphism
fact' :: Nat -> Nat
fact' = snd . cata algFact'

-- This is the mutu defined in the paper
mutu :: forall f a b. (Functor f) => (f (a, b) -> a) -> (f (a, b) -> b) -> (Mu f -> a, Mu f -> b)
mutu f g = (fst . cata alg, snd . cata alg)
 where
  alg :: f (a, b) -> (a, b)
  alg x = (f x, g x)

-- can we generalize mutu?
newtype Mu1 f g = In1 {unIn1 :: f (Mu1 f g) (Mu2 f g)}
newtype Mu2 f g = In2 {unIn2 :: g (Mu1 f g) (Mu2 f g)}

mutu' :: (Bifunctor f, Bifunctor g) => (f a b -> a) -> (g a b -> b) -> Mu1 f g -> Mu2 f g -> (a, b)
mutu' alg1 alg2 m1 m2 = (x m1, y m2)
 where
  -- intuitively, x handles the `f` component of the substructure of our mutually inductive definition
  -- dually, y handles the `g` component
  -- the mutual recursion scheme is captured by the `bimap x y`
  x = alg1 . bimap x y . unIn1
  y = alg2 . bimap x y . unIn2

-- Ron's example translated into haskell
data NatBF x y = ZeroBF | SuccBF x y

type Nat1 = Mu1 NatBF NatBF
type Nat2 = Mu2 NatBF NatBF

-- The functor and bifunctor definitions are all standard
-- (You can derive their implementations)
instance Functor (NatBF x) where
  fmap f ZeroBF = ZeroBF
  fmap f (SuccBF x y) = SuccBF x (f y)

instance Bifunctor NatBF where
  bimap f g ZeroBF = ZeroBF
  bimap f g (SuccBF x y) = SuccBF (f x) (g y)

-- At this point, you probably already see how repetetive this construction is.
-- We basically have to duplicate everything between Nat1 and Nat2

-- But let's try to finish this example by defining their f-algebras
-- We basically defined Nat twice (which the exact same definition), so that we can write two separate f-algebras
alg1 :: NatBF Int Int -> Int
alg1 ZeroBF = 0
alg1 (SuccBF x y) = x + y

alg2 :: NatBF Int Int -> Int
alg2 ZeroBF = 1
alg2 (SuccBF x y) = x

-- some constants for testing
-- NOTE: the awkward thing here is to construct values in both nat1 and nat2.
--  This cannot really be avoid because of the definition of Mu1 and Mu2
--  But notice the construction of nat1 and nat2 values are identical modulo the constructor names.
--  This also suggests that the original `mutu` is more desirable if the mutually recursive functions
--  are defined on the same inductive datatypes.
zero1 :: Nat1
zero1 = In1 ZeroBF

zero2 :: Nat2
zero2 = In2 ZeroBF

one1 :: Nat1
one1 = In1 (SuccBF zero1 zero2)

one2 :: Nat2
one2 = In2 (SuccBF zero1 zero2)

succ1 :: Nat1 -> Nat2 -> Nat1
succ1 n1 n2 = In1 (SuccBF n1 n2)

succ2 :: Nat1 -> Nat2 -> Nat2
succ2 n1 n2 = In2 (SuccBF n1 n2)

two1 :: Nat1
two1 = succ1 one1 one2

two2 :: Nat2
two2 = succ2 one1 one2

three1 :: Nat1
three1 = succ1 two1 two2

three2 :: Nat2
three2 = succ2 two1 two2

four1 :: Nat1
four1 = succ1 three1 three2

four2 :: Nat2
four2 = succ2 three1 three2

five1 :: Nat1
five1 = succ1 four1 four2

five2 :: Nat2
five2 = succ2 four1 four2

six1 :: Nat1
six1 = succ1 five1 five2

six2 :: Nat2
six2 = succ2 five1 five2

seven1 :: Nat1
seven1 = succ1 six1 six2

seven2 :: Nat2
seven2 = succ2 six1 six2

-- Notice that the second nat (value of Nat2) we pass in does not matter.
-- Therefore I used a dummy value zero2.
-- This intuitively makes sense because the f-algebra `alg2` is only useful as an aux function,
-- in other words, its usage is for handling the substructure of `n1`.
-- Therefore at the top level we just want to give a dummy value for the 2nd element of the pair.
fibb :: Nat1 -> Int
fibb n1 = fst $ mutu' alg1 alg2 n1 zero2

-- fib 5
test_fibb1 :: Int
test_fibb1 = fibb five1

-- fib 7
test_fibb2 :: Int
test_fibb2 = fibb seven1

-- comutu
newtype Nu1 f g = UnOut1 {out1 :: f (Nu1 f g) (Nu2 f g)}
newtype Nu2 f g = UnOut2 {out2 :: g (Nu1 f g) (Nu2 f g)}

-- The comutu presented in the paper
comutu :: (Bifunctor f, Bifunctor g) => (c -> f c c) -> (c -> g c c) -> c -> (Nu1 f g, Nu2 f g)
comutu coalg1 coalg2 c = (x c, y c)
 where
  x = UnOut1 . bimap x y . coalg1
  y = UnOut2 . bimap x y . coalg2

comutu' :: (Bifunctor f, Bifunctor g) => (a -> f a b) -> (b -> g a b) -> a -> b -> (Nu1 f g, Nu2 f g)
comutu' coalg1 coalg2 a b = (x a, y b)
 where
  x = UnOut1 . bimap x y . coalg1
  y = UnOut2 . bimap x y . coalg2

-- cofree and histo
data Cofree f a where
  (:<) :: a -> f (Cofree f a) -> Cofree f a

extract :: Cofree f a -> a
extract (a :< _) = a

histo :: (Functor f) => (f (Cofree f a) -> a) -> Mu f -> a
histo alg = extract . cata (\x -> alg x :< x)
