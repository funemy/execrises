{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import Prelude hiding (succ)
import Data.Bifunctor (Bifunctor, bimap)

newtype Fix f = In { unIn :: f (Fix f) }

type Mu f = Fix f

cata :: Functor f => (f a -> a) -> Mu f -> a
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

para :: Functor f => (f (Mu f, a) -> a) -> Mu f -> a
para alg = snd . cata ((In . fmap fst) `delta` alg)
-- para alg n = snd $ ((In . fmap fst) `delta` alg) $ fmap (cata ((In . fmap fst) `delta` alg)) (unIn n)
-- para alg n = snd $ ((In . fmap fst) `delta` alg) $ fmap (cata ((In . fmap fst) `delta` alg)) Zero
-- para alg n = snd $ ((In . fmap fst) `delta` alg) Zero
-- para alg n = snd $ ((In . fmap fst) Zero, alg Zero)
-- para alg n = snd $ ((In one), one)
--
-- para alg n = snd $ ((In . fmap fst) `delta` alg) $ fmap (cata ((In . fmap fst) `delta` alg)) (unIn n)
-- para alg n = snd $ ((In . fmap fst) `delta` alg) $ fmap (cata ((In . fmap fst) `delta` alg)) (Succ (In Zero))
-- para alg n = snd $ ((In . fmap fst) `delta` alg) $ Succ (cata ((In . fmap fst) `delta` alg) $ In Zero)
-- para alg n = snd $ ((In . fmap fst) (Succ (In one, one)), alg (Succ (In one, one)))
-- para alg n = snd $ ((In . fmap fst) (Succ (In one, one)), one)
-- para alg n = snd $ ((In $ Succ (fst (In one, one))) , one)
-- para alg n = snd $ ((In (Succ (In one)) , one)
-- para alg n = snd $ (two , one)

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

-- TODO: cata to mutu

-- This is the mutu defined in the paper
mutu :: forall f a b . Functor f => (f (a,b) -> a) -> (f (a, b) -> b) -> (Mu f -> a, Mu f -> b)
mutu f g = (fst . cata alg, snd . cata alg)
  where
    alg :: f (a, b) -> (a, b)
    alg x = (f x, g x)

-- can we generalize mutu?
newtype Mu1 f g = In1 { unIn1 :: f (Mu1 f g) (Mu2 f g) }
newtype Mu2 f g = In2 { unIn2 :: g (Mu1 f g) (Mu2 f g) }

mutu' :: (Bifunctor f, Bifunctor g) => (f a b -> a) -> (g a b -> b) -> Mu1 f g -> Mu2 f g -> (a, b)
mutu' alg1 alg2 m1 m2 = (x m1, y m2)
  where
    -- intuitively, x handles the `f` component of the substructure of our mutually inductive definition
    -- dually, y handles the `g` component
    -- the mutual recursion scheme is captured by the `bimap x y`
    x = alg1 . bimap x y . unIn1
    y = alg2 . bimap x y . unIn2

-- Ron's example translated into haskell
data Nat1F x y = Zero1 | Succ1 x y
data Nat2F x y = Zero2 | Succ2 x y

type Nat1 = Mu1 Nat1F Nat2F
type Nat2 = Mu2 Nat1F Nat2F

-- The functor and bifunctor definitions are all standard
-- (You can derive their implementations)
instance Functor (Nat1F x) where
  fmap f Zero1 = Zero1
  fmap f (Succ1 x y) = Succ1 x (f y)

instance Bifunctor Nat1F where
  bimap f g Zero1 = Zero1
  bimap f g (Succ1 x y) = Succ1 (f x) (g y)

instance Functor (Nat2F x) where
  fmap f Zero2 = Zero2
  fmap f (Succ2 x y)= Succ2 x (f y)

instance Bifunctor Nat2F where
  bimap f g Zero2 = Zero2
  bimap f g (Succ2 x y) = Succ2 (f x) (g y)

-- At this point, you probably already see how repetetive this construction is.
-- We basically have to duplicate everything between Nat1 and Nat2

-- But let's try to finish this example by defining their f-algebras
-- We basically defined Nat twice (which the exact same definition), so that we can write two separate f-algebras
alg1 :: Nat1F Int Int -> Int
alg1 Zero1 = 0
alg1 (Succ1 x y) = x + y

alg2 :: Nat2F Int Int -> Int
alg2 Zero2 = 1
alg2 (Succ2 x y) = x

-- some constants for testing
zero1 :: Nat1
zero1 = In1 Zero1

zero2 :: Nat2
zero2 = In2 Zero2

one1 :: Nat1
one1 = In1 (Succ1 zero1 zero2)

one2 :: Nat2
one2 = In2 (Succ2 zero1 zero2)

succ1 :: Nat1 -> Nat2 -> Nat1
succ1 n1 n2 = In1 (Succ1 n1 n2)

succ2 :: Nat1 -> Nat2 -> Nat2
succ2 n1 n2 = In2 (Succ2 n1 n2)

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

fibb :: Nat1 -> Int
fibb n1 = fst $ mutu' alg1 alg2 n1 zero2

-- fib 5
test_fibb1 :: Int
test_fibb1 = fibb five1

-- fib 7
test_fibb2 :: Int
test_fibb2 = fibb seven1

-- comutu
newtype Nu1 f g = UnOut1 { out1 :: f (Nu1 f g) (Nu2 f g) }
newtype Nu2 f g = UnOut2 { out2 :: g (Nu1 f g) (Nu2 f g) }

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


main :: IO ()
main = putStrLn "Hello World"
