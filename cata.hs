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

-- This is the same definition as the paper
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
    -- intuitively, x handles the `f` component of the substructure of out mutually inductive definition
    -- dually, y handles the `g` component
    -- the mutual recursion scheme is reflected by `bimap x y`
    x = alg1 . bimap x y . unIn1
    y = alg2 . bimap x y . unIn2

-- comutu
newtype Nu1 f g = UnOut1 { out1 :: f (Nu1 f g) (Nu2 f g) }
newtype Nu2 f g = UnOut2 { out2 :: g (Nu1 f g) (Nu2 f g) }

comutu :: (Bifunctor f, Bifunctor g) => (a -> f a b) -> (b -> g a b) -> a -> b -> (Nu1 f g, Nu2 f g)
comutu coalg1 coalg2 a b = (x a, y b)
  where
    x = UnOut1 . bimap x y . coalg1
    y = UnOut2 . bimap x y . coalg2


main :: IO ()
main = putStrLn "Hello World"
