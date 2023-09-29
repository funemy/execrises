module Main where

import Prelude hiding (succ)

newtype Fix f = In { unIn :: f (Fix f) }

cata :: Functor f => (f a -> a) -> Fix f -> a

cata alg = alg . fmap (cata alg) . unIn

delta :: (a -> b) -> (a -> c) -> a -> (b, c)
delta f g x = (f x, g x)

data NatF x = Zero | Succ x

type Nat = Fix NatF

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

para :: Functor f => (f (Fix f, a) -> a) -> Fix f -> a
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

main :: IO ()
main = putStrLn "Hello World"
