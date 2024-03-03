module Contra where

-- See more on Data.Functor.Contravariant
-- and also https://github.com/rampion/kinder-functor

import Prelude hiding (Functor (..))

class Functor f where
    fmap :: (a -> b) -> f a -> f b

-- For function i -> o (i for input, o for ouput)
-- i -> _ is a covariant functor
instance Functor ((->) i) where
    fmap f g = f . g

class Contra f where
    cmap :: (a -> b) -> f b -> f a

-- Op means "Opposite"
-- This is essentially the same thing as the C^op categories you see in category theory.
-- Op o i == i -> o
newtype Op o i = Op { getOp :: i -> o }

instance Contra (Op o) where
    cmap f g = Op $ getOp g . f

