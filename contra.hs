module Contra where

-- See more on Data.Functor.Contravariant

import Prelude hiding (Functor (..))

class Functor f where
    fmap :: (a -> b) -> f a -> f b

instance Functor ((->) r) where
    fmap f g = f . g

class Contra f where
    cmap :: (a -> b) -> f b -> f a

newtype Op r a = Op { getOp :: a -> r }

instance Contra (Op r) where
    cmap f g = Op $ getOp g . f

