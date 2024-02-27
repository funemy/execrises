{-# OPTIONS_GHC -W #-}

module Free where

-- forall m . Monad m => (a -> m) -> Free
data Free f a
    = Pure a
    | Free (f (Free f a))

instance (Functor f) => Functor (Free f) where
    fmap :: (a -> b) -> Free f a -> Free f b
    fmap g (Pure a) = Pure (g a)
    fmap g (Free f) = Free (fmap (fmap g) f)

instance (Functor f) => Applicative (Free f) where
    pure = Pure
    (<*>) = undefined

instance (Functor f) => Monad (Free f) where
    (>>=) :: Free f a -> (a -> Free f b) -> Free f b
    (Pure a) >>= g = g a
    (Free f) >>= g = Free $ fmap (>>= g) f

data ListF a b
    = NilF
    | ConsF a b
    deriving (Show)

instance Functor (ListF a) where
  fmap :: (b -> c) -> ListF a b -> ListF a c
  fmap _ NilF = NilF
  fmap f (ConsF a b) = ConsF a (f b)

instance (Show a, Show b) => Show (Free (ListF a) b) where
    show (Pure a) = "(Pure " ++ show a ++ ")"
    show (Free f) = "(Free " ++ show f ++ ")"

test1 :: Free (ListF Int) Int
test1 = Pure 1

test2 :: Free (ListF Int) ()
test2 = Free (ConsF 2 (Free (ConsF 1 (Pure ()))))

test3 :: Free (ListF Int) ()
test3 = do
    test2
    test2

interp :: Free (ListF Int) a -> [String]
interp (Pure _) = []
interp (Free NilF) = []
interp (Free (ConsF a b)) = show a : interp b
