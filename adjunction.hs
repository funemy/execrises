module Adjunction where

-- Notice left/rightAdjunct and unit/counit are mutually recursive
-- They are two equivlant ways of defining adjunctions
class (Functor f, Functor g) => Adjunction f g where
  leftAdjunct :: (f a -> b) -> a -> g b
  leftAdjunct h a =  fmap h (unit a)

  rightAdjunct :: (a -> g b) -> f a -> b
  rightAdjunct h fa = counit (fmap h fa)

  -- g b -> g (f (g b))
  -- id :: f a -> f a
  unit :: a -> g (f a)
  unit = leftAdjunct id

  -- id :: g a -> g a
  counit :: f (g a) -> a
  counit = rightAdjunct id

newtype F s a =  F (a, s)
  deriving (Functor)

newtype G s a =  G (s -> a)
  deriving (Functor)

instance Adjunction (F s) (G s) where
  --             ((a, s) -> b) -> a -> (s -> a)
  leftAdjunct :: (F s a -> b) -> a -> G s b
  leftAdjunct f a = G (\s -> f (F (a, s)))

  --              (a -> s -> b) -> (a, s) -> b
  rightAdjunct :: (a -> G s b) -> F s a -> b
  rightAdjunct f (F (a, s)) = case f a of G f' -> f' s

  --      a -> s -> (a, s)
  unit :: a -> G s (F s a)
  unit a = G (\s -> F (a, s))

  --        (s -> a, s) -> a
  counit :: F s (G s a) -> a
  counit (F (G f, a)) = f a

-- impossible to define below
-- instance Adjunction (G s) (F s) where


class Functor w => Comonad w where
  extract :: w a -> a
  duplicate :: w a -> w (w a)

  (=>>) :: w a -> (w a -> b) -> w b
  wa =>> f = fmap f (duplicate wa)

-- for comparison
class Functor m => Monad m where
  return :: a -> m a
  join :: m (m a) -> m a

  (>>=) :: m a -> (a -> m b) -> m b
  ma >>= f = join (fmap f ma)

newtype Store idx a = Store (idx -> a, idx)

instance Functor (Store idx) where
  fmap f (Store (s, i)) = Store (f . s, i)

instance Comonad (Store idx) where
  extract :: Store idx a -> a
  extract (Store (s, i)) = s i

  duplicate :: Store idx a -> Store idx (Store idx a)
  duplicate (Store (s, i)) = Store (\idx -> Store (s, idx), i)

type Bitmap2D = Store (Int, Int) Int

lowpass :: Bitmap2D -> Bitmap2D
lowpass bmp = bmp =>> mean
  where
    mean :: Bitmap2D -> Int
    mean (Store (m, (x, y))) =
      let pts = [(x', y') | x' <- [x-1, x, x+1], y' <- [y-1, y, y+1]]
          total = (sum . map m) pts
       in total `div` length pts

