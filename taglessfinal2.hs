{-# OPTIONS_GHC -W #-}

-- After reading "Finally Tagless, Partially Evaluated"
module TaglessFinal2 where

import qualified Data.Function as F (fix)

-- There are some essence of tagless final that wasn't captured in our previous
-- file (i.e., taglessfinal.hs)
--
-- Take the algebra below as an example, following our previous recipe
class Bad t where
    bool_bad :: Bool -> t
    lam_bad :: (t -> t) -> t
    app_bad :: t -> t -> t

-- This still type check, so the type still fails to capture the well-typedness
-- of our language
test :: (Bad f) => f
test = app_bad (bool_bad True) (bool_bad False)

-- This is because we use a type param `t` to encapsulate the entire representation
-- of our language, thus essentially "uni-typed" our object language.
class Good repr where
    bool_good :: Bool -> repr Bool
    lam_good :: (repr a -> repr b) -> repr (a -> b)
    app_good :: repr (a -> b) -> repr a -> repr b

-- And now the term below doesn't type check!
--
-- test_should_fail :: (Good f) => f a
-- test_should_fail = app_good (bool_good True) (bool_good False)

-- Let's do the language in the paper!
-- The interface gives the syntax of the language,
-- and its instances give the semantics
class Algebra repr where
    int :: Int -> repr Int
    bool :: Bool -> repr Bool
    lam :: (repr a -> repr b) -> repr (a -> b)
    app :: repr (a -> b) -> repr a -> repr b
    -- it seems also fine to define fix as:
    -- fix :: repr (a -> a) -> repr a
    -- just need to additionally use a `lam` when constructing terms
    -- The current definition simplifies our instance definition (see below)
    fix :: (repr a -> repr a) -> repr a
    add :: repr Int -> repr Int -> repr Int
    sub :: repr Int -> repr Int -> repr Int
    mul :: repr Int -> repr Int -> repr Int
    leq :: repr Int -> repr Int -> repr Bool
    if_ :: repr Bool -> repr a -> repr a -> repr a

fibF' :: (Int -> Int) -> Int -> Int
fibF' =
    \f ->
        \n ->
            if n == 0
                then 0
                else if n == 1
                    then 1
                    else f (n - 1) + f (n - 2)


fibF :: (Algebra repr) => repr (Int -> Int) -> repr (Int -> Int)
fibF =
    \f -> lam (\n ->
        if_ (leq n (int 0))
            (int 0)
            (if_ (leq n (int 1))
                (int 1)
                (add
                    (app f (sub n (int 1)))
                    (app f (sub n (int 2))))))


fib :: (Algebra repr) => repr (Int -> Int)
fib = fix fibF

-- this is kinda verbose, but...
newtype R a = R {unR :: a}
    deriving (Show)

instance Algebra R where
  int :: Int -> R Int
  int = R
  bool :: Bool -> R Bool
  bool = R
  lam :: (R a -> R b) -> R (a -> b)
  lam f = R $ \a -> unR $ f (R a)
  app :: R (a -> b) -> R a -> R b
  app (R f) (R a) = R (f a)
  fix :: (R a -> R a) -> R a
  fix = F.fix
  add :: R Int -> R Int -> R Int
  add (R x) (R y) = R $ x + y
  sub :: R Int -> R Int -> R Int
  sub (R x) (R y) = R $ x - y
  mul :: R Int -> R Int -> R Int
  mul (R x) (R y) = R $ x * y
  leq :: R Int -> R Int -> R Bool
  leq (R x) (R y) = R $ x <= y
  if_ :: R Bool -> R a -> R a -> R a
  if_ (R b) (R t) (R e) = R $ if b then t else e
