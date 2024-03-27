-- Cont is a monad encoding the computation that:
--  takes a continuation (a -> r), and produce the final result r.
--
-- In that sense, Cont monad encapsulate a computation that's waiting for
-- its continuation, where the continuation is function (a -> r).
--
-- And the continuation (a -> r) can just be seen as a computation with a hole,
-- where the type of the hole if `a`, and the result of the computation is `r`.
--
-- Since the Cont monad takes a continuation as input, it is really describing
-- values in CPS.
--
-- Because `Cont r a` can compute result `r` either by taking an `a -> r` or
-- directly producing an `r`, the implementation of `Cont r a` must know how
-- to produce a value of either `a` or `r`.
--
-- Another way to look at `Cont` is that this is the elimination form of value `a`.
-- (final encoding?)
newtype Cont r a = Cont { runCont :: (a -> r) -> r }

instance Functor (Cont r) where
  -- Since `Cont r a` knows how to produce either value `a` or `r`,
  -- now it knows how to produce `a`, then by know the transformation `a -> b`,
  -- it now knows how to produce a value of `v`, therefore we can construct
  -- `Cont r b` (in the cause it knows how to produce `r`, we don't need to do anything).
  fmap :: (a -> b) -> Cont r a -> Cont r b
  fmap f c = Cont $ \k -> runCont c (k . f)

instance Applicative (Cont r) where
  -- If we know how to produce `a`, then when given an arbitrary continuation `a -> r`,
  -- I know how to produce `r` (by plug in the `a`).
  --
  -- The implementation of `pure` best shown why the Cont monad is doing CPS transform.
  pure :: a -> Cont r a
  pure a = Cont $ \k -> k a
  (<*>) :: Cont r (a -> b) -> Cont r a -> Cont r b
  (<*>) cf ca = Cont $ \k -> runCont cf (\f -> runCont ca (k . f))

instance Monad (Cont r) where
  -- As mentioned above, `Cont` monad is representing a value in CPS,
  -- this bind is essentially constructing programs in CPS.
  (>>=) :: Cont r a -> (a -> Cont r b) -> Cont r b
  m >>= f = Cont $ \k -> runCont m (\a -> runCont (f a) k)

test1 :: Int
test1 =
  let cont1 = Cont (\k -> k 2)
      cont2 = do
        a <- cont1
        return (a + a)
   in runCont cont2 id

class Monad m => MonadCont m where
  callCC :: ((a -> m b) -> m a) -> m a

-- Take an arbitrary continuation, and go to this _specific_ continuation
-- Notice in the returned Cont, the provided continuation is discarded.
-- Also notice because the provided continuation is not gonna used, it can produce arbitrary value (thus the return type is `Cont r x`)
goto :: (a -> r) -> a -> Cont r x
goto c a = Cont $ \_ -> c a

-- The current-continuation is actually the function (a -> r) hidden in `Cont r a`.
-- We call 'f with the current continuation.
instance MonadCont (Cont r) where
  -- Taking the "final encoding" view, this is essentially:
  -- ((a -> x) -> a) -> a
  -- i.e., Peirce's law in classical logic
  --
  -- the `Cont r x` makes the type more informative, suggesting that this is a computation where the continuation doesn't matter,
  -- i.e., the continuation can be an arbitrary `x -> r`, in other words, the continuation here (the rest of the computation) is
  -- not being used, precisely because we are jumping to the continuation where `callCC` is called.
  --
  -- It's also not hard to see that `goto` exactly captures this semantics.
  callCC :: ((a -> Cont r x) -> Cont r a) -> Cont r a
  -- With the `goto` function defined above, we can re-define `callCC` in a more intuitive way.
  -- `callCC` calls function f with the current continuation.
  -- The type of `f` is weird, it take a function (a -> Cont r x), and returns `Cont r a`
  -- Let's call it an _escape_ function.
  -- The type of a _escape_ function says, given a value of type 'a, I'll return a continuation Cont r x, that eventually computes a value of r
  -- when given (x -> r) as the rest of the computation.
  -- ('x is a free type variable, therefore universally quantified. So this `Cont r x` will compute 'r with arbitrary continuation (x -> r))
  -- This sounds like magic! The reason this is even possible, is we already have another continuation 'k captured from the syntactic scope.
  -- Moreover, 'k is a function of type (a -> r). So once the input value of type 'a is given, we can just apply 'k to it and get our result 'r.
  -- Therefore, `escape` is just `goto k`
  -- Provided with `escape`, 'f will return a computation of `Cont r a`
  -- But now if you think about it, 'f has two ways to construct `Cont r a`.
  -- 1. Applying `escape` on a value of type 'a
  -- 2. Not using `escape`, but directly return a `Cont r a`
  -- Approach 1 provides an "early escape" for 'f to return to the current continuation earlier, without finishing its remaining computation.
  callCC f = Cont $ \k -> runCont (f (goto k)) k
  -- callCC f = Cont $ \k -> runCont (f (\a -> Cont (\_ -> k a))) k

test2 :: IO ()
test2 =
  let cont1 = callCC $ \exit1 -> do
        e <- callCC $ \exit2 -> if True then exit1 42 else exit2 0
        return (e + 1)
   in runCont cont1 (\a -> putStrLn ("exit with " ++ show a))
