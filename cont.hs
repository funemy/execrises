-- Cont datatype encode the fact that:
--  We know how to compute an intermediate value of type 'a,
--  if we are given a continuation to finish the computation,
--  then we can compute the value of type 'r.
--
-- In that sense, Cont monad encapsulate "what's left to be done"
-- Or if you may, "a CPS execution environment"
--
-- `runCont` can be thought of as runing some actions in some continuations
-- i.e., runCont someAction someContinuation
newtype Cont r a = Cont { runCont :: (a -> r) -> r }

instance Functor (Cont r) where
  -- I already know how to compute value of type 'a
  -- and I know how to convert value of 'a to value of 'b.
  -- Then I know how to finish the computation of 'r as long as you give me the computation from 'b to 'r
  --
  -- In other word, we are closer to the final computation.
  -- We only require a continuation starting from b now.
  fmap :: (a -> b) -> Cont r a -> Cont r b
  fmap f c = Cont $ \k -> runCont c (k . f)

instance Applicative (Cont r) where
  pure :: a -> Cont r a
  pure a = Cont $ \k -> k a
  (<*>) :: Cont r (a -> b) -> Cont r a -> Cont r b
  (<*>) cf ca = Cont $ \k -> runCont cf (\f -> runCont ca (k . f))

instance Monad (Cont r) where
  (>>=) :: Cont r a -> (a -> Cont r b) -> Cont r b
  ca >>= m = Cont $ \k -> runCont ca (\a -> runCont (m a) k)

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
  callCC :: ((a -> Cont r x) -> Cont r a) -> Cont r a
  -- callCC f = Cont $ \k -> runCont (f (\a -> Cont (\_ -> k a))) k
  --
  -- With the `goto` function defined above, we can re-define `callCC` in a more intuitive way.
  -- `callCC` calls function f with the current continuation.
  -- The type of `f` is weird, it take a function (a -> Cont r x), and returns `Cont r a`
  -- Let's call the first argument _escape_ operation.
  -- _escape_ says, given a value of type 'a, I'll return a computation that will result in a value of 'r, not matter what continuation is given.
  -- ('x is a free type variable, therefore universally quantified. So this `Cont r x` will compute 'r with arbitrary continuation (x -> r))
  -- This sounds like magic! The reason this is even possible, is we already have another continuation 'k captured from the syntactic scope.
  -- Moreover, 'k is a continuation of (a -> r). So once the input value of type 'a is given, we can just apply 'k to it and get our result 'r.
  -- Therefore, `escape` is just `goto k`
  -- Provided with `escape`, 'f will return a computation of `Cont r a`
  -- But now if you think about it, 'f has two ways to construct `Cont r a`.
  -- 1. providing `escape` with a value 'a
  -- 2. not using `escape`, but return a `Cont r a`
  -- Approach 1 provides an "early escape" for 'f to return to the current continuation earlier, without finishing its remaining computation.
  callCC f = Cont $ \k -> runCont (f (goto k)) k

test2 :: IO ()
test2 =
  let cont1 = callCC $ \exit1 -> do
        e <- callCC $ \exit2 -> if True then exit1 42 else exit2 0
        return $ (e + 1)
   in runCont cont1 (\a -> putStrLn ("exit with " ++ show a))
