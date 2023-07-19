data St a = Mk a (St a)
    deriving (Show)

data St' a = St'
    { hd' :: a
    , tl' :: St' a
    }

instance Functor St where
    fmap f (Mk h t) = Mk (f h) (fmap f t)

hd :: St a -> a
hd (Mk n s) = n

tl :: St a -> St a
tl (Mk n s) = s

tk :: Int -> St a -> [a]
tk 0 _ = []
tk n (Mk n' s) = n' : tk (n - 1) s

ones :: St Int
ones = Mk 1 ones

ones' :: St Int
ones' = Mk 1 (tl ones')

nats :: St Int
nats = Mk 0 (fmap (+ 1) nats)

s :: St Bool
s = if hd s then undefined else undefined
