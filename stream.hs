data St a = Mk a (St a)
    deriving (Show)

hd :: St a -> a
hd (Mk n s) = n

tl :: St a -> St a
tl (Mk n s) = s

tk :: Int -> St a -> [a]
tk 0 _         = []
tk n (Mk n' s) = n' : tk (n-1) s

ones :: St Int
ones = Mk 1 ones

ones' :: St Int
ones' = Mk 1 (tl ones')

s :: St Bool
s = if hd s then undefined else undefined
