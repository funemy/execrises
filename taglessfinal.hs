{-# OPTIONS_GHC -W #-}

module TaglessFinal where
import Text.Printf (printf)

-- our first language
class Algebra t where
    lit :: Int -> t
    add :: t -> t -> t

instance Algebra Int where
    lit = id
    add = (+)

genAST :: Algebra t => t
genAST = add (add (lit 1) (lit 2)) (add (lit 3) (lit 4))

testLang1 :: Int
testLang1 = genAST

-- extend the language with mul
class Algebra t => MulAlgebra t where
    mul :: t -> t -> t

instance MulAlgebra Int where
    mul = (*)

genAST' :: MulAlgebra t => t
genAST' = mul (add (lit 1) (lit 2)) (lit 4)

testLang2 :: Int
testLang2 = genAST'

-- extend a pretty printer
instance Algebra String where
    lit =  show
    add = printf "( %s + %s )"

instance MulAlgebra String where
    mul = printf "( %s * %s )"

testLang1' :: String
testLang1' = genAST

testLang2' :: String
testLang2' = genAST'

-- The implementation above has the problem that for each representation type 't'.
-- We can write only one interpreter
-- For example, the code below won't compile due to duplicated instance
--
-- instance Algebra String where
--     lit = show
--     add = printf "(%s+%s)"
--

-- I guess we can use proxy type
newtype Proxy a t = Proxy t

instance Show t => Show (Proxy a t) where
    show (Proxy t) = show t

data P

instance Algebra (Proxy P String) where
    lit i = Proxy (show i)
    add (Proxy s1) (Proxy s2) = Proxy $ "(" ++ s1 ++ "+" ++ s2 ++ ")"
