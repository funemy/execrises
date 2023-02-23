module Normalizer where

import           Data.Bifunctor (second)
import           Prelude        hiding (lookup)

newtype Name = Name String
    deriving (Eq)

instance Show Name where
  show (Name s) = s

data Expr =
    Var Name
    | Lam Name Expr
    | App Expr Expr
    deriving (Eq)

instance Show Expr where
  show (Var n)     = show n
  show (Lam n e)   = "λ" ++ show n ++ "." ++ show e
  show (App e1 e2) = "(" ++ show e1 ++ " " ++ show e2 ++ ")"


-- Value is a semi-normal form
-- Notice that VClosure is not a fully normal form,
-- where the Expr (i.e., the closure body) has not been normalized
data Value =
    VClosure (Env Value) Name Expr
    | VNeutral Neutral
    deriving (Show, Eq)

data Neutral =
    NVar Name
    | NApp Neutral Value
    deriving (Show, Eq)

newtype Env val = Env [(Name, val)]
    deriving (Show, Eq)

emptyEnv :: Env v
emptyEnv = Env []

instance Functor Env where
  fmap f (Env xs) = Env (map (second f) xs)

newtype Msg = Msg String
    deriving (Show)

type Res v = Either Msg v

failure :: String -> Res v
failure =  Left . Msg

lookup :: Env v -> Name -> Res v
lookup (Env []) (Name n) = failure ("Not found identifier " ++ n)
lookup (Env ((x, v) : xs)) n
    | x == n = Right v
    | otherwise = lookup (Env xs) n

extend :: Env v -> Name -> v -> Env v
extend (Env xs) n val = Env ((n, val) : xs)

-- Given a list of used names and a proposed name,
-- return a non-conflicting name
-- The proposed name will be returned if it is non-conflicting
freshen :: [Name] -> Name -> Name
freshen used x
    | x `elem` used  = freshen used (nextName x)
    | otherwise = x
    where
        nextName :: Name -> Name
        nextName (Name s) = Name (s ++ "'")

-- Given an environment, evaluate an expression to a value (or an error message)
-- The implementation for Lam and App is worth noticing.
-- Lambdas are evaluated to closures, which carry their contexts
-- Applications thus apply a closure to an argument via a helper function `apply`, which in turn extend the context (with the argument) and evaluate the lambda body
-- Another way of implementing untyped lambda calculus is to define substitution (refer to TAPL's impl).
eval :: Env Value -> Expr -> Res Value
eval env (Var n)   = lookup env n
eval env (Lam n b) = return $ VClosure env n b
eval env (App f a) = do
    fun <- eval env f
    arg <- eval env a
    apply fun arg

apply :: Value -> Value -> Res Value
apply (VClosure env n b) arg =
    let env' = extend env n arg
     in eval env' b
apply (VNeutral neu) arg = return $ VNeutral $ NApp neu arg

readback :: [Name] -> Value -> Res Expr
readback used closure@(VClosure _ n _) =
    let n' = freshen used n
        used' = n' : used
     in do
        val <- apply closure (VNeutral (NVar n'))
        b' <- readback used' val
        return $ Lam n' b'
readback _ (VNeutral (NVar n)) = return $ Var n
readback used (VNeutral (NApp neu val)) = do
    neu' <- readback used (VNeutral neu)
    val' <- readback used val
    return $ App neu' val'

define :: Env Value -> [(Name, Expr)] -> Res (Env Value)
define env [] = return env
define env ((n, e) : xs) = do
    v <- eval env e
    let env' = extend env n v
     in define env' xs

-- Zero in Church numeral
-- \s.\z.z
zero :: Expr
zero =
    let s = Name "s"
        z = Name "z"
     in Lam s (Lam z (Var z))

-- add1 in Church numeral
-- \n.\s.\z. s (n s z)
add1 :: (Name, Expr)
add1 =
    let n = Name "n"
        s = Name "s"
        z = Name "z"
     in (Name "add1", Lam n $ Lam s $ Lam z $ App (Var s) (App (App (Var n) (Var s)) (Var z)))

-- plus in Church numeral
-- \x.\y.\s.\z. x s (y s z)
plus :: (Name, Expr)
plus =
    let x = Name "x"
        y = Name "y"
        s = Name "s"
        z = Name "z"
     in (Name "plus", Lam x $ Lam y $ Lam s $ Lam z $ App (App (Var x) (Var s)) (App (App (Var y) (Var s)) (Var z)))

church :: Int -> Expr
church n
    | n == 0 = zero
    | otherwise = App (Var (Name "add1")) (church (n-1))

-- top-level definitions
toplevels :: [(Name, Expr)]
toplevels = [
    add1,
    plus
    ]

-- Initalize the environment from an empty one and add a set of top-level definitions to it.
initEnv :: Res (Env Value)
initEnv = define emptyEnv toplevels

normalize :: Expr -> Res Expr
normalize e = do
    initEnv' <- initEnv
    val <- eval initEnv' e
    readback [] val

test1 :: Res Expr
test1 =
    let expr = App (App (Var (Name "plus")) (church 2)) (church 3)
     in normalize expr

-- Even if we have some reducible terms wrapped inside a lambda, the lambda body will still be normalized by `readback`
test2 :: Res Expr
test2 =
    let expr = Lam (Name "x") (App (App (Var (Name "plus")) (church 2)) (church 3))
     in normalize expr

-- \x. x (\x. x)
test3 :: Res Expr
test3 =
    let expr = Lam (Name "x") (App (Var (Name "x")) (Lam (Name "x") (Var (Name "x"))))
     in normalize expr
