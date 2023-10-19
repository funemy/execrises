{-# OPTIONS_GHC -W #-}

module NbE where

import Prelude hiding (lookup)

newtype Name = Name String
    deriving (Eq, Show)

newtype Env v = Env [(Name, v)]
    deriving (Eq, Show)

data Expr
    = Lit Int
    | Lambda Name Expr
    | App Expr Expr
    | Var Name
    deriving (Eq)

instance Show Expr where
    show (Lit i) = show i
    show (Lambda (Name n) e) = "λ " ++ n ++ " . " ++ show e
    show (App f a) = "(" ++ show f ++ " " ++ show a ++ ")"
    show (Var (Name n)) = n

data Value
    = VLit Int
    | Closure (Env Normal) Name Expr
    deriving (Eq, Show)

-- NOTE:
-- Neutrals are:
-- 1. a variable,
-- 2. an eliminator whose target is neutral and all other arguments are *type annotated Normals*.
--    the reason for require type annotations is because we will have to call readbackNormal recursively
--    on those Normal terms, which requires a type as input.
data Neutral
    = NVar Name
    | NApp Neutral (Ty, Normal)
    deriving (Eq, Show)

-- NOTE:
-- The key design of NbE is that:
-- 1. Embedding a Neutral as a Normal requires a type annotations
-- 2. Building a Neutral with a Normal subterm requires a type annotation.
data Normal
    = NValue Value
    | Neutral Ty Neutral
    deriving (Eq, Show)

data Ty
    = TyInt
    | TyFun Ty Ty
    deriving (Eq)

instance Show Ty where
    show TyInt = "Int"
    show (TyFun t1@(TyFun{}) t2) = "(" ++ show t1 ++ ")" ++ " -> " ++ show t2
    show (TyFun t1 t2) = show t1 ++ " -> " ++ show t2

lookup :: Env v -> Name -> v
lookup (Env []) _ = error "lookup failure"
lookup (Env (x : xs)) n = if fst x == n then snd x else lookup (Env xs) n

extend :: Env v -> Name -> v -> Env v
extend (Env e) n v = Env $ (n, v) : e

emptyEnv :: Env v
emptyEnv = Env []

toVal :: Env Normal -> Expr -> Normal
toVal _ (Lit i) = NValue (VLit i)
toVal env (Lambda n b) = NValue (Closure env n b)
toVal env (App f a) = doApp (toVal env f) (toVal env a)
toVal env (Var v) = lookup env v

doApp :: Normal -> Normal -> Normal
doApp (NValue (Closure env n body)) arg = toVal (extend env n arg) body
doApp (Neutral (TyFun tyIn tyOut) neu) arg = Neutral tyOut (NApp neu (tyIn, arg))
doApp _ _ = error "Invalid application"

-- An ugly implementation of a fresh name generator
fresh :: [Name] -> Name -> Name
fresh used n@(Name str) =
    if n `elem` used
        then fresh used (Name (str ++ "'"))
        else n

readbackNormal :: [Name] -> Ty -> Normal -> Expr
readbackNormal _ _ (NValue (VLit i)) = Lit i
readbackNormal used (TyFun tyIn tyOut) f =
    let x = fresh used (Name "x")
        app = doApp f (Neutral tyIn (NVar x))
        app' = readbackNormal (x : used) tyOut app
     in Lambda x app'
readbackNormal used _ (Neutral _ neu) = readbackNeutral used neu
readbackNormal _ ty norm = error $ "Invalid typed readback of " ++ show norm ++ " : " ++ show ty

readbackNeutral ::  [Name] -> Neutral -> Expr
readbackNeutral _ (NVar n) = Var n
readbackNeutral used (NApp f a) =
    let f' = readbackNeutral used f
        a' = uncurry (readbackNormal used) a
     in App f' a'

normalize :: Expr -> Ty -> Expr
normalize e ty = readbackNormal [] ty (toVal emptyEnv e)

test :: Expr -> Ty -> IO ()
test e ty = do
    putStrLn "Normalizing:"
    putStrLn "Type: "
    print ty
    putStrLn "Term: "
    print e
    putStrLn "Result: "
    print (normalize e ty)
    putStrLn ""

f, x, y :: Name
f = Name "f"
x = Name "x"
y = Name "y"

e1, e2, e3 :: Expr
ty1, ty2, ty3 :: Ty

e1 = Lambda f (Var f)
ty1 = TyFun (TyFun TyInt TyInt) (TyFun TyInt TyInt)

e2 = App (Lambda x (Lambda y (Var y))) (Lit 1)
ty2 = TyFun TyInt TyInt

e3 = App (Lambda x (Lambda y (Var x))) (Lit 1)
ty3 = TyFun TyInt TyInt

main :: IO ()
main = do
    test e1 ty1
    test e2 ty2
    test e3 ty3
