module BiDiTyCk where

import           Control.Monad.State
import qualified Data.Map            as M
import           Data.Maybe          (isJust)
import qualified Data.Set            as S

-- variable names are represented as strings
type Name = String

-- base values
newtype Base = B Bool
    deriving (Show)

-- types
data Ty = TyBool | Func !Ty !Ty
    deriving (Show, Eq)

-- terms
data Term =
    Atom !Base
    | Var !Name
    | App !Term !Term
    | Lam !Name !Term
    | If !Term !Term !Term
    | Annot !Term !Ty
    deriving (Show)

-- used names
type Used = S.Set String

initUsed :: Used
initUsed = S.empty

-- typing context
type TyCtx = M.Map Name Ty

initTyCtx :: TyCtx
initTyCtx = M.empty

-- a state monad carrying the set of used variable names
type FreshM = State Used

-- a state monad carrying the typing context
type TyCtxM = State TyCtx

-- append a star at the end of the given string
addStar :: String -> String
addStar =  (++ "*")

-- generate a fresh variable name
-- and store the generated name into the state monad
fresh :: String -> FreshM Name
fresh name = do
    used <- get
    if S.member name used
        then fresh (addStar name)
        else do
            put (S.insert name used)
            return name

-- checking rules
-- NOTE: instead of returning Nothing
-- we can return another datatype that carries error messages
checkTy :: Term -> Ty -> TyCtxM (Maybe Ty)
checkTy (Lam n t) fTy@(Func argTy retTy) = do
    ctx <- get
    put (M.insert n argTy ctx)
    ty <- checkTy t retTy
    put ctx
    if isJust ty then return (Just fTy) else return Nothing
checkTy (Lam n t) _ = return Nothing
checkTy (If b t1 t2) ty    = do
    maybeBTy <- inferTy b
    case maybeBTy of
        Just bTy -> if bTy == TyBool
            then do
                maybeT1Ty <- checkTy t1 ty
                maybeT2Ty <- checkTy t2 ty
                case (maybeT1Ty, maybeT2Ty) of
                    (Just t1Ty, Just t2Ty) -> if t1Ty == t2Ty && t1Ty == ty then return (Just ty) else return Nothing
                    _ -> return Nothing
            else return Nothing
        Nothing  -> return Nothing
checkTy t ty = do
    maybeTy' <- inferTy t
    case maybeTy' of
      Nothing  -> return Nothing
      Just ty' -> if ty' == ty then return (Just ty) else return Nothing

-- inference rules
inferTy :: Term -> TyCtxM (Maybe Ty)
inferTy (Atom v)     = case v of { B b -> return (Just TyBool) }
inferTy (Var n)      = do
    ctx <- get
    case M.lookup n ctx of
      Nothing -> return Nothing
      Just ty -> return (Just ty)
inferTy (App t1 t2)  = do
    maybeT1Ty <- inferTy t1
    case maybeT1Ty of
      Nothing -> return Nothing
      Just ty -> case ty of
        (Func argTy retTy) -> do
            t2Ty <- checkTy t2 argTy
            if isJust t2Ty then return (Just retTy) else return Nothing
        _                  -> return Nothing
inferTy (Lam n t)    = error "No inference rule for lambda abstrations"
inferTy (If b t1 t2) = error "No inference rule for if expressions"
inferTy (Annot t ty) = checkTy t ty

true :: Term
true = Atom (B True)

false :: Term
false = Atom (B False)

-- example
-- \b . if b then False else True : Bool -> Bool
term1 :: FreshM Term
term1 = do
    x <- fresh "x"
    return $ Annot (Lam x (If (Var x) false true)) (Func TyBool TyBool)

test1 :: (Maybe Ty, TyCtx)
test1 = let term = evalState term1 initUsed
         in runState (inferTy term) initTyCtx

-- example
-- \f . \g . \b . g (f b) : (Bool -> Bool) -> (Bool -> Bool) -> Bool -> Bool
term2 :: FreshM Term
term2 = do
    f <- fresh "f"
    g <- fresh "g"
    b <- fresh "b"
    let tyAnnot = Func (Func TyBool TyBool) (Func (Func TyBool TyBool) (Func TyBool TyBool))
        term = Lam f (Lam g (Lam b (App (Var g) (App (Var f) (Var b)))))
     in return $ Annot term tyAnnot

test2 :: (Maybe Ty, TyCtx)
test2 = let term = evalState term2 initUsed
         in runState (inferTy term) initTyCtx

-- example
-- (\b . if b then False else True) True : Bool
-- NOTE: This one should not type check
term3 :: FreshM Term
term3 = do
    b <- fresh "b"
    let term = App (Lam b (If (Var b) false true)) true
     in return $ Annot term TyBool

test3 :: Maybe Ty
test3 = let term = evalState term3 initUsed
         in evalState (inferTy term) initTyCtx

-- if True then False else True
term4 :: Term
term4 = If true false true

test4 :: Maybe Ty
test4 = evalState (inferTy term4) initTyCtx

-- (\b . if b then False else True : Bool -> Bool) True
term5 :: FreshM Term
term5 = do
    b <- fresh "b"
    return $ App (Annot (Lam b (If (Var b) false true)) (Func TyBool TyBool)) true

test5 :: Maybe Ty
test5 = let term = evalState term5 initUsed
         in evalState (inferTy term) initTyCtx
