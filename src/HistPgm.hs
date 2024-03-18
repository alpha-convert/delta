{-# LANGUAGE FlexibleContexts #-}
module HistPgm where

import Var
import Util.PrettyPrint (PrettyPrint(..))
import Values (Lit(..), Prefix (LitPEmp), MaximalPrefix(..))
import Control.Monad.Except ( ExceptT, MonadError (throwError), withExceptT )
import qualified Data.Map as M
import Types
import Control.Monad.Reader (MonadReader, asks)
import Data.Semigroup (Max)
import Control.Monad (when)
import Data.List (intercalate)
import Control.Monad.Loops (allM)
import Control.Monad (foldM)
import Event


data Value =
      VUnit
    | VInt Int
    | VBool Bool
    | VPair Value Value
    | VInl Value
    | VInr Value
    | VList [Value]
    deriving (Eq,Ord,Show)

maximalPrefixToValue :: MaximalPrefix -> Value
maximalPrefixToValue (LitMP (LInt n)) = VInt n
maximalPrefixToValue (LitMP (LBool b)) = VBool b
maximalPrefixToValue EpsMP = VUnit
maximalPrefixToValue (CatMP p1 p2) = VPair (maximalPrefixToValue p1) (maximalPrefixToValue p2)
maximalPrefixToValue (ParMP p1 p2) = VPair (maximalPrefixToValue p1) (maximalPrefixToValue p2)
maximalPrefixToValue (SumMPA p) = VInl (maximalPrefixToValue p)
maximalPrefixToValue (SumMPB p) = VInr (maximalPrefixToValue p)
maximalPrefixToValue (StMP ps) = VList (map maximalPrefixToValue ps)


instance PrettyPrint Value where
    pp VUnit = "()"
    pp (VInt n) = pp n
    pp (VBool b) = pp b
    pp (VPair v1 v2) = "(" ++ pp v1 ++ "," ++ pp v2 ++ ")"
    pp (VInl v) = "inl(" ++ pp v ++ ")"
    pp (VInr v) = "inr(" ++ pp v ++ ")"
    pp (VList vs) = "[" ++ intercalate "," (map pp vs) ++ "]"

data MonOp = Neg | Not
    deriving (Eq,Ord,Show)

instance PrettyPrint MonOp where
    pp Neg = "-"
    pp Not = "!"


data BinOp = Add | Sub | Mul | Div | Or | And | Lt | Gt | Leq | Geq | Eq | Mod
    deriving (Eq,Ord,Show)

instance PrettyPrint BinOp where
    pp Add = "+"
    pp Sub = "-"
    pp Mul = "*"
    pp Div = "/"
    pp Or = "||"
    pp And = "&&"
    pp Lt = "<"
    pp Gt = ">"
    pp Leq = "<="
    pp Geq = ">="
    pp Eq = "=="
    pp Mod = "%"

data Term =
      TmValue Value
    | TmEps
    | TmVar Var
    | TmPair Term Term
    | TmInl Term
    | TmInr Term
    | TmNil
    | TmCons Term Term
    | TmMonOp MonOp Term
    | TmBinOp BinOp Term Term
    | TmIte Term Term Term
    deriving (Eq,Ord,Show)


instance PrettyPrint Term where
    pp = go False
        where
            go _ (TmValue l) = pp l
            go _ (TmVar x) = pp x
            go _ TmNil = "nil"
            go _ TmEps = "eps"
            go _ (TmPair e1 e2) = concat ["(",go False e1,";",go False e2,")"]
            go True e = concat ["(", go False e, ")"]
            go False (TmInl e) = "inl " ++ go True e
            go False (TmInr e) = "inl " ++ go True e
            go False (TmCons e1 e2) = concat [go True e1," :: ", go True e2]
            go False (TmMonOp m e) = pp m ++ go True e
            go False (TmBinOp b e1 e2) = concat [go True e1," ",pp b," ",go True e2]
            go False (TmIte e e1 e2) = concat ["if ", go True e," then ", go True e1, " else ",go True e2]

data SemErr =
      NonClosed Var
    | BadCons Value Term Term
    | NotValue Term Value
    | NotBool Term Value
    | MonOpError MonOp Value
    | BinOpError BinOp Value Value
    | DivideByZero
    | WrongTypeValueLift Value Ty
    deriving (Eq, Ord, Show)

instance PrettyPrint SemErr where
    pp (NonClosed x) = "Term not closed, encountered variable " ++ pp x
    pp (BadCons p2 e1 e2) = concat ["Could not compute cons ", pp (TmCons e1 e2), " because ", pp e2, " evaluated to ", pp p2]
    pp (NotValue e p) = concat ["Expected term ", pp e," to evaluate to a Valueeral, it evaluated to ", pp p]
    pp (NotBool e l) = concat ["Expected term ", pp e," to evaluate to a boolean, it evaluated to ", pp l]
    pp (MonOpError m l) = concat ["Could not compute MonOp ", pp m, " of ", pp l]
    pp (BinOpError b l l') = concat ["Could not compute BinOp ", pp b, " of ", pp l, " and ", pp l']
    pp DivideByZero = "You divided by zero, silly!"
    pp (WrongTypeValueLift v t) = concat ["Cannot lift value ", pp v, " to a maximal prefix of type ", pp t]




evalBool e = do
    l <- eval e
    case l of
        VBool b -> return b
        _ -> throwError (NotBool e l)

evalMonOp :: (MonadError SemErr m) => MonOp -> Value -> m Value
evalMonOp Neg (VInt n) = return (VInt (-n))
evalMonOp m@Neg l = throwError (MonOpError m l)
evalMonOp Not (VBool b) = return (VBool (not b))
evalMonOp m@Not l = throwError (MonOpError m l)

evalBinOp :: (MonadError SemErr m) => BinOp -> Value -> Value -> m Value
evalBinOp Add (VInt x) (VInt y) = return (VInt (x + y))
evalBinOp b@Add l l' = throwError (BinOpError b l l')
evalBinOp Sub (VInt x) (VInt y) = return (VInt (x - y))
evalBinOp b@Sub l l' = throwError (BinOpError b l l')
evalBinOp Mul (VInt x) (VInt y) = return (VInt (x * y))
evalBinOp b@Mul l l' = throwError (BinOpError b l l')
evalBinOp Div (VInt x) (VInt 0) = throwError DivideByZero
evalBinOp Div (VInt x) (VInt y) = return (VInt (x `div` y))
evalBinOp b@Div l l' = throwError (BinOpError b l l')
evalBinOp And (VBool x) (VBool y) = return (VBool (x && y))
evalBinOp b@And l l' = throwError (BinOpError b l l')
evalBinOp Or (VBool x) (VBool y) = return (VBool (x || y))
evalBinOp b@Or l l' = throwError (BinOpError b l l')
evalBinOp Lt (VInt x) (VInt y) = return (VBool (x < y))
evalBinOp b@Lt l l' = throwError (BinOpError b l l')
evalBinOp Gt (VInt x) (VInt y) = return (VBool (x > y))
evalBinOp b@Gt l l' = throwError (BinOpError b l l')
evalBinOp Geq (VInt x) (VInt y) = return (VBool (x >= y))
evalBinOp b@Geq l l' = throwError (BinOpError b l l')
evalBinOp Leq (VInt x) (VInt y) = return (VBool (x <= y))
evalBinOp b@Leq l l' = throwError (BinOpError b l l')
evalBinOp Eq (VInt x) (VInt y) = return (VBool (x == y))
evalBinOp b@Eq l l' = throwError (BinOpError b l l')
evalBinOp Mod (VInt x) (VInt y) = return (VInt (x `mod` y))
evalBinOp b@Mod l l' = throwError (BinOpError b l l')

eval :: (MonadError SemErr m) => Term -> m Value
eval (TmValue l) = return l
eval TmEps = return VUnit
eval (TmVar x) = throwError (NonClosed x)
eval (TmMonOp m e) = do
    v <- eval e
    evalMonOp m v
eval (TmBinOp b e1 e2) = do
    l <- eval e1
    l' <- eval e2
    evalBinOp b l l'
eval (TmPair e1 e2) = do
    v1 <- eval e1
    v2 <- eval e2
    return (VPair v1 v2)
eval (TmInl e) = VInl <$> eval e
eval (TmInr e) = VInr <$> eval e
eval TmNil = return (VList [])
eval (TmCons e1 e2) = do
    v1 <- eval e1
    v2 <- eval e2
    case v2 of
        VList vs -> return (VList (v1:vs))
        _ -> throwError (BadCons v2 e1 e2)
eval (TmIte e e1 e2) = do
    b <- evalBool e
    if b then eval e1 else eval e2


type HistCtx = M.Map Var OpenTy

data TckErr =
     UnboundVar Var
    | WrongType Term OpenTy
    | WrongTypeValue Value OpenTy
    | WrongTypeVar Var OpenTy OpenTy
    | CheckTerm Term
    | CheckValue Value
    | TurnAroundErr Term OpenTy OpenTy
    | UnequalBranches OpenTy OpenTy Term
    deriving (Eq, Ord, Show)

instance PrettyPrint TckErr where
    pp (UnboundVar x) = "Unbound variable " ++ pp x ++ ". May not be in historical context."
    pp (WrongType e t) = concat ["Term ", pp e, " does not have type ", pp t]
    pp (WrongTypeValue v t) = concat ["Value ", pp v, " does not have type ", pp t]
    pp (WrongTypeVar x t t') = concat ["Expected type ", pp x, " to have type ", pp t," but it has type ", pp t']
    pp (CheckTerm e) = concat ["Term ", pp e, " cannot be inferred"]
    pp (CheckValue v) = concat ["Value ", pp v, " cannot be inferred"]
    pp (TurnAroundErr e t t') = concat ["Expected term ", pp e," to have type ", pp t," but got type ", pp t']
    pp (UnequalBranches s s' e) = concat ["Branches of term ", pp e, " had types ", pp s," and ", pp s']

lookupVar :: (MonadReader (M.Map Var b) m, MonadError TckErr m) => Var -> m b
lookupVar x = asks (M.lookup x) >>= maybe (throwError (UnboundVar x)) return

inferMonOp :: (MonadError TckErr m, MonadReader HistCtx m) => MonOp -> Term -> m OpenTy
inferMonOp Neg e = check e TyInt >> return TyInt
inferMonOp Not e = check e TyBool >> return TyBool

checkMonOp :: (MonadError TckErr m, MonadReader HistCtx m) => MonOp -> Term -> OpenTy -> m ()
checkMonOp Neg e TyInt = check e TyInt
checkMonOp m@Neg e t = throwError (WrongType (TmMonOp m e) t)
checkMonOp Not e TyBool = check e TyBool
checkMonOp m@Not e t = throwError (WrongType (TmMonOp m e) t)

inferBinOp :: (MonadError TckErr m, MonadReader HistCtx m) => BinOp -> Term -> Term -> m OpenTy
inferBinOp Add e1 e2 = check e1 TyInt >> check e2 TyInt >> return TyInt
inferBinOp Sub e1 e2 = check e1 TyInt >> check e2 TyInt >> return TyInt
inferBinOp Mul e1 e2 = check e1 TyInt >> check e2 TyInt >> return TyInt
inferBinOp Div e1 e2 = check e1 TyInt >> check e2 TyInt >> return TyInt
inferBinOp Or e1 e2 = check e1 TyBool >> check e2 TyBool >> return TyBool
inferBinOp And e1 e2 = check e1 TyBool >> check e2 TyBool >> return TyBool
inferBinOp Lt e1 e2 = check e1 TyInt >> check e2 TyInt >> return TyBool
inferBinOp Gt e1 e2 = check e1 TyInt >> check e2 TyInt >> return TyBool
inferBinOp Leq e1 e2 = check e1 TyInt >> check e2 TyInt >> return TyBool
inferBinOp Geq e1 e2 = check e1 TyInt >> check e2 TyInt >> return TyBool
inferBinOp Eq e1 e2 = do
    s <- infer e1
    check e2 s
    return TyBool
inferBinOp Mod e1 e2 = check e1 TyInt >> check e2 TyInt >> return TyInt

checkBinOp :: (MonadError TckErr m, MonadReader HistCtx m) => BinOp -> Term -> Term -> OpenTy -> m ()
checkBinOp Add e1 e2 TyInt = check e1 TyInt >> check e2 TyInt >> return ()
checkBinOp b@Add e1 e2 t = throwError (WrongType (TmBinOp b e1 e2) t)
checkBinOp Sub e1 e2 TyInt = check e1 TyInt >> check e2 TyInt >> return ()
checkBinOp b@Sub e1 e2 t = throwError (WrongType (TmBinOp b e1 e2) t)
checkBinOp Mul e1 e2 TyInt = check e1 TyInt >> check e2 TyInt >> return ()
checkBinOp b@Mul e1 e2 t = throwError (WrongType (TmBinOp b e1 e2) t)
checkBinOp Div e1 e2 TyInt = check e1 TyInt >> check e2 TyInt >> return ()
checkBinOp b@Div e1 e2 t = throwError (WrongType (TmBinOp b e1 e2) t)
checkBinOp And e1 e2 TyBool = check e1 TyBool >> check e2 TyBool >> return ()
checkBinOp b@And e1 e2 t = throwError (WrongType (TmBinOp b e1 e2) t)
checkBinOp Or e1 e2 TyBool = check e1 TyBool >> check e2 TyBool >> return ()
checkBinOp b@Or e1 e2 t = throwError (WrongType (TmBinOp b e1 e2) t)
checkBinOp Lt e1 e2 TyBool = check e1 TyInt >> check e2 TyInt >> return ()
checkBinOp b@Lt e1 e2 t = throwError (WrongType (TmBinOp b e1 e2) t)
checkBinOp Gt e1 e2 TyBool = check e1 TyInt >> check e2 TyInt >> return ()
checkBinOp b@Gt e1 e2 t = throwError (WrongType (TmBinOp b e1 e2) t)
checkBinOp Leq e1 e2 TyBool = check e1 TyInt >> check e2 TyInt >> return ()
checkBinOp b@Leq e1 e2 t = throwError (WrongType (TmBinOp b e1 e2) t)
checkBinOp Geq e1 e2 TyBool = check e1 TyInt >> check e2 TyInt >> return ()
checkBinOp b@Geq e1 e2 t = throwError (WrongType (TmBinOp b e1 e2) t)
checkBinOp Eq e1 e2 TyBool = do
    s <- infer e1
    check e2 s
    return ()
checkBinOp b@Eq e1 e2 t = throwError (WrongType (TmBinOp b e1 e2) t)
checkBinOp Mod e1 e2 TyInt = check e1 TyInt >> check e2 TyInt >> return ()
checkBinOp b@Mod e1 e2 t = throwError (WrongType (TmBinOp b e1 e2) t)

inferValue :: (MonadError TckErr m, MonadReader HistCtx m) => Value -> m OpenTy
inferValue VUnit = return TyEps
inferValue (VInt _) = return TyInt
inferValue (VBool _) = return TyInt
inferValue v@(VPair {}) = throwError (CheckValue v)
inferValue v@(VInl _) = throwError (CheckValue v)
inferValue v@(VInr _) = throwError (CheckValue v)
inferValue v@(VList []) = throwError (CheckValue v)
inferValue (VList (v:vs)) = do
    t <- inferValue v
    mapM_ (`checkValue` t) vs
    return t

infer :: (MonadError TckErr m, MonadReader HistCtx m) => Term -> m OpenTy
infer (TmValue v) = inferValue v
infer TmEps = return TyEps
infer (TmVar x) = lookupVar x
infer (TmMonOp m e) = inferMonOp m e
infer (TmBinOp b e1 e2) = inferBinOp b e1 e2
infer (TmPair e1 e2) = error "Cannot infer type of pair -- could be cat or par."
infer e@(TmInl _) = throwError (CheckTerm e)
infer e@(TmInr _) = throwError (CheckTerm e)
infer e@TmNil = throwError (CheckTerm e)
infer (TmCons e1 e2) = do
    s <- infer e1
    () <- check e2 (TyStar s)
    return (TyStar s)
infer e0@(TmIte e e1 e2) = do
    check e TyBool
    s <- infer e1
    s' <- infer e2
    when (s /= s') (throwError (UnequalBranches s s' e0))
    return s

turnaround :: (MonadError TckErr m, MonadReader HistCtx m) => Term -> OpenTy -> m ()
turnaround e t = do
    t' <- infer e
    when (t /= t') $ throwError (TurnAroundErr e t t')

checkValue :: (MonadError TckErr m, MonadReader HistCtx m) => Value -> OpenTy -> m ()
checkValue VUnit TyEps = return ()
checkValue v@VUnit t = throwError (WrongTypeValue v t)
checkValue (VInt _) TyInt = return ()
checkValue v@(VInt _) t = throwError (WrongTypeValue v t)
checkValue (VBool _) TyBool = return ()
checkValue v@(VBool _) t = throwError (WrongTypeValue v t)

checkValue (VPair v1 v2) (TyCat s t) = checkValue v1 s >> checkValue v2 t
checkValue (VPair v1 v2) (TyPar s t) = checkValue v1 s >> checkValue v2 t
checkValue v@(VPair {}) t = throwError (WrongTypeValue v t)

checkValue (VInl v) (TyPlus s _) = checkValue v s
checkValue v@(VInl _) t = throwError (WrongTypeValue v t)

checkValue (VInr v) (TyPlus _ t) = checkValue v t
checkValue v@(VInr _) t = throwError (WrongTypeValue v t)

checkValue (VList vs) (TyStar s) = mapM_ (`checkValue` s) vs
checkValue v@(VList _) t = throwError (WrongTypeValue v t)

check :: (MonadError TckErr m, MonadReader HistCtx m) => Term -> OpenTy -> m ()
check (TmValue v) t = checkValue v t

check TmEps TyEps = return ()
check e@TmEps t = throwError (WrongType e t)

check (TmVar x) t = do
    t' <- lookupVar x
    if t == t' then return () else throwError (WrongTypeVar x t t')

check e@(TmPair e1 e2) (TyCat s t) = do
    () <- check e1 s
    () <- check e2 t
    return ()
check e@(TmPair e1 e2) (TyPar s t) = do
    () <- check e1 s
    () <- check e2 t
    return ()
check e@(TmPair {}) t = throwError (WrongType e t)

check (TmInl e) (TyPlus s _) = check e s
check e@(TmInl _) t = throwError (WrongType e t)

check (TmInr e) (TyPlus _ t) = check e t
check e@(TmInr _) t = throwError (WrongType e t)

check TmNil (TyStar _) = return ()
check e@TmNil t = throwError (WrongType e t)

check (TmCons e1 e2) (TyStar s) = do
    () <- check e1 s
    () <- check e2 (TyStar s)
    return ()
check e@(TmCons {}) t = throwError (WrongType e t)

check (TmMonOp m e) t = checkMonOp m e t
check (TmBinOp b e e') t = checkBinOp b e e' t

check (TmIte e e1 e2) s = do
    check e TyBool
    check e1 s
    check e2 s

substVar :: Term -> Var -> Var -> Term
substVar e@(TmValue _) _ _ = e
substVar e@TmEps _ _ = e
substVar (TmVar z) x y | z == y = TmVar x
substVar (TmVar z) _ _ = TmVar z
substVar (TmMonOp m e) x y = TmMonOp m (substVar e x y)
substVar (TmBinOp b e e') x y = TmBinOp b (substVar e x y) (substVar e' x y)
substVar (TmPair e1 e2) x y = TmPair (substVar e1 x y) (substVar e2 x y)
substVar (TmInl e) x y = TmInl (substVar e x y)
substVar (TmInr e) x y = TmInr (substVar e x y)
substVar e@TmNil _ _ = e
substVar (TmCons e1 e2) x y = TmCons (substVar e1 x y) (substVar e2 x y)
substVar (TmIte e e1 e2) x y = TmIte (substVar e x y) (substVar e1 x y) (substVar e2 x y)

maximalPrefixSubst :: Monad m => MaximalPrefix -> Var -> Term -> ExceptT (Var, MaximalPrefix , Term) m Term
maximalPrefixSubst p x e = withExceptT (const (x,p,e)) $ valueSubst (maximalPrefixToValue p) x e

valueSubst :: (Monad m) => Value -> Var -> Term -> ExceptT (Var,Value,Term) m Term
valueSubst _ _ e@(TmValue _) = return e
valueSubst _ _ e@TmEps = return e
valueSubst v x (TmVar y) | x == y = return (TmValue v)
valueSubst _ _ e@(TmVar _) = return e

valueSubst p x (TmMonOp m e) = TmMonOp m <$> valueSubst p x e

valueSubst p x (TmBinOp b e1 e2) = do
  e1' <- valueSubst p x e1
  e2' <- valueSubst p x e2
  return (TmBinOp b e1' e2')

valueSubst p x (TmPair e1 e2) = do
  e1' <- valueSubst p x e1
  e2' <- valueSubst p x e2
  return (TmPair e1' e2')
valueSubst p x (TmInl e') = TmInl <$> valueSubst p x e'
valueSubst p x (TmInr e') = TmInr <$> valueSubst p x e'


valueSubst _ _ e@TmNil = return e
valueSubst p x (TmCons e1 e2) = do
  e1' <- valueSubst p x e1
  e2' <- valueSubst p x e2
  return (TmCons e1' e2')

valueSubst p x (TmIte e e1 e2) = do
  e' <- valueSubst p x e
  e1' <- valueSubst p x e1
  e2' <- valueSubst p x e2
  return (TmIte e' e1' e2')

valueToMaximalPrefix :: (MonadError SemErr m) => Ty -> Value -> m MaximalPrefix
valueToMaximalPrefix TyEps VUnit = return EpsMP
valueToMaximalPrefix t v@VUnit = throwError (WrongTypeValueLift v t)

valueToMaximalPrefix TyInt (VInt n) = return (LitMP (LInt n))
valueToMaximalPrefix t v@(VInt _)= throwError (WrongTypeValueLift v t)

valueToMaximalPrefix TyBool (VBool b) = return (LitMP (LBool b))
valueToMaximalPrefix t v@(VBool _)= throwError (WrongTypeValueLift v t)

valueToMaximalPrefix (TyPar s t) (VPair v1 v2) = ParMP <$> valueToMaximalPrefix s v1 <*> valueToMaximalPrefix t v2
valueToMaximalPrefix (TyCat s t) (VPair v1 v2) = CatMP <$> valueToMaximalPrefix s v1 <*> valueToMaximalPrefix t v2
valueToMaximalPrefix t v@(VPair {})= throwError (WrongTypeValueLift v t)

valueToMaximalPrefix (TyPlus s _) (VInl v) = SumMPA <$> valueToMaximalPrefix s v
valueToMaximalPrefix t v@(VInl _)= throwError (WrongTypeValueLift v t)

valueToMaximalPrefix (TyPlus _ t) (VInr v) = SumMPB <$> valueToMaximalPrefix t v
valueToMaximalPrefix t v@(VInr _)= throwError (WrongTypeValueLift v t)

valueToMaximalPrefix (TyStar s) (VList vs) = StMP <$> mapM (valueToMaximalPrefix s) vs
valueToMaximalPrefix t v@(VList {}) = throwError (WrongTypeValueLift v t)

valueToEventList :: MonadError SemErr m => Ty -> Value -> m [Event]
valueToEventList s v = undefined