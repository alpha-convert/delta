{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
module CoreSyntax (
  Var,
  Term(..),
  Program,
  Cmd(..),
  substVar,
  sinkTm,
  cut,
  maximalPrefixSubst
) where

import Types ( Ty , Ctx (EmpCtx, SngCtx, SemicCtx), ctxFoldM )
import Values ( Lit(..), Env, lookupEnv, bindEnv, unbindEnv, Prefix (..), rebindEnv, MaximalPrefix (..))
import Var (Var (..))
import qualified Data.Map as M
import Util.PrettyPrint (PrettyPrint(..))
import Control.Monad.Except (MonadError (throwError), ExceptT, withExceptT)
import Data.Bifunctor
import qualified HistPgm as Hist

data Term =
      TmLitR Lit
    | TmEpsR
    | TmVar Var
    | TmCatL Ty Var Var Var Term
    | TmCatR Term Term
    | TmInl Term
    | TmInr Term
    | TmPlusCase (M.Map Var Ty) (Env Var Prefix) Ty Var Var Term Var Term
    | TmNil
    | TmCons Term Term
    | TmStarCase (M.Map Var Ty) (Env Var Prefix) Ty Ty Var Term Var Var Term {- first return type, then star type -}
    | TmFix (Ctx Var Term) (Ctx Var Ty) Ty Term
    | TmRec (Ctx Var Term)
    | TmWait (Env Var Prefix) Ty Var Term
    | TmCut Var Term Term
    | TmHistPgm Ty Hist.Term
    deriving (Eq, Ord, Show)

data Cmd =
    FunDef String (Ctx Var.Var Ty) Ty Term
  | RunCommand String (Env Var Prefix)
  | RunStepCommand String (Env Var Prefix)
    deriving (Eq,Ord,Show)

type Program = [Cmd]

instance PrettyPrint Term where
    pp = go False
        where
            go _ (TmLitR l) = pp l
            go _ TmEpsR = "sink"
            go _ (TmVar (Var x)) = x
            go _ (TmCatR e1 e2) = concat ["(",go False e1,";",go False e2,")"]
            go _ TmNil = "nil"
            go _ (TmRec args) = "rec(" ++ pp args ++ ")"
            go _ (TmHistPgm _ he) = concat ["{", pp he, "}"]
            go True e = concat ["(", go False e, ")"]
            go _ (TmFix _ _ _ e) = concat ["fix(",go False e,")"]
            go _ (TmCatL t (Var x) (Var y) (Var z) e) = concat ["let_{",pp t,"} (",x,";",y,") = ",z," in ",go False e]
            go _ (TmInl e) = "inl " ++ go True e
            go _ (TmInr e) = "inl " ++ go True e
            go _ (TmPlusCase m rho _ (Var z) (Var x) e1 (Var y) e2) = concat ["case_",pp rho,"|",pp m," ",z," of inl ",x," => ",go True e1," | inr",y," => ",go True e2]
            go _ (TmCons e1 e2) = concat [go True e1," :: ",go True e2]
            go _ (TmStarCase m rho _ _ (Var z) e1 (Var x) (Var xs) e2) = concat ["case_",pp rho,"|",pp m," ",z," of nil => ",go True e1," | ",x,"::",xs," => ",go True e2]
            go False (TmWait rho _ x e) = concat ["wait_",pp rho," ", pp x," do ", go True e]
            go _ (TmCut x e e') = concat ["let ",pp x," = ", go True e, " in ", go True e']

rebind :: Ord k => M.Map k a -> k -> k -> M.Map k a
rebind m x z = case M.lookup z m of
                 Nothing -> error "Impossible"
                 Just p -> M.insert x p (M.delete z m)

-- substVar e x y = e[x/y]
-- Requires e be fully alpha-distinct (no shadowing.)
substVar :: Term -> Var -> Var -> Term
substVar (TmLitR l) _ _ = TmLitR l
substVar TmEpsR _ _ = TmEpsR
substVar (TmVar x') x y | y == x' = TmVar x
substVar (TmVar x') _ _ = TmVar x'
substVar (TmCatL t x' y' z e) x y | y == z = TmCatL t x' y' x (substVar e x y)
substVar (TmCatL t x' y' z e) x y = TmCatL t x' y' z (substVar e x y) {- FIXME: ensure this doesn't capture!! -}
substVar (TmCatR e1 e2) x y = TmCatR (substVar e1 x y) (substVar e2 x y)
substVar (TmInl e) x y = TmInl (substVar e x y)
substVar (TmInr e) x y = TmInr (substVar e x y)
substVar (TmPlusCase m rho r z x' e1 y' e2) x y | y == z = TmPlusCase m' rho' r x x' (substVar e1 x y) y' (substVar e2 x y)
  where
    rho' = case Values.lookupEnv z rho of
           Nothing -> error "Impossible"
           Just p -> bindEnv x p (unbindEnv z rho)
    m' = rebind m x z
substVar (TmPlusCase m rho r z x' e1 y' e2) x y = TmPlusCase m' rho r z x' (substVar e1 x y) y' (substVar e2 x y)
  where
    m' = case M.lookup y m of
           Nothing -> m
           Just p -> M.insert x p (M.delete y m)

substVar TmNil _ _ = TmNil
substVar (TmCons e1 e2) x y = TmCons (substVar e1 x y) (substVar e2 x y)
substVar (TmStarCase m rho r s z e1 x' xs' e2) x y | y == z = TmStarCase m' rho' r s z (substVar e1 x y) x' xs' (substVar e2 x y)
  where
    rho' = case Values.lookupEnv z rho of
           Nothing -> error "Impossible"
           Just p -> bindEnv x p (unbindEnv z rho)
    m' = rebind m x z
substVar (TmStarCase m rho r s z e1 x' xs' e2) x y = TmStarCase m' rho r s z (substVar e1 x y) x' xs' (substVar e2 x y)
  where
    m' = case M.lookup y m of
           Nothing -> m
           Just p -> M.insert x p (M.delete y m)

-- TODO: are these correct?
substVar (TmRec args) x y = TmRec $ second (\e -> substVar e x y) args
substVar (TmFix args g s e) x y = TmFix (second (\e' -> substVar e' x y) args) g s e
substVar (TmWait rho t u e) x y = if x == u then TmWait rho' t y (substVar e x y) else TmWait rho' t u (substVar e x y)
  where
    rho' = rebindEnv rho y u

substVar (TmCut x' e1 e2) x y = TmCut x' (substVar e1 x y) (substVar e2 x y)

substVar (TmHistPgm t he) x y = TmHistPgm t (Hist.substVar he x y)

cut :: (MonadError (Var,Term,Term) m) => Var -> Term -> Term -> m Term
cut _ _ e'@(TmLitR _) = return e'
cut _ _ e'@TmEpsR = return e'
cut _ _ e'@TmNil = return e'
cut x e e'@(TmVar y) = if x == y then return e else return e'

cut x (TmCatL t' x'' y'' z' e'') e' = TmCatL t' x'' y'' z' <$> cut x e'' e'
cut x (TmPlusCase m rho r z x'' e1 y'' e2) e' = do
    e1' <- cut x e1 e'
    e2' <- cut x e2 e'
    -- FIXME: Is this "rho" correct here? I think it might not be.
    return (TmPlusCase m rho r z x'' e1' y'' e2')

cut x e                     (TmCatL t x' y' z e') | x /= z = TmCatL t x' y' z <$> cut x e e'
cut _ (TmVar z)        (TmCatL t x' y' _ e') = return (TmCatL t  x' y' z e')
cut _ (TmCatR e1 e2)   (TmCatL _ x' y' _ e') = cut x' e1 e' >>= cut y' e2
-- cut x e                     e'@(TmCatL {}) = throwError (x,e,e')

cut x e                 (TmPlusCase m rho t z x' e1 y' e2) | x /= z = do
    e1' <- cut x e e1
    e2' <- cut x e e2
    return (TmPlusCase (M.delete x m) rho t z x' e1' y' e2')
cut z (TmVar x)    (TmPlusCase m rho t _ x' e1 y' e2) = return (TmPlusCase (rebind m x z) rho t x x' e1 y' e2)
cut _ (TmInl e)    (TmPlusCase _ _ _ _ x' e1 _ _) = cut x' e e1
cut _ (TmInr e)    (TmPlusCase _ _ _ _ _ _ y' e2) = cut y' e e2
-- cut x e                 e'@(TmPlusCase {}) = throwError (x,e,e')

cut x e (TmCatR e1 e2) = TmCatR <$> cut x e e1 <*> cut x e e2
cut x e (TmInl e') = TmInl <$> cut x e e'
cut x e (TmInr e') = TmInr <$> cut x e e'

cut x e (TmCons e1 e2) = TmCons <$> cut x e e1 <*> cut x e e2

cut x e                     (TmStarCase m rho t s z e1 y ys e2) | x /= z = do
    e1' <- cut x e e1
    e2' <- cut x e e2
    return (TmStarCase (M.delete x m) rho t s z e1' y ys e2')

cut z (TmVar x)        (TmStarCase m rho t s _ e1 y ys e2) = return (TmStarCase (rebind m x z) rho t s x e1 y ys e2)
cut _ TmNil            (TmStarCase _ _ _ _ _ e1 _ _ _) = return e1
cut _ (TmCons eh et)   (TmStarCase _ _ _ _ _ _ y ys e2) = cut y eh e2 >>= cut ys et
-- cut x e                     e'@(TmStarCase {}) = throwError (x,e,e')

cut x e (TmFix args g s e') = do
  args' <- mapM (cut x e) args
  return (TmFix args' g s e')
cut x e (TmRec args) = TmRec <$> mapM (cut x e) args

-- We don't know how to cut into a wait. 
cut x e e' = return (TmCut x e e')


-- Throws p if p is not maximal. if p : s and p maximal, the sinkTm : d_p s.
-- At the moment (without par), this returns only TmEpsR
sinkTm :: (MonadError Prefix m) => Prefix -> m Term
sinkTm p@LitPEmp = throwError p
sinkTm (LitPFull _) = return TmEpsR
sinkTm EpsP = return TmEpsR
sinkTm p@(CatPA _) = throwError p
sinkTm (CatPB _ p) = sinkTm p
sinkTm p@SumPEmp = throwError p
sinkTm (SumPA p) = sinkTm p
sinkTm (SumPB p) = sinkTm p
sinkTm p@StpEmp = throwError p
sinkTm StpDone = return TmEpsR
sinkTm p@(StpA _) = throwError p
sinkTm (StpB _ p) = sinkTm p

maximalPrefixToTerm :: MaximalPrefix -> Term
maximalPrefixToTerm EpsMP = TmEpsR
maximalPrefixToTerm (LitMP l) = TmLitR l
maximalPrefixToTerm (CatMP p1 p2) = TmCatR (maximalPrefixToTerm p1) (maximalPrefixToTerm p2)
maximalPrefixToTerm (SumMPA p) = TmInl (maximalPrefixToTerm p)
maximalPrefixToTerm (SumMPB p) = TmInr (maximalPrefixToTerm p)
maximalPrefixToTerm (StMP ps) = go ps
  where
    go [] = TmNil
    go (p:ps') = TmCons (maximalPrefixToTerm p) (go ps')

maximalPrefixSubst :: (Monad m) => MaximalPrefix -> Var -> Term -> ExceptT (Var,MaximalPrefix,Term) m Term
maximalPrefixSubst _ _ e@(TmLitR _) = return e
maximalPrefixSubst _ _ e@TmEpsR = return e
maximalPrefixSubst p x (TmVar y) | x == y = return (maximalPrefixToTerm p)
maximalPrefixSubst _ _ e@(TmVar _) = return e

maximalPrefixSubst p x (TmCatL t x' y' z e') | x /= z = TmCatL t x' y' z <$> maximalPrefixSubst p x e'
maximalPrefixSubst (CatMP p1 p2) _ (TmCatL _ x' y' _ e') = do
  e'' <- maximalPrefixSubst p1 x' e'
  maximalPrefixSubst p2 y' e''
maximalPrefixSubst p x e@(TmCatL {}) = throwError (x,p,e)

maximalPrefixSubst p x (TmCatR e1 e2) = do
  e1' <- maximalPrefixSubst p x e1
  e2' <- maximalPrefixSubst p x e2
  return (TmCatR e1' e2')
maximalPrefixSubst p x (TmInl e') = TmInl <$> maximalPrefixSubst p x e'
maximalPrefixSubst p x (TmInr e') = TmInr <$> maximalPrefixSubst p x e'

maximalPrefixSubst p x (TmPlusCase m rho t z x' e1 y' e2) | x /= z = do
  e1' <- maximalPrefixSubst p x e1
  e2' <- maximalPrefixSubst p x e2
  return (TmPlusCase (M.delete x m) (unbindEnv x rho) t z x' e1' y' e2')
maximalPrefixSubst (SumMPA p) _ (TmPlusCase _ _ _ _ x' e1 _ _) = maximalPrefixSubst p x' e1
maximalPrefixSubst (SumMPB p) _ (TmPlusCase _ _ _ _ _ _ y' e2) = maximalPrefixSubst p y' e2
maximalPrefixSubst p x e@(TmPlusCase {}) = throwError (x,p,e)

maximalPrefixSubst p x (TmStarCase m rho t r z e1 y' ys' e2) | x /= z = do
  e1' <- maximalPrefixSubst p x e1
  e2' <- maximalPrefixSubst p x e2
  return (TmStarCase (M.delete x m) (unbindEnv x rho) t r z e1' y' ys' e2')
maximalPrefixSubst (StMP []) _ (TmStarCase _ _ _ _ _ e1 _ _ _) = return e1
maximalPrefixSubst (StMP (p:ps)) _ (TmStarCase _ _ _ _ _ _ y' ys' e2) = do
  e2' <- maximalPrefixSubst p y' e2
  maximalPrefixSubst (StMP ps) ys' e2'
maximalPrefixSubst p x e@(TmStarCase {}) = throwError (x,p,e)

maximalPrefixSubst _ _ e@TmNil = return e
maximalPrefixSubst p x (TmCons e1 e2) = do
  e1' <- maximalPrefixSubst p x e1
  e2' <- maximalPrefixSubst p x e2
  return (TmCons e1' e2')

maximalPrefixSubst p x (TmWait rho s z e') | x /= z = TmWait (unbindEnv x rho) s z <$> maximalPrefixSubst p x e'
maximalPrefixSubst p _ (TmWait _ _ x e') = maximalPrefixSubst p x e'

maximalPrefixSubst p x (TmFix args g s e') = do
  args' <- mapM (maximalPrefixSubst p x) args
  return (TmFix args' g s e')

maximalPrefixSubst p x (TmRec args) = TmRec <$> mapM (maximalPrefixSubst p x) args

maximalPrefixSubst p x (TmCut y e1 e2) = do
  e1' <- maximalPrefixSubst p x e1
  e2' <- maximalPrefixSubst p x e2
  return (TmCut y e1' e2')

maximalPrefixSubst p x (TmHistPgm t he) = TmHistPgm t <$> withExceptT liftErr (Hist.maximalPrefixSubst p x he)
  where
    liftErr (x,p,e) = (x,p,TmHistPgm t e)
