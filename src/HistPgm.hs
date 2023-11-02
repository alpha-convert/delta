{-# LANGUAGE FlexibleContexts #-}
module HistPgm where

import Var
import Util.PrettyPrint (PrettyPrint(..))
import Values (MaximalPrefix (..), Lit, Prefix (LitPEmp))
import Control.Monad.Except ( ExceptT, MonadError (throwError) )

data Term =
      TmLit Lit
    | TmEps
    | TmVar Var
    | TmPair Term Term
    | TmInl Term
    | TmInr Term
    | TmNil
    | TmCons Term Term
    deriving (Eq,Ord,Show)


instance PrettyPrint Term where
    pp = go False
        where
            go _ (TmLit l) = pp l
            go _ (TmVar x) = pp x
            go _ TmNil = "nil"
            go _ TmEps = "eps"
            go _ (TmPair e1 e2) = concat ["(",go False e1,";",go False e2,")"]
            go True e = concat ["(", go False e, ")"]
            go False (TmInl e) = "inl " ++ go True e
            go False (TmInr e) = "inl " ++ go True e
            go False (TmCons e1 e2) = concat [go True e1," :: ", go True e2]

data HistSemErr = NonClosed Var | BadCons MaximalPrefix Term Term

instance PrettyPrint HistSemErr where
    pp (NonClosed x) = "Term not closed, encountered variable " ++ pp x
    pp (BadCons p2 e1 e2) = concat ["Could not compute cons ", pp (TmCons e1 e2), " because ", pp e2, " evaluated to ", pp p2]

eval :: (MonadError HistSemErr m) => Term -> m MaximalPrefix
eval (TmLit l) = return (LitMP l)
eval TmEps = return EpsMP
eval (TmVar x) = throwError (NonClosed x)
eval (TmPair e1 e2) = do
    p1 <- eval e1
    p2 <- eval e2
    return (CatMP p1 p2)
eval (TmInl e) = SumMPA <$> eval e
eval (TmInr e) = SumMPB <$> eval e
eval TmNil = return (StMP [])
eval (TmCons e1 e2) = do
    p1 <- eval e1
    p2 <- eval e2
    case p2 of
        StMP ps -> return (StMP (p1:ps))
        _ -> throwError (BadCons p2 e1 e2)


substVar :: Term -> Var -> Var -> Term
substVar e@(TmLit _) _ _ = e
substVar e@TmEps _ _ = e
substVar (TmVar z) x y | z == y = TmVar x
substVar (TmVar z) _ _ = TmVar z
substVar (TmPair e1 e2) x y = TmPair (substVar e1 x y) (substVar e2 x y)
substVar (TmInl e) x y = TmInl (substVar e x y)
substVar (TmInr e) x y = TmInr (substVar e x y)
substVar e@TmNil _ _ = e
substVar (TmCons e1 e2) x y = TmCons (substVar e1 x y) (substVar e2 x y)


maximalPrefixToTerm :: MaximalPrefix -> Term
maximalPrefixToTerm EpsMP = TmEps
maximalPrefixToTerm (LitMP l) = TmLit l
maximalPrefixToTerm (CatMP p1 p2) = TmPair (maximalPrefixToTerm p1) (maximalPrefixToTerm p2)
maximalPrefixToTerm (SumMPA p) = TmInl (maximalPrefixToTerm p)
maximalPrefixToTerm (SumMPB p) = TmInr (maximalPrefixToTerm p)
maximalPrefixToTerm (StMP ps) = go ps
  where
    go [] = TmNil
    go (p:ps') = TmCons (maximalPrefixToTerm p) (go ps')

maximalPrefixSubst :: (Monad m) => MaximalPrefix -> Var -> Term -> ExceptT (Var,MaximalPrefix,Term) m Term
maximalPrefixSubst _ _ e@(TmLit _) = return e
maximalPrefixSubst _ _ e@TmEps = return e
maximalPrefixSubst p x (TmVar y) | x == y = return (maximalPrefixToTerm p)
maximalPrefixSubst _ _ e@(TmVar _) = return e

maximalPrefixSubst p x (TmPair e1 e2) = do
  e1' <- maximalPrefixSubst p x e1
  e2' <- maximalPrefixSubst p x e2
  return (TmPair e1' e2')
maximalPrefixSubst p x (TmInl e') = TmInl <$> maximalPrefixSubst p x e'
maximalPrefixSubst p x (TmInr e') = TmInr <$> maximalPrefixSubst p x e'


maximalPrefixSubst _ _ e@TmNil = return e
maximalPrefixSubst p x (TmCons e1 e2) = do
  e1' <- maximalPrefixSubst p x e1
  e2' <- maximalPrefixSubst p x e2
  return (TmCons e1' e2')