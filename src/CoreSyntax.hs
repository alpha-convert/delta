module CoreSyntax (Var, Term(..), substVar, Program, FunDef(..), RunCmd(..)) where

import Types ( Ty , Ctx )
import Values ( Lit(..), Env, lookupEnv, bindEnv, unbindEnv, Prefix)
import Var (Var (..))
import qualified Data.Map as M
import Util.PrettyPrint (PrettyPrint(..))

data Term =
      TmLitR Lit
    | TmEpsR
    | TmVar Var
    | TmCatL Ty Var Var Var Term
    | TmCatR Term Term
    | TmInl Term
    | TmInr Term
    | TmPlusCase (Env Var) Ty Var Var Term Var Term
    deriving (Eq, Ord, Show)

data FunDef = FD String (Ctx Var.Var) Ty Term deriving (Eq,Ord,Show)

data RunCmd = RC String (Env Var)

type Program = [Either FunDef RunCmd]

instance PrettyPrint Term where
    pp = go False
        where
            go _ (TmLitR l) = pp l
            go _ TmEpsR = "sink"
            go _ (TmVar (Var x)) = x
            go _ (TmCatR e1 e2) = concat ["(",go False e1,";",go False e2,")"]
            go True e = concat ["(", go False e, ")"]
            go False (TmCatL t (Var x) (Var y) (Var z) e) = concat ["let_{",pp t,"} (",x,";",y,") = ",z," in ",go False e]
            go False (TmInl e) = "inl " ++ go True e
            go False (TmInr e) = "inl " ++ go True e
            go False (TmPlusCase _ _ (Var z) (Var x) e1 (Var y) e2) = concat ["case ",z," of inl ",x," => ",go True e1," | inr",y," => ",go True e2]

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
substVar (TmPlusCase rho r z x' e1 y' e2) x y | y == z = TmPlusCase rho' r x x' (substVar e1 x y) y' (substVar e2 x y)
  where
    rho' = case Values.lookupEnv z rho of
           Nothing -> error "Impossible"
           Just p -> bindEnv x p (unbindEnv z rho)
substVar (TmPlusCase rho r z x' e1 y' e2) x y = TmPlusCase rho r z x' (substVar e1 x y) y' (substVar e2 x y)