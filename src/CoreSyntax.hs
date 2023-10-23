module CoreSyntax (Var, Term(..), Lit(..), substVar) where

import Types ( Ty )
import Values ( Lit(..), Env(..) )
import Var (Var)
import qualified Data.Map as M

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
substVar (TmPlusCase (Env m) r z x' e1 y' e2) x y | y == z = TmPlusCase (Env m') r x x' (substVar e1 x y) y' (substVar e2 x y)
  where
    m' = case M.lookup z m of
           Nothing -> error "Impossible"
           Just p -> M.insert x p (M.delete z m)
substVar (TmPlusCase rho r z x' e1 y' e2) x y = TmPlusCase rho r z x' (substVar e1 x y) y' (substVar e2 x y)