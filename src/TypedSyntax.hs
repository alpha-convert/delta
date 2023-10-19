module TypedSyntax (Var, Term(..), Lit(..), substVar) where

import Types ( Ty )
import Values ( Lit(..), Env )

data Var = Var String deriving (Eq,Ord,Show)

data Term =
      TmLitR Lit
    | TmEpsR
    | TmVar Var
    | TmCatL Ty Var Var Var Term
    | TmCatR Term Term
    | TmInl Term
    | TmInr Term
    | TmPlusCase (Env Var) Ty Var Var Term Var Term
    | TmCut Var Term Term
    deriving (Eq, Ord, Show)

freshen :: Term -> Term
freshen = undefined

-- substVar e x y = e[x/y]
substVar :: Term -> Var -> Var -> Term
substVar = undefined