module SurfaceSyntax where

data Var = Var String

data Lit = LInt Int | LBool Bool

data Term =
      TmLitR Lit
    | TmEpsR
    | TmVar Var
    | TmCatL (Maybe Var) (Maybe Var) Term Term
    | TmCatR Term Term
    | TmInl Term
    | TmInr Term
    | TmPlusCase Term (Maybe Var) Term (Maybe Var) Term
    | TmNil
    | TmCons Term Term
    | TmStarCase Term Term (Maybe Var) (Maybe Var) Term