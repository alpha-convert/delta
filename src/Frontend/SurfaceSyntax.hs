{-# LANGUAGE DeriveTraversable, DeriveFoldable, DeriveFunctor #-}
module Frontend.SurfaceSyntax(Term(..), FunDef(..), Program(..)) where
import Values ( Lit(..), Prefix)
import Var(Var(..))
import Types

data Term =
      TmLitR Lit
    | TmEpsR
    | TmVar Var.Var
    | TmCatL (Maybe Var.Var) (Maybe Var.Var) Term Term
    | TmCatR Term Term
    | TmInl Term
    | TmInr Term
    | TmPlusCase Term (Maybe Var.Var) Term (Maybe Var.Var) Term
    deriving (Eq,Ord,Show)

data FunDef a = FD String (Ctx Var.Var) Ty a deriving (Eq,Ord,Show, Functor, Foldable, Traversable)

type Program a = [FunDef a]