module SurfaceSyntax where
import Values ( Lit(..))
import Var(Var(..))

data Term =
      TmLitR Lit
    | TmEpsR
    | TmVar Var.Var
    | TmCatL (Maybe Var.Var) (Maybe Var.Var) Var.Var Term
    | TmCatR Term Term
    | TmInl Term
    | TmInr Term
    | TmPlusCase Var.Var (Maybe Var.Var) Term (Maybe Var.Var) Term
    deriving (Eq,Ord,Show)