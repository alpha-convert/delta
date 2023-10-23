module Frontend.SurfaceSyntax(Term(..), FunDef(..)) where
import Values ( Lit(..))
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

data FunDef = FD String [(Var.Var,Ty)] Ty Term deriving (Eq,Ord,Show)