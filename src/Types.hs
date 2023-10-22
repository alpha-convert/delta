module Types where
import Var ( Var )

data Ty = TyEps | TyInt | TyBool | TyCat Ty Ty | TyPlus Ty Ty deriving (Eq,Ord,Show)