module Var(
    Var(..),
    TyVar(..)
) where
import Util.PrettyPrint (PrettyPrint (..))

data Var = Var String deriving (Eq, Ord, Show)

data TyVar = TyVar String deriving (Eq,Ord,Show)

instance PrettyPrint Var where
    pp (Var x) = x

instance PrettyPrint TyVar where
    pp (TyVar x) = x