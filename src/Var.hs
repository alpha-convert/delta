module Var(
    Var(..),
    TyVar(..),
    FunVar(..)
) where
import Util.PrettyPrint (PrettyPrint (..))

data Var = Var String deriving (Eq, Ord, Show)

data TyVar = TyVar String deriving (Eq,Ord,Show)

data FunVar = FunVar String deriving (Eq,Ord,Show)

instance PrettyPrint Var where
    pp (Var x) = x

instance PrettyPrint TyVar where
    pp (TyVar x) = x

instance PrettyPrint FunVar where
    pp (FunVar x) = x