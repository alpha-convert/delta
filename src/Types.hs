module Types where

data Ty = TyEps | TyInt | TyBool | TyCat Ty Ty | TyPlus Ty Ty deriving (Eq,Ord,Show)

data Ctx