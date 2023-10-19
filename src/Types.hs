module Types where

data Ty = TyInt | TyBool | TyCat Ty Ty | TyPlus Ty Ty deriving (Eq,Ord,Show)