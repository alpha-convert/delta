{-# LANGUAGE DeriveTraversable, DeriveFoldable, DeriveFunctor #-}
module Frontend.SurfaceSyntax(
  Term(..),
  Cmd(..),
  Program,
  UntypedPrefix(..),
) where
import Values ( Lit(..), Prefix)
import Var(Var(..))
import Types
import qualified HistPgm as Hist

data Term =
      TmLitR Lit
    | TmEpsR
    | TmVar Var.Var
    | TmCatL (Maybe Var.Var) (Maybe Var.Var) Term Term
    | TmCatR Term Term
    | TmParL (Maybe Var.Var) (Maybe Var.Var) Term Term
    | TmParR Term Term
    | TmInl Term
    | TmInr Term
    | TmPlusCase Term (Maybe Var.Var) Term (Maybe Var.Var) Term
    | TmNil
    | TmCons Term Term
    | TmStarCase Term Term (Maybe Var.Var) (Maybe Var.Var) Term
    | TmRec [Term]
    | TmWait [Var] Term
    | TmHistPgm Hist.Term
    deriving (Eq,Ord,Show)
  
  
data UntypedPrefix =
      EmpP
    | LitP Lit
    | CatPA UntypedPrefix
    | CatPB UntypedPrefix UntypedPrefix
    | ParP UntypedPrefix UntypedPrefix
    | SumPA UntypedPrefix
    | SumPB UntypedPrefix
    | StpA UntypedPrefix
    | StpB UntypedPrefix UntypedPrefix
    | StpDone
    deriving (Eq, Ord, Show)

data Cmd =
    FunDef String (Ctx Var.Var Ty) Ty Term
  | RunCommand String [UntypedPrefix]
  | RunStepCommand String [UntypedPrefix]
 deriving (Eq,Ord,Show)

type Program = [Cmd]