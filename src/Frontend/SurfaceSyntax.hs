{-# LANGUAGE DeriveTraversable, DeriveFoldable, DeriveFunctor #-}
module Frontend.SurfaceSyntax(
  Term(..),
  Cmd(..),
  Program,
  UntypedPrefix(..),
) where
import Values ( Lit(..), Prefix)
import qualified Var
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
    | TmIte Term Term Term
    | TmPlusCase Term (Maybe Var.Var) Term (Maybe Var.Var) Term
    | TmNil
    | TmCons Term Term
    | TmStarCase Term Term (Maybe Var.Var) (Maybe Var.Var) Term
    | TmRec (CtxStruct Term)
    | TmWait [Var.Var] Term
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
    FunDef String [Var.TyVar] (Ctx Var.Var (TyF Var.TyVar)) (TyF Var.TyVar) Term
  | RunCommand String [TyF Var.TyVar] (Ctx Var.Var UntypedPrefix)
  | RunStepCommand String (Ctx Var.Var UntypedPrefix)
 deriving (Eq,Ord,Show)

type Program = [Cmd]