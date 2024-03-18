{-# LANGUAGE DeriveTraversable, DeriveFoldable, DeriveFunctor #-}
module Frontend.SurfaceSyntax(
  Term(..),
  Cmd(..),
  Program,
  UntypedPrefix(..),
  MacroParam(..),
  MacroArg(..)
) where
import Values ( Lit(..), Prefix)
import qualified Var
import Types
import qualified HistPgm as Hist
import Util.PrettyPrint

data MacroArg = NamedMacroArg Var.FunVar
              | MacroUseMacroArg Var.FunVar MacroArg deriving (Eq,Ord,Show)

instance PrettyPrint MacroArg where
    pp (NamedMacroArg f) = pp f
    pp (MacroUseMacroArg f a) = pp f ++ "<" ++ pp a ++ ">"


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
    | TmIte Hist.Term Term Term
    | TmPlusCase Term (Maybe Var.Var) Term (Maybe Var.Var) Term
    | TmNil
    | TmCons Term Term
    | TmStarCase Term Term (Maybe Var.Var) (Maybe Var.Var) Term
    | TmWait [Either (Var.Var) (Term,Var.Var)] Term
    | TmHistPgm Hist.Term
    | TmCut Var.Var Term Term
    | TmFunCall Var.FunVar [TyF Var.TyVar] [Hist.Term] (Maybe MacroArg) (CtxStruct Term)
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

data MacroParam = MP Var.FunVar [OpenTy] (CtxStruct OpenTy) OpenTy
  deriving (Eq,Ord,Show)

data Cmd =
    FunOrMacDef Var.FunVar [Var.TyVar] (Maybe MacroParam) [(Var.Var,OpenTy)] (Ctx Var.Var (TyF Var.TyVar)) (TyF Var.TyVar) Term
  -- | MacroDef Var.FunVar [Var.TyVar] MacroParam (Ctx Var.Var (TyF Var.TyVar)) (TyF Var.TyVar) Term
  | SpecializeCommand Var.FunVar [TyF Var.TyVar] [Var.FunVar]
  | RunCommand Var.FunVar [UntypedPrefix] (Ctx Var.Var UntypedPrefix)
  | RunStepCommand Var.FunVar [UntypedPrefix] (Ctx Var.Var UntypedPrefix)
  | QuickCheckCommand Var.FunVar
 deriving (Eq,Ord,Show)

type Program = [Cmd]