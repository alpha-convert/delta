{-# LANGUAGE DeriveFoldable, DeriveFoldable, DeriveTraversable, MultiParamTypeClasses, FunctionalDependencies #-}
module Types (Ty(..), Ctx(..), Derivative(..), DerivErr, emptyPrefix) where

import qualified Data.Map as M
import Control.Monad.Except (ExceptT, throwError, runExceptT, withExceptT)
import Values (Prefix(..), Env(..), Lit(..), isMaximal, isEmpty)

data Ty = TyEps | TyInt | TyBool | TyCat Ty Ty | TyPlus Ty Ty deriving (Eq,Ord,Show)

data Ctx v = EmpCtx | SngCtx v Ty | SemicCtx (Ctx v) (Ctx v) deriving (Functor, Foldable, Traversable)

data DerivErr a t = IllTypedDeriv a t

class Derivative a t | a -> t where
  hasType :: a -> t -> Bool
  deriv :: (Monad m) => a -> t -> ExceptT (DerivErr a t) m t

instance Derivative Prefix Ty where
  hasType LitPEmp TyInt = True
  hasType LitPEmp TyBool = True
  hasType LitPEmp _ = False

  hasType (LitPFull (LInt _)) TyInt = True
  hasType (LitPFull (LBool _)) TyBool = True
  hasType (LitPFull _) _ = False

  hasType EpsP TyEps = True
  hasType EpsP _ = False

  hasType (CatPA p) (TyCat s _) = hasType p s
  hasType (CatPA _) _ = False

  hasType (CatPB p p') (TyCat s t) = isMaximal p && hasType p s && hasType p' t
  hasType (CatPB _ _) _ = False

  hasType SumPEmp (TyPlus _ _) = True
  hasType SumPEmp _ = False

  hasType (SumPA p) (TyPlus s _) = hasType p s
  hasType (SumPA _) _ = False

  hasType (SumPB p) (TyPlus _ t) = hasType p t
  hasType (SumPB _) _ = False

  deriv LitPEmp TyInt = return TyInt
  deriv LitPEmp TyBool = return TyBool
  deriv p@LitPEmp t = throwError (IllTypedDeriv p t)

  deriv (LitPFull (LInt _)) TyInt = return TyEps
  deriv (LitPFull (LBool _)) TyBool = return TyEps
  deriv p@(LitPFull _) t = throwError (IllTypedDeriv p t)

  deriv EpsP TyEps = return TyEps
  deriv p@EpsP t = throwError (IllTypedDeriv p t)

  deriv (CatPA p) (TyCat s t) = do
    s' <- deriv p s
    return (TyCat s' t)
  deriv p@(CatPA _) t = throwError (IllTypedDeriv p t)

  deriv (CatPB _ p') (TyCat _ t) = deriv p' t
  deriv p@(CatPB {}) t = throwError (IllTypedDeriv p t)

  deriv SumPEmp (TyPlus s t) = return (TyPlus s t)
  deriv p@SumPEmp t = throwError (IllTypedDeriv p t)

  deriv (SumPA p) (TyPlus s _) = deriv p s
  deriv p@(SumPA _) t = throwError (IllTypedDeriv p t)

  deriv (SumPB p) (TyPlus _ t) = deriv p t
  deriv p@(SumPB _) t = throwError (IllTypedDeriv p t)


instance (Ord v) => Derivative (Env v) (Ctx v) where
  hasType (Env m) = go
    where
      go EmpCtx = True
      go (SngCtx x t) = case M.lookup x m of
                          Nothing -> False
                          Just p -> hasType p t
      go (SemicCtx g g') = go g && go g' && (all maximal g || all empty g')

      maximal x = maybe False isMaximal (M.lookup x m)
      empty x = maybe False isEmpty (M.lookup x m)

  deriv _ EmpCtx = return EmpCtx
  deriv (Env m) (SngCtx x s) = case M.lookup x m of
                                 Nothing -> throwError (IllTypedDeriv (Env m) (SngCtx x s))
                                 Just p -> withExceptT promoteErr (SngCtx x <$> deriv p s)
    where
      promoteErr (IllTypedDeriv p' t') = IllTypedDeriv (Env (M.singleton x p')) (SngCtx x t')
  deriv rho (SemicCtx g g') = SemicCtx <$> deriv rho g <*> deriv rho g'

emptyPrefix :: Ty -> Prefix
emptyPrefix TyInt = LitPEmp
emptyPrefix TyBool = LitPEmp
emptyPrefix TyEps = EpsP
emptyPrefix (TyCat s _) = CatPA (emptyPrefix s)
emptyPrefix (TyPlus _ _) = SumPEmp