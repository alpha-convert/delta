{-# LANGUAGE DeriveFoldable, DeriveFoldable, DeriveTraversable, MultiParamTypeClasses, FunctionalDependencies #-}
module Types (Ty(..), Ctx(..), ValueLike(..), TypeLike(..), DerivErr(..), HasTypeErr(..), emptyPrefix) where

import qualified Data.Map as M
import Control.Monad.Except (ExceptT, throwError, runExceptT, withExceptT, MonadError)
import Values (Prefix(..), Env(..), Lit(..), isMaximal, isEmpty)
import Util.ErrUtil(guard)

data Ty = TyEps | TyInt | TyBool | TyCat Ty Ty | TyPlus Ty Ty deriving (Eq,Ord,Show)

data Ctx v = EmpCtx | SngCtx v Ty | SemicCtx (Ctx v) (Ctx v) deriving (Functor, Foldable, Traversable)


class TypeLike t where
  isNull :: t -> Bool

instance TypeLike Ty where
  isNull = undefined

instance TypeLike (Ctx v) where
  isNull = undefined

data DerivErr a t = IllTypedDeriv a t
data HasTypeErr a t = IllTyped a t

promotePrefixTypeErr x (IllTyped p' t') = IllTyped (Env (M.singleton x p')) (SngCtx x t')
promotePrefixDerivErr x (IllTypedDeriv p' t') = IllTypedDeriv (Env (M.singleton x p')) (SngCtx x t')


class TypeLike t => ValueLike a t where
  hasType :: (Monad m) => a -> t -> ExceptT (HasTypeErr a t) m ()
  deriv :: (Monad m) => a -> t -> ExceptT (DerivErr a t) m t

instance ValueLike Prefix Ty where
  hasType LitPEmp TyInt = return ()
  hasType LitPEmp TyBool = return ()
  hasType p@LitPEmp t = throwError (IllTyped p t)

  hasType (LitPFull (LInt _)) TyInt = return ()
  hasType (LitPFull (LBool _)) TyBool = return ()
  hasType p@(LitPFull _) t = throwError (IllTyped p t)

  hasType EpsP TyEps = return ()
  hasType p@EpsP t = throwError (IllTyped p t)

  hasType (CatPA p) (TyCat s _) = hasType p s
  hasType p@(CatPA _) t = throwError (IllTyped p t)

  hasType (CatPB p p') (TyCat s t) = do
    hasType p s
    hasType p' t
    if isMaximal p then return () else throwError (IllTyped (CatPB p p') (TyCat s t))
  hasType p@(CatPB _ _) t = throwError (IllTyped p t)

  hasType SumPEmp (TyPlus _ _) = return ()
  hasType p@SumPEmp t = throwError (IllTyped p t)

  hasType (SumPA p) (TyPlus s _) = hasType p s
  hasType p@(SumPA _) t = throwError (IllTyped p t)

  hasType (SumPB p) (TyPlus _ t) = hasType p t
  hasType p@(SumPB _) t = throwError (IllTyped p t)

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


instance (Ord v) => ValueLike (Env v) (Ctx v) where
  hasType (Env m) = go
    where
      go EmpCtx = return ()
      go (SngCtx x t) = case M.lookup x m of
                          Nothing -> return ()
                          Just p -> withExceptT (promotePrefixTypeErr x) (hasType p t)
      go (SemicCtx g g') = do
        go g >> go g' >> guard (all maximal g || all empty g') (IllTyped (Env m) (SemicCtx g g'))

      maximal x = maybe False isMaximal (M.lookup x m)
      empty x = maybe False isEmpty (M.lookup x m)

  deriv _ EmpCtx = return EmpCtx
  deriv (Env m) (SngCtx x s) = case M.lookup x m of
                                 Nothing -> throwError (IllTypedDeriv (Env m) (SngCtx x s))
                                 Just p -> withExceptT (promotePrefixDerivErr x) (SngCtx x <$> deriv p s)
  deriv rho (SemicCtx g g') = SemicCtx <$> deriv rho g <*> deriv rho g'

emptyPrefix :: Ty -> Prefix
emptyPrefix TyInt = LitPEmp
emptyPrefix TyBool = LitPEmp
emptyPrefix TyEps = EpsP
emptyPrefix (TyCat s _) = CatPA (emptyPrefix s)
emptyPrefix (TyPlus _ _) = SumPEmp