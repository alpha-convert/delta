{-# LANGUAGE DeriveFoldable, DeriveFoldable, DeriveTraversable, MultiParamTypeClasses, FunctionalDependencies #-}
module Types (Ty(..), Ctx(..), ValueLike(..), TypeLike(..), ValueLikeErr(..), emptyPrefix, ctxBindings, ctxVars) where

import qualified Data.Map as M
import Control.Monad.Except (ExceptT, throwError, withExceptT, runExceptT)
import Values (Prefix(..), Env, Lit(..), isMaximal, isEmpty, bindEnv, emptyEnv, lookupEnv)
import Util.ErrUtil(guard)
import Util.PrettyPrint
import Control.Monad.IO.Class (MonadIO)

data Ty = TyEps | TyInt | TyBool | TyCat Ty Ty | TyPlus Ty Ty | TyStar Ty deriving (Eq,Ord,Show)

instance PrettyPrint Ty where
  pp TyEps = "Eps"
  pp TyInt = "Int"
  pp TyBool = "Bool"
  pp (TyCat s t) = concat ["(", pp s," . ", pp t, ")"]
  pp (TyPlus s t) = concat ["(", pp s," + ", pp t, ")"]
  pp (TyStar s) = concat ["(", pp s,")*"]

data Ctx v = EmpCtx | SngCtx v Ty | SemicCtx (Ctx v) (Ctx v) deriving (Eq,Ord,Show,Functor, Foldable, Traversable)

ctxBindings :: (Ord v) => Ctx v -> M.Map v Ty
ctxBindings EmpCtx = M.empty
ctxBindings (SngCtx x t) = M.singleton x t
ctxBindings (SemicCtx g g') = M.union (ctxBindings g) (ctxBindings g')

ctxVars :: Ctx v -> [v]
ctxVars EmpCtx = []
ctxVars (SngCtx x _) = [x]
ctxVars (SemicCtx g g') = ctxVars g ++ ctxVars g'

instance PrettyPrint v => PrettyPrint (Ctx v) where
  pp EmpCtx = "(.)"
  pp (SngCtx v t) = concat ["[",pp v," : ", pp t,"]"]
  pp (SemicCtx g g') = concat ["(", pp g, " ; ", pp g', ")"]


class TypeLike t where
  isNull :: t -> Bool

instance TypeLike Ty where
  isNull = undefined

instance TypeLike (Ctx v) where
  isNull = undefined

data ValueLikeErr a t = IllTyped a t

promotePrefixTypeErr :: Ord v => v -> ValueLikeErr Prefix Ty -> ValueLikeErr (Env v) (Ctx v)
promotePrefixTypeErr x (IllTyped p' t') = IllTyped (bindEnv x p' emptyEnv) (SngCtx x t')

promotePrefixDerivErr :: Ord v => v -> ValueLikeErr Prefix Ty -> ValueLikeErr (Env v) (Ctx v)
promotePrefixDerivErr x (IllTyped p' t') = IllTyped (bindEnv x p' emptyEnv) (SngCtx x t')


class TypeLike t => ValueLike a t where
  hasType :: (Monad m) => a -> t -> ExceptT (ValueLikeErr a t) m ()
  deriv :: (Monad m) => a -> t -> ExceptT (ValueLikeErr a t) m t

  hasTypeB :: (Monad m) => a -> t -> m Bool
  hasTypeB v t = runExceptT (hasType v t) >>= either (const (return False)) (const (return True))

  doDeriv :: (PrettyPrint a, PrettyPrint t, MonadIO m) => a -> t -> m t
  doDeriv v t = runExceptT (deriv v t) >>= either (\(IllTyped v' t' ) -> error $ concat ["Tried to take the derivative of ", pp t', " with respect to ", pp v',". This is bug."]) return


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
    () <- hasType p s
    () <- hasType p' t
    if isMaximal p then return () else throwError (IllTyped (CatPB p p') (TyCat s t))
  hasType p@(CatPB _ _) t = throwError (IllTyped p t)

  hasType SumPEmp (TyPlus _ _) = return ()
  hasType p@SumPEmp t = throwError (IllTyped p t)

  hasType (SumPA p) (TyPlus s _) = hasType p s
  hasType p@(SumPA _) t = throwError (IllTyped p t)

  hasType (SumPB p) (TyPlus _ t) = hasType p t
  hasType p@(SumPB _) t = throwError (IllTyped p t)

  hasType StpEmp (TyStar _) = return ()
  hasType p@StpEmp t = throwError (IllTyped p t)

  hasType StpDone (TyStar _) = return ()
  hasType p@StpDone t = throwError (IllTyped p t)

  hasType (StpA p) (TyStar s) = hasType p s
  hasType p@(StpA _) t = throwError (IllTyped p t)

  hasType (StpB p p') (TyStar s) = do
    () <- hasType p s
    () <- hasType p' (TyStar s)
    if isMaximal p then return () else throwError (IllTyped (StpB p p') (TyStar s))
  hasType p@(StpB {}) t = throwError (IllTyped p t)

  deriv LitPEmp TyInt = return TyInt
  deriv LitPEmp TyBool = return TyBool
  deriv p@LitPEmp t = throwError (IllTyped p t)

  deriv (LitPFull (LInt _)) TyInt = return TyEps
  deriv (LitPFull (LBool _)) TyBool = return TyEps
  deriv p@(LitPFull _) t = throwError (IllTyped p t)

  deriv EpsP TyEps = return TyEps
  deriv p@EpsP t = throwError (IllTyped p t)

  deriv (CatPA p) (TyCat s t) = do
    s' <- deriv p s
    return (TyCat s' t)
  deriv p@(CatPA _) t = throwError (IllTyped p t)

  deriv (CatPB _ p') (TyCat _ t) = deriv p' t
  deriv p@(CatPB {}) t = throwError (IllTyped p t)

  deriv SumPEmp (TyPlus s t) = return (TyPlus s t)
  deriv p@SumPEmp t = throwError (IllTyped p t)

  deriv (SumPA p) (TyPlus s _) = deriv p s
  deriv p@(SumPA _) t = throwError (IllTyped p t)

  deriv (SumPB p) (TyPlus _ t) = deriv p t
  deriv p@(SumPB _) t = throwError (IllTyped p t)

  deriv StpEmp (TyStar s) = return (TyStar s)
  deriv p@StpEmp t = throwError (IllTyped p t)

  deriv StpDone (TyStar _) = return TyEps
  deriv p@StpDone t = throwError (IllTyped p t)

  deriv (StpA p) (TyStar s) = do
    s' <- deriv p s
    return (TyCat s' (TyStar s))
  deriv p@(StpA _) t = throwError (IllTyped p t)

  deriv (StpB _ p) (TyStar s) = deriv p (TyStar s)
  deriv p@(StpB {}) t = throwError (IllTyped p t)


instance (Ord v) => ValueLike (Env v) (Ctx v) where
  hasType rho = go
    where
      go EmpCtx = return ()
      go (SngCtx x t) = case Values.lookupEnv x rho of
                          Nothing -> return ()
                          Just p -> withExceptT (promotePrefixTypeErr x) (hasType p t)
      go (SemicCtx g g') = do
        go g >> go g' >> guard (all maximal g || all empty g') (IllTyped rho (SemicCtx g g'))

      maximal x = maybe False isMaximal (Values.lookupEnv x rho)
      empty x = maybe False isEmpty (Values.lookupEnv x rho)

  deriv _ EmpCtx = return EmpCtx
  deriv rho (SngCtx x s) = case Values.lookupEnv x rho of
                                 Nothing -> throwError (IllTyped rho (SngCtx x s))
                                 Just p -> withExceptT (promotePrefixDerivErr x) (SngCtx x <$> deriv p s)
  deriv rho (SemicCtx g g') = SemicCtx <$> deriv rho g <*> deriv rho g'

emptyPrefix :: Ty -> Prefix
emptyPrefix TyInt = LitPEmp
emptyPrefix TyBool = LitPEmp
emptyPrefix TyEps = EpsP
emptyPrefix (TyCat s _) = CatPA (emptyPrefix s)
emptyPrefix (TyPlus _ _) = SumPEmp
emptyPrefix (TyStar _) = StpEmp