{-# LANGUAGE DeriveFoldable, DeriveFoldable, DeriveTraversable, MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances, FlexibleContexts #-}
module Types (Ty(..), Ctx(..), ValueLike(..), TypeLike(..), ValueLikeErr(..), emptyPrefix, ctxBindings, ctxVars, ctxAssoc) where

import qualified Data.Map as M
import Control.Monad.Except (ExceptT, throwError, withExceptT, runExceptT)
import Values (Prefix(..), Env, Lit(..), isMaximal, isEmpty, bindEnv, emptyEnv, lookupEnv, singletonEnv)
import Util.ErrUtil(guard)
import Util.PrettyPrint
import Control.Monad.IO.Class (MonadIO)
import Control.Monad (foldM)

data Ty = TyEps | TyInt | TyBool | TyCat Ty Ty | TyPlus Ty Ty | TyStar Ty deriving (Eq,Ord,Show)

instance PrettyPrint Ty where
  pp TyEps = "Eps"
  pp TyInt = "Int"
  pp TyBool = "Bool"
  pp (TyCat s t) = concat ["(", pp s," . ", pp t, ")"]
  pp (TyPlus s t) = concat ["(", pp s," + ", pp t, ")"]
  pp (TyStar s) = concat ["(", pp s,")*"]

data Ctx v t = EmpCtx | SngCtx v t | SemicCtx (Ctx v t) (Ctx v t) deriving (Eq,Ord,Show,Functor, Foldable, Traversable)

ctxBindings :: (Ord v) => Ctx v t -> M.Map v t
ctxBindings = M.fromList . ctxAssoc

ctxVars :: Ctx v t -> [v]
ctxVars = map fst . ctxAssoc

ctxAssoc :: Ctx v t -> [(v,t)]
ctxAssoc EmpCtx = []
ctxAssoc (SngCtx x s) = [(x,s)]
ctxAssoc (SemicCtx g g') = ctxAssoc g ++ ctxAssoc g'

instance (PrettyPrint v, PrettyPrint t) => PrettyPrint (Ctx v t) where
  pp EmpCtx = "(.)"
  pp (SngCtx v t) = concat ["[",pp v," : ", pp t,"]"]
  pp (SemicCtx g g') = concat ["(", pp g, " ; ", pp g', ")"]


class TypeLike t where
  isNull :: t -> Bool

instance TypeLike Ty where
  isNull TyInt = False
  isNull TyBool = False
  isNull TyEps = True
  isNull (TyCat _ _) = False
  isNull (TyPlus _ _) = False
  isNull (TyStar _) = False

instance TypeLike t => TypeLike (Ctx v t) where
  isNull EmpCtx = True
  isNull (SngCtx _ s) = isNull s
  isNull (SemicCtx g g') = isNull g && isNull g'

instance TypeLike t => TypeLike (M.Map v t) where
  isNull = all isNull

data ValueLikeErr a t = IllTyped a t

promotePrefixTypeErr :: Ord v => v -> ValueLikeErr p t -> ValueLikeErr (Env v p) (Ctx v t)
promotePrefixTypeErr x (IllTyped p' t') = IllTyped (bindEnv x p' emptyEnv) (SngCtx x t')

promotePrefixDerivErr :: Ord v => v -> ValueLikeErr p t -> ValueLikeErr (Env v p) (Ctx v t)
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


instance (Ord v, ValueLike Prefix Ty) => ValueLike (Env v Prefix) (Ctx v Ty) where
  hasType rho = go
    where
      go EmpCtx = return ()
      go (SngCtx x t) = case Values.lookupEnv x rho of
                          Nothing -> return ()
                          Just p -> withExceptT (promotePrefixTypeErr x) (hasType p t)
      go (SemicCtx g g') = do
        go g >> go g' >> guard (all maximal (ctxVars g) || all empty (ctxVars g')) (IllTyped rho (SemicCtx g g'))

      maximal x = maybe False isMaximal (Values.lookupEnv x rho)
      empty x = maybe False isEmpty (Values.lookupEnv x rho)

  deriv _ EmpCtx = return EmpCtx
  deriv rho (SngCtx x s) = case Values.lookupEnv x rho of
                                 Nothing -> throwError (IllTyped rho (SngCtx x s))
                                 Just p -> withExceptT (promotePrefixDerivErr x) (SngCtx x <$> deriv p s)
  deriv rho (SemicCtx g g') = SemicCtx <$> deriv rho g <*> deriv rho g'

instance (Ord v, ValueLike p t) => ValueLike (Env v p) (M.Map v t) where
  hasType rho m = M.foldrWithKey go (return ()) m
    where
      go x t k = do
        () <- case lookupEnv x rho of
                Just p -> withExceptT (\(IllTyped p' t') -> IllTyped (singletonEnv x p') (M.singleton x t')) $ hasType p t
                Nothing -> throwError (IllTyped rho m)
        k
  deriv rho m = M.foldrWithKey go (return M.empty) m
    where
      go x t k = do
        t' <- case lookupEnv x rho of
                Just p -> withExceptT (\(IllTyped p' t') -> IllTyped (singletonEnv x p') (M.singleton x t')) $ deriv p t
                Nothing -> throwError (IllTyped rho m)
        M.insert x t' <$> k


emptyPrefix :: Ty -> Prefix
emptyPrefix TyInt = LitPEmp
emptyPrefix TyBool = LitPEmp
emptyPrefix TyEps = EpsP
emptyPrefix (TyCat s _) = CatPA (emptyPrefix s)
emptyPrefix (TyPlus _ _) = SumPEmp
emptyPrefix (TyStar _) = StpEmp