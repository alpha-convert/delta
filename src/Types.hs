{-# LANGUAGE DeriveFoldable, DeriveTraversable, MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances, FlexibleContexts, TupleSections #-}
module Types (Ty(..), CtxStruct(..), Ctx, CtxEntry(..), ValueLike(..), TypeLike(..), ValueLikeErr(..), emptyPrefix, ctxBindings, ctxVars, ctxAssoc, ctxMap, ctxFoldM) where

import qualified Data.Map as M
import Control.Monad.Except (ExceptT, throwError, withExceptT, runExceptT)
import Values (Prefix(..), Env, Lit(..), isMaximal, isEmpty, bindEnv, emptyEnv, lookupEnv, singletonEnv)
import Util.ErrUtil(guard)
import Util.PrettyPrint
import Control.Monad.IO.Class (MonadIO)
import Control.Monad (foldM)
import Data.Bifunctor (Bifunctor (..))

data Ty = TyEps | TyInt | TyBool | TyCat Ty Ty | TyPar Ty Ty | TyPlus Ty Ty | TyStar Ty deriving (Eq,Ord,Show)

instance PrettyPrint Ty where
  pp TyEps = "Eps"
  pp TyInt = "Int"
  pp TyBool = "Bool"
  pp (TyCat s t) = concat ["(", pp s," . ", pp t, ")"]
  pp (TyPar s t) = concat ["(", pp s," || ", pp t, ")"]
  pp (TyPlus s t) = concat ["(", pp s," + ", pp t, ")"]
  pp (TyStar s) = concat ["(", pp s,")*"]

data CtxStruct a =
    EmpCtx
  | SngCtx a
  | SemicCtx (CtxStruct a) (CtxStruct a)
  | CommaCtx (CtxStruct a) (CtxStruct a)
  deriving (Eq,Ord,Show,Functor, Foldable, Traversable)

data CtxEntry v t = CE {_fst :: v, _snd :: t}
  deriving (Eq,Ord,Show)

instance (PrettyPrint v, PrettyPrint t) => PrettyPrint (CtxEntry v t) where
  pp (CE x t) = pp x ++ " : " ++ pp t

type Ctx v t = CtxStruct (CtxEntry v t)

ctxMap :: (v -> t -> (v',t')) -> Ctx v t -> Ctx v' t'
ctxMap _ EmpCtx = EmpCtx
ctxMap f (SngCtx (CE x t)) = let (x',y') = f x t in SngCtx (CE x' y')
ctxMap f (SemicCtx g g') = SemicCtx (ctxMap f g) (ctxMap f g')
ctxMap f (CommaCtx g g') = CommaCtx (ctxMap f g) (ctxMap f g')

ctxFoldM :: (Monad m) => m b -> (a -> m b) -> (b -> b -> m b) -> CtxStruct a -> m b
ctxFoldM x f g EmpCtx = x
ctxFoldM _ f g (SngCtx x) = f x
ctxFoldM x f g (SemicCtx g1 g2) = do
  a1 <- ctxFoldM x f g g1
  a2 <- ctxFoldM x f g g2
  g a1 a2
ctxFoldM x f g (CommaCtx g1 g2) = do
  a1 <- ctxFoldM x f g g1
  a2 <- ctxFoldM x f g g2
  g a1 a2

ctxBindings :: (Ord v) => Ctx v t -> M.Map v t
ctxBindings = M.fromList . ctxAssoc

ctxVars :: Ctx v t -> [v]
ctxVars = map fst . ctxAssoc

ctxAssoc :: Ctx v t -> [(v,t)]
ctxAssoc EmpCtx = []
ctxAssoc (SngCtx (CE x s)) = [(x,s)]
ctxAssoc (SemicCtx g g') = ctxAssoc g ++ ctxAssoc g'
ctxAssoc (CommaCtx g g') = ctxAssoc g ++ ctxAssoc g'

instance (PrettyPrint a) => PrettyPrint (CtxStruct a) where
  pp EmpCtx = "(.)"
  pp (SngCtx x) = pp x
  pp (SemicCtx g g') = concat ["(", pp g, " ; ", pp g', ")"]
  pp (CommaCtx g g') = concat ["(", pp g, " , ", pp g', ")"]

class TypeLike t where
  isNull :: t -> Bool

instance TypeLike Ty where
  isNull TyInt = False
  isNull TyBool = False
  isNull TyEps = True
  isNull (TyCat _ _) = False
  isNull (TyPlus _ _) = False
  isNull (TyStar _) = False
  isNull (TyPar s t) = isNull s && isNull t

instance TypeLike t => TypeLike (Ctx v t) where
  isNull EmpCtx = True
  isNull (SngCtx (CE _ s)) = isNull s
  isNull (SemicCtx g g') = isNull g && isNull g'
  isNull (CommaCtx g g') = isNull g && isNull g'

instance TypeLike t => TypeLike (M.Map v t) where
  isNull = all isNull

data ValueLikeErr a t = IllTyped a t

instance (PrettyPrint a, PrettyPrint t) => PrettyPrint (ValueLikeErr a t) where
  pp (IllTyped a t) = concat ["Value ", pp a, " does not have type ", pp t]

promotePrefixTypeErr :: Ord v => v -> ValueLikeErr p t -> ValueLikeErr (Env v p) (Ctx v t)
promotePrefixTypeErr x (IllTyped p' t') = IllTyped (bindEnv x p' emptyEnv) (SngCtx (CE x t'))

promotePrefixDerivErr :: Ord v => v -> ValueLikeErr p t -> ValueLikeErr (Env v p) (Ctx v t)
promotePrefixDerivErr x (IllTyped p' t') = IllTyped (bindEnv x p' emptyEnv) (SngCtx (CE x t'))


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

  hasType (ParP p p') (TyPar s t) = do
    () <- hasType p s
    () <- hasType p' t
    return ()
  hasType p@(ParP {}) t = throwError (IllTyped p t)

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

  deriv (ParP p p') (TyPar s t) = do
    s' <- deriv p s
    t' <- deriv p' t
    return (TyPar s' t')
  deriv p@(ParP {}) t = throwError (IllTyped p t)

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
      go (SngCtx (CE x t)) = case Values.lookupEnv x rho of
                          Nothing -> return ()
                          Just p -> withExceptT (promotePrefixTypeErr x) (hasType p t)
      go (SemicCtx g g') = go g >> go g' >> guard (all maximal (ctxVars g) || all empty (ctxVars g')) (IllTyped rho (SemicCtx g g'))
      go (CommaCtx g g') = go g >> go g'

      maximal x = maybe False isMaximal (Values.lookupEnv x rho)
      empty x = maybe False isEmpty (Values.lookupEnv x rho)

  deriv _ EmpCtx = return EmpCtx
  deriv rho (SngCtx (CE x t)) = case Values.lookupEnv x rho of
                                 Nothing -> throwError (IllTyped rho (SngCtx (CE x t)))
                                 Just p -> withExceptT (promotePrefixDerivErr x) (SngCtx . (CE x) <$> deriv p t)
  deriv rho (SemicCtx g g') = SemicCtx <$> deriv rho g <*> deriv rho g'
  deriv rho (CommaCtx g g') = CommaCtx <$> deriv rho g <*> deriv rho g'

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
emptyPrefix (TyPar s t) = ParP (emptyPrefix s) (emptyPrefix t)
emptyPrefix (TyPlus _ _) = SumPEmp
emptyPrefix (TyStar _) = StpEmp