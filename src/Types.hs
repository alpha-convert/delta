{-# LANGUAGE DeriveFoldable, DeriveTraversable, MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances, FlexibleContexts, TupleSections, UndecidableInstances #-}
module Types (
  TyF(..),
  Ty,
  OpenTy,
  CtxStruct(..),
  Ctx,
  CtxEntry(..),
  ValueLike(..),
  GenValueLike(..),
  TypeLike(..),
  ValueLikeErr(..),
  emptyPrefix,
  ctxBindings,
  ctxVars,
  ctxAssoc,
  ctxMap,
  ctxFoldM,
  closeTy,
  reparameterizeTy,
  reparameterizeCtx,
  genOf,
  genSequenceOf
) where

import qualified Data.Map as M
import Control.Monad.Except (ExceptT, throwError, withExceptT, runExceptT, replicateM)
import Values (Prefix(..), Env, Lit(..), isMaximal, isEmpty, bindEnv, emptyEnv, lookupEnv, singletonEnv, MaximalPrefix (..), maximalDemote, unionDisjointEnv)
import Util.ErrUtil(guard)
import Util.PrettyPrint
import Control.Monad.IO.Class (MonadIO)
import Control.Monad (foldM)
import Data.Bifunctor (Bifunctor (..))
import Data.Void
import qualified Var
import Test.QuickCheck.Gen (Gen, frequency, choose)
import Test.QuickCheck (Arbitrary(arbitrary), Property, forAll)
import Data.Foldable (foldrM)

data TyF v =
    TyVar v
  | TyEps
  | TyInt
  | TyBool
  | TyCat (TyF v) (TyF v)
  | TyPar (TyF v) (TyF v)
  | TyPlus (TyF v) (TyF v)
  | TyStar (TyF v)
  deriving (Eq,Ord,Show,Foldable)


closeTy :: TyF v -> Either v Ty
closeTy (TyVar x) = Left x
closeTy TyEps = return TyEps
closeTy TyInt = return TyInt
closeTy TyBool = return TyBool
closeTy (TyCat s t) = TyCat <$> closeTy s <*> closeTy t
closeTy (TyPar s t) = TyPar <$> closeTy s <*> closeTy t
closeTy (TyPlus s t) = TyPlus <$> closeTy s <*> closeTy t
closeTy (TyStar s) = TyStar <$> closeTy s

type Ty = TyF Void

instance Arbitrary Ty where
  arbitrary = choose (0 :: Int,5) >>= go
    where
      go 0 = frequency [(1,return TyEps), (3,return TyInt), (3,return TyBool)]
      go n = frequency [
        (1,return TyEps),
        (3,return TyInt),
        (3,return TyBool),
        (3,TyCat <$> go (n `div` 2) <*> go (n `div` 2)),
        (3,TyPar <$> go (n `div` 2) <*> go (n `div` 2)),
        (3,TyPlus<$> go (n `div` 2) <*> go (n `div` 2)),
        (2,TyStar <$> go (n `div` 2))
        ]

type OpenTy = TyF Var.TyVar

instance (PrettyPrint v) => PrettyPrint (TyF v) where
  pp TyEps = "Eps"
  pp TyInt = "Int"
  pp TyBool = "Bool"
  pp (TyCat s t) = concat ["(", pp s," . ", pp t, ")"]
  pp (TyPar s t) = concat ["(", pp s," || ", pp t, ")"]
  pp (TyPlus s t) = concat ["(", pp s," + ", pp t, ")"]
  pp (TyStar s) = concat ["(", pp s,")*"]
  pp (TyVar x) = "TyVar(" ++ pp x ++ ")"

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

instance TypeLike (TyF a) where
  isNull TyInt = False
  isNull TyBool = False
  isNull TyEps = True
  isNull (TyCat _ _) = False
  isNull (TyPlus _ _) = False
  isNull (TyStar _) = False
  isNull (TyPar s t) = isNull s && isNull t
{-
TODO: this (isNull (TyVar x) = False) is a hack for the moment to simplify the inertness analysis.
Otherwise it'd have to happen after templating time, because you don't know if waiting on `x : TyVar s` is
going to be inert or not. For now, we just require that you always instantiate polymorphic functions with non-nullable types
(which isn't too strong of a restriction.)
-}
  isNull (TyVar x) = False

instance TypeLike t => TypeLike (Ctx v t) where
  isNull EmpCtx = True
  isNull (SngCtx (CE _ s)) = isNull s
  isNull (SemicCtx g g') = isNull g && isNull g'
  isNull (CommaCtx g g') = isNull g && isNull g'

instance TypeLike t => TypeLike (M.Map v t) where
  isNull = all isNull

data ValueLikeErr a t = IllTyped a t deriving (Show)

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

  doDeriv :: (Show a, Show t, MonadIO m) => a -> t -> m t
  doDeriv v t = runExceptT (deriv v t) >>= either (\(IllTyped v' t' ) -> error $ concat ["Tried to take the derivative of ", show t', " with respect to ", show v',". This is bug."]) return


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
emptyPrefix (TyVar x) = absurd x

reparameterizeTy :: (Ord v', Monad m) => M.Map v' (TyF v) -> TyF v' -> ExceptT v' m (TyF v)
reparameterizeTy m = go
  where
    go TyInt = return TyInt
    go TyBool = return TyBool
    go TyEps = return TyEps
    go (TyCat s t) = TyCat <$> go s <*> go t
    go (TyPar s t) = TyPar <$> go s <*> go t
    go (TyPlus s t) = TyPlus <$> go s <*> go t
    go (TyStar s) = TyStar <$> go s
    go (TyVar x) = maybe (throwError x) return (M.lookup x m)

reparameterizeCtx :: (Ord v', Monad m) => M.Map v' (TyF v) -> Ctx k (TyF v') -> ExceptT v' m (Ctx k (TyF v))
reparameterizeCtx m = go
  where
    go EmpCtx = return EmpCtx
    go (SngCtx (CE x s)) = do
      s' <- reparameterizeTy m s
      return (SngCtx (CE x s'))
    go (CommaCtx g g') = CommaCtx <$> go g <*> go g'
    go (SemicCtx g g') = SemicCtx <$> go g <*> go g'


-----

genMaximalPrefixOfTy :: Ty -> Gen MaximalPrefix
genMaximalPrefixOfTy TyEps = return EpsMP
genMaximalPrefixOfTy TyInt = LitMP . LInt <$> arbitrary
genMaximalPrefixOfTy TyBool = LitMP . LBool <$> arbitrary
genMaximalPrefixOfTy (TyVar a) = absurd a
genMaximalPrefixOfTy (TyCat s t) = CatMP <$> genMaximalPrefixOfTy s <*> genMaximalPrefixOfTy t
genMaximalPrefixOfTy (TyPar s t) = ParMP <$> genMaximalPrefixOfTy s <*> genMaximalPrefixOfTy t
genMaximalPrefixOfTy (TyPlus s t) = frequency [(1,SumMPA <$> genMaximalPrefixOfTy s), (1,SumMPB <$> genMaximalPrefixOfTy t)]
genMaximalPrefixOfTy (TyStar s) = do
  n <- choose (0,5)
  StMP <$> replicateM n (genMaximalPrefixOfTy s)

genPrefixOfTy :: Ty -> Gen Prefix
genPrefixOfTy TyEps = return EpsP
genPrefixOfTy TyInt = frequency [(1,return LitPEmp),(2, LitPFull . LInt <$> arbitrary)]
genPrefixOfTy TyBool = frequency [(1,return LitPEmp),(2, LitPFull . LBool <$> arbitrary)]
genPrefixOfTy (TyVar a) = absurd a
genPrefixOfTy (TyCat s t) = frequency [(3, CatPA <$> genPrefixOfTy s),(1, CatPB <$> (maximalDemote <$> genMaximalPrefixOfTy s) <*> genPrefixOfTy t)]
genPrefixOfTy (TyPar s t) = ParP <$> genPrefixOfTy s <*> genPrefixOfTy t
genPrefixOfTy (TyPlus s t) = frequency [(1,return SumPEmp), (2, SumPA <$> genPrefixOfTy s), (2,SumPB <$> genPrefixOfTy t)]
genPrefixOfTy (TyStar s) = frequency [(1,return StpEmp), (1,return StpDone), (2, StpA <$> genPrefixOfTy s), (2, StpB <$> (maximalDemote <$> genMaximalPrefixOfTy s) <*> genPrefixOfTy (TyStar s))]

genMaximalEnvOfCtx :: Ctx Var.Var Ty -> Gen (Env Var.Var Prefix)
genMaximalEnvOfCtx = foldrM (\(CE x s) -> go x s) emptyEnv
  where
    go x s rho = do
      p <- genMaximalPrefixOfTy s
      return (bindEnv x (maximalDemote p) rho)

genEmptyEnvOfCtx :: Ctx Var.Var Ty -> Gen (Env Var.Var Prefix)
genEmptyEnvOfCtx = return . foldr (\(CE x s) -> go x s) emptyEnv
  where
    go x s = bindEnv x (emptyPrefix s)

genUnion :: Env Var.Var Prefix -> Env Var.Var Prefix -> Gen (Env Var.Var Prefix)
genUnion rho rho' = runExceptT (unionDisjointEnv rho rho') >>= either (\(x,p,p') -> error "") return

genEnvOfCtx :: Ctx Var.Var Ty -> Gen (Env Var.Var Prefix)
genEnvOfCtx EmpCtx = return emptyEnv
genEnvOfCtx (SngCtx (CE x s)) = do
  p <- genPrefixOfTy s
  return (singletonEnv x p)
genEnvOfCtx (CommaCtx g g') = do
  rho <- genEnvOfCtx g
  rho' <- genEnvOfCtx g'
  genUnion rho rho'
genEnvOfCtx (SemicCtx g g') = frequency [(2,do {rho <- genEnvOfCtx g; rho' <- genEmptyEnvOfCtx g'; genUnion rho rho'}),(1,do {rho <- genMaximalEnvOfCtx g; rho' <- genEnvOfCtx g'; genUnion rho rho'})]

class ValueLike v t => GenValueLike v t where
  genOf :: t -> Gen v


instance GenValueLike Prefix Ty where
  genOf = genPrefixOfTy

instance GenValueLike (Env Var.Var Prefix) (Ctx Var.Var Ty) where
  genOf = genEnvOfCtx

genSequenceOf :: (PrettyPrint v, PrettyPrint t, GenValueLike v t) => Int -> t -> Gen [v]
genSequenceOf 0 _ = return []
genSequenceOf n t = do
  v <- genOf t
  mt' <- runExceptT (deriv v t)
  case mt' of
    Right t' -> (v:) <$> genSequenceOf (n - 1) t'
    Left err -> error (pp err)