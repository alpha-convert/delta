-- AUTHORS: Emeka Nkurumeh, Joe Cutler
{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, BangPatterns, TupleSections, ScopedTypeVariables #-}

module Frontend.Typecheck(
    doCheckElabPgm,
    doCheckElabTm,
    tckTests
) where

import qualified Frontend.ElabSyntax as Elab
import qualified CoreSyntax as Core
import Control.Monad.Except (MonadError (throwError), runExceptT, ExceptT, withExceptT, Except)
import Types (Ctx, CtxStruct(..), TyF(..), Ty, ctxBindings, ctxVars, emptyPrefix, ctxAssoc, deriv, ValueLikeErr (IllTyped), ValueLike (hasType), ctxMap, CtxEntry (..))
import Control.Monad.Reader (MonadReader (ask, local), asks, ReaderT (runReaderT), withReaderT)
import Var (Var (Var), TyVar)
import Values (Lit(..), Env, Prefix (..), emptyEnv, bindEnv, isMaximal, isEmpty, allEnv, unionDisjointEnv, singletonEnv)
import qualified Data.Map as M
import qualified Util.PartialOrder as P
import Control.Monad.Identity (Identity (runIdentity))
import Util.PrettyPrint (PrettyPrint,pp)
import Control.Monad.State.Strict (StateT(runStateT), MonadState (put, get), MonadTrans (lift), gets, modify)
import qualified Frontend.SurfaceSyntax as Surf
import Control.Monad.IO.Class (MonadIO (liftIO))
import Util.PartialOrder (substSingAll)
import Control.Monad (when, foldM)
import Data.Void
import Test.HUnit
import Data.Bifunctor
import qualified HistPgm as Hist
import Debug.Trace (trace)
import qualified Data.Set as S
import Frontend.Monomorphizer

data TckErr t v = VarNotFound Var t
            | OutOfOrder Var Var t
            | SomeOrder Var Var t
            | ReUse Var t
            | ExpectedTyCat Var (TyF v) t
            | ExpectedTyPar Var (TyF v) t
            | ExpectedTyPlus Var (TyF v) t
            | ExpectedTyStar Var (TyF v) t
            | ExpectedTyBool Var (TyF v) t
            | CheckTermInferPos t
            | UnequalReturnTypes (TyF v) (TyF v) t
            | WrongTypeLit Lit (TyF v)
            | WrongTypeEpsR (TyF v)
            | WrongTypeVar Var (TyF v) (TyF v)
            | WrongTypeCatR t t (TyF v)
            | WrongTypeParR t t (TyF v)
            | WrongTypeInl t (TyF v)
            | WrongTypeInr t (TyF v)
            | WrongTypeNil (TyF v)
            | WrongTypeCons t t (TyF v)
            | ListedTypeError Ty Ty Core.Term
            | ImpossibleCut Var Core.Term Core.Term
            | UnsaturatedRecursiveCall (Ctx Var (TyF v)) (CtxStruct t)
            | HasTypeErr (Env Var.Var Prefix) (M.Map Var.Var (TyF v))
            | NonMatchingRecursiveArgs (Ctx Var (TyF v)) (CtxStruct t)
            | HistTckErr t Hist.TckErr

instance (PrettyPrint v, PrettyPrint t) => PrettyPrint (TckErr t v) where
    pp (VarNotFound (Var x) e) = concat ["Variable ",x," not found in term ", pp e]
    pp (OutOfOrder (Var x) (Var y) e) = concat ["Variable ",y," came before ",x," in term ",pp e," but expected the other order."]
    pp (SomeOrder (Var x) (Var y) e) = concat ["Variables ",x," and ",y," used in some order in term ",pp e," but expected them to be used in parallel."]
    pp (ReUse (Var x) e) = concat ["Variable ",x," was reused in disjoint branches of ", pp e]
    pp (ExpectedTyCat (Var x) t e) = concat ["Variable ",x," expected to be of concatenation type, but it has type ", pp t, " in term ", pp e]
    pp (ExpectedTyPar (Var x) t e) = concat ["Variable ",x," expected to be of parallel type, but it has type ", pp t, " in term ", pp e]
    pp (ExpectedTyPlus (Var x) t e) = concat ["Variable ",x," expected to be of sum type, but it has type ", pp t, " in term ", pp e]
    pp (ExpectedTyStar (Var x) t e)= concat ["Variable ",x," expected to be of star type, but it has type ", pp t, " in term ", pp e]
    pp (ExpectedTyBool (Var x) t e)= concat ["Variable ",x," expected to be of bool type, but it has type ", pp t, " in term ", pp e]
    pp (CheckTermInferPos e) = concat ["The type of the term ",pp e," cannot be inferred"]
    pp (UnequalReturnTypes t1 t2 e) = concat ["Different types ",pp t1," and ",pp t2," inferred for the branches of the term ", pp e]
    pp (WrongTypeLit l t) = concat ["Literal ", pp l, " does not have type ", pp t]
    pp (WrongTypeEpsR t) = concat ["sink does not have type ", pp t]
    pp (WrongTypeVar (Var x) t s) = concat ["Variable ",x," has type ",pp s," but expected ", pp t]
    pp (WrongTypeCatR e1 e2 t) = concat ["Term (",pp e1,";",pp e2,") has concatenation type, but checking against ", pp t]
    pp (WrongTypeParR e1 e2 t) = concat ["Term (",pp e1,",",pp e2,") has parallel type, but checking against ", pp t]
    pp (WrongTypeInl e t) = concat ["Term inl(", pp e,") has sum type, but checking against ", pp t]
    pp (WrongTypeInr e t) = concat ["Term inr(", pp e, ") has sum type, but checking against ", pp t]
    pp (WrongTypeNil t) = concat ["nil does not have type ", pp t]
    pp (WrongTypeCons e1 e2 t) = concat ["Term (",pp e1,") :: (",pp e2,") has star type, but checking against ", pp t]
    pp (ImpossibleCut x e1 e2) = concat ["Impossible cut term ", ppCut x e1 e2, " detected. This is a bug -- please tell Joe."]
        where
            ppCut (Var x') e e' = concat ["let ",x',"= (",pp e,") in (",pp e',")"]
    pp (ListedTypeError t' t e) = concat ["Listed type ", pp t'," in term ", pp e, " did not match type ", pp t]
    pp (UnsaturatedRecursiveCall g g') = concat ["Expected arguments structured like ", pp g, ", instead got ", pp g']
    pp (HasTypeErr rho m) = concat ["Environment ",pp rho," does not hav expected types ", pp m]
    pp (NonMatchingRecursiveArgs g g') = concat ["Recursive arguments ", pp g', " do not match context ", pp g]
    pp (HistTckErr he err) = concat ["Error while checking historical program ", pp he, ": ", pp err]

data RecSig v = Rec (Ctx Var (TyF v)) (TyF v)

data TckCtx v = TckCtx { mp :: M.Map Var.Var (TyF v), rs :: RecSig v, histCtx :: M.Map Var (TyF v), tyVars :: S.Set v }

emptyEnvOfType :: (Ord v) => TckCtx v -> Mono v (Env Var Prefix)
emptyEnvOfType (TckCtx m _ _ _) =
    M.foldrWithKey (\x t m_rho -> do
        t' <- monomorphizeTy t
        bindEnv x (emptyPrefix t') <$> m_rho
    )
    (return emptyEnv) m

class (MonadError (TckErr t v) m, MonadReader (TckCtx v) m) => TckM t v m where
instance TckM t v (ReaderT (TckCtx v) (ExceptT (TckErr t v) Identity)) where

lookupTy :: (TckM t v m) => t -> Var -> m (TyF v)
lookupTy e x = do
    m <- asks mp
    maybe (throwError (VarNotFound x e)) return (M.lookup x m)

lookupTyBool :: (TckM t v m) => t -> Var -> m ()
lookupTyBool e x = do
    s <- lookupTy e x
    case s of
        TyBool -> return ()
        _ -> throwError (ExpectedTyBool x s e)

lookupTyCat :: (TckM t v m) => t -> Var -> m (TyF v, TyF v)
lookupTyCat e x = do
    s' <- lookupTy e x
    case s' of
        TyCat s t -> return (s,t)
        _ -> throwError (ExpectedTyCat x s' e)

lookupTyPar :: (TckM t v m) => t -> Var -> m (TyF v, TyF v)
lookupTyPar e x = do
    s' <- lookupTy e x
    case s' of
        TyPar s t -> return (s,t)
        _ -> throwError (ExpectedTyPar x s' e)

lookupTyPlus :: (TckM t v m) => t -> Var -> m (TyF v, TyF v)
lookupTyPlus e x = do
    s' <- lookupTy e x
    case s' of
        TyPlus s t -> return (s,t)
        _ -> throwError (ExpectedTyPlus x s' e)

lookupTyStar :: (TckM t v m) => t -> Var -> m (TyF v)
lookupTyStar e x = do
    s' <- lookupTy e x
    case s' of
        TyStar s -> return s
        _ -> throwError (ExpectedTyStar x s' e)

withUnbind :: (TckM t v m) => Var -> m a -> m a
withUnbind x = local (\t -> TckCtx (M.delete x (mp t)) (rs t) (histCtx t) (tyVars t))

withBind :: (TckM t v m) => Var -> (TyF v) -> m a -> m a
withBind x s = local (\t -> TckCtx (M.insert x s (mp t)) (rs t) (histCtx t) (tyVars t))

withBindAll :: (TckM t v m) => [(Var,TyF v)] -> m a -> m a
withBindAll xs = local $ \t -> TckCtx (foldr (\(x,s) -> (M.insert x s .)) id xs (mp t)) (rs t) (histCtx t) (tyVars t)

withUnbindAll :: (TckM t v m) => [Var] -> m a -> m a
withUnbindAll xs = local (\t -> TckCtx (foldr M.delete (mp t) xs) (rs t) (histCtx t) (tyVars t))

withRecSig :: (TckM t v m) => Ctx Var (TyF v) -> TyF v -> m a -> m a
withRecSig g s = local $ \t -> TckCtx (mp t) (Rec g s) (histCtx t) (tyVars t)

withCtx :: (TckM t v m) => M.Map Var (TyF v) -> m a -> m a
withCtx m = local (\(TckCtx _ rs hc tv) -> TckCtx m rs hc tv)

withBindHist :: (TckM t v m) => Var -> (TyF v) -> m a -> m a
withBindHist x s = local (\t -> TckCtx (mp t) (rs t) (M.insert x s (histCtx t)) (tyVars t))

handleHasTypeErr :: Types.ValueLikeErr (Env Var Prefix) (M.Map Var (TyF v)) -> TckErr t v
handleHasTypeErr (IllTyped rho m) = HasTypeErr rho m

guard :: (TckM t v m) => Bool -> TckErr t v -> m ()
guard b e = if b then return () else throwError e

reThrow :: (TckM t v m) => (e -> TckErr t v) -> ExceptT e m a -> m a
reThrow k x = runExceptT x >>= either (throwError . k) return

handleOutOfOrder :: t -> (Var,Var) -> TckErr t v
handleOutOfOrder e (x,y) = OutOfOrder x y e

handleConsistentWith :: t -> P.ConsistentWithErr Var -> TckErr t v
handleConsistentWith e (P.OutOfOrder x y) = OutOfOrder x y e
handleConsistentWith e (P.SomeOrder x y) = SomeOrder x y e

handleReUse :: t -> Var -> TckErr t v
handleReUse e x = ReUse x e

handleImpossibleCut :: (Var, Core.Term, Core.Term) -> TckErr t v
handleImpossibleCut (x,e,e') = ImpossibleCut x e e'



data InferElabResult v = IR { ty :: TyF v , iusages :: P.Partial Var, itm :: Mono v Core.Term }
data CheckElabResult v = CR { cusages :: P.Partial Var, ctm :: Mono v Core.Term }


promoteResult :: TyF v -> CheckElabResult v -> InferElabResult v
promoteResult t (CR p e) = IR t p e

liftHistCheck :: (TckM t v m') => t -> ReaderT (M.Map Var (TyF v)) (ExceptT Hist.TckErr Identity) a -> m' a
liftHistCheck e m = do
    ma <- asks ((runIdentity . runExceptT . runReaderT m) . histCtx)
    case ma of
        Left err -> throwError (HistTckErr e err)
        Right a -> return a

checkElab :: (Ord v, TckM Elab.Term v m) => TyF v -> Elab.Term -> m (CheckElabResult v)
checkElab TyInt (Elab.TmLitR l@(LInt _)) = return $ CR P.empty (return (Core.TmLitR l))
checkElab TyBool (Elab.TmLitR l@(LBool _)) = return $ CR P.empty (return (Core.TmLitR l))
checkElab t (Elab.TmLitR l) = throwError (WrongTypeLit l t)
checkElab TyEps Elab.TmEpsR = return $ CR P.empty (return Core.TmEpsR)
checkElab t Elab.TmEpsR = throwError (WrongTypeEpsR t)

checkElab t e@(Elab.TmVar x) = do
    s <- lookupTy e x
    guard (s == t) (WrongTypeVar x t s)
    return $ CR (P.singleton x) (return (Core.TmVar x))

checkElab r e@(Elab.TmCatL x y z e') = do
    (s,t) <- lookupTyCat e z
    (CR p e'') <- withBindAll [(x,s),(y,t)] $ withUnbind z (checkElab r e')
    -- Ensure that x and y are used in order in e: y cannot be before x.
    guard (not $ P.lessThan p y x) (OutOfOrder x y e')
    -- Replace x and y with z in the output
    p' <- reThrow (handleOutOfOrder e') $ P.substSingAll p [(P.singleton z,x),(P.singleton z,y)]
    return $ CR p' $ do
        t' <- monomorphizeTy t
        Core.TmCatL t' x y z <$> e''

checkElab (TyCat s t) (Elab.TmCatR e1 e2) = do
    CR p1 e1' <- checkElab s e1
    CR p2 e2' <- checkElab t e2
    reThrow (handleReUse (Elab.TmCatR e1 e2)) (P.checkDisjoint p1 p2)
    p' <- reThrow (handleOutOfOrder (Elab.TmCatR e1 e2)) $ P.concat p1 p2
    return $ CR p' (Core.TmCatR <$> e1' <*> e2')
checkElab t (Elab.TmCatR e1 e2) = throwError (WrongTypeCatR e1 e2 t)

checkElab r e@(Elab.TmParL x y z e') = do
    (s,t) <- lookupTyPar e z
    (CR p e'') <- withBindAll [(x,s),(y,t)] $ withUnbind z (checkElab r e')
    when (P.comparable p y x) (throwError (SomeOrder x y e'))
    p' <- reThrow (handleOutOfOrder e') $ P.substSingAll p [(P.singleton z,x),(P.singleton z,y)]
    return $ CR p' (Core.TmParL x y z <$> e'')

checkElab (TyPar s t) e@(Elab.TmParR e1 e2) = do
    CR p1 e1' <- checkElab s e1
    CR p2 e2' <- checkElab t e2
    p' <- reThrow (handleOutOfOrder e) $ P.union p1 p2
    return $ CR p' (Core.TmParR <$> e1' <*> e2')
checkElab t (Elab.TmParR e1 e2) = throwError (WrongTypeParR e1 e2 t)

checkElab (TyPlus s _) (Elab.TmInl e) = do
    CR p e' <- checkElab s e
    return $ CR p (Core.TmInl <$> e')
checkElab t (Elab.TmInl e) = throwError (WrongTypeInl e t)

checkElab (TyPlus _ t) (Elab.TmInr e) = do
    CR p e' <- checkElab t e
    return $ CR p (Core.TmInr <$> e')
checkElab t (Elab.TmInr e) = throwError (WrongTypeInr e t)

checkElab r e@(Elab.TmPlusCase z x e1 y e2) = do
    (s,t) <- lookupTyPlus e z
    CR p1 e1' <- withBind x s $ withUnbind z $ checkElab r e1
    CR p2 e2' <- withBind y t $ withUnbind z $ checkElab r e2
    p' <- reThrow (handleOutOfOrder e) (P.union p1 p2)
    p'' <- reThrow (handleOutOfOrder e) (P.substSingAll p' [(P.singleton z,x),(P.singleton z,y)])
    m_rho <- asks emptyEnvOfType
    -- m <- asks mp
    m <- undefined
    return $ CR p'' $ do
        r' <- monomorphizeTy r
        me1' <- e1'
        me2' <- e2'
        rho <- m_rho
        return (Core.TmPlusCase m rho r' z x me1' y me2')

checkElab r e@(Elab.TmIte z e1 e2) = do
    lookupTyBool e z
    CR p1 e1' <- checkElab r e1
    CR p2 e2' <- checkElab r e2
    p' <- reThrow (handleOutOfOrder e) (P.union p1 p2)
    -- rho <- asks emptyEnvOfType
    rho <- undefined
    -- m <- asks mp
    m <- undefined
    return $ CR p' $ do
        r' <- monomorphizeTy r
        Core.TmIte m rho r' z <$> e1' <*> e2'


checkElab (TyStar _) Elab.TmNil = return (CR P.empty (return Core.TmNil))
checkElab t Elab.TmNil = throwError (WrongTypeNil t)

checkElab (TyStar s) (Elab.TmCons e1 e2) = do
    CR p1 e1' <- checkElab s e1
    CR p2 e2' <- checkElab (TyStar s) e2
    reThrow (handleReUse (Elab.TmCons e1 e2)) (P.checkDisjoint p1 p2)
    p' <- reThrow (handleOutOfOrder (Elab.TmCatR e1 e2)) $ P.concat p1 p2
    return $ CR p' (Core.TmCons <$> e1' <*> e2')

checkElab t (Elab.TmCons e1 e2) = throwError (WrongTypeCons e1 e2 t)

checkElab r e@(Elab.TmStarCase z e1 x xs e2) = do
    s <- lookupTyStar e z
    CR p1 e1' <- withUnbind z (checkElab r e1)
    CR p2 e2' <- withBindAll [(x,s),(xs,TyStar s)] $ withUnbind z (checkElab r e2)
    guard (not $ P.lessThan p2 xs x) (OutOfOrder x xs e2)
    p' <- reThrow (handleOutOfOrder e) $ P.union p1 p2
    p'' <- reThrow (handleOutOfOrder e) (P.substSingAll p' [(P.singleton z,x),(P.singleton z,xs)])
    m_rho <- asks emptyEnvOfType
    -- m <- asks mp
    m <- undefined
    return $ CR p'' $ do
        s' <- monomorphizeTy s
        r' <- monomorphizeTy r
        me1' <- e1'
        me2' <- e2'
        rho <- m_rho
        return (Core.TmStarCase m rho r' s' z me1' x xs me2')

checkElab r e@(Elab.TmCut x e1 e2) = do
    IR s p be1 <- inferElab e1
    CR p' be2 <- withBind x s . withUnbindAll (P.list p) $ checkElab r e2
    reThrow (handleReUse e) (P.checkDisjoint p p')
    p'' <- reThrow (handleOutOfOrder (Elab.TmCut x e1 e2)) $ P.substSing p' p x
    return (CR p'' (Core.TmCut x <$> be1 <*> be2))

checkElab r e@(Elab.TmRec es) = do
    Rec g r' <- asks rs
    when (r /= r') $ throwError (UnequalReturnTypes r r' e) -- ensure the return type is the proper one
    (p,args) <- elabRec g es
    return (CR p (Core.TmRec <$> args))

checkElab r e@(Elab.TmWait x e') = do
    -- rho <- asks emptyEnvOfType
    rho <- undefined
    s <- lookupTy e x
    CR p e'' <- withBindHist x s $ withUnbind x $ checkElab r e'
    return $ CR p $ do
        s' <- monomorphizeTy s
        Core.TmWait rho s' x <$> e''

checkElab r e@(Elab.TmHistPgm he) = undefined
    -- () <- liftHistCheck e (Hist.check he r)
    -- return (CR P.empty (Core.TmHistPgm _ he))


elabRec :: (Ord v, TckM Elab.Term v m) => Ctx Var (TyF v) -> CtxStruct Elab.Term -> m (P.Partial Var, Mono v (CtxStruct Core.Term))
elabRec EmpCtx EmpCtx = return (P.empty,return EmpCtx)
elabRec g@EmpCtx g' = throwError (UnsaturatedRecursiveCall g g')
elabRec (SngCtx (CE _ s)) (SngCtx e) = do
    CR p e' <- checkElab s e
    return (p,SngCtx <$> e')
elabRec g@(SngCtx {}) g' = throwError (UnsaturatedRecursiveCall g g')
elabRec (SemicCtx g1 g2) (SemicCtx args1 args2) = do
    (p,args1') <- elabRec g1 args1
    (p',args2') <- elabRec g2 args2
    reThrow (error "asdf") (P.checkDisjoint p p')
    p'' <- reThrow (handleOutOfOrder (error "Arguments use variables inconsistently")) $ P.concat p p'
    return (p'',SemicCtx <$> args1' <*> args2')
elabRec g@(SemicCtx {}) g' = throwError (UnsaturatedRecursiveCall g g')
elabRec (CommaCtx g1 g2) (CommaCtx args1 args2) = do
    (p,args1') <- elabRec g1 args1
    (p',args2') <- elabRec g2 args2
    p'' <- reThrow (handleOutOfOrder (error "Arguments use variables inconsistently")) $ P.union p p'
    return (p'',CommaCtx <$> args1' <*> args2')
elabRec g@(CommaCtx {}) g' = throwError (UnsaturatedRecursiveCall g g')


inferElab :: (Ord v, TckM Elab.Term v m) => Elab.Term -> m (InferElabResult v)
inferElab (Elab.TmLitR (LInt n)) = return $ IR TyInt P.empty (return (Core.TmLitR (LInt n)))
inferElab (Elab.TmLitR (LBool b)) = return $ IR TyBool P.empty (return (Core.TmLitR (LBool b)))
inferElab Elab.TmEpsR = return $ IR TyEps P.empty (return Core.TmEpsR)

inferElab e@(Elab.TmVar x) = do
    s <- lookupTy e x
    return $ IR s (P.singleton x) (return (Core.TmVar x))

inferElab e@(Elab.TmCatL x y z e') = do
    -- Find the type for x and y
    (s,t) <- lookupTyCat e z
    -- Bind x:s,y:t, unbind z, and recursively check 
    (IR r p e'') <- withBindAll [(x,s),(y,t)] $ withUnbind z (inferElab e')
    -- Ensure that x and y are used in order in e: y cannot be before x.
    guard (not $ P.lessThan p y x) (OutOfOrder x y e')
    -- Replace x and y with z in the output
    p' <- reThrow (handleOutOfOrder e') $ P.substSingAll p [(P.singleton z,x),(P.singleton z,y)]
    return $ IR r p' $ do
        t' <- monomorphizeTy t
        Core.TmCatL t' x y z <$> e''

inferElab e@(Elab.TmCatR e1 e2) = do
    IR s p1 e1' <- inferElab e1
    IR t p2 e2' <- inferElab e2
    p' <- reThrow (handleOutOfOrder e) $ P.concat p1 p2
    reThrow (handleReUse e) (P.checkDisjoint p1 p2)
    return $ IR (TyCat s t) p' (Core.TmCatR <$> e1' <*> e2')

inferElab e@(Elab.TmParL x y z e') = do
    (s,t) <- lookupTyPar e z
    (IR r p e'') <- withBindAll [(x,s),(y,t)] $ withUnbind z (inferElab e')
    when (P.comparable p y x) (throwError (SomeOrder x y e'))
    p' <- reThrow (handleOutOfOrder e') $ P.substSingAll p [(P.singleton z,x),(P.singleton z,y)]
    return $ IR r p' (Core.TmParL x y z <$> e'')

inferElab e@(Elab.TmParR e1 e2) = do
    IR s p1 e1' <- inferElab e1
    IR t p2 e2' <- inferElab e2
    p' <- reThrow (handleOutOfOrder e) $ P.union p1 p2
    return $ IR (TyPar s t) p' (Core.TmParR <$> e1' <*> e2')

inferElab e@(Elab.TmInl {}) = throwError (CheckTermInferPos e)
inferElab e@(Elab.TmInr {}) = throwError (CheckTermInferPos e)

inferElab e@(Elab.TmPlusCase z x e1 y e2) = do
    (s,t) <- lookupTyPlus e z
    IR r1 p1 e1' <- withBind x s $ withUnbind z $ inferElab e1
    IR r2 p2 e2' <- withBind y t $ withUnbind z $ inferElab e2
    guard (r1 == r2) (UnequalReturnTypes r1 r2 e)
    p' <- reThrow (handleOutOfOrder e) $ P.union p1 p2
    -- rho <- asks emptyEnvOfType
    rho <- undefined
    -- m <- asks mp
    m <- undefined
    return $ IR r1 p' $ do
        r1' <- monomorphizeTy r1
        me1' <- e1'
        me2' <- e2'
        return (Core.TmPlusCase m rho r1' z x me1' y me2')

inferElab e@(Elab.TmIte z e1 e2) = do
    lookupTyBool e z
    IR r1 p1 e1' <- inferElab e1
    IR r2 p2 e2' <- inferElab e2
    guard (r1 == r2) (UnequalReturnTypes r1 r2 e)
    p' <- reThrow (handleOutOfOrder e) $ P.union p1 p2
    m_rho <- asks emptyEnvOfType
    -- rho <- undefined
    -- m <- asks mp
    m <- undefined
    return $ IR r1 p' $ do
        rho <- m_rho
        r <- monomorphizeTy r1
        Core.TmIte m rho r z <$> e1' <*> e2'

inferElab e@Elab.TmNil = throwError (CheckTermInferPos e)

inferElab e@(Elab.TmCons e1 e2) = do
    IR s p1 e1' <- inferElab e1
    CR p2 e2' <- checkElab (TyStar s) e2
    reThrow (handleReUse e) (P.checkDisjoint p1 p2)
    p' <- reThrow (handleOutOfOrder e) $ P.concat p1 p2
    return $ IR (TyStar s) p' (Core.TmCons <$> e1' <*> e2')

inferElab e@(Elab.TmStarCase z e1 x xs e2) = do
    s <- lookupTyStar e z
    IR r1 p1 e1' <- withUnbind z $ inferElab e1
    IR r2 p2 e2' <- withBindAll [(x,s),(xs,TyStar s)] $ withUnbind z $ inferElab e2
    guard (r1 == r2) (UnequalReturnTypes r1 r2 e)
    p' <- reThrow (handleOutOfOrder e) $ P.union p1 p2
    -- rho <- asks emptyEnvOfType
    rho <- undefined
    -- m <- asks mp
    m <- undefined
    return $ IR r1 p' $ do
        mr <- monomorphizeTy r1
        ms <- monomorphizeTy s
        me1' <- e1'
        me2' <- e2'
        return (Core.TmStarCase m rho mr ms z me1' x xs me2')

inferElab e@(Elab.TmCut x e1 e2) = do
    IR s p e1' <- inferElab e1
    IR t p' e2' <- withBind x s . withUnbindAll (P.list p) $ inferElab e2
    reThrow (handleReUse e) (P.checkDisjoint p p') {- this should be guaranteed by the fact that we unbind all the vars in p -}
    p'' <- reThrow (handleOutOfOrder (Elab.TmCut x e1 e2)) $ P.substSing p' p x
    -- e' <- reThrow handleImpossibleCut (Core.cut x e1' e2')
    return (IR t p'' (Core.TmCut x <$> e1' <*> e2'))

inferElab e@(Elab.TmRec es) = do
    Rec g r <- asks rs
    (p,args) <- elabRec g es
    return (IR r p (Core.TmRec <$> args))

inferElab e@(Elab.TmWait x e') = do
    -- rho <- asks emptyEnvOfType
    rho <- undefined
    s <- lookupTy e x
    IR t p e'' <- withBindHist x s $ withUnbind x $ inferElab e'
    return $ IR t p $ do
        s' <- monomorphizeTy s
        Core.TmWait rho s' x <$>e''

inferElab e@(Elab.TmHistPgm he) = undefined
    -- r <- liftHistCheck e (Hist.infer he)
    -- return (IR _ P.empty (Core.TmHistPgm r he))


{-
checkCore :: (TckM Core.Term v m) => TyF v -> Core.Term -> m (P.Partial Var.Var)
checkCore TyInt (Core.TmLitR (LInt _)) = return P.empty
checkCore TyBool (Core.TmLitR (LBool _)) = return P.empty
checkCore t (Core.TmLitR l) = throwError (WrongTypeLit l t)
checkCore TyEps Core.TmEpsR = return P.empty
checkCore t Core.TmEpsR = throwError (WrongTypeEpsR t)

checkCore t e@(Core.TmVar x) = do
    s <- lookupTy e x
    guard (s == t) (WrongTypeVar x t s)
    return (P.singleton x)

checkCore r e@(Core.TmCatL t' x y z e') = do
    (s,t) <- lookupTyCat e z
    guard (t == t') (ListedTypeError t' t e)
    p <- withBindAll [(x,s),(y,t)] $ withUnbind z (checkCore r e')
    guard (not $ P.lessThan p y x) (OutOfOrder x y e')
    -- Replace x and y with z in the output
    reThrow (handleOutOfOrder e') $ P.substSingAll p [(P.singleton z,x),(P.singleton z,y)]

checkCore (TyCat s t) e@(Core.TmCatR e1 e2) = do
    p1 <- checkCore s e1
    p2 <- checkCore t e2
    reThrow (handleReUse e) (P.checkDisjoint p1 p2)
    reThrow (handleOutOfOrder (Core.TmCatR e1 e2)) $ P.concat p1 p2
checkCore t (Core.TmCatR e1 e2) = throwError (WrongTypeCatR e1 e2 t)

checkCore r e@(Core.TmParL x y z e') = do
    (s,t) <- lookupTyPar e z
    p <- withBindAll [(x,s),(y,t)] $ withUnbind z (checkCore r e')
    when (P.comparable p y x) (throwError (SomeOrder x y e'))
    reThrow (handleOutOfOrder e') $ P.substSingAll p [(P.singleton z,x),(P.singleton z,y)]

checkCore (TyPar s t) e@(Core.TmParR e1 e2) = do
    p1 <- checkCore s e1
    p2 <- checkCore t e2
    reThrow (handleOutOfOrder e) $ P.union p1 p2
checkCore t (Core.TmParR e1 e2) = throwError (WrongTypeParR e1 e2 t)



checkCore (TyPlus s _) (Core.TmInl e) = checkCore s e
checkCore t (Core.TmInl e) = throwError (WrongTypeInl e t)

checkCore (TyPlus _ t) (Core.TmInr e) = checkCore t e
checkCore t (Core.TmInr e) = throwError (WrongTypeInr e t)

checkCore r e@(Core.TmPlusCase m rho r' z x e1 y e2) = do
    reThrow handleHasTypeErr (hasType rho m)
    withCtx m $ do
        (s,t) <- lookupTyPlus e z
        guard (r == r') (ListedTypeError r' r e)
        p1 <- withBind x s $ withUnbind z $ checkCore r e1
        p2 <- withBind y t $ withUnbind z $ checkCore r e2
        p' <- reThrow (handleOutOfOrder e) (P.union p1 p2)
        reThrow (handleOutOfOrder e) (P.substSingAll p' [(P.singleton z,x),(P.singleton z,y)])

checkCore r e@(Core.TmIte m rho r' z e1 e2) = do
    reThrow handleHasTypeErr (hasType rho m)
    withCtx m $ do
        lookupTyBool e z
        guard (r == r') (ListedTypeError r' r e)
        p1 <- checkCore r e1
        p2 <- checkCore r e2
        reThrow (handleOutOfOrder e) (P.union p1 p2)

checkCore (TyStar _) Core.TmNil = return P.empty
checkCore t Core.TmNil = throwError (WrongTypeNil t)

checkCore (TyStar s) e@(Core.TmCons e1 e2) = do
    p1 <- checkCore s e1
    p2 <- checkCore (TyStar s) e2
    reThrow (handleReUse e) (P.checkDisjoint p1 p2)
    reThrow (handleOutOfOrder (Core.TmCatR e1 e2)) $ P.concat p1 p2
checkCore t e@(Core.TmCons e1 e2) = throwError (WrongTypeCons e1 e2 t)

checkCore r e@(Core.TmStarCase m rho r' s' z e1 x xs e2) = do
    reThrow handleHasTypeErr (hasType rho m)
    withCtx m $ do
        guard (r == r') (ListedTypeError r' r e)
        s <- lookupTyStar e z
        guard (s == s') (ListedTypeError s' s e)
        p1 <- withUnbind z (checkCore r e1)
        p2 <- withBindAll [(x,s),(xs,TyStar s)] $ withUnbind z (checkCore r e2)
        guard (not $ P.lessThan p2 xs x) (OutOfOrder x xs e2)
        p' <- reThrow (handleOutOfOrder e) $ P.union p1 p2
        reThrow (handleOutOfOrder e) (P.substSingAll p' [(P.singleton z,x),(P.singleton z,xs)])

checkCore r e@(Core.TmRec args) = do
    TckCtx g_bound (Rec g r') _ _ <- ask
    guard (r == r') (UnequalReturnTypes r r' e) --return types are the same
    checkRec g args

checkCore r e@(Core.TmFix args g s e') = do
    p <- checkRec g args
    p' <- withRecSig g s (checkCore r e')
    reThrow (handleConsistentWith e) (P.consistentWith p' (_fst <$> g))
    return p

checkCore r e@(Core.TmCut x e1 e2) = do
    (s,p) <- inferCore e1
    p' <- withBind x s $ checkCore r e2
    reThrow (handleReUse e) (P.checkDisjoint p p')
    reThrow (handleOutOfOrder (Core.TmCut x e1 e2)) $ P.substSing p' p x

checkCore r e@(Core.TmWait _ r' x e') = do
    guard (r == r') (ListedTypeError r r' e)
    s <- lookupTy e x
    withBindHist x s $ withUnbind x $ checkCore r e'

checkCore r e@(Core.TmHistPgm r' he) = do
    when (r /= r') $ throwError (ListedTypeError r' r e)
    () <- liftHistCheck e (Hist.check he r)
    return P.empty


inferCore :: (TckM Core.Term v m) => Core.Term -> m (Ty,P.Partial Var.Var)
inferCore (Core.TmLitR (LInt _)) = return (TyInt,P.empty)
inferCore (Core.TmLitR (LBool _)) = return (TyBool,P.empty)
inferCore Core.TmEpsR = return (TyEps,P.empty)

inferCore e@(Core.TmVar x) = do
    s <- lookupTy e x
    return (s,P.singleton x)

inferCore e@(Core.TmCatL t' x y z e') = do
    (s,t) <- lookupTyCat e z
    guard (t == t') (ListedTypeError t' t e)
    (r,p) <- withBindAll [(x,s),(y,t)] $ withUnbind z (inferCore e')
    guard (not $ P.lessThan p y x) (OutOfOrder x y e')
    p'' <- reThrow (handleOutOfOrder e') $ P.substSingAll p [(P.singleton z,x),(P.singleton z,y)]
    return (r,p'')

inferCore e@(Core.TmCatR e1 e2) = do
    (s,p1) <- inferCore e1
    (t,p2) <- inferCore e2
    reThrow (handleReUse e) (P.checkDisjoint p1 p2)
    p'' <- reThrow (handleOutOfOrder e) $ P.concat p1 p2
    return (TyCat s t,p'')

inferCore e@(Core.TmParL x y z e') = do
    (s,t) <- lookupTyPar e z
    (r,p) <- withBindAll [(x,s),(y,t)] $ withUnbind z (inferCore e')
    when (P.comparable p y x) (throwError (SomeOrder x y e'))
    p'' <- reThrow (handleOutOfOrder e') $ P.substSingAll p [(P.singleton z,x),(P.singleton z,y)]
    return (r,p'')

inferCore e@(Core.TmParR e1 e2) = do
    (s,p1) <- inferCore e1
    (t,p2) <- inferCore e2
    p'' <- reThrow (handleOutOfOrder e) $ P.union p1 p2
    return (TyCat s t,p'')

inferCore (Core.TmInl e) = undefined
inferCore (Core.TmInr e) = undefined

inferCore e@(Core.TmPlusCase m rho r z x e1 y e2) = do
    reThrow handleHasTypeErr (hasType rho m)
    withCtx m $ do
        (s,t) <- lookupTyPlus e z
        p1 <- withBind x s $ withUnbind z $ checkCore r e1
        p2 <- withBind y t $ withUnbind z $ checkCore r e2
        p' <- reThrow (handleOutOfOrder e) (P.union p1 p2)
        p'' <- reThrow (handleOutOfOrder e) (P.substSingAll p' [(P.singleton z,x),(P.singleton z,y)])
        return (r,p'')

inferCore e@(Core.TmIte m rho r z e1 e2) = do
    reThrow handleHasTypeErr (hasType rho m)
    withCtx m $ do
        lookupTyBool e z
        p1 <- checkCore r e1
        p2 <- checkCore r e2
        (r,) <$> reThrow (handleOutOfOrder e) (P.union p1 p2)

inferCore Core.TmNil = undefined

inferCore e@(Core.TmCons e1 e2) = do
    (s,p1) <- inferCore e1
    p2 <- checkCore (TyStar s) e2
    reThrow (handleReUse e) (P.checkDisjoint p1 p2)
    p <- reThrow (handleOutOfOrder (Core.TmCatR e1 e2)) $ P.concat p1 p2
    return (TyStar s, p)

inferCore e@(Core.TmStarCase m rho r s' z e1 x xs e2) = do
    reThrow handleHasTypeErr (hasType rho m)
    withCtx m $ do
        s <- lookupTyStar e z
        guard (s == s') (ListedTypeError s' s e)
        p1 <- withUnbind z (checkCore r e1)
        p2 <- withBindAll [(x,s),(xs,TyStar s)] $ withUnbind z (checkCore r e2)
        guard (not $ P.lessThan p2 xs x) (OutOfOrder x xs e2)
        p' <- reThrow (handleOutOfOrder e) $ P.union p1 p2
        p'' <- reThrow (handleOutOfOrder e) (P.substSingAll p' [(P.singleton z,x),(P.singleton z,xs)])
        return (r,p'')

inferCore e@(Core.TmRec args) = do
    TckCtx _ (Rec g r) _ _ <- ask
    p <- checkRec g args
    return (r,p)

inferCore (Core.TmFix args g s e') =  do
    p <- checkRec g args
    !_ <- withRecSig g s (checkCore s e')
    return (s,p)

inferCore e@(Core.TmCut x e1 e2) = do
    (s,p) <- inferCore e1
    (t,p') <- withBind x s $ inferCore e2
    reThrow (handleReUse e) (P.checkDisjoint p p')
    p'' <- reThrow (handleOutOfOrder (Core.TmCut x e1 e2)) $ P.substSing p' p x
    return (t,p'')

inferCore e@(Core.TmWait _ r x e') = do
    s <- lookupTy e x
    p <- withBindHist x s $ withUnbind x $ checkCore r e'
    return (r,p)

inferCore e@(Core.TmHistPgm s he) = do
    () <- liftHistCheck e (Hist.check he s)
    return (s,P.empty)

checkRec :: (TckM Core.Term v m) => Ctx Var Ty -> CtxStruct Core.Term -> m (P.Partial Var)
checkRec EmpCtx EmpCtx = return P.empty
checkRec g@EmpCtx g' = throwError (NonMatchingRecursiveArgs g g')
checkRec (SngCtx (CE x t)) (SngCtx e) = checkCore t e
checkRec g@(SngCtx {}) g' = throwError (NonMatchingRecursiveArgs g g')
checkRec (SemicCtx g1 g2) (SemicCtx g1' g2') = do
    p1 <- checkRec g1 g1'
    p2 <- checkRec g2 g2'
    reThrow (handleReUse (error "ahhhh")) (P.checkDisjoint p1 p2)
    reThrow (handleOutOfOrder (error "eek")) (P.concat p1 p2)
checkRec g@(SemicCtx {}) g' = throwError (NonMatchingRecursiveArgs g g')
checkRec (CommaCtx g1 g2) (CommaCtx g1' g2') = do
    p1 <- checkRec g1 g1'
    p2 <- checkRec g2 g2'
    reThrow (handleOutOfOrder (error "eek")) (P.union p1 p2)
checkRec g@(CommaCtx {}) g' = throwError (NonMatchingRecursiveArgs g g')
-}

data PrefixCheckErr =
      WrongType Ty Surf.UntypedPrefix
    | WrongArgShape (Ctx Var Ty) (Ctx Var Surf.UntypedPrefix)
    | OrderIssueCtx (Env Var Prefix) (Env Var Prefix)
    | OrderIssue Prefix Prefix
    | NotDisjointCtx Var Prefix Prefix
    | IllegalStp Prefix
    deriving (Eq, Ord, Show)

checkUntypedPrefix :: (Monad m) => Ty -> Surf.UntypedPrefix -> ExceptT PrefixCheckErr m Prefix
checkUntypedPrefix t Surf.EmpP = return (emptyPrefix t)
checkUntypedPrefix t@TyEps p = throwError $ WrongType t p
checkUntypedPrefix TyInt (Surf.LitP l@(LInt _)) = return (LitPFull l)
checkUntypedPrefix t@TyInt p = throwError $ WrongType t p
checkUntypedPrefix TyBool (Surf.LitP l@(LBool _)) = return (LitPFull l)
checkUntypedPrefix t@TyBool p = throwError $ WrongType t p
checkUntypedPrefix (TyCat s _) (Surf.CatPA p) = do
    p' <- checkUntypedPrefix s p
    return (CatPA p')
checkUntypedPrefix (TyCat s t) (Surf.CatPB p1 p2) = do
    p1' <- checkUntypedPrefix s p1
    p2' <- checkUntypedPrefix t p2
    if isMaximal p1' || isEmpty p2' then return (CatPB p1' p2')
    else throwError $ OrderIssue p1' p2'
checkUntypedPrefix t@(TyCat {}) p = throwError $ WrongType t p

checkUntypedPrefix (TyPar s t) (Surf.ParP p1 p2) = do
    p1' <- checkUntypedPrefix s p1
    p2' <- checkUntypedPrefix t p2
    return (ParP p1' p2')
checkUntypedPrefix t@(TyPar {}) p = throwError $ WrongType t p

checkUntypedPrefix (TyPlus s _) (Surf.SumPA p) = do
    p' <- checkUntypedPrefix s p
    return (SumPA p')
checkUntypedPrefix (TyPlus _ t) (Surf.SumPB p) = do
    p' <- checkUntypedPrefix t p
    return (SumPB p')
checkUntypedPrefix t@(TyPlus {}) p = throwError $ WrongType t p

checkUntypedPrefix (TyStar _) Surf.StpDone = return StpDone
checkUntypedPrefix (TyStar s) (Surf.StpA p) = do
    p' <- checkUntypedPrefix s p
    return (StpA p')
checkUntypedPrefix (TyStar s) (Surf.StpB p1 p2) = do
    p1' <- checkUntypedPrefix s p1
    p2' <- checkUntypedPrefix (TyStar s) p2
    if isMaximal p1' || isEmpty p2' then return (StpB p1' p2') else throwError (IllegalStp (StpB p1' p2'))

checkUntypedPrefix t@(TyStar _) p = throwError $ WrongType t p

checkUntypedPrefix (TyVar x) _ = absurd x

checkUntypedStp :: (Monad m) => Ty -> [Surf.UntypedPrefix] -> ExceptT PrefixCheckErr m Prefix
checkUntypedStp _ [] = return StpDone
checkUntypedStp s (p:ps) = do
    p' <- checkUntypedPrefix s p
    if isMaximal p' then do
        p'' <- checkUntypedStp s ps
        return (StpB p' p'')
    else if null ps then return (StpA p')
    else throwError (IllegalStp p')

checkUntypedPrefixCtx :: (Monad m) => Ctx Var Ty -> Ctx Var Surf.UntypedPrefix -> ExceptT PrefixCheckErr m (Env Var Prefix)
checkUntypedPrefixCtx EmpCtx EmpCtx = return emptyEnv
checkUntypedPrefixCtx g@EmpCtx g' = throwError (WrongArgShape g g')
checkUntypedPrefixCtx g@(SngCtx (CE x s)) g'@(SngCtx (CE y p)) =
    if x == y then singletonEnv x <$> checkUntypedPrefix s p
    else throwError (WrongArgShape g g')
checkUntypedPrefixCtx g@(SngCtx {}) g' = throwError (WrongArgShape g g')
checkUntypedPrefixCtx (SemicCtx g1 g2) (SemicCtx g1' g2') = do
    rho1 <- checkUntypedPrefixCtx g1 g1'
    rho2 <- checkUntypedPrefixCtx g2 g2'
    if allEnv isMaximal rho1 || allEnv isEmpty rho2 then
        runExceptT (unionDisjointEnv rho1 rho2) >>= either (\(v,p,p') -> throwError (NotDisjointCtx v p p')) return
    else throwError (OrderIssueCtx rho1 rho2)
checkUntypedPrefixCtx g@(SemicCtx {}) g' = throwError (WrongArgShape g g')
checkUntypedPrefixCtx (CommaCtx g1 g2) (CommaCtx g1' g2') = do
    rho1 <- checkUntypedPrefixCtx g1 g1'
    rho2 <- checkUntypedPrefixCtx g2 g2'
    runExceptT (unionDisjointEnv rho1 rho2) >>= either (\(v,p,p') -> throwError (NotDisjointCtx v p p')) return
checkUntypedPrefixCtx g@(CommaCtx {}) g' = throwError (WrongArgShape g g')

type FileInfo = M.Map String ([Var.TyVar], Mono Var.TyVar (Ctx Var Ty), Mono Var.TyVar Ty)

-- Doublecheck argument typechecks the resulting term, again.
doCheckElabTm :: (MonadIO m) => [Var.TyVar] -> Ctx Var (TyF Var.TyVar) -> TyF Var.TyVar -> Elab.Term -> m (Mono Var.TyVar Core.Term)
doCheckElabTm vs g t e = do
    let ck = runIdentity $ runExceptT $ runReaderT (checkElab t e :: (ReaderT (TckCtx Var.TyVar) (ExceptT (TckErr Elab.Term Var.TyVar) Identity) (CheckElabResult Var.TyVar))) (TckCtx (ctxBindings g) (Rec g t) M.empty (S.fromList vs))
    case ck of
        Left err -> error (pp err)
        Right (CR usages m_tm) -> do
            (usageConsist :: Either (TckErr Elab.Term Void) ())<- runExceptT (withExceptT (handleConsistentWith e) $ P.consistentWith usages (_fst <$> g))
            case usageConsist of
                Left err -> error (pp err)
                Right _ -> return $ do
                    tm <- m_tm
                    t' <- monomorphizeTy t
                    g' <- monomorphizeCtx g
                    return (Core.TmFix (fmap (\(CE x _) -> Core.TmVar x) g') g' t' tm)


-- doCheckCoreTm :: (MonadIO m) => Ctx Var Ty -> Ty -> Core.Term -> m ()
-- doCheckCoreTm g t e = do
--     let ck = runIdentity $ runExceptT $ runReaderT (checkCore t e :: (ReaderT (TckCtx Var.TyVar) (ExceptT (TckErr Core.Term Var.TyVar) Identity) (P.Partial Var))) (TckCtx (ctxBindings g) (Rec g t) M.empty S.empty)
--     case ck of
--         Left err -> error ("ERROR: " ++ pp err ++ " while checking " ++ pp e ++ " against type " ++ pp t ++ " in context " ++ pp g)
--         Right usages -> do
--             usageConsist <- runExceptT (withExceptT (handleConsistentWith e) $ P.consistentWith usages (_fst <$> g))
--             either (error . pp) return usageConsist

doCheckElabPgm :: (MonadIO m) => Elab.Program -> m Core.Program
doCheckElabPgm xs = fst <$> runStateT (mapM go xs) M.empty
    where
        go :: (MonadIO m) => Elab.Cmd -> StateT FileInfo m Core.Cmd
        go (Elab.FunDef f tvs g t e) = do
            -- Typecheck the function
            e' <- lift $ doCheckElabTm tvs g t e
            liftIO $ putStrLn $ "Function " ++ f ++ " typechecked OK."
            fi <- get
            -- Insert the information for f into the file info: a monomorphizer for the type, term, and the list of type variables.
            let mg = monomorphizeCtx g
            let mt = monomorphizeTy t
            put (M.insert f (tvs,mg,mt) fi)
            return (Core.FunDef f tvs mg mt e')
        go (Elab.RunCommand f ts p) = do
            -- Look up the type parameters
            (tvs,mg,_) <- gets (M.lookup f) >>= maybe (error $ "Function " ++ f ++ " not defined.") return
            when (length ts /= length tvs) $ error $ "Unsaturated type parameters."
            -- Build the map from type variables to closed types being applied
            let monomap = foldr (uncurry M.insert) M.empty (zip tvs ts)
            -- Monomorphize the context that "f" was typed in.
            case runMono mg monomap of
                Left err -> error (pp err)
                Right g -> do
                    -- Build concrete (core) input prefixes for the monomorphized context g
                    mps <- lift (runExceptT (checkUntypedPrefixCtx g p))
                    case mps of
                        Left err -> error (show err)
                        Right ps -> return (Core.RunCommand f ts ps)

        go (Elab.RunStepCommand f p) = undefined
            -- (g,s) <- gets (M.lookup f) >>= maybe (error $ "Function " ++ f ++ " not defined.") return
            -- mps <- lift (runExceptT (checkUntypedPrefixCtx g p))
            -- case mps of
                -- Left err -> error (show err)
                -- Right rho -> do
                    -- g' <- runExceptT (deriv rho g) >>= either (error . pp) return
                    -- modify (M.insert f (g',s))
                    -- return (Core.RunStepCommand f rho)

tckTests = TestList []