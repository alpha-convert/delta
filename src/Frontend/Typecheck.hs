-- AUTHORS: Emeka Nkurumeh, Joe Cutler
{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, BangPatterns #-}

module Frontend.Typecheck(
    doCheckElabPgm,
    doCheckCoreTm,
    doCheckElabTm,
    tckTests
) where

import qualified Frontend.ElabSyntax as Elab
import qualified CoreSyntax as Core
import Control.Monad.Except (MonadError (throwError), runExceptT, ExceptT)
import Types (Ctx (..), Ty(..), ctxBindings, ctxVars, emptyPrefix, ctxAssoc, deriv, ValueLikeErr (IllTyped), ValueLike (hasType), ctxMap)
import Control.Monad.Reader (MonadReader (ask, local), asks, ReaderT (runReaderT))
import Var (Var (Var))
import Values (Lit(..), Env, Prefix (..), emptyEnv, bindEnv, isMaximal, isEmpty, allEnv, unionDisjointEnv)
import qualified Data.Map as M
import qualified Util.PartialOrder as P
import Control.Monad.Identity (Identity (runIdentity))
import Util.PrettyPrint (PrettyPrint,pp)
import Control.Monad.State.Strict (StateT(runStateT), MonadState (put, get), MonadTrans (lift))
import qualified Frontend.SurfaceSyntax as Surf
import Control.Monad.IO.Class (MonadIO (liftIO))
import Util.PartialOrder (substSingAll)
import Control.Monad (when)
import Test.HUnit
import Data.Bifunctor
import Debug.Trace (trace)

data TckErr t = VarNotFound Var t
            | OutOfOrder Var Var t
            | ReUse Var t
            | ExpectedTyCat Var Ty t
            | ExpectedTyPlus Var Ty t
            | ExpectedTyStar Var Ty t
            | CheckTermInferPos t
            | UnequalReturnTypes Ty Ty t
            | WrongTypeLit Lit Ty
            | WrongTypeEpsR Ty
            | WrongTypeVar Var Ty Ty
            | WrongTypeCatR t t Ty
            | WrongTypeInl t Ty
            | WrongTypeInr t Ty
            | WrongTypeNil Ty
            | WrongTypeCons t t Ty
            | ListedTypeError Ty Ty Core.Term
            | ImpossibleCut Var Core.Term Core.Term
            | UnsaturatedRecursiveCall Int Elab.Term
            | HasTypeErr (Env Var.Var Prefix) (M.Map Var.Var Ty)
            | NonMatchingRecursiveArgs (Ctx Var Ty) (Ctx Var t)

instance PrettyPrint t => PrettyPrint (TckErr t) where
    pp (VarNotFound (Var x) e) = concat ["Variable ",x," not found in term ", pp e]
    pp (OutOfOrder (Var x) (Var y) e) = concat ["Variable ",y," came before ",x," in term ",pp e," but expected the other order."]
    pp (ReUse (Var x) e) = concat ["Variable ",x," was reused in disjoint branches of ", pp e]
    pp (ExpectedTyCat (Var x) t e) = concat ["Variable ",x," expected to be of concatenation type, but it has type ", pp t, " in term ", pp e]
    pp (ExpectedTyPlus (Var x) t e) = concat ["Variable ",x," expected to be of sum type, but it has type ", pp t, " in term ", pp e]
    pp (ExpectedTyStar (Var x) t e)= concat ["Variable ",x," expected to be of star type, but it has type ", pp t, " in term ", pp e]
    pp (CheckTermInferPos e) = concat ["The type of the term ",pp e," cannot be inferred"]
    pp (UnequalReturnTypes t1 t2 e) = concat ["Different types ",pp t1," and ",pp t2," inferred for the branches of the term ", pp e]
    pp (WrongTypeLit l t) = concat ["Literal ", pp l, " does not have type ", pp t]
    pp (WrongTypeEpsR t) = concat ["sink does not have type ", pp t]
    pp (WrongTypeVar (Var x) t s) = concat ["Variable ",x," has type ",pp s," but expected ", pp t]
    pp (WrongTypeCatR e1 e2 t) = concat ["Term (",pp e1,";",pp e2,") has concatenation type, but checking against ", pp t]
    pp (WrongTypeInl e t) = concat ["Term inl(", pp e,") has sum type, but checking against ", pp t]
    pp (WrongTypeInr e t) = concat ["Term inr(", pp e, ") has sum type, but checking against ", pp t]
    pp (WrongTypeNil t) = concat ["nil does not have type ", pp t]
    pp (WrongTypeCons e1 e2 t) = concat ["Term (",pp e1,") :: (",pp e2,") has star type, but checking against ", pp t]
    pp (ImpossibleCut x e1 e2) = concat ["Impossible cut term ", ppCut x e1 e2, " detected. This is a bug -- please tell Joe."]
        where
            ppCut (Var x') e e' = concat ["let ",x',"= (",pp e,") in (",pp e',")"]
    pp (ListedTypeError t' t e) = concat ["Listed type ", pp t'," in term ", pp e, " did not match type ", pp t]
    pp (UnsaturatedRecursiveCall n e) = concat ["Expected ", show n, " argments to recursive call ", pp e]
    pp (HasTypeErr rho m) = concat ["Environment ",pp rho," does not hav expected types ", pp m]
    pp (NonMatchingRecursiveArgs g g') = concat ["Recursive arguments ", pp g', " do not match context ", pp g]

data RecSig = Rec (Ctx Var Ty) Ty

data TckCtx = TckCtx { mp :: M.Map Var.Var Ty, rs :: RecSig, hc :: M.Map Var Ty }

emptyEnvOfType :: TckCtx -> Env Var Prefix
emptyEnvOfType (TckCtx m _ _) = M.foldrWithKey (\x t -> bindEnv x (emptyPrefix t)) emptyEnv m

class (MonadError (TckErr t) m, MonadReader TckCtx m) => TckM t m where

instance TckM t (ReaderT TckCtx (ExceptT (TckErr t) Identity)) where

lookupTy :: (TckM t m) => t -> Var -> m Ty
lookupTy e x = do
    m <- asks mp
    maybe (throwError (VarNotFound x e)) return (M.lookup x m)

lookupTyCat :: (TckM t m) => t -> Var -> m (Ty, Ty)
lookupTyCat e x = do
    s' <- lookupTy e x
    case s' of
        TyCat s t -> return (s,t)
        _ -> throwError (ExpectedTyCat x s' e)

lookupTyPlus :: (TckM t m) => t -> Var -> m (Ty, Ty)
lookupTyPlus e x = do
    s' <- lookupTy e x
    case s' of
        TyPlus s t -> return (s,t)
        _ -> throwError (ExpectedTyPlus x s' e)

lookupTyStar :: (TckM t m) => t -> Var -> m Ty
lookupTyStar e x = do
    s' <- lookupTy e x
    case s' of
        TyStar s -> return s
        _ -> throwError (ExpectedTyStar x s' e)

withUnbind :: (TckM t m) => Var -> m a -> m a
withUnbind x = local (\t -> TckCtx (M.delete x (mp t)) (rs t) (hc t))

withBind :: (TckM t m) => Var -> Ty -> m a -> m a
withBind x s = local (\t -> TckCtx (M.insert x s (mp t)) (rs t) (hc t))

withBindAll :: (TckM t m) => [(Var,Ty)] -> m a -> m a
withBindAll xs = local $ \t -> TckCtx (foldr (\(x,s) -> (M.insert x s .)) id xs (mp t)) (rs t) (hc t)

withRecSig :: (TckM t m) => Ctx Var Ty -> Ty -> m a -> m a
withRecSig g s = local $ \t -> TckCtx (mp t) (Rec g s) (hc t)

withCtxDeriv :: (TckM t m) => Env Var Prefix -> m a -> m a
withCtxDeriv rho m = do
    TckCtx g rs hc <- ask
    g' <- reThrow handleHasTypeErr (deriv rho g)
    local (const (TckCtx g' rs hc)) m

withCtx :: (TckM t m) => M.Map Var Ty -> m a -> m a
withCtx m = local (\(TckCtx _ rs hc) -> TckCtx m rs hc)

withBindHist :: (TckM t m) => Var -> Ty -> m a -> m a
withBindHist x s = local (\t -> TckCtx (mp t) (rs t) (M.insert x s (hc t)))

handleHasTypeErr :: Types.ValueLikeErr (Env Var Prefix) (M.Map Var Ty) -> TckErr t
handleHasTypeErr (IllTyped rho m) = HasTypeErr rho m

guard :: (TckM t m) => Bool -> TckErr t -> m ()
guard b e = if b then return () else throwError e

reThrow :: (TckM t m) => (e -> TckErr t) -> ExceptT e m a -> m a
reThrow k x = runExceptT x >>= either (throwError . k) return

handleOutOfOrder :: t -> (Var,Var) -> TckErr t
handleOutOfOrder e (x,y) = OutOfOrder x y e

handleReUse :: t -> Var -> TckErr t
handleReUse e x = ReUse x e

handleImpossibleCut :: (Var, Core.Term, Core.Term) -> TckErr t
handleImpossibleCut (x,e,e') = ImpossibleCut x e e'

data InferElabResult = IR { ty :: Ty, iusages :: P.Partial Var, itm :: Core.Term }

data CheckElabResult = CR { cusages :: P.Partial Var, ctm :: Core.Term }

promoteResult :: Ty -> CheckElabResult -> InferElabResult
promoteResult t (CR p e) = IR t p e

checkElab :: (TckM Elab.Term m) => Ty -> Elab.Term -> m CheckElabResult
checkElab TyInt (Elab.TmLitR l@(LInt _)) = return $ CR P.empty (Core.TmLitR l)
checkElab TyBool (Elab.TmLitR l@(LBool _)) = return $ CR P.empty (Core.TmLitR l)
checkElab t (Elab.TmLitR l) = throwError (WrongTypeLit l t)
checkElab TyEps Elab.TmEpsR = return $ CR P.empty Core.TmEpsR
checkElab t Elab.TmEpsR = throwError (WrongTypeEpsR t)

checkElab t e@(Elab.TmVar x) = do
    s <- lookupTy e x
    guard (s == t) (WrongTypeVar x t s)
    return $ CR (P.singleton x) (Core.TmVar x)

checkElab r e@(Elab.TmCatL x y z e') = do
    (s,t) <- lookupTyCat e z
    (CR p e'') <- withBindAll [(x,s),(y,t)] $ withUnbind z (checkElab r e')
    -- Ensure that x and y are used in order in e: y cannot be before x.
    guard (not $ P.lessThan p y x) (OutOfOrder x y e')
    -- Replace x and y with z in the output
    p' <- reThrow (handleOutOfOrder e') $ P.substSingAll p [(P.singleton z,x),(P.singleton z,y)]
    return $ CR p' (Core.TmCatL t x y z e'')

checkElab (TyCat s t) (Elab.TmCatR e1 e2) = do
    CR p1 e1' <- checkElab s e1
    CR p2 e2' <- checkElab t e2
    reThrow (handleReUse (Elab.TmCatR e1 e2)) (P.checkDisjoint p1 p2)
    p' <- reThrow (handleOutOfOrder (Elab.TmCatR e1 e2)) $ P.concat p1 p2
    return $ CR p' (Core.TmCatR e1' e2')
checkElab t (Elab.TmCatR e1 e2) = throwError (WrongTypeCatR e1 e2 t)

checkElab (TyPlus s _) (Elab.TmInl e) = do
    CR p e' <- checkElab s e
    return $ CR p (Core.TmInl e')
checkElab t (Elab.TmInl e) = throwError (WrongTypeInl e t)

checkElab (TyPlus _ t) (Elab.TmInr e) = do
    CR p e' <- checkElab t e
    return $ CR p (Core.TmInr e')
checkElab t (Elab.TmInr e) = throwError (WrongTypeInr e t)

checkElab r e@(Elab.TmPlusCase z x e1 y e2) = do
    (s,t) <- lookupTyPlus e z
    CR p1 e1' <- withBind x s $ withUnbind z $ checkElab r e1
    CR p2 e2' <- withBind y t $ withUnbind z $ checkElab r e2
    p' <- reThrow (handleOutOfOrder e) (P.union p1 p2)
    p'' <- reThrow (handleOutOfOrder e) (P.substSingAll p' [(P.singleton z,x),(P.singleton z,y)])
    rho <- asks emptyEnvOfType
    m <- asks mp
    return $ CR p'' (Core.TmPlusCase m rho r z x e1' y e2')

checkElab (TyStar _) Elab.TmNil = return (CR P.empty Core.TmNil)
checkElab t Elab.TmNil = throwError (WrongTypeNil t)

checkElab (TyStar s) (Elab.TmCons e1 e2) = do
    CR p1 e1' <- checkElab s e1
    CR p2 e2' <- checkElab (TyStar s) e2
    reThrow (handleReUse (Elab.TmCons e1 e2)) (P.checkDisjoint p1 p2)
    p' <- reThrow (handleOutOfOrder (Elab.TmCatR e1 e2)) $ P.concat p1 p2
    return $ CR p' (Core.TmCons e1' e2')

checkElab t (Elab.TmCons e1 e2) = throwError (WrongTypeCons e1 e2 t)

checkElab r e@(Elab.TmStarCase z e1 x xs e2) = do
    s <- lookupTyStar e z
    CR p1 e1' <- withUnbind z (checkElab r e1)
    CR p2 e2' <- withBindAll [(x,s),(xs,TyStar s)] $ withUnbind z (checkElab r e2)
    guard (not $ P.lessThan p2 xs x) (OutOfOrder x xs e2)
    p' <- reThrow (handleOutOfOrder e) $ P.union p1 p2
    p'' <- reThrow (handleOutOfOrder e) (P.substSingAll p' [(P.singleton z,x),(P.singleton z,xs)])
    rho <- asks emptyEnvOfType
    m <- asks mp
    return $ CR p'' (Core.TmStarCase m rho r s z e1' x xs e2')

checkElab r (Elab.TmCut x e1 e2) = do
    IR s p e1' <- inferElab e1
    CR p' e2' <- withBind x s $ checkElab r e2
    reThrow (handleReUse (Elab.TmCatR e1 e2)) (P.checkDisjoint p p')
    p'' <- reThrow (handleOutOfOrder (Elab.TmCut x e1 e2)) $ P.substSing p' p x
    e' <- reThrow handleImpossibleCut (Core.cut x e1' e2')
    return (CR p'' e')

checkElab r e@(Elab.TmRec es) = do
    Rec g r' <- asks rs
    when (r /= r') $ throwError (UnequalReturnTypes r r' e) -- ensure the return type is the proper one
    let g_assoc = ctxAssoc g
    when (length g_assoc /= length es) $ throwError (UnsaturatedRecursiveCall (length g_assoc) e) -- ensure we have the right number of arguments
    es' <- mapM inferElab es -- infer all the arguments
    (_,(p,args)) <- elabRec g es'
    return (CR p (Core.TmRec args))

checkElab r e@(Elab.TmWait x e') = do
    rho <- asks emptyEnvOfType
    s <- lookupTy e x
    CR p e'' <- withBindHist x s $ withUnbind x $ checkElab r e'
    return (CR p (Core.TmWait rho r x e''))

checkElab r e@(Elab.TmHistPgm he) = undefined

-- Given a context and a list of inferred terms, return the "context" mapping variables to terms.
elabRec :: (TckM Elab.Term m) => Ctx Var Ty -> [InferElabResult] -> m ([InferElabResult],(P.Partial Var,Ctx Var Core.Term))
elabRec EmpCtx [] = return ([],(P.empty,EmpCtx))
elabRec EmpCtx _ = error "impossible"
elabRec (SngCtx x s) (IR s' p e : es) = do
    when (s /= s') $ throwError (error "HERE!!")
    return (es,(p,SngCtx x e))
elabRec (SngCtx {}) _ = error "impossible"
elabRec (SemicCtx g1 g2) es = do
    (es',(p,g1')) <- elabRec g1 es
    (es'',(p',g2')) <- elabRec g2 es'
    reThrow (error "asdf") (P.checkDisjoint p p')
    p'' <- reThrow (handleOutOfOrder (error "Arguments use variables inconsistently")) $ P.concat p p'
    return (es'',(p'',SemicCtx g1' g2'))


inferElab :: (TckM Elab.Term m) => Elab.Term -> m InferElabResult
inferElab (Elab.TmLitR (LInt n)) = return $ IR TyInt P.empty (Core.TmLitR (LInt n))
inferElab (Elab.TmLitR (LBool b)) = return $ IR TyBool P.empty (Core.TmLitR (LBool b))
inferElab Elab.TmEpsR = return $ IR TyEps P.empty Core.TmEpsR

inferElab e@(Elab.TmVar x) = do
    s <- lookupTy e x
    return $ IR s (P.singleton x) (Core.TmVar x)

inferElab e@(Elab.TmCatL x y z e') = do
    -- Find the type for x and y
    (s,t) <- lookupTyCat e z
    -- Bind x:s,y:t, unbind z, and recursively check 
    (IR r p e'') <- withBindAll [(x,s),(y,t)] $ withUnbind z (inferElab e')
    -- Ensure that x and y are used in order in e: y cannot be before x.
    guard (not $ P.lessThan p y x) (OutOfOrder x y e')
    -- Replace x and y with z in the output
    p' <- reThrow (handleOutOfOrder e') $ P.substSingAll p [(P.singleton z,x),(P.singleton z,y)]
    return $ IR r p' (Core.TmCatL t x y z e'')

inferElab e@(Elab.TmCatR e1 e2) = do
    IR s p1 e1' <- inferElab e1
    IR t p2 e2' <- inferElab e2
    p' <- reThrow (handleOutOfOrder e) $ P.concat p1 p2
    reThrow (handleReUse e) (P.checkDisjoint p1 p2)
    return $ IR (TyCat s t) p' (Core.TmCatR e1' e2')

inferElab e@(Elab.TmInl {}) = throwError (CheckTermInferPos e)
inferElab e@(Elab.TmInr {}) = throwError (CheckTermInferPos e)

inferElab e@(Elab.TmPlusCase z x e1 y e2) = do
    (s,t) <- lookupTyPlus e z
    IR r1 p1 e1' <- withBind x s $ withUnbind z $ inferElab e1
    IR r2 p2 e2' <- withBind y t $ withUnbind z $ inferElab e2
    guard (r1 == r2) (UnequalReturnTypes r1 r2 e)
    p' <- reThrow (handleOutOfOrder e) $ P.union p1 p2
    rho <- asks emptyEnvOfType
    m <- asks mp
    return $ IR r1 p' (Core.TmPlusCase m rho r1 z x e1' y e2')

inferElab e@Elab.TmNil = throwError (CheckTermInferPos e)

inferElab e@(Elab.TmCons e1 e2) = do
    IR s p1 e1' <- inferElab e1
    CR p2 e2' <- checkElab (TyStar s) e2
    reThrow (handleReUse e) (P.checkDisjoint p1 p2)
    p' <- reThrow (handleOutOfOrder e) $ P.concat p1 p2
    return $ IR (TyStar s) p' (Core.TmCons e1' e2')

inferElab e@(Elab.TmStarCase z e1 x xs e2) = do
    s <- lookupTyStar e z
    IR r1 p1 e1' <- withUnbind z $ inferElab e1
    IR r2 p2 e2' <- withBindAll [(x,s),(xs,TyStar s)] $ withUnbind z $ inferElab e2
    guard (r1 == r2) (UnequalReturnTypes r1 r2 e)
    p' <- reThrow (handleOutOfOrder e) $ P.union p1 p2
    rho <- asks emptyEnvOfType
    m <- asks mp
    return $ IR r1 p' (Core.TmStarCase m rho r1 s z e1' x xs e2')

inferElab e@(Elab.TmCut x e1 e2) = do
    IR s p e1' <- inferElab e1
    IR t p' e2' <- withBind x s $ inferElab e2
    reThrow (handleReUse e) (P.checkDisjoint p p')
    p'' <- reThrow (handleOutOfOrder (Elab.TmCut x e1 e2)) $ P.substSing p' p x
    e' <- reThrow handleImpossibleCut (Core.cut x e1' e2')
    return (IR t p'' e')

inferElab e@(Elab.TmRec es) = do
    Rec g r <- asks rs
    let g_assoc = ctxAssoc g
    when (length g_assoc /= length es) $ throwError (UnsaturatedRecursiveCall (length g_assoc) e) -- ensure we have the right number of arguments
    es' <- mapM inferElab es -- infer all the arguments
    (_,(p,args)) <- elabRec g es'
    return (IR r p (Core.TmRec args))

inferElab e@(Elab.TmWait x e') = do
    rho <- asks emptyEnvOfType
    s <- lookupTy e x
    IR t p e'' <- withBindHist x s $ withUnbind x $ inferElab e'
    return (IR t p (Core.TmWait rho t x e''))

inferElab e@(Elab.TmHistPgm he) = undefined


checkCore :: (TckM Core.Term m) => Ty -> Core.Term -> m (P.Partial Var.Var)
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
    m <- asks mp
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

checkCore (TyPlus s _) (Core.TmInl e) = checkCore s e
checkCore t (Core.TmInl e) = throwError (WrongTypeInl e t)

checkCore (TyPlus _ t) (Core.TmInr e) = checkCore t e
checkCore t (Core.TmInr e) = throwError (WrongTypeInr e t)

checkCore r e@(Core.TmPlusCase m rho r' z x e1 y e2) = do
    !() <- trace ("Here :" ++ pp m ++ ", " ++ pp z) (return ())
    reThrow handleHasTypeErr (hasType rho m)
    !() <- trace ("Here :" ++ pp m ++ ", " ++ pp z) (return ())
    withCtx m $ do
        (s,t) <- lookupTyPlus e z
        guard (r == r') (ListedTypeError r' r e)
        p1 <- withBind x s $ withUnbind z $ checkCore r e1
        p2 <- withBind y t $ withUnbind z $ checkCore r e2
        p' <- reThrow (handleOutOfOrder e) (P.union p1 p2)
        reThrow (handleOutOfOrder e) (P.substSingAll p' [(P.singleton z,x),(P.singleton z,y)])

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

-- NOTE: this just checks that we have all the binders we expect for the term, not that they arrive in the right order!
checkCore r e@(Core.TmRec args) = do
    TckCtx g_bound (Rec g r') _ <- ask
    guard (r == r') (UnequalReturnTypes r r' e) --return types are the same
    checkRec g args

checkCore r e@(Core.TmFix args g s e') = do
    p <- checkRec g args
    p' <- withRecSig g s (checkCore r e')
    reThrow (handleOutOfOrder e) (P.consistentWith p' (ctxVars g))
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

checkCore r e@(Core.TmHistPgm s he) = undefined


inferCore :: (TckM Core.Term m) => Core.Term -> m (Ty,P.Partial Var.Var)
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
    p'' <- reThrow (handleOutOfOrder (Core.TmCatR e1 e2)) $ P.concat p1 p2
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
    TckCtx _ (Rec g r) _ <- ask
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

inferCore e@(Core.TmHistPgm s he) = undefined

checkRec :: (TckM Core.Term m) => Ctx Var Ty -> Ctx Var Core.Term -> m (P.Partial Var)
checkRec g g' = go g g'
    where
        go EmpCtx EmpCtx = return P.empty
        go (SngCtx x t) (SngCtx y e) | x == y = checkCore t e
        go (SemicCtx g1 g2) (SemicCtx g1' g2') = do
            p1 <- go g1 g1'
            p2 <- go g2 g2'
            reThrow (handleReUse (error "ahhhh")) (P.checkDisjoint p1 p2)
            reThrow (handleOutOfOrder (error "eek")) (P.concat p1 p2)
        go _ _ = throwError (NonMatchingRecursiveArgs g g')

data PrefixCheckErr = WrongType Ty Surf.UntypedPrefix | OrderIssue Prefix Prefix | NotDisjointCtx Var Prefix Prefix | OrderIssueCtx (Env Var Prefix) (Env Var Prefix) | IllegalStp Prefix deriving (Eq, Ord, Show)

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

checkUntypedPrefix (TyPlus s _) (Surf.SumPA p) = do
    p' <- checkUntypedPrefix s p
    return (SumPA p')
checkUntypedPrefix (TyPlus _ t) (Surf.SumPB p) = do
    p' <- checkUntypedPrefix t p
    return (SumPB p')
checkUntypedPrefix t@(TyPlus {}) p = throwError $ WrongType t p

checkUntypedPrefix (TyStar s) (Surf.Stp ps) = checkUntypedStp s ps
checkUntypedPrefix t@(TyStar _) p = throwError $ WrongType t p

checkUntypedStp :: (Monad m) => Ty -> [Surf.UntypedPrefix] -> ExceptT PrefixCheckErr m Prefix
checkUntypedStp _ [] = return StpDone
checkUntypedStp s (p:ps) = do
    p' <- checkUntypedPrefix s p
    if isMaximal p' then do
        p'' <- checkUntypedStp s ps
        return (StpB p' p'')
    else if null ps then return (StpA p')
    else throwError (IllegalStp p')

checkUntypedPrefixCtx :: (Monad m) => Ctx Var Ty -> M.Map Var Surf.UntypedPrefix -> ExceptT PrefixCheckErr m (Env Var Prefix)
checkUntypedPrefixCtx EmpCtx _ = return emptyEnv
checkUntypedPrefixCtx (SngCtx x s) m = do
    p' <- maybe (return (emptyPrefix s)) (checkUntypedPrefix s) (M.lookup x m)
    return (bindEnv x p' emptyEnv)
checkUntypedPrefixCtx (SemicCtx g g') m = do
    rho <- checkUntypedPrefixCtx g m
    rho' <- checkUntypedPrefixCtx g' m
    if allEnv isMaximal rho || allEnv isEmpty rho' then
        runExceptT (unionDisjointEnv rho rho') >>= either (\(v,p,p') -> throwError (NotDisjointCtx v p p')) return
    else throwError (OrderIssueCtx rho rho')

type FileInfo = M.Map String (Ctx Var Ty, Ty)

-- Doublecheck argument typechecks the resulting term, again.
doCheckElabTm :: (MonadIO m) => Bool -> Ctx Var Ty -> Ty -> Elab.Term -> m Core.Term
doCheckElabTm doubleCheck g t e = do
    let ck = runIdentity $ runExceptT $ runReaderT (checkElab t e :: (ReaderT TckCtx (ExceptT (TckErr Elab.Term) Identity) CheckElabResult)) (TckCtx (ctxBindings g) (Rec g t) M.empty)
    case ck of
        Left err -> error (pp err)
        Right (CR usages tm) -> do
            usageConsist <- runExceptT (P.consistentWith usages (ctxVars g))
            let tm' = Core.TmFix (ctxMap (\x _ -> (x,Core.TmVar x)) g) g t tm -- put the ``fix'' on the outside, just pass the inputs along.
            case usageConsist of
                Left (x,y) -> error $ pp $ OutOfOrder x y e
                Right _ -> if doubleCheck then doCheckCoreTm g t tm' >> return tm' else return tm'

doCheckCoreTm :: (MonadIO m) => Ctx Var Ty -> Ty -> Core.Term -> m ()
doCheckCoreTm g t e = do
    let ck = runIdentity $ runExceptT $ runReaderT (checkCore t e :: (ReaderT TckCtx (ExceptT (TckErr Core.Term) Identity) (P.Partial Var))) (TckCtx (ctxBindings g) (Rec g t) M.empty)
    case ck of
        Left err -> error ("ERROR: " ++ pp err ++ " while checking " ++ pp e ++ " against type " ++ pp t ++ " in context " ++ pp g)
        Right usages -> do
            usageConsist <- runExceptT (P.consistentWith usages (ctxVars g))
            case usageConsist of
                Left (x,y) -> error $ pp $ OutOfOrder x y e
                Right _ -> return ()

doCheckElabPgm :: (MonadIO m) => Elab.Program -> m Core.Program
doCheckElabPgm xs = fst <$> runStateT (mapM go xs) M.empty
    where
        go :: (MonadIO m) => Either Elab.FunDef Elab.RunCmd -> StateT FileInfo m (Either Core.FunDef Core.RunCmd)
        go (Left (Elab.FD f g t e)) = do
            e' <- lift $ doCheckElabTm False g t e
            liftIO $ putStrLn $ "Function " ++ f ++ " typechecked OK. Core term: " ++ pp e'
            fi <- get
            put (M.insert f (g,t) fi)
            return (Left (Core.FD f g t e'))
        go (Right (Elab.RC f p)) = do
            fi <- get -- Get the current file information
            case M.lookup f fi of
                Nothing -> error ""
                Just (g,_) -> do
                    mps <- lift (runExceptT (checkUntypedPrefixCtx g p))
                    case mps of
                        Left err -> error (show err)
                        Right ps -> return (Right (Core.RC f ps))

tckTests = TestList []