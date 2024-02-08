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
import Types (Ctx, CtxStruct(..), TyF(..), Ty, ctxBindings, ctxVars, emptyPrefix, ctxAssoc, deriv, ValueLikeErr (IllTyped), ValueLike (hasType), ctxMap, CtxEntry (..), OpenTy, reparameterizeCtx, reparameterizeTy, isNull)
import Control.Monad.Reader (MonadReader (ask, local), asks, ReaderT (runReaderT), withReaderT)
import Var (Var (Var), TyVar, FunVar)
import Values (Lit(..), Env, Prefix (..), emptyEnv, bindEnv, isMaximal, isEmpty, allEnv, unionDisjointEnv, singletonEnv)
import qualified Data.Map as M
import qualified Util.PartialOrder as P
import Control.Monad.Identity (Identity (runIdentity))
import Util.PrettyPrint (PrettyPrint,pp)
import Control.Monad.State.Strict (StateT(runStateT), MonadState (put, get), MonadTrans (lift), gets, modify, modify')
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
import Backend.Template
import Control.Monad (unless)
import Data.List (intercalate)
import Buffer
import CoreSyntax
import GHC.IO (unsafePerformIO)

data TckErr t = VarNotFound Var t
            | OutOfOrder Var Var t
            | AntiSym Var Var t
            | SomeOrder Var Var t
            | ReUse Var t
            | ContUse Var t
            | ExpectedTyCat Var OpenTy t
            | ExpectedTyPar Var OpenTy t
            | ExpectedTyPlus Var OpenTy t
            | ExpectedTyStar Var OpenTy t
            | ExpectedTyBool Var OpenTy t
            | CheckTermInferPos t
            | UnequalReturnTypes OpenTy OpenTy t
            | WrongTypeLit Lit OpenTy
            | WrongTypeEpsR OpenTy
            | WrongTypeVar Var OpenTy OpenTy
            | WrongTypeCatR t t OpenTy
            | WrongTypeParR t t OpenTy
            | WrongTypeInl t OpenTy
            | WrongTypeInr t OpenTy
            | WrongTypeNil OpenTy
            | WrongTypeCons t t OpenTy
            | ListedTypeError Ty Ty t
            | ImpossibleCut Var t t
            | UnsaturatedRecursiveCall (CtxStruct OpenTy) (CtxStruct t)
            | HasTypeErr (Env Var.Var Prefix) (M.Map Var.Var OpenTy)
            | NonMatchingRecursiveArgs (Ctx Var OpenTy) (CtxStruct t)
            | HistTckErr t Hist.TckErr
            | FunRecordNotFound Var.FunVar
            | FunArgNotFound Var.FunVar
            | NonInertCut Var.Var t t

instance (PrettyPrint t) => PrettyPrint (TckErr t) where
    pp (VarNotFound x e) = concat ["Variable ",pp x," not found while checking term ", pp e]
    pp (AntiSym x y e) = concat ["Variables ", pp x," and ",pp y," used in both orders in ",pp e,"."]
    pp (OutOfOrder x y e) = concat ["Variable ", pp y," came before ",pp x," in term ",pp e," but expected the other order."]
    pp (SomeOrder (Var x) (Var y) e) = concat ["Variables ",x," and ",y," used in some order in term ",pp e," but expected them to be used in parallel."]
    pp (ReUse (Var x) e) = concat ["Variable ",x," was reused in disjoint branches of ", pp e]
    pp (ContUse x e) = concat ["Variable ",pp x," was destructed and then re-used in the continuation of ", pp e]
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
    pp (FunRecordNotFound f) = concat ["Could not find (toplevel-bound) function ", pp f]
    pp (FunArgNotFound f) = concat ["Could not find (arg-bound) function ", pp f]
    pp (NonInertCut x e e') = concat ["Let-binding ", pp "let ", pp x, " = ", pp e, " in ... is disallowed, because scrutinee is not inert." ]

data Inertness = Inert | Jumpy deriving (Eq,Show)

instance Ord Inertness where
    Inert <= _ = True
    Jumpy <= Jumpy = True
    Jumpy <= Inert = False

data RecSig = Rec (Ctx Var OpenTy) OpenTy Inertness

data FunMacRecord buf =
      PolyFun { funTyVars :: [Var.TyVar], funCtx :: Ctx Var OpenTy, funTy :: OpenTy, funInert :: Inertness, funMonoTerm :: Template (Core.Term buf) (Core.Term buf) } -- shoud really be void second param, but whatever.
    | PolyMac { macTyVars :: [Var.TyVar], macCtx :: Ctx Var OpenTy, macTy :: OpenTy, macParam :: MacroParam buf, macInert :: Inertness, macMonoTerm :: Template (Core.Term buf) (Core.Term buf) }
    | SpecFun { specCtx :: Ctx Var Ty }

type FileInfo buf = M.Map Var.FunVar (FunMacRecord buf)

data TckCtx buf = TckCtx
    { fileInfo :: FileInfo buf,
      argsTypes :: M.Map Var.Var OpenTy,
      rs :: RecSig ,
      histCtx :: M.Map Var OpenTy,
      tyVars :: S.Set Var.TyVar,
      curMacParam :: Maybe (Surf.MacroParam) -- the macro parameter, if we're typing a macro.
    --   funArgsTypes :: M.Map Var.FunVar (CtxStruct OpenTy,OpenTy)
    }


class (MonadError (TckErr t) m, MonadReader (TckCtx buf) m) => TckM t buf m where
instance TckM t buf (ReaderT (TckCtx buf) (ExceptT (TckErr t) Identity)) where

lookupTy :: (TckM t buf m) => t -> Var -> m OpenTy
lookupTy e x = do
    m <- asks argsTypes
    maybe (throwError (VarNotFound x e)) return (M.lookup x m)

lookupTyBool :: (TckM t buf m) => t -> Var -> m ()
lookupTyBool e x = do
    s <- lookupTy e x
    case s of
        TyBool -> return ()
        _ -> trace ("TYPE IS: ") $ throwError (ExpectedTyBool x s e)

lookupTyCat :: (TckM t buf m) => t -> Var -> m (OpenTy, OpenTy)
lookupTyCat e x = do
    s' <- lookupTy e x
    case s' of
        TyCat s t -> return (s,t)
        _ -> throwError (ExpectedTyCat x s' e)

lookupTyPar :: (TckM t buf m) => t -> Var -> m (OpenTy, OpenTy)
lookupTyPar e x = do
    s' <- lookupTy e x
    case s' of
        TyPar s t -> return (s,t)
        _ -> throwError (ExpectedTyPar x s' e)

lookupTyPlus :: (TckM t buf m) => t -> Var -> m (OpenTy, OpenTy)
lookupTyPlus e x = do
    s' <- lookupTy e x
    case s' of
        TyPlus s t -> return (s,t)
        _ -> throwError (ExpectedTyPlus x s' e)

lookupTyStar :: (TckM t buf m) => t -> Var -> m OpenTy
lookupTyStar e x = do
    s' <- lookupTy e x
    case s' of
        TyStar s -> return s
        _ -> throwError (ExpectedTyStar x s' e)

-- Don't tell me to use lens, i refuse.
lookupFunMacRecord :: (TckM t buf m) => Var.FunVar -> m (FunMacRecord buf)
lookupFunMacRecord f = do
    asks (M.lookup f . fileInfo) >>= maybe (throwError (FunRecordNotFound f)) return

-- lookupFunArg :: (TckM t buf m) => Var.FunVar -> m (CtxStruct OpenTy, OpenTy)
-- lookupFunArg f = do
--     asks (M.lookup f . funArgsTypes) >>= maybe (throwError (FunArgNotFound f)) return


withUnbind :: (TckM t buf m) => Var -> m a -> m a
withUnbind x = local (\t -> TckCtx (fileInfo t) (M.delete  x (argsTypes t)) (rs t) (histCtx t) (tyVars t) (curMacParam t) {-(funArgsTypes t)-})

withBind :: (TckM t buf m) => Var -> OpenTy -> m a -> m a
withBind x s = local (\t -> TckCtx (fileInfo t) (M.insert x s (argsTypes t)) (rs t) (histCtx t) (tyVars t) (curMacParam t) {-(funArgsTypes t)-})

withBindAll :: (TckM t buf m) => [(Var,OpenTy)] -> m a -> m a
withBindAll xs = local $ \t -> TckCtx (fileInfo t) (foldr (\(x,s) -> (M.insert x s .)) id xs (argsTypes t)) (rs t) (histCtx t) (tyVars t) (curMacParam t) {-(funArgsTypes t)-}

withUnbindAll :: (TckM t buf m) => [Var] -> m a -> m a
withUnbindAll xs = local (\t -> TckCtx (fileInfo t) (foldr M.delete (argsTypes t) xs) (rs t) (histCtx t) (tyVars t) (curMacParam t){-(funArgsTypes t)-})

withRecSig :: (TckM t buf m) => Ctx Var OpenTy -> OpenTy -> Inertness -> m a -> m a
withRecSig g s i = local $ \t -> TckCtx (fileInfo t) (argsTypes t) (Rec g s i) (histCtx t) (tyVars t) (curMacParam t) {-(funArgsTypes t)-}

withCtx :: (TckM t buf m) => M.Map Var OpenTy -> m a -> m a
withCtx m = local (\(TckCtx fi _ rs hc tv mp) -> TckCtx fi m rs hc tv mp)

withBindHist :: (TckM t buf m) => Var -> OpenTy -> m a -> m a
withBindHist x s = local (\t -> TckCtx (fileInfo t) (argsTypes t) (rs t) (M.insert x s (histCtx t)) (tyVars t) (curMacParam t){-(funArgsTypes t)-})

handleHasTypeErr :: Types.ValueLikeErr (Env Var Prefix) (M.Map Var OpenTy) -> TckErr t
handleHasTypeErr (IllTyped rho m) = HasTypeErr rho m

guard :: (TckM t buf m) => Bool -> TckErr t -> m ()
guard b e = if b then return () else throwError e

reThrow :: (TckM t buf m) => (e -> TckErr t) -> ExceptT e m a -> m a
reThrow k x = runExceptT x >>= either (throwError . k) return

handleOrderErr :: t -> P.OrderErr Var -> TckErr t
handleOrderErr e (P.OutOfOrder x y) = OutOfOrder x y e
handleOrderErr e (P.SomeOrder x y) = SomeOrder x y e
handleOrderErr e (P.AntiSym x y) = AntiSym x y e

handleReUse :: t -> Var -> TckErr t
handleReUse e x = ReUse x e

handleContUse :: t -> Var -> TckErr t
handleContUse e x = ContUse x e

handleImpossibleCut :: (Var, t, t) -> TckErr t
handleImpossibleCut (x,e,e') = ImpossibleCut x e e'

handleReparErr :: Var.TyVar -> TckErr t
handleReparErr = undefined

data InferElabResult buf = IR { ty :: OpenTy , iusages :: P.Partial Var, iinertness :: Inertness, itm :: Template (Core.Term buf) (Core.Term buf )}
data CheckElabResult buf = CR { cusages :: P.Partial Var, cinertness :: Inertness, ctm :: Template (Core.Term buf) (Core.Term buf) }

promoteResult :: OpenTy -> CheckElabResult buf -> InferElabResult buf
promoteResult t (CR p e i) = IR t p e i

liftHistCheck :: (TckM t buf m') => t -> ReaderT (M.Map Var OpenTy) (ExceptT Hist.TckErr Identity) a -> m' a
liftHistCheck e m = do
    ma <- asks ((runIdentity . runExceptT . runReaderT m) . histCtx)
    case ma of
        Left err -> throwError (HistTckErr e err)
        Right a -> return a

dropVarsCtx :: Ctx v t -> CtxStruct t
dropVarsCtx = ((\(CE _ t) -> t) <$>)

checkElab :: (Buffer buf, TckM Elab.Term buf m) => OpenTy -> Elab.Term -> m (CheckElabResult buf)
checkElab TyInt (Elab.TmLitR l@(LInt _)) = return $ CR P.empty Jumpy (return (Core.TmLitR l))
checkElab TyBool (Elab.TmLitR l@(LBool _)) = return $ CR P.empty Jumpy (return (Core.TmLitR l))
checkElab t (Elab.TmLitR l) = throwError (WrongTypeLit l t)
checkElab TyEps Elab.TmEpsR = return $ CR P.empty Inert (return Core.TmEpsR)
checkElab t Elab.TmEpsR = throwError (WrongTypeEpsR t)

checkElab t e@(Elab.TmVar x) = do
    s <- lookupTy e x
    guard (s == t) (WrongTypeVar x t s)
    return $ CR (P.singleton x) Inert (return (Core.TmVar x))

checkElab r e@(Elab.TmCatL x y z e') = do
    (s,t) <- lookupTyCat e z
    (CR p i e'') <- withBindAll [(x,s),(y,t)] (checkElab r e')
    -- Ensure that x and y are used in order in e: y cannot be before x.
    guard (not $ P.lessThan p y x) (OutOfOrder x y e')
    -- Replace x and y with z in the output
    p' <- reThrow (handleOrderErr e') $ P.substSingAll p [(P.singleton z,x),(P.singleton z,y)]
    return $ CR p' i $ do
        t' <- monomorphizeTy t
        Core.TmCatL t' x y z <$> e''

checkElab (TyCat s t) (Elab.TmCatR e1 e2) = do
    CR p1 i e1' <- checkElab s e1
    CR p2 _ e2' <- checkElab t e2
    reThrow (handleReUse (Elab.TmCatR e1 e2)) (P.checkDisjoint p1 p2)
    p' <- reThrow (handleOrderErr (Elab.TmCatR e1 e2)) $ P.concat p1 p2
    let i' = if i == Inert && not (isNull s) then Inert else Jumpy
    return $ CR p' i' (Core.TmCatR <$> monomorphizeTy s <*> e1' <*> e2')
checkElab t (Elab.TmCatR e1 e2) = throwError (WrongTypeCatR e1 e2 t)

checkElab r e@(Elab.TmParL x y z e') = do
    (s,t) <- lookupTyPar e z
    (CR p i e'') <- withBindAll [(x,s),(y,t)] (checkElab r e')
    reThrow (handleContUse e) (P.checkNotIn z p)
    when (P.comparable p y x) (throwError (SomeOrder x y e'))
    p' <- reThrow (handleOrderErr e') $ P.substSingAll p [(P.singleton z,x),(P.singleton z,y)]
    return $ CR p' i (Core.TmParL x y z <$> e'')

checkElab (TyPar s t) e@(Elab.TmParR e1 e2) = do
    CR p1 i1 e1' <- checkElab s e1
    CR p2 i2 e2' <- checkElab t e2
    p' <- reThrow (handleOrderErr e) $ P.union p1 p2
    let i = if i1 == Inert && i2 == Inert then Inert else Jumpy
    return $ CR p' i (Core.TmParR <$> e1' <*> e2')
checkElab t (Elab.TmParR e1 e2) = throwError (WrongTypeParR e1 e2 t)

checkElab (TyPlus s _) (Elab.TmInl e) = do
    CR p _ e' <- checkElab s e
    return $ CR p Jumpy (Core.TmInl <$> e')
checkElab t (Elab.TmInl e) = throwError (WrongTypeInl e t)

checkElab (TyPlus _ t) (Elab.TmInr e) = do
    CR p _ e' <- checkElab t e
    return $ CR p Jumpy (Core.TmInr <$> e')
checkElab t (Elab.TmInr e) = throwError (WrongTypeInr e t)

checkElab r e@(Elab.TmPlusCase z x e1 y e2) = do
    (s,t) <- lookupTyPlus e z
    CR p1 _ e1' <- withBind x s (checkElab r e1)
    CR p2 _ e2' <- withBind y t (checkElab r e2)
    reThrow (handleContUse e1) (P.checkNotIn z p1)
    reThrow (handleContUse e2) (P.checkNotIn z p2)
    p' <- reThrow (handleOrderErr e) (P.union p1 p2)
    p'' <- reThrow (handleOrderErr e) (P.substSingAll p' [(P.singleton z,x),(P.singleton z,y)])
    m_rho <- asks (emptyBufOfType . argsTypes)
    return $ CR p'' Inert $ do
        r' <- monomorphizeTy r
        me1' <- e1'
        me2' <- e2'
        rho <- m_rho
        return (Core.TmPlusCase rho r' z x me1' y me2')

checkElab r e@(Elab.TmIte m e1 e2) = do
    () <- liftHistCheck e (Hist.check m TyBool)
    CR p1 _ e1' <- checkElab r e1
    CR p2 _ e2' <- checkElab r e2
    p' <- reThrow (handleOrderErr e) (P.union p1 p2)
    return $ CR p' Inert $ do
        Core.TmIte m <$> e1' <*> e2'


checkElab (TyStar _) Elab.TmNil = return (CR P.empty Jumpy (return Core.TmNil))
checkElab t Elab.TmNil = throwError (WrongTypeNil t)

checkElab (TyStar s) (Elab.TmCons e1 e2) = do
    CR p1 i e1' <- checkElab s e1
    CR p2 _ e2' <- checkElab (TyStar s) e2
    reThrow (handleReUse (Elab.TmCons e1 e2)) (P.checkDisjoint p1 p2)
    p' <- reThrow (handleOrderErr (Elab.TmCatR e1 e2)) $ P.concat p1 p2
    let i' = if i == Inert && not (isNull s) then Inert else Jumpy
    return $ CR p' i' (Core.TmCons <$> monomorphizeTy s <*> e1' <*> e2')

checkElab t (Elab.TmCons e1 e2) = throwError (WrongTypeCons e1 e2 t)

checkElab r e@(Elab.TmStarCase z e1 x xs e2) = do
    s <- lookupTyStar e z
    CR p1 _ e1' <- checkElab r e1
    CR p2 _ e2' <- withBindAll [(x,s),(xs,TyStar s)] $ checkElab r e2
    guard (not $ P.lessThan p2 xs x) (OutOfOrder x xs e2)
    reThrow (handleContUse e) (P.checkNotIn z p1)
    reThrow (handleContUse e) (P.checkNotIn z p2)
    p' <- reThrow (handleOrderErr e) $ P.union p1 p2
    p'' <- reThrow (handleOrderErr e) (P.substSingAll p' [(P.singleton z,x),(P.singleton z,xs)])
    m_rho <- asks (emptyBufOfType . argsTypes)
    return $ CR p'' Inert $ do
        s' <- monomorphizeTy s
        r' <- monomorphizeTy r
        me1' <- e1'
        me2' <- e2'
        rho <- m_rho
        return (Core.TmStarCase rho r' s' z me1' x xs me2')

checkElab r e@(Elab.TmCut x e1 e2) = do
    IR s p i be1 <- inferElab e1
    guard (i == Inert) (NonInertCut x e1 e2)
    CR p' i' be2 <- withBind x s (checkElab r e2)
    reThrow (handleReUse e) (P.checkDisjoint p p')
    p'' <- reThrow (handleOrderErr (Elab.TmCut x e1 e2)) $ P.substSing p' p x
    return (CR p'' i' (Core.TmCut x <$> be1 <*> be2))

checkElab r e@(Elab.TmRec es) = do
    Rec g r' i <- asks rs
    when (r /= r') $ throwError (UnequalReturnTypes r r' e) -- ensure the return type is the proper one
    (p,args) <- elabRec (dropVarsCtx g) es
    return (CR p i (Core.TmRec <$> args))

checkElab r e@(Elab.TmWait x e') = do
    m_rho <- asks (emptyBufOfType . argsTypes)
    s <- lookupTy e x
    CR p _ e'' <- withBindHist x s (checkElab r e')
    reThrow (handleContUse e) (P.checkNotIn x p)
    let i = if not (isNull s) then Inert else Jumpy
    return $ CR (P.insert p x x) i $ do
        rho <- m_rho
        r' <- monomorphizeTy r
        s' <- monomorphizeTy s
        Core.TmWait rho r' s' x <$> e''


checkElab r e@(Elab.TmHistPgm he) = do
    () <- liftHistCheck e (Hist.check he r)
    return $ CR P.empty Jumpy $ do
        r' <- monomorphizeTy r
        return (Core.TmHistPgm r' he)

checkElab r e@(Elab.TmFunCall f ts {-fs-} es) = do
    fr <- lookupFunMacRecord f
    case fr of
        PolyFun {funTyVars = tvs, funCtx = g, funTy = r', funMonoTerm = me, funInert = i} -> do
            when (length ts /= length tvs) $ error "Unsaturated type args for function call" -- not saturated type arguments for recursive call.
            let repar_map = foldr (uncurry M.insert) M.empty (zip tvs ts)
            -- compute g'', r'': the  context and return types, after applying the type substitution (tvs |-> ts)
            g' <- reThrow handleReparErr (reparameterizeCtx repar_map g)
            r'' <- reThrow handleReparErr (reparameterizeTy repar_map r')
            when (r /= r'') $ throwError (UnequalReturnTypes r r'' e) -- ensure the return type is the proper one
            (p,margs) <- elabRec (dropVarsCtx g') es
            return $ CR p i $ do
                g_mono <- monomorphizeCtx g'
                r_mono <- monomorphizeTy r''
                args <- margs
                e <- reparameterizeTemplate repar_map me
                case e of
                    Core.TmFix _ _ _ e' -> return (Core.TmFix args g_mono r_mono e')
                    _ -> error "Top level definition isn't a fix"
        _ -> error "..."

-- TODO:JWC fix inertness analysis here.
checkElab s' (Elab.TmMacroParamUse f' args) = do
    mmp <- asks curMacParam -- TODO:JWC do the typechecking here. probably want to make sure f and f' are the same.
    case mmp of
        Just (Surf.MP f g s) ->  do
            (p,margs) <- elabRec g args
            when (s /= s') $ error "Expected macro parameter to return, one thing, its signature got the other."
            return $ CR p Inert $ do
                args <- margs
                me <- getMacParamReplacement
                case me of
                    Nothing -> error "uh oh, no replacement."
                    Just (Core.TmFix _ g t e) -> return (Core.TmFix args g t e)
                    _ -> error "replacement is not a term with top level fix..."
        _ -> error "Typechecking a place where a macro parameter use occurs"

checkElab t (Elab.TmMacroUse macName ts f args) = do
    let !() = unsafePerformIO (print $ "HEre!! calling" ++ pp macName)
    let !() = unsafePerformIO (print $ "with fun arg " ++ pp f)
    let !() = unsafePerformIO (print $ "and args " ++ pp args)
    let !() = unsafePerformIO (print $ "checking against type " ++ pp t)
    mr <- lookupFunMacRecord macName
    mf <- lookupFunMacRecord f
    case mr of
        PolyMac {macTyVars = m_tvs, macCtx = m_g, macTy = m_r, macMonoTerm = mac_me, macInert = i_mac, macParam = MP _ mp_g mp_r} ->
            (case mf of
                PolyFun {funTyVars = tvs, funCtx = g, funTy = r', funMonoTerm = me, funInert = i_fun} -> do
                    let !() = unsafePerformIO (print $ "g context is: " ++ pp g)
                    (p,margs) <- elabRec (dropVarsCtx m_g) args
                    --TODO:JWC TYPECHECKING, figure out type variables!! need to reparameterize everything in the right way.
                    return $ CR p i_mac $ do
                        args <- margs
                        g_mono <- monomorphizeCtx m_g
                        r_mono <- monomorphizeTy m_r
                        mac_param_term <- me
                        mac_inlined <- withMacParamReplacement mac_param_term mac_me
                        case mac_inlined of
                            Core.TmFix _ _ _ e' -> return (Core.TmFix args g_mono r_mono e')
                            _ -> error "Macro definition isn't a fix"
                PolyMac {} -> error "cannot call macro with another macro"
                SpecFun {} -> error "cannot call macro with specified function")
        SpecFun {} -> error "Macro use lookup resolved to specialized function... "
        PolyFun {} -> error "Macro use lookup resolved to polymorphic function... "
    



-- checkElab r (Elab.TmFunArgCall f es) = undefined

{-
-}


elabRec :: (Buffer buf, TckM Elab.Term buf m) => CtxStruct OpenTy -> CtxStruct Elab.Term -> m (P.Partial Var, Template (Core.Term buf) (CtxStruct (Core.Term buf)))
elabRec EmpCtx EmpCtx = return (P.empty,return EmpCtx)
elabRec g@EmpCtx g' = throwError (UnsaturatedRecursiveCall g g')
elabRec (SngCtx s) (SngCtx e) = do
    CR p _ e' <- checkElab s e
    return (p,SngCtx <$> e')
elabRec g@(SngCtx {}) g' = throwError (UnsaturatedRecursiveCall g g')
elabRec (SemicCtx g1 g2) (SemicCtx args1 args2) = do
    (p,args1') <- elabRec g1 args1
    (p',args2') <- elabRec g2 args2
    reThrow (error "asdf") (P.checkDisjoint p p')
    p'' <- reThrow (handleOrderErr (error "Arguments use variables inconsistently")) $ P.concat p p'
    return (p'',SemicCtx <$> args1' <*> args2')
elabRec g@(SemicCtx {}) g' = throwError (UnsaturatedRecursiveCall g g')
elabRec (CommaCtx g1 g2) (CommaCtx args1 args2) = do
    (p,args1') <- elabRec g1 args1
    (p',args2') <- elabRec g2 args2
    p'' <- reThrow (handleOrderErr (error "Arguments use variables inconsistently")) $ P.union p p'
    return (p'',CommaCtx <$> args1' <*> args2')
elabRec g@(CommaCtx {}) g' = throwError (UnsaturatedRecursiveCall g g')


inferElab :: (Buffer buf, TckM Elab.Term buf m) => Elab.Term -> m (InferElabResult buf)
inferElab (Elab.TmLitR (LInt n)) = return $ IR TyInt P.empty Jumpy (return (Core.TmLitR (LInt n)))
inferElab (Elab.TmLitR (LBool b)) = return $ IR TyBool P.empty Jumpy (return (Core.TmLitR (LBool b)))
inferElab Elab.TmEpsR = return $ IR TyEps P.empty Inert (return Core.TmEpsR)

inferElab e@(Elab.TmVar x) = do
    s <- lookupTy e x
    return $ IR s (P.singleton x) Inert (return (Core.TmVar x))

inferElab e@(Elab.TmCatL x y z e') = do
    -- Find the type for x and y
    (s,t) <- lookupTyCat e z
    -- Bind x:s,y:t, unbind z, and recursively check 
    (IR r p i e'') <- withBindAll [(x,s),(y,t)] (inferElab e')
    -- Ensure that x and y are used in order in e: y cannot be before x.
    guard (not $ P.lessThan p y x) (OutOfOrder x y e')
    -- Ensure that the destructed variable z is not used in e'
    reThrow (handleContUse e) (P.checkNotIn z p)
    -- Replace x and y with z in the output
    p' <- reThrow (handleOrderErr e') $ P.substSingAll p [(P.singleton z,x),(P.singleton z,y)]
    return $ IR r p' i $ do
        t' <- monomorphizeTy t
        Core.TmCatL t' x y z <$> e''

inferElab e@(Elab.TmCatR e1 e2) = do
    IR s p1 i e1' <- inferElab e1
    IR t p2 _ e2' <- inferElab e2
    p' <- reThrow (handleOrderErr e) $ P.concat p1 p2
    reThrow (handleReUse e) (P.checkDisjoint p1 p2)
    let i' = if i == Inert && not (isNull s) then Inert else Jumpy
    return $ IR (TyCat s t) p' i' (Core.TmCatR <$> monomorphizeTy s <*> e1' <*> e2')

inferElab e@(Elab.TmParL x y z e') = do
    (s,t) <- lookupTyPar e z
    (IR r p i e'') <- withBindAll [(x,s),(y,t)] (inferElab e')
    when (P.comparable p y x) (throwError (SomeOrder x y e'))
    reThrow (handleContUse e) (P.checkNotIn z p)
    p' <- reThrow (handleOrderErr e') $ P.substSingAll p [(P.singleton z,x),(P.singleton z,y)]
    return $ IR r p' i (Core.TmParL x y z <$> e'')

inferElab e@(Elab.TmParR e1 e2) = do
    IR s p1 i1 e1' <- inferElab e1
    IR t p2 i2 e2' <- inferElab e2
    let i = if i1 == Inert && i2 == Inert then Inert else Jumpy
    p' <- reThrow (handleOrderErr e) $ P.union p1 p2
    return $ IR (TyPar s t) p' i (Core.TmParR <$> e1' <*> e2')

inferElab e@(Elab.TmInl {}) = throwError (CheckTermInferPos e)
inferElab e@(Elab.TmInr {}) = throwError (CheckTermInferPos e)

inferElab e@(Elab.TmPlusCase z x e1 y e2) = do
    (s,t) <- lookupTyPlus e z
    IR r1 p1 _ e1' <- withBind x s $ inferElab e1
    IR r2 p2 _ e2' <- withBind y t $ inferElab e2
    guard (r1 == r2) (UnequalReturnTypes r1 r2 e)
    reThrow (handleContUse e1) (P.checkNotIn z p1)
    reThrow (handleContUse e2) (P.checkNotIn z p2)
    p' <- reThrow (handleOrderErr e) $ P.union p1 p2
    m_rho <- asks (emptyBufOfType . argsTypes)
    return $ IR r1 p' Inert $ do
        r1' <- monomorphizeTy r1
        me1' <- e1'
        me2' <- e2'
        rho <- m_rho
        return (Core.TmPlusCase rho r1' z x me1' y me2')

inferElab e@(Elab.TmIte m e1 e2) = do
    () <- liftHistCheck e (Hist.check m TyBool)
    IR r1 p1 _ e1' <- inferElab e1
    IR r2 p2 _ e2' <- inferElab e2
    guard (r1 == r2) (UnequalReturnTypes r1 r2 e)
    p' <- reThrow (handleOrderErr e) $ P.union p1 p2
    return $ IR r1 p' Inert $ do
        r <- monomorphizeTy r1
        Core.TmIte m <$> e1' <*> e2'
    

inferElab e@Elab.TmNil = throwError (CheckTermInferPos e)

inferElab e@(Elab.TmCons e1 e2) = do
    IR s p1 i e1' <- inferElab e1
    CR p2 _ e2' <- checkElab (TyStar s) e2
    reThrow (handleReUse e) (P.checkDisjoint p1 p2)
    p' <- reThrow (handleOrderErr e) $ P.concat p1 p2
    let i' = if i == Inert && not (isNull s) then Inert else Jumpy
    return $ IR (TyStar s) p' i' (Core.TmCons <$> monomorphizeTy s <*> e1' <*> e2')

inferElab e@(Elab.TmStarCase z e1 x xs e2) = do
    s <- lookupTyStar e z
    IR r1 p1 _ e1' <- inferElab e1
    IR r2 p2 _ e2' <- withBindAll [(x,s),(xs,TyStar s)] $ inferElab e2
    reThrow (handleContUse e) (P.checkNotIn z p1)
    reThrow (handleContUse e) (P.checkNotIn z p2)
    guard (r1 == r2) (UnequalReturnTypes r1 r2 e)
    p' <- reThrow (handleOrderErr e) $ P.union p1 p2
    m_rho <- asks (emptyBufOfType . argsTypes)
    return $ IR r1 p' Inert $ do
        mr <- monomorphizeTy r1
        ms <- monomorphizeTy s
        me1' <- e1'
        me2' <- e2'
        rho <- m_rho
        return (Core.TmStarCase rho mr ms z me1' x xs me2')

inferElab e@(Elab.TmCut x e1 e2) = do
    IR s p i e1' <- inferElab e1
    IR t p' i' e2' <- withBind x s $ inferElab e2
    guard (i == Inert) (NonInertCut x e1 e2)
    reThrow (handleReUse e) (P.checkDisjoint p p') {- this should be guaranteed by the fact that we unbind all the vars in p -}
    p'' <- reThrow (handleOrderErr (Elab.TmCut x e1 e2)) $ P.substSing p' p x
    -- e' <- reThrow handleImpossibleCut (Core.cut x e1' e2')
    return (IR t p'' i' (Core.TmCut x <$> e1' <*> e2'))

inferElab e@(Elab.TmRec es) = do
    Rec g r i <- asks rs
    (p,args) <- elabRec (dropVarsCtx g) es
    return (IR r p i (Core.TmRec <$> args))

inferElab e@(Elab.TmWait x e') = do
    m_rho <- asks (emptyBufOfType . argsTypes)
    s <- lookupTy e x
    IR t p _ e'' <- withBindHist x s $ inferElab e'
    reThrow (handleContUse e) (P.checkNotIn x p)
    let i = if not (isNull s) then Inert else Jumpy
    return $ IR t (P.insert p x x) i $ do
        t' <- monomorphizeTy t
        s' <- monomorphizeTy s
        rho <- m_rho
        Core.TmWait rho t' s' x <$> e''

inferElab e@(Elab.TmHistPgm he) = do
    r <- liftHistCheck e (Hist.infer he)
    return $ IR r P.empty Jumpy $ do
        r' <- monomorphizeTy r
        return (Core.TmHistPgm r' he)

inferElab e@(Elab.TmFunCall f ts {-fs-} es) = do
    fr <- lookupFunMacRecord f
    case fr of
        PolyFun {funTyVars = tvs, funCtx = g, funTy = r, funMonoTerm = me, funInert = i} -> do
            when (length ts /= length tvs) $ error "unsatured function call type arguments" -- not saturated type arguments for recursive call.
            let repar_map = foldr (uncurry M.insert) M.empty (zip tvs ts)
            -- compute g'', r'': the  context and return types, after applying the type substitution (tvs |-> ts)
            g' <- reThrow handleReparErr (reparameterizeCtx repar_map g)
            r' <- reThrow handleReparErr (reparameterizeTy repar_map r)
            (p,margs) <- elabRec (dropVarsCtx g') es
            return $ IR r' p i $ do
                g_mono <- monomorphizeCtx g'
                r_mono <- monomorphizeTy r'
                args <- margs
                e' <- reparameterizeTemplate repar_map me
                case e' of
                    Core.TmFix _ _ _ e'' -> return (Core.TmFix args g_mono r_mono e'')
                    _ -> error "Top level definition isn't a fix"
        SpecFun {} -> error "..."
        PolyMac {} -> error "FUnction call lookup resolved to polymorphic macro..."
        -- return (Core.TmFix args g_mono r_mono e)

-- inferElab (Elab.TmFunArgCall f es) = undefined

-- TODO:JWC fix inertness analysis here.
inferElab (Elab.TmMacroParamUse f' args) = do
    mmp <- asks curMacParam -- TODO:JWC do the typechecking here. probably want to make sure f and f' are the same.
    case mmp of
        Just (Surf.MP f g s) ->  do
            (p,margs) <- elabRec g args
            return $ IR s p Inert $ do
                args <- margs
                me <- getMacParamReplacement
                case me of
                    Nothing -> error "uh oh, no replacement."
                    Just (Core.TmFix _ g t e) -> return (Core.TmFix args g t e)
                    _ -> error "replacement is not a term with top level fix..."
        _ -> error "Typechecking a place where a macro parameter use occurs"

inferElab (Elab.TmMacroUse macName ts f args) = do
    mr <- lookupFunMacRecord macName
    mf <- lookupFunMacRecord f
    case mr of
        PolyMac {macTyVars = m_tvs, macCtx = m_g, macTy = m_r, macMonoTerm = mac_me, macInert = i_mac} ->
            (case mf of
                PolyFun {funTyVars = tvs, funCtx = g, funTy = r', funMonoTerm = me, funInert = i_fun} -> do
                    (p,margs) <- elabRec (dropVarsCtx m_g) args
                    --TODO:JWC TYPECHECKING, figure out type variables!! need to reparameterize everything in the right way.
                    return $ IR m_r p i_mac $ do
                        args <- margs
                        g_mono <- monomorphizeCtx m_g
                        r_mono <- monomorphizeTy m_r
                        mac_param_term <- me
                        mac_inlined <- withMacParamReplacement mac_param_term mac_me
                        case mac_inlined of
                            Core.TmFix _ _ _ e' -> return (Core.TmFix args g_mono r_mono e')
                            _ -> error "Macro definition isn't a fix"

                PolyMac {} -> error "cannot call macro with another macro"
                SpecFun {} -> error "cannot call macro with specified function")
        SpecFun {} -> error "Macro use lookup resolved to specialized function... "
        PolyFun {} -> error "Macro use lookup resolved to polymorphic function... "
 


{-
checkCore :: (TckM Core.Term v m) => OpenTy -> Core.Term -> m (P.Partial Var.Var)
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
    reThrow (handleOrderErr e') $ P.substSingAll p [(P.singleton z,x),(P.singleton z,y)]

checkCore (TyCat s t) e@(Core.TmCatR e1 e2) = do
    p1 <- checkCore s e1
    p2 <- checkCore t e2
    reThrow (handleReUse e) (P.checkDisjoint p1 p2)
    reThrow (handleOrderErr (Core.TmCatR e1 e2)) $ P.concat p1 p2
checkCore t (Core.TmCatR e1 e2) = throwError (WrongTypeCatR e1 e2 t)

checkCore r e@(Core.TmParL x y z e') = do
    (s,t) <- lookupTyPar e z
    p <- withBindAll [(x,s),(y,t)] $ withUnbind z (checkCore r e')
    when (P.comparable p y x) (throwError (SomeOrder x y e'))
    reThrow (handleOrderErr e') $ P.substSingAll p [(P.singleton z,x),(P.singleton z,y)]

checkCore (TyPar s t) e@(Core.TmParR e1 e2) = do
    p1 <- checkCore s e1
    p2 <- checkCore t e2
    reThrow (handleOrderErr e) $ P.union p1 p2
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
        p' <- reThrow (handleOrderErr e) (P.union p1 p2)
        reThrow (handleOrderErr e) (P.substSingAll p' [(P.singleton z,x),(P.singleton z,y)])

checkCore r e@(Core.TmIte m rho r' z e1 e2) = do
    reThrow handleHasTypeErr (hasType rho m)
    withCtx m $ do
        lookupTyBool e z
        guard (r == r') (ListedTypeError r' r e)
        p1 <- checkCore r e1
        p2 <- checkCore r e2
        reThrow (handleOrderErr e) (P.union p1 p2)

checkCore (TyStar _) Core.TmNil = return P.empty
checkCore t Core.TmNil = throwError (WrongTypeNil t)

checkCore (TyStar s) e@(Core.TmCons e1 e2) = do
    p1 <- checkCore s e1
    p2 <- checkCore (TyStar s) e2
    reThrow (handleReUse e) (P.checkDisjoint p1 p2)
    reThrow (handleOrderErr (Core.TmCatR e1 e2)) $ P.concat p1 p2
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
        p' <- reThrow (handleOrderErr e) $ P.union p1 p2
        reThrow (handleOrderErr e) (P.substSingAll p' [(P.singleton z,x),(P.singleton z,xs)])

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
    reThrow (handleOrderErr (Core.TmCut x e1 e2)) $ P.substSing p' p x

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
    p'' <- reThrow (handleOrderErr e') $ P.substSingAll p [(P.singleton z,x),(P.singleton z,y)]
    return (r,p'')

inferCore e@(Core.TmCatR e1 e2) = do
    (s,p1) <- inferCore e1
    (t,p2) <- inferCore e2
    reThrow (handleReUse e) (P.checkDisjoint p1 p2)
    p'' <- reThrow (handleOrderErr e) $ P.concat p1 p2
    return (TyCat s t,p'')

inferCore e@(Core.TmParL x y z e') = do
    (s,t) <- lookupTyPar e z
    (r,p) <- withBindAll [(x,s),(y,t)] $ withUnbind z (inferCore e')
    when (P.comparable p y x) (throwError (SomeOrder x y e'))
    p'' <- reThrow (handleOrderErr e') $ P.substSingAll p [(P.singleton z,x),(P.singleton z,y)]
    return (r,p'')

inferCore e@(Core.TmParR e1 e2) = do
    (s,p1) <- inferCore e1
    (t,p2) <- inferCore e2
    p'' <- reThrow (handleOrderErr e) $ P.union p1 p2
    return (TyCat s t,p'')

inferCore (Core.TmInl e) = undefined
inferCore (Core.TmInr e) = undefined

inferCore e@(Core.TmPlusCase m rho r z x e1 y e2) = do
    reThrow handleHasTypeErr (hasType rho m)
    withCtx m $ do
        (s,t) <- lookupTyPlus e z
        p1 <- withBind x s $ withUnbind z $ checkCore r e1
        p2 <- withBind y t $ withUnbind z $ checkCore r e2
        p' <- reThrow (handleOrderErr e) (P.union p1 p2)
        p'' <- reThrow (handleOrderErr e) (P.substSingAll p' [(P.singleton z,x),(P.singleton z,y)])
        return (r,p'')

inferCore e@(Core.TmIte m rho r z e1 e2) = do
    reThrow handleHasTypeErr (hasType rho m)
    withCtx m $ do
        lookupTyBool e z
        p1 <- checkCore r e1
        p2 <- checkCore r e2
        (r,) <$> reThrow (handleOrderErr e) (P.union p1 p2)

inferCore Core.TmNil = undefined

inferCore e@(Core.TmCons e1 e2) = do
    (s,p1) <- inferCore e1
    p2 <- checkCore (TyStar s) e2
    reThrow (handleReUse e) (P.checkDisjoint p1 p2)
    p <- reThrow (handleOrderErr (Core.TmCatR e1 e2)) $ P.concat p1 p2
    return (TyStar s, p)

inferCore e@(Core.TmStarCase m rho r s' z e1 x xs e2) = do
    reThrow handleHasTypeErr (hasType rho m)
    withCtx m $ do
        s <- lookupTyStar e z
        guard (s == s') (ListedTypeError s' s e)
        p1 <- withUnbind z (checkCore r e1)
        p2 <- withBindAll [(x,s),(xs,TyStar s)] $ withUnbind z (checkCore r e2)
        guard (not $ P.lessThan p2 xs x) (OutOfOrder x xs e2)
        p' <- reThrow (handleOrderErr e) $ P.union p1 p2
        p'' <- reThrow (handleOrderErr e) (P.substSingAll p' [(P.singleton z,x),(P.singleton z,xs)])
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
    p'' <- reThrow (handleOrderErr (Core.TmCut x e1 e2)) $ P.substSing p' p x
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
    reThrow (handleOrderErr (error "eek")) (P.concat p1 p2)
checkRec g@(SemicCtx {}) g' = throwError (NonMatchingRecursiveArgs g g')
checkRec (CommaCtx g1 g2) (CommaCtx g1' g2') = do
    p1 <- checkRec g1 g1'
    p2 <- checkRec g2 g2'
    reThrow (handleOrderErr (error "eek")) (P.union p1 p2)
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


-- Doublecheck argument typechecks the resulting term, again.
doCheckElabTm :: (Buffer buf, MonadIO m) => FileInfo buf -> [Var.TyVar] -> (Maybe Surf.MacroParam) ->  Ctx Var OpenTy -> OpenTy -> Inertness -> Elab.Term -> m (Template (Core.Term buf) (Core.Term buf))
doCheckElabTm fi tvs mmp g t i e = do
    let ck = runIdentity $ runExceptT $ runReaderT (checkElab t e) (TckCtx fi (ctxBindings g) (Rec g t i) M.empty (S.fromList tvs) mmp)
    case ck of
        Left err -> error (pp err)
        Right (CR usages i' m_tm) -> do
            (usageConsist :: Either (TckErr Elab.Term) ()) <- runExceptT (withExceptT (handleOrderErr e) $ P.consistentWith usages (_fst <$> g))
            case usageConsist of
                Left err -> error (pp err)
                Right _ -> return $ do
                    tm <- m_tm
                    t' <- monomorphizeTy t
                    g' <- monomorphizeCtx g
                    return (Core.TmFix (fmap (\(CE x _) -> Core.TmVar x) g') g' t' tm)


wfCtx :: (Eq v) => [v] -> Ctx k (TyF v) -> Bool
wfCtx tvs = all (\(CE _ t) -> wfTy tvs t)

wfTy :: (Eq v) => [v] -> TyF v -> Bool
wfTy tvs = all (`elem` tvs)

mapMaybeM :: (Monad m) => (a -> m (Maybe b)) -> [a] -> m [b]
mapMaybeM f [] = return []
mapMaybeM f (x:xs) = do
    fx <- f x
    case fx of
        Just b -> (b:) <$> mapMaybeM f xs
        Nothing -> mapMaybeM f xs


doCheckElabPgm :: (MonadIO m, Buffer buf) => Elab.Program -> m (Core.Program buf)
doCheckElabPgm xs = fst <$> runStateT (mapMaybeM go xs) M.empty
    where
        go :: (MonadIO m, Buffer buf) => Elab.Cmd -> StateT (FileInfo buf) m (Maybe (Core.Cmd buf))
        go (Elab.FunDef f tvs g t e) = do
            -- Check that type type and context are well-formed with the type variables
            unless (wfCtx tvs g) $ error $ "Context " ++ pp g ++ " ill-formed with type variables " ++ (intercalate "," $ pp <$> tvs)
            unless (wfTy tvs t) $ error $ "Type " ++ pp t ++ " ill-formed with type variables " ++ (intercalate "," $ pp <$> tvs)
            -- Typecheck the function
            fi <- get
            e' <- lift $ doCheckElabTm fi tvs Nothing g t Inert e
            liftIO $ putStrLn $ "Function " ++ pp f ++ " typechecked OK."
            put (M.insert f (PolyFun {funTyVars = tvs, funCtx = g, funTy = t, funMonoTerm = e', funInert = Inert}) fi)
            return $ Just (Core.FunDef f tvs (monomorphizeCtx g) (monomorphizeTy t) e')
        go (Elab.MacroDef f tvs mp@(Surf.MP f_mp g_mp t_mp) g t e) = do
            -- Check that type type and context are well-formed with the type variables
            unless (wfCtx tvs g) $ error $ "Context " ++ pp g ++ " ill-formed with type variables " ++ (intercalate "," $ pp <$> tvs)
            unless (wfTy tvs t) $ error $ "Type " ++ pp t ++ " ill-formed with type variables " ++ (intercalate "," $ pp <$> tvs)
            unless (all (wfTy tvs) g_mp) $ error $ "Macro Parameter Context " ++ pp g ++ " ill-formed with type variables " ++ (intercalate "," $ pp <$> tvs)
            unless (wfTy tvs t_mp) $ error $ "Macro Parameter Return Type " ++ pp t ++ " ill-formed with type variables " ++ (intercalate "," $ pp <$> tvs)
            -- Typecheck the function
            fi <- get
            e' <- lift $ doCheckElabTm fi tvs (Just mp) g t Inert e
            liftIO $ putStrLn $ "Macro " ++ pp f ++ " typechecked OK."
            put (M.insert f (PolyMac {macTyVars = tvs, macCtx = g, macTy = t, macParam = Core.MP f_mp (monomorphizeCtxStruct monomorphizeTy g_mp) (monomorphizeTy t_mp), macMonoTerm = e', macInert = Inert}) fi)
            return Nothing
            -- return (Core.FunDef f tvs (monomorphizeCtx g) (monomorphizeTy t) e')
        go (Elab.SpecializeCommand f ts _) = do
            fr <- gets (M.lookup f) >>= maybe (error $ "Can not specialize unbound function " ++ pp f) return
            case fr of
                PolyFun tvs og _ _ _ -> do
                    when (length ts /= length tvs) $ error ("Unsaturated type parameters when specializing " ++ pp f)
                    when (any isNull ts) $ error ("Cannot specialize with nullable type. ")
                    let monomap = foldr (uncurry M.insert) M.empty (zip tvs ts)
                    case runTemplate (monomorphizeCtx og) monomap Nothing of -- TODO:JWC (is this right here? typecheck the funvars?)
                        Left err -> error (pp err)
                        Right g -> do
                            modify' (M.insert f (SpecFun g))
                            return $ Just (Core.SpecializeCommand f ts)
                SpecFun {} -> error ("Cannot re-specialize function " ++ pp f)
                PolyMac {} -> error ("Cannot specialize macro " ++ pp f)
        go (Elab.RunCommand f p) = do
            fr <- gets (M.lookup f) >>= maybe (error $ "Can not run unbound function " ++ pp f) return
            case fr of
                SpecFun g -> do
                    mrho <- lift (runExceptT (checkUntypedPrefixCtx g p))
                    case mrho of
                        Left err -> error (show err)
                        Right rho -> return $ Just (Core.RunCommand f rho)
                PolyFun {} -> error ("Cannot run un-specialized function " ++ pp f)
                PolyMac {} -> error ("Cannot run macro" ++ pp f)

        go (Elab.RunStepCommand f p) = do
            fr <- gets (M.lookup f) >>= maybe (error $ "Can not step-run unbound function " ++ pp f) return
            case fr of
                SpecFun g -> do
                    mrho <- lift (runExceptT (checkUntypedPrefixCtx g p))
                    case mrho of
                        Left err -> error (show err)
                        Right rho -> do
                            -- Update the input type of f to the derivative
                            g' <- runExceptT (deriv rho g) >>= either (error . pp) return
                            modify' (M.insert f (SpecFun g'))
                            return $ Just (Core.RunStepCommand f rho)
                PolyFun {} -> error ("Cannot run un-specialized function " ++ pp f)
                PolyMac {} -> error ("Cannot run macro")
        go (Elab.QuickCheckCommand f) = do
            fr <- gets (M.lookup f) >>= maybe (error $ "Can not quickcheck unbound function " ++ pp f) return
            case fr of
                PolyFun {} -> error ("Cannot quickcheck unspecialized function" ++ pp f)
                PolyMac {} -> error ("Cannot QC macro")
                SpecFun _ -> return $ Just (Core.QuickCheckCommand f)

tckTests = TestList []