-- AUTHORS: Emeka Nkurumeh, Joe Cutler

{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
module Frontend.Typecheck(
    doCheckElabPgm,
    doCheckCoreTm,
    doCheckElabTm
) where

import qualified Frontend.ElabSyntax as Elab
import qualified CoreSyntax as Core
import Control.Monad.Except (MonadError (throwError), runExceptT, ExceptT)
import Types (Ctx (..), Ty(..), ctxBindings, ctxVars, emptyPrefix)
import Control.Monad.Reader (MonadReader (ask, local), asks, ReaderT (runReaderT))
import Var (Var (Var))
import Values (Lit(..), Env, Prefix (..), emptyEnv, bindEnv, isMaximal, isEmpty, allEnv, unionDisjointEnv)
import qualified Data.Map as M
import qualified Util.PartialOrder as P
import Control.Monad.Identity (Identity (runIdentity))
import Util.PrettyPrint (PrettyPrint,pp)
import Control.Monad.State.Strict (StateT(runStateT), MonadState (put, get), MonadTrans (lift))
import qualified Frontend.SurfaceSyntax as Surf
import Control.Monad.IO.Class (MonadIO)

data TckErr = VarNotFound Var
            | OutOfOrder Var Var Elab.Term
            | OutOfOrderCore Var Var Core.Term
            | ExpectedTyCat Var Ty
            | ExpectedTyPlus Var Ty
            | ExpectedTyStar Var Ty
            | CheckTermInferPos Elab.Term
            | UnequalReturnTypes Ty Ty Elab.Term
            | WrongTypeLit Lit Ty
            | WrongTypeEpsR Ty
            | WrongTypeVar Var Ty Ty
            | WrongTypeCatR Elab.Term Elab.Term Ty
            | WrongTypeInl Elab.Term Ty
            | WrongTypeInr Elab.Term Ty
            | WrongTypeNil Ty
            | WrongTypeCons Elab.Term Elab.Term Ty
            | ImpossibleCut Var Core.Term Core.Term

instance PrettyPrint TckErr where
    pp (VarNotFound (Var x)) = concat ["Variable ",x," not found"]
    pp (OutOfOrder (Var x) (Var y) e) = concat ["Variable ",y," came before ",x," in term ",pp e," but expected the other order."]
    pp (OutOfOrderCore (Var x) (Var y) e) = concat ["Variable ",y," came before ",x," in term ",pp e," but expected the other order."]
    pp (ExpectedTyCat (Var x) t) = concat ["Variable ",x," expected to be of concatenation type, but it has type", pp t]
    pp (ExpectedTyPlus (Var x) t) = concat ["Variable ",x," expected to be of sum type, but it has type", pp t]
    pp (ExpectedTyStar (Var x) t) = concat ["Variable ",x," expected to be of star type, but it has type", pp t]
    pp (CheckTermInferPos e) = concat ["The type of the term ",pp e," cannot be inferred"]
    pp (UnequalReturnTypes t1 t2 e) = concat ["Different types ",pp t1," and ",pp t2," inferred for the branches of the term ", pp e]
    pp (WrongTypeLit l t) = concat ["Literal ", pp l, " does not have type ", pp t]
    pp (WrongTypeEpsR t) = concat ["sink does not have type ", pp t]
    pp (WrongTypeVar (Var x) t s) = concat ["Variable ",x," has type ",pp s," but expected ", pp t]
    pp (WrongTypeCatR e1 e2 t) = concat ["Term ", pp (Elab.TmCatR e1 e2), " has concatenation type, but checking against ", pp t]
    pp (WrongTypeInl e t) = concat ["Term ", pp (Elab.TmInl e), " has sum type, but checking against ", pp t]
    pp (WrongTypeInr e t) = concat ["Term ", pp (Elab.TmInr e), " has sum type, but checking against ", pp t]
    pp (WrongTypeNil t) = concat ["nil does not have type ", pp t]
    pp (WrongTypeCons e1 e2 t) = concat ["Term ", pp (Elab.TmCons e1 e2), " has star type, but checking against ", pp t]
    pp (ImpossibleCut x e1 e2) = concat ["Impossible cut term ", ppCut x e1 e2, " detected. This is a bug -- please tell Joe."]
        where
            ppCut (Var x') e e' = concat ["let ",x',"= (",pp e,") in (",pp e',")"]

newtype TckCtx = TckCtx { mp :: M.Map Var.Var Ty }

emptyEnvOfType :: TckCtx -> Env Var
emptyEnvOfType (TckCtx m) = M.foldrWithKey (\x t -> bindEnv x (emptyPrefix t)) emptyEnv m

class (MonadError TckErr m, MonadReader TckCtx m) => TckM m where

instance TckM (ReaderT TckCtx (ExceptT TckErr Identity)) where

lookupTy :: (TckM m) => Var -> m Ty
lookupTy x = do
    m <- asks mp
    maybe (throwError (VarNotFound x)) return (M.lookup x m)

lookupTyCat :: (TckM m) => Var -> m (Ty, Ty)
lookupTyCat x = do
    s' <- lookupTy x
    case s' of
        TyCat s t -> return (s,t)
        _ -> throwError (ExpectedTyCat x s')

lookupTyPlus :: (TckM m) => Var -> m (Ty, Ty)
lookupTyPlus x = do
    s' <- lookupTy x
    case s' of
        TyPlus s t -> return (s,t)
        _ -> throwError (ExpectedTyPlus x s')

lookupTyStar :: (TckM m) => Var -> m Ty
lookupTyStar x = do
    s' <- lookupTy x
    case s' of
        TyStar s -> return s
        _ -> throwError (ExpectedTyStar x s')

withUnbind :: (TckM m) => Var -> m a -> m a
withUnbind x = local (TckCtx . M.delete x . mp)

withBind :: (TckM m) => Var -> Ty -> m a -> m a
withBind x s = local (TckCtx . M.insert x s . mp)

withBindAll :: (TckM m) => [(Var,Ty)] -> m a -> m a
withBindAll xs = local (TckCtx . foldr (\(x,s) -> (M.insert x s .)) id xs . mp)

guard :: (TckM m) => Bool -> TckErr -> m ()
guard b e = if b then return () else throwError e

reThrow :: (TckM m) => (e -> TckErr) -> ExceptT e m a -> m a
reThrow k x = runExceptT x >>= either (throwError . k) return

handleOutOfOrder :: Elab.Term -> (Var,Var) -> TckErr
handleOutOfOrder e (x,y) = OutOfOrder x y e

handleImpossibleCut :: (Var, Core.Term, Core.Term) -> TckErr
handleImpossibleCut (x,e,e') = ImpossibleCut x e e'

data InferElabResult = IR { ty :: Ty, iusages :: P.Partial Var, itm :: Core.Term }

data CheckElabResult = CR { cusages :: P.Partial Var, ctm :: Core.Term }

checkElab :: (TckM m) => Ty -> Elab.Term -> m CheckElabResult
checkElab TyInt (Elab.TmLitR l@(LInt _)) = return $ CR P.empty (Core.TmLitR l)
checkElab TyBool (Elab.TmLitR l@(LBool _)) = return $ CR P.empty (Core.TmLitR l)
checkElab t (Elab.TmLitR l) = throwError (WrongTypeLit l t)
checkElab TyEps Elab.TmEpsR = return $ CR P.empty Core.TmEpsR
checkElab t Elab.TmEpsR = throwError (WrongTypeEpsR t)

checkElab t (Elab.TmVar x) = do
    s <- lookupTy x
    guard (s == t) (WrongTypeVar x t s)
    return $ CR (P.singleton x) (Core.TmVar x)

checkElab r (Elab.TmCatL x y z e) = do
    (s,t) <- lookupTyCat z
    (CR p e') <- withBindAll [(x,s),(y,t)] $ withUnbind z (checkElab r e)
    -- Ensure that x and y are used in order in e: y cannot be before x.
    guard (not $ P.lessThan p y x) (OutOfOrder x y e)
    -- Replace x and y with z in the output
    p' <- reThrow (handleOutOfOrder e) $ P.substSingAll p [(P.singleton z,x),(P.singleton z,y)]
    return $ CR p' (Core.TmCatL t x y z e')

checkElab (TyCat s t) (Elab.TmCatR e1 e2) = do
    CR p1 e1' <- checkElab s e1
    CR p2 e2' <- checkElab t e2
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
    (s,t) <- lookupTyPlus z
    CR p1 e1' <- withBind x s $ withUnbind z $ checkElab r e1
    CR p2 e2' <- withBind y t $ withUnbind z $ checkElab r e2
    p' <- reThrow (handleOutOfOrder e) $ P.union p1 p2
    rho <- asks emptyEnvOfType
    return $ CR p' (Core.TmPlusCase rho r z x e1' y e2')

checkElab (TyStar _) Elab.TmNil = return (CR P.empty Core.TmNil)
checkElab t Elab.TmNil = throwError (WrongTypeNil t)

checkElab (TyStar s) (Elab.TmCons e1 e2) = do
    CR p1 e1' <- checkElab s e1
    CR p2 e2' <- checkElab (TyStar s) e2
    p' <- reThrow (handleOutOfOrder (Elab.TmCatR e1 e2)) $ P.concat p1 p2
    return $ CR p' (Core.TmCons e1' e2')

checkElab t (Elab.TmCons e1 e2) = throwError (WrongTypeCons e1 e2 t)

checkElab r e@(Elab.TmStarCase z e1 x xs e2) = do
    s <- lookupTyStar z
    CR p1 e1' <- withUnbind z (checkElab r e1)
    CR p2 e2' <- withBindAll [(x,s),(xs,TyStar s)] $ withUnbind z (checkElab r e2)
    p' <- reThrow (handleOutOfOrder e) $ P.union p1 p2
    rho <- asks emptyEnvOfType
    return $ CR p' (Core.TmStarCase rho r s z e1' x xs e2')

checkElab r (Elab.TmCut x e1 e2) = do
    IR s p e1' <- inferElab e1
    CR p' e2' <- withBind x s $ checkElab r e2
    e <- reThrow handleImpossibleCut (Core.cut x e1' e2')
    p'' <- reThrow (handleOutOfOrder (Elab.TmCut x e1 e2)) $ P.substSing p' p x
    return (CR p'' e)




inferElab :: (TckM m) => Elab.Term -> m InferElabResult
inferElab (Elab.TmLitR (LInt n)) = return $ IR TyInt P.empty (Core.TmLitR (LInt n))
inferElab (Elab.TmLitR (LBool b)) = return $ IR TyBool P.empty (Core.TmLitR (LBool b))
inferElab Elab.TmEpsR = return $ IR TyEps P.empty Core.TmEpsR

inferElab (Elab.TmVar x) = do
    s <- lookupTy x
    return $ IR s (P.singleton x) (Core.TmVar x)

inferElab (Elab.TmCatL x y z e) = do
    -- Find the type for x and y
    (s,t) <- lookupTyCat z
    -- Bind x:s,y:t, unbind z, and recursively check 
    (IR r p e') <- withBindAll [(x,s),(y,t)] $ withUnbind z (inferElab e)
    -- Ensure that x and y are used in order in e: y cannot be before x.
    guard (not $ P.lessThan p y x) (OutOfOrder x y e)
    -- Replace x and y with z in the output
    p' <- reThrow (handleOutOfOrder e) $ P.substSingAll p [(P.singleton z,x),(P.singleton z,y)]
    return $ IR r p' (Core.TmCatL t x y z e')

inferElab e@(Elab.TmCatR e1 e2) = do
    IR s p1 e1' <- inferElab e1
    IR t p2 e2' <- inferElab e2
    p' <- reThrow (handleOutOfOrder e) $ P.concat p1 p2
    return $ IR (TyCat s t) p' (Core.TmCatR e1' e2')

inferElab e@(Elab.TmInl {}) = throwError (CheckTermInferPos e)
inferElab e@(Elab.TmInr {}) = throwError (CheckTermInferPos e)

inferElab e@(Elab.TmPlusCase z x e1 y e2) = do
    (s,t) <- lookupTyPlus z
    IR r1 p1 e1' <- withBind x s $ withUnbind z $ inferElab e1
    IR r2 p2 e2' <- withBind y t $ withUnbind z $ inferElab e2
    guard (r1 == r2) (UnequalReturnTypes r1 r2 e)
    p' <- reThrow (handleOutOfOrder e) $ P.union p1 p2
    rho <- asks emptyEnvOfType
    return $ IR r1 p' (Core.TmPlusCase rho r1 z x e1' y e2')

inferElab e@Elab.TmNil = throwError (CheckTermInferPos e)

inferElab e@(Elab.TmCons e1 e2) = do
    IR s p1 e1' <- inferElab e1
    CR p2 e2' <- checkElab (TyStar s) e2
    p' <- reThrow (handleOutOfOrder e) $ P.concat p1 p2
    return $ IR (TyStar s) p' (Core.TmCons e1' e2')

inferElab e@(Elab.TmStarCase z e1 x xs e2) = do
    s <- lookupTyStar z
    IR r1 p1 e1' <- withUnbind z $ inferElab e1
    IR r2 p2 e2' <- withBindAll [(x,s),(xs,TyStar s)] $ withUnbind z $ inferElab e2
    guard (r1 == r2) (UnequalReturnTypes r1 r2 e)
    p' <- reThrow (handleOutOfOrder e) $ P.union p1 p2
    rho <- asks emptyEnvOfType
    return $ IR r1 p' (Core.TmStarCase rho r1 s z e1' x xs e2')

inferElab (Elab.TmCut x e1 e2) = do
    IR s p e1' <- inferElab e1
    IR t p' e2' <- withBind x s $ inferElab e2
    e <- reThrow handleImpossibleCut (Core.cut x e1' e2')
    p'' <- reThrow (handleOutOfOrder (Elab.TmCut x e1 e2)) $ P.substSing p' p x
    return (IR t p'' e)



checkCore :: (TckM m) => Ty -> Core.Term -> m (P.Partial Var.Var)
checkCore = undefined

inferCore :: (TckM m) => Ty -> Core.Term -> m (P.Partial Var.Var,Ty)
inferCore = undefined

data PrefixCheckErr = WrongType Ty Surf.UntypedPrefix | OrderIssue Prefix Prefix | NotDisjointCtx Var Prefix Prefix | OrderIssueCtx (Env Var) (Env Var) | IllegalStp Prefix deriving (Eq, Ord, Show)

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

checkUntypedPrefixCtx :: (Monad m) => Ctx Var -> M.Map Var Surf.UntypedPrefix -> ExceptT PrefixCheckErr m (Env Var)
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

type FileInfo = M.Map String (Ctx Var, Ty)

doCheckElabTm :: (MonadIO m) => Ctx Var -> Ty -> Elab.Term -> m Core.Term
doCheckElabTm g t e = do
    let ck = runIdentity $ runExceptT $ runReaderT (checkElab t e :: (ReaderT TckCtx (ExceptT TckErr Identity) CheckElabResult)) (TckCtx $ ctxBindings g)
    case ck of
        Left err -> error (pp err)
        Right (CR usages tm) -> do
            usageConsist <- runExceptT (P.consistentWith usages (ctxVars g))
            case usageConsist of
                Left (x,y) -> error $ pp $ OutOfOrder x y e
                Right _ -> return tm

doCheckCoreTm :: (MonadIO m) => Ctx Var -> Ty -> Core.Term -> m ()
doCheckCoreTm g t e = do
    let ck = runIdentity $ runExceptT $ runReaderT (checkCore t e :: (ReaderT TckCtx (ExceptT TckErr Identity) (P.Partial Var))) (TckCtx $ ctxBindings g)
    case ck of
        Left err -> error (pp err)
        Right usages -> do
            usageConsist <- runExceptT (P.consistentWith usages (ctxVars g))
            case usageConsist of
                Left (x,y) -> error $ pp $ OutOfOrderCore x y e
                Right _ -> return ()

doCheckElabPgm :: (MonadIO m) => Elab.Program -> m Core.Program
doCheckElabPgm xs = fst <$> runStateT (mapM go xs) M.empty
    where
        go :: (MonadIO m) => Either Elab.FunDef Elab.RunCmd -> StateT FileInfo m (Either Core.FunDef Core.RunCmd)
        go (Left (Elab.FD f g t e)) = do
            e' <- lift $ doCheckElabTm g t e
            fi <- get
            put (M.insert f (g,t) fi)
            return (Left (Core.FD f g t e'))
        go (Right (Elab.RC f p)) = do
            fi <- get
            case M.lookup f fi of
                Nothing -> error ""
                Just (g,_) -> do
                    mps <- lift (runExceptT (checkUntypedPrefixCtx g p))
                    case mps of
                        Left err -> lift (error (show err))
                        Right ps -> return (Right (Core.RC f ps))

