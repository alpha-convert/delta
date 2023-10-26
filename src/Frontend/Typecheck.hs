-- AUTHORS: Emeka Nkurumeh, Joe Cutler

{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
module Frontend.Typecheck (doCheck) where

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

data TckErr = VarNotFound Var
            | OutOfOrder Var Var Elab.Term
            | ExpectedTyCat Var Ty
            | ExpectedTyPlus Var Ty
            | CheckTermInferPos Elab.Term
            | UnequalReturnTypes Ty Ty Elab.Term
            | WrongTypeLit Lit Ty
            | WrongTypeEpsR Ty
            | WrongTypeVar Var Ty Ty
            | WrongTypeCatR Elab.Term Elab.Term Ty
            | WrongTypeInl Elab.Term Ty
            | WrongTypeInr Elab.Term Ty
            | ImpossibleCut Var Core.Term Core.Term

instance PrettyPrint TckErr where
    pp (VarNotFound (Var x)) = concat ["Variable ",x," not found"]
    pp (OutOfOrder (Var x) (Var y) e) = concat ["Variable ",y," came before ",x," in term ",pp e," but expected the other order. CHECK THIS?"]
    pp (ExpectedTyCat (Var x) t) = concat ["Variable ",x," expected to be of concatenation type, but it has type", pp t]
    pp (ExpectedTyPlus (Var x) t) = concat ["Variable ",x," expected to be of sum type, but it has type", pp t]
    pp (CheckTermInferPos e) = concat ["The type of the term ",pp e," cannot be inferred"]
    pp (UnequalReturnTypes t1 t2 e) = concat ["Different types ",pp t1," and ",pp t2," inferred for the branches of the term ", pp e]
    pp (WrongTypeLit l t) = concat ["Literal ", pp l, " does not have type ", pp t]
    pp (WrongTypeEpsR t) = concat ["sink does not have type ", pp t]
    pp (WrongTypeVar (Var x) t s) = concat ["Variable ",x," has type ",pp s," but expected ", pp t]
    pp (WrongTypeCatR e1 e2 t) = concat ["Term ", pp (Elab.TmCatR e1 e2), " has concatenation type, but checking against ", pp t]
    pp (WrongTypeInl e t) = concat ["Term ", pp (Elab.TmInl e), " has sum type, but checking against ", pp t]
    pp (WrongTypeInr e t) = concat ["Term ", pp (Elab.TmInr e), " has sum type, but checking against ", pp t]
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

data InferResult = IR { ty :: Ty, iusages :: P.Partial Var, itm :: Core.Term }

data CheckResult = CR { cusages :: P.Partial Var, ctm :: Core.Term }

check :: (TckM m) => Ty -> Elab.Term -> m CheckResult
check TyInt (Elab.TmLitR l@(LInt _)) = return $ CR P.empty (Core.TmLitR l)
check TyBool (Elab.TmLitR l@(LBool _)) = return $ CR P.empty (Core.TmLitR l)
check t (Elab.TmLitR l) = throwError (WrongTypeLit l t)
check TyEps Elab.TmEpsR = return $ CR P.empty Core.TmEpsR
check t Elab.TmEpsR = throwError (WrongTypeEpsR t)

check t (Elab.TmVar x) = do
    s <- lookupTy x
    guard (s == t) (WrongTypeVar x t s)
    return $ CR (P.singleton x) (Core.TmVar x)

check r (Elab.TmCatL x y z e) = do
    (s,t) <- lookupTyCat z
    (CR p e') <- withBindAll [(x,s),(y,t)] $ withUnbind z (check r e)
    -- Ensure that x and y are used in order in e: y cannot be before x.
    guard (not $ P.lessThan p y x) (OutOfOrder x y e)
    -- Replace x and y with z in the output
    p' <- reThrow (handleOutOfOrder e) $ P.substSingAll p [(P.singleton z,x),(P.singleton z,y)]
    return $ CR p' (Core.TmCatL t x y z e')

check (TyCat s t) (Elab.TmCatR e1 e2) = do
    CR p1 e1' <- check s e1
    CR p2 e2' <- check t e2
    p' <- reThrow (handleOutOfOrder (Elab.TmCatR e1 e2)) $ P.concat p1 p2
    return $ CR p' (Core.TmCatR e1' e2')
check t (Elab.TmCatR e1 e2) = throwError (WrongTypeCatR e1 e2 t)

check (TyPlus s _) (Elab.TmInl e) = do
    CR p e' <- check s e
    return $ CR p (Core.TmInl e')
check t (Elab.TmInl e) = throwError (WrongTypeInl e t)

check (TyPlus _ t) (Elab.TmInr e) = do
    CR p e' <- check t e
    return $ CR p (Core.TmInr e')
check t (Elab.TmInr e) = throwError (WrongTypeInr e t)

check r e@(Elab.TmPlusCase z x e1 y e2) = do
    (s,t) <- lookupTyPlus z
    CR p1 e1' <- withBind x s $ withUnbind z $ check r e1
    CR p2 e2' <- withBind y t $ withUnbind z $ check r e2
    p' <- reThrow (handleOutOfOrder e) $ P.union p1 p2
    rho <- asks emptyEnvOfType
    return $ CR p' (Core.TmPlusCase rho r z x e1' y e2')

check r (Elab.TmCut x e1 e2) = do
    IR s p e1' <- infer e1
    CR p' e2' <- withBind x s $ check r e2
    e <- cut x e1' e2'
    p'' <- reThrow (handleOutOfOrder (Elab.TmCut x e1 e2)) $ P.substSing p' p x
    return (CR p'' e)



infer :: (TckM m) => Elab.Term -> m InferResult
infer (Elab.TmLitR (LInt n)) = return $ IR TyInt P.empty (Core.TmLitR (LInt n))
infer (Elab.TmLitR (LBool b)) = return $ IR TyBool P.empty (Core.TmLitR (LBool b))
infer Elab.TmEpsR = return $ IR TyEps P.empty Core.TmEpsR

infer (Elab.TmVar x) = do
    s <- lookupTy x
    return $ IR s (P.singleton x) (Core.TmVar x)

infer (Elab.TmCatL x y z e) = do
    -- Find the type for x and y
    (s,t) <- lookupTyCat z
    -- Bind x:s,y:t, unbind z, and recursively check 
    (IR r p e') <- withBindAll [(x,s),(y,t)] $ withUnbind z (infer e)
    -- Ensure that x and y are used in order in e: y cannot be before x.
    guard (not $ P.lessThan p y x) (OutOfOrder x y e)
    -- Replace x and y with z in the output
    p' <- reThrow (handleOutOfOrder e) $ P.substSingAll p [(P.singleton z,x),(P.singleton z,y)]
    return $ IR r p' (Core.TmCatL t x y z e')

infer e@(Elab.TmCatR e1 e2) = do
    IR s p1 e1' <- infer e1
    IR t p2 e2' <- infer e2
    p' <- reThrow (handleOutOfOrder e) $ P.concat p1 p2
    return $ IR (TyCat s t) p' (Core.TmCatR e1' e2')

infer e@(Elab.TmInl {}) = throwError (CheckTermInferPos e)
infer e@(Elab.TmInr {}) = throwError (CheckTermInferPos e)

infer e@(Elab.TmPlusCase z x e1 y e2) = do
    (s,t) <- lookupTyPlus z
    IR r1 p1 e1' <- withBind x s $ withUnbind z $ infer e1
    IR r2 p2 e2' <- withBind y t $ withUnbind z $ infer e2
    guard (r1 == r2) (UnequalReturnTypes r1 r2 e)
    p' <- reThrow (handleOutOfOrder e) $ P.union p1 p2
    rho <- asks emptyEnvOfType
    return $ IR r1 p' (Core.TmPlusCase rho r1 z x e1' y e2')

infer (Elab.TmCut x e1 e2) = do
    IR s p e1' <- infer e1
    IR t p' e2' <- withBind x s $ infer e2
    e <- cut x e1' e2'
    p'' <- reThrow (handleOutOfOrder (Elab.TmCut x e1 e2)) $ P.substSing p' p x
    return (IR t p'' e)

cut :: (TckM m) => Var -> Core.Term -> Core.Term -> m Core.Term
cut _ _ e'@(Core.TmLitR _) = return e'
cut _ _ e'@Core.TmEpsR = return e'
cut x e e'@(Core.TmVar y) = if x == y then return e else return e'

cut x (Core.TmCatL t' x'' y'' z' e'') e' = Core.TmCatL t' x'' y'' z' <$> cut x e'' e'
cut x (Core.TmPlusCase rho r z x'' e1 y'' e2) e' = do
    e1' <- cut x e1 e'
    e2' <- cut x e2 e'
    -- FIXME: Is this "rho" correct here? I think it might not be.
    return (Core.TmPlusCase rho r z x'' e1' y'' e2')

cut x e                     (Core.TmCatL t x' y' z e') | x /= z = Core.TmCatL t x' y' z <$> cut x e e'
cut _ (Core.TmVar z)        (Core.TmCatL t x' y' _ e') = return (Core.TmCatL t  x' y' z e')
cut _ (Core.TmCatR e1 e2)   (Core.TmCatL _ x' y' _ e') = cut x' e1 e' >>= cut y' e2
cut x e                     e'@(Core.TmCatL {}) = throwError (ImpossibleCut x e e')

cut x e                 (Core.TmPlusCase rho t z x' e1 y' e2) | x /= z = do
    e1' <- cut x e e1
    e2' <- cut x e e2
    return (Core.TmPlusCase rho t z x' e1' y' e2')
cut _ (Core.TmVar z)    (Core.TmPlusCase rho t _ x' e1 y' e2) = return (Core.TmPlusCase rho t z x' e1 y' e2)
cut _ (Core.TmInl e)    (Core.TmPlusCase _ _ _ x' e1 _ _) = cut x' e e1
cut _ (Core.TmInr e)    (Core.TmPlusCase _ _ _ _ _ y' e2) = cut y' e e2
cut x e                 e'@(Core.TmPlusCase {}) = throwError (ImpossibleCut x e e')

cut x e (Core.TmCatR e1 e2) = Core.TmCatR <$> cut x e e1 <*> cut x e e2
cut x e (Core.TmInl e') = Core.TmInl <$> cut x e e'
cut x e (Core.TmInr e') = Core.TmInr <$> cut x e e'

data PrefixCheckErr = WrongType Ty Surf.UntypedPrefix | OrderIssue Prefix Prefix | NotDisjointCtx Var Prefix Prefix | OrderIssueCtx (Env Var) (Env Var) deriving (Eq, Ord, Show)

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

doCheckTm :: Ctx Var -> Ty -> Elab.Term -> IO Core.Term
doCheckTm g t e = do
    let ck = runIdentity $ runExceptT $ runReaderT (check t e :: (ReaderT TckCtx (ExceptT TckErr Identity) CheckResult)) (TckCtx $ ctxBindings g)
    case ck of
        Left err -> error (pp err)
        Right (CR usages tm) -> do
            usageConsist <- runExceptT (P.consistentWith usages (ctxVars g))
            case usageConsist of
                Left (x,y) -> error $ pp $ OutOfOrder x y e
                Right _ -> return tm

doCheck :: Elab.Program -> IO Core.Program
doCheck xs = fst <$> runStateT (mapM go xs) M.empty
    where
        go :: Either Elab.FunDef Elab.RunCmd -> StateT FileInfo IO (Either Core.FunDef Core.RunCmd)
        go (Left (Elab.FD f g t e)) = do
            e' <- lift $ doCheckTm g t e
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

