{-# LANGUAGE FlexibleContexts, BangPatterns, FlexibleInstances, TupleSections #-}
module Backend.EnvSemantics where

import CoreSyntax
    ( Term(..), Program, Cmd(..), substVar, sinkTm, maximalPrefixSubst, fixSubst, bufMap)
import qualified Data.Map as M
import Control.Monad.Reader
    ( Monad(return), sequence, MonadReader(ask, local), ReaderT (runReaderT), guard, asks )
import Control.Monad.Identity (Identity (runIdentity))
import Control.Monad.Except ( ExceptT, runExceptT, MonadError(throwError) )
import Prelude
import Types (emptyPrefix, TyF (..), Ty, CtxStruct(..), Ctx, ValueLike (..), CtxEntry (..), genSequenceOf, genOf, ValueLikeErr (IllTyped))
import Values (Prefix (..), Env, isMaximal, bindAllEnv, bindEnv, bindAllEnv, lookupEnv, prefixConcat, concatEnv, emptyEnv, Lit (..), maximalLift, MaximalPrefix, maximalDemote, unbindEnv, sinkPrefix, unionDisjointEnv, singletonEnv, rebindEnv)
import Data.Map (Map, unionWith)
import Control.Applicative (Applicative(liftA2))
import Control.Monad.State (runStateT, StateT, modify', gets, get, lift, modify)
import Util.PrettyPrint (PrettyPrint (pp))

import qualified Var (Var(..), TyVar, FunVar)
-- import Frontend.Typecheck (doCheckCoreTm)
import Test.HUnit
import Debug.Trace (trace)
import qualified HistPgm as Hist
import GHC.IO.Handle.Types (Handle__(Handle__))
import qualified Data.Bifunctor
import Backend.Template
import Control.Monad (unless)
import Data.MonadicStreamFunction (MSF, arrM, iPost, constM)
import Data.MonadicStreamFunction.Util (next)
import Control.Arrow
import Data.MonadicStreamFunction.Parallel ((&|&))
import Data.MonadicStreamFunction.Core (feedback, embed)
import Control.Monad.Trans.MSF (switch, dSwitch)
import Control.Monad (when)
import Data.MonadicStreamFunction.InternalCore (MSF(..))
import Test.QuickCheck
import Buffer
import Util.ErrUtil (reThrow, reThrowIO)
import Util.MSFUtil
import Test.QuickCheck.Monadic
import Data.List (intercalate)
import Event (envToEvents, eventsToPrefix, eventToPrefix)
import Data.Maybe (isJust)
import Control.Monad (foldM)
import GHC.IO (unsafePerformIO)

type EnvBuf = Env Var.Var Prefix

instance Buffer EnvBuf where
    emptyBufOfType m = M.foldrWithKey (\x t rho -> bindEnv x <$> (emptyPrefix <$> monomorphizeTy t) <*> rho) (return emptyEnv) m
    unbindBuf x = unbindEnv x
    rebindBuf = rebindEnv

data SemError =
      VarLookupFailed Var.Var
    | NotCatPrefix Var.Var Prefix
    | NotParPrefix Var.Var Prefix
    | NotPlusPrefix Var.Var Prefix
    | NotStarPrefix Var.Var Prefix
    | NotBoolPrefix Var.Var Prefix
    | ConcatError (Term EnvBuf) Var.Var Prefix Prefix
    | RuntimeCutError Var.Var (Term EnvBuf) (Term EnvBuf)
    | SinkError Prefix
    | MaximalPrefixSubstErr Var.Var Ty Values.MaximalPrefix (Term EnvBuf)
    | MaximalPrefixError Prefix
    | HistSemErr Hist.SemErr Hist.Term
    | NonMatchingArgs (Ctx Var.Var Ty) (CtxStruct (Term EnvBuf))
    | UnionEnvError Var.Var Prefix Prefix
    | IllTypedPrefix Prefix Ty
    deriving (Eq, Ord, Show)


instance PrettyPrint SemError where
    pp (VarLookupFailed (Var.Var x)) = concat ["Variable ",x," is unbound. This is a compiler bug."]
    pp (NotCatPrefix (Var.Var z) p) = concat ["Expected variable ",z," to be a cat-prefix. Instead got: ",pp p]
    pp (NotParPrefix (Var.Var z) p) = concat ["Expected variable ",z," to be a par-prefix. Instead got: ",pp p]
    pp (NotPlusPrefix (Var.Var z) p) = concat ["Expected variable ",z," to be a plus-prefix. Instead got: ",pp p]
    pp (NotStarPrefix (Var.Var z) p) = concat ["Expected variable ",z," to be a star-prefix. Instead got: ",pp p]
    pp (NotBoolPrefix (Var.Var z) p) = concat ["Expected variable ",z," to be a bool-prefix. Instead got: ",pp p]
    pp (ConcatError e x p p') = concat ["Tried to concatenate prefixes ", pp p," and ",pp p', " for variable ", pp x, " in term ", pp e]
    pp (RuntimeCutError x e e') = concat ["Error occurred when trying to cut ",pp x," = ",pp e, " in ", pp e',". This is a bug."]
    pp (SinkError p) = concat ["Tried to build sink term for prefix ", pp p, ". This is a bug."]
    pp (MaximalPrefixSubstErr x s p e) = concat ["Failed to substitute prefix ", pp p, " at type ", pp s, " for ", pp x, " in term ", pp e]
    pp (MaximalPrefixError p) = concat ["Expected prefix ", pp p," to be maximal."]
    pp (HistSemErr err he) = concat ["Encountered error while evaluating historical term ", pp he, ": ", pp err]
    pp (NonMatchingArgs g g') = concat ["Arguments ", pp g', " do not match ", pp g]
    pp (UnionEnvError x p p') = concat ["Variable ", pp x, " has two different bindings: ", pp p, " and ", pp p']
    pp (IllTypedPrefix p t) = concat ["Prefix ", pp p, " does not have type ", pp t]

handleConcatError :: Term EnvBuf -> (Var.Var,Prefix, Prefix) -> SemError
handleConcatError e (x,p,p') = ConcatError e x p p'

handleRuntimeCutError :: (Var.Var, Term EnvBuf, Term EnvBuf) -> SemError
handleRuntimeCutError (x,e,e') = RuntimeCutError x e e'

handlePrefixSubstError :: (Var.Var,Ty,Values.MaximalPrefix, Term EnvBuf) -> SemError
handlePrefixSubstError (x,s,p,e) = MaximalPrefixSubstErr x s p e

handleHistEvalErr :: Hist.Term -> Hist.SemErr -> SemError
handleHistEvalErr e err = HistSemErr err e

handleValueLikeErr :: ValueLikeErr Prefix Ty -> SemError
handleValueLikeErr (IllTyped p t) = IllTypedPrefix p t


class (MonadReader EnvBuf m, MonadError SemError m) => EvalM m where

instance EvalM (ReaderT EnvBuf (ExceptT SemError Identity)) where

doEval :: ReaderT (Env Var.Var Prefix) (ExceptT SemError Identity) a -> Env Var.Var Prefix -> Either SemError a
doEval x rho = runIdentity (runExceptT (runReaderT x rho))

doEvalN :: Term EnvBuf -> [Env Var.Var Prefix] -> Either SemError [Prefix]
doEvalN _ [] = return []
doEvalN e (rho:rhos) = do
    (p,e') <- doEval (eval e) rho
    ps <- doEvalN e' rhos
    return (p:ps)


withEnv :: (EvalM m) => (Env Var.Var Prefix -> Env Var.Var Prefix) -> m a -> m a
withEnv = local

withEnvM :: (EvalM m) => (Env Var.Var Prefix -> m (Env Var.Var Prefix)) -> m a -> m a
withEnvM f m = do
    e <- ask
    e' <- f e
    local (const e') m


lookupVar :: (MonadError SemError m, MonadReader (Env Var.Var Prefix) m) => Var.Var -> m Prefix
lookupVar x = do
    rho <- ask
    case Values.lookupEnv x rho of
        Nothing -> throwError (VarLookupFailed x)
        Just p -> return p


concatEnvM e rho' rho = reThrow (handleConcatError e) (concatEnv rho' rho)

eval :: (EvalM m) => Term EnvBuf -> m (Prefix,Term EnvBuf)
eval (TmLitR v) = return (LitPFull v,TmEpsR)

eval TmEpsR = return (EpsP,TmEpsR)

eval (TmVar x) = do
    p <- lookupVar x
    return (p, TmVar x)

eval (TmCatL t x y z e) = do
    p <- lookupVar z
    case p of
        CatPA p1 -> do
            (p',e') <- withEnv (bindAllEnv [(x,p1),(y,emptyPrefix t)] . unbindEnv z) (eval e)
            return (p',TmCatL t x y z e')
        CatPB p1 p2 -> do
            (p',e') <- withEnv (bindAllEnv [(x,p1),(y,p2)] . unbindEnv z) (eval e)
            let e'' = substVar e' z y
            sink <- reThrow SinkError (sinkTm p1)
            return (p', TmCut x sink e'')
        _ -> throwError (NotCatPrefix z p)

{-
the "s" in TmCatR is supposed to be the type of the first component.  as of
right now (12/2/23), the environment semantics doesn't require this invariant to
hold (only the event semantics), and so we break the invariant here: s is not
the type of e1', `deriv p s` is.
-}
eval (TmCatR s e1 e2) = do
    (p,e1') <- eval e1
    if not (isMaximal p) then

        return (CatPA p, TmCatR s e1' e2)
    else do
        (p',e2') <- eval e2
        return (CatPB p p',e2')

eval (TmParL x y z e) = do
    p <- lookupVar z
    case p of
        ParP p1 p2 -> do
            (p',e') <- withEnv (bindAllEnv [(x,p1),(y,p2)] . unbindEnv z) (eval e)
            return (p', TmParL x y z e')
        _ -> throwError (NotParPrefix z p)

eval (TmParR e1 e2) = do
    (p,e1') <- eval e1
    (p',e2') <- eval e2
    return (ParP p p', TmParR e1' e2')

eval (TmInl e) = do
    (p,e') <- eval e
    return (SumPA p, e')

eval (TmInr e) = do
    (p,e') <- eval e
    return (SumPB p, e')

eval e@(TmPlusCase rho' r z x e1 y e2) = do
    withEnvM (concatEnvM e rho') $ do
        p <- lookupVar z
        (case p of
            SumPEmp -> do
                rho'' <- ask
                return (emptyPrefix r, TmPlusCase rho'' r z x e1 y e2)
            SumPA p' -> do
                (p'',e1') <- withEnv (bindEnv x p') (eval e1)
                return (p'', substVar e1' z x)
            SumPB p' -> do
                rho <- ask
                (p'',e2') <- withEnv (bindEnv y p') (eval e2)
                return (p'', substVar e2' z y)
            _ -> throwError (NotPlusPrefix z p))

-- eval (TmHistPgm s he) = do
--     p 
--     e <- reThrow SinkError (sinkTm p)
--     return (p,e)


eval e@(TmIte m e1 e2) = do
    b <- reThrow (handleHistEvalErr m) $ do
        v <- Hist.eval m
        case v of
            Hist.VBool b -> return b
            _ -> error ""
    if b then eval e1 else eval e2

eval TmNil = return (StpDone,TmEpsR)

{-Same disclaimer as TmCatR here: s is wrong in the result. -}
eval (TmCons s e1 e2) = do
    (p,e1') <- eval e1
    if not (isMaximal p) then
        return (StpA p, TmCatR s e1' e2)
    else do
        (p',e2') <- eval e2
        return (StpB p p',e2')

eval e@(TmStarCase rho' r s z e1 x xs e2) = do
    withEnvM (concatEnvM e rho') $ do
        p <- lookupVar z
        (case p of
            StpEmp -> do
                rho'' <- ask
                return (emptyPrefix r, TmStarCase rho'' r s z e1 x xs e2)
            StpDone -> eval e1
            StpA p' -> do
                (p'',e2') <- withEnv (bindAllEnv [(x,p'),(xs,StpEmp)] . unbindEnv z) (eval e2)
                return (p'', TmCatL (TyStar s) x xs z e2')
            StpB p1 p2 -> do
                (p'',e2') <- withEnv (bindAllEnv [(x,p1),(xs,p2)] . unbindEnv z) (eval e2)
                sink <- reThrow SinkError (sinkTm p1)
                -- e'' <- reThrow handleRuntimeCutError (cut x sink e2')
                return (p'', substVar (TmCut x sink e2') z xs)
            _ -> throwError (NotStarPrefix z p))

eval (TmCut x e1 e2) = do
    (p,e1') <- eval e1
    withEnv (bindEnv x p) $ do
        (p',e2') <- eval e2
        -- e' <- reThrow handleRuntimeCutError (cut x e1' e2')
        return (p',TmCut x e1' e2')
        -- return (p',e')

eval (TmFix ms mg args g s e) = do
    let msmg = zip ms mg
    mps <- mapM (\(he,(x,t)) -> reThrow (handleHistEvalErr he) $ do
                        v <- Hist.eval he
                        mp <- Hist.valueToMaximalPrefix t v
                        return (t,mp,x)
                    ) msmg
    let e' = fixSubst mg g s e e
    e'' <- foldM (\e0 (t,mp,x) -> reThrow handlePrefixSubstError $ maximalPrefixSubst t mp x e0) e' mps
    eval (TmArgsCut g args e'')

eval (TmRec {}) = error "Impossible."

eval e@(TmWait rho' r s x e') = do
    withEnvM (concatEnvM e rho') $ do
        p <- lookupVar x
        case maximalLift p of
            Just p' -> do
                e'' <- reThrow handlePrefixSubstError $ maximalPrefixSubst s p' x e'
                withEnv (unbindEnv x) (eval e'')
            Nothing -> do
                rho'' <- ask
                return (emptyPrefix r, TmWait rho'' r s x e')

eval (TmHistPgm s he) = do
    p <- reThrow (handleHistEvalErr he) $ do
        v <- Hist.eval he
        mp <- Hist.valueToMaximalPrefix s v
        return (maximalDemote mp)
    e <- reThrow SinkError (sinkTm p)
    return (p,e)

eval (TmArgsCut g args e) = do
    (eta,g',args') <- evalArgs g args
    (p,e') <- withEnv (const eta) (eval e)
    return (p,TmArgsCut g' args' e')

{-
This is not the only way or the most efficient way to do this, it's just the way that was
easiest with the machinery we have right now. You really don't have to compute derivatives at runtime,
you should just check for maximality once, and then mark the term to not run it again.
-}
evalArgs :: (EvalM m) => Ctx Var.Var Ty -> CtxStruct (Term EnvBuf) -> m (Env Var.Var Prefix,Ctx Var.Var Ty, CtxStruct (Term EnvBuf))
evalArgs EmpCtx EmpCtx = return (emptyEnv,EmpCtx,EmpCtx)
evalArgs _ EmpCtx = undefined
evalArgs (SngCtx (CE x s)) (SngCtx e) = do
    (p,e') <- eval e
    s' <- reThrow handleValueLikeErr (deriv p s)
    return (singletonEnv x p,SngCtx (CE x s'), SngCtx e')
evalArgs _ (SngCtx {}) = undefined
evalArgs (CommaCtx g1 g2) (CommaCtx e1 e2) = do
    (env1,g1',e1') <- evalArgs g1 e1
    (env2,g2',e2') <- evalArgs g2 e2
    env <- reThrow (\(x,p,p') -> UnionEnvError x p p') (unionDisjointEnv env1 env2)
    return (env, CommaCtx g1' g2', CommaCtx e1' e2')
evalArgs _ (CommaCtx {}) = undefined
evalArgs (SemicCtx g1 g2) (SemicCtx e1 e2) = do
    (env1,g1',e1') <- evalArgs g1 e1
    if env1 `maximalOn` g1 then do
        (env2,g2',e2') <- evalArgs g2 e2
        env <- reThrow (\(x,p,p') -> UnionEnvError x p p') (unionDisjointEnv env1 env2)
        return (env,SemicCtx g1' g2', SemicCtx e1' e2')
    else do
        let env2 = emptyEnvFor g2
        env <- reThrow (\(x,p,p') -> UnionEnvError x p p') (unionDisjointEnv env1 env2)
        return (env,SemicCtx g1' g2, SemicCtx e1' e2)
        where
            env `maximalOn` g = all (\(CE x _) -> isJust (lookupEnv x env >>= Values.maximalLift)) g
            emptyEnvFor g = foldr (\(CE x s) rho -> bindEnv x (emptyPrefix s) rho) emptyEnv g
evalArgs _ (SemicCtx {}) = undefined



-- eval (TmArgsCut {}) = error "unimplemented"

-- A function can be in one of two states. It can have been defined (and not yet specialized), or specialized.
-- An unspecialized function is a monomorphizer, accepting type varibles matching its required type arguments.
data FunState =
      PolymorphicDefn [Var.TyVar] (Template (Term EnvBuf) (Term EnvBuf)) (Template (Term EnvBuf) [(Var.Var,Ty)]) (Template (Term EnvBuf) (Ctx Var.Var Ty)) (Template (Term EnvBuf) Ty)
    | SpecTerm (Term EnvBuf) [(Var.Var,Ty)] (Ctx Var.Var Ty) Ty

type TopLevel = M.Map Var.FunVar FunState

doRunPgm :: Program EnvBuf -> IO ()
doRunPgm p = do
    !_ <- runStateT (mapM go p) M.empty
    return ()
    where
        go :: Cmd EnvBuf -> StateT TopLevel IO ()
        go (FunDef f tvs hg g s e) = modify' (M.insert f (PolymorphicDefn tvs e hg g s))
        go (SpecializeCommand f ts) = do
            lift (putStrLn "\n")
            fs <- gets (M.lookup f) >>= maybe (error ("Runtime Error: Tried to execute unbound function " ++ pp f)) return
            case fs of
                SpecTerm {} -> error ("Cannot re-specialize function " ++ pp f)
                PolymorphicDefn tvs me mhg mg ms -> do
                    when (length ts /= length tvs) $ error ("Unsaturated type arguments when specializing " ++ pp f)
                    -- Build the map from type variables to closed types being applied
                    let monomap = foldr (uncurry M.insert) M.empty (zip tvs ts)
                    let monoAll = do {e <- me; g <- mg; hg <- mhg; s <- ms; return (e,hg,g,s)}
                    -- Monomorphize everything, then insert it as a specialized term into the file info.
                    case runTemplate monoAll monomap Nothing of
                        Left err -> error (pp err)
                        Right (e,hg,g,s) -> modify' (M.insert f (SpecTerm e hg g s))
        go (RunCommand f vs rho) = do
            lift (putStrLn "\n")
            fs <- gets (M.lookup f) >>= maybe (error ("Runtime Error: Tried to execute unbound function " ++ pp f)) return
            case fs of
                PolymorphicDefn {} -> error ("Cannot run un-specialized function " ++ pp f)
                SpecTerm e hg _ t -> do
                    when (length hg /= length hg) $ error ("Runtime error: unsaturated historical arguments for function " ++ pp f ++ ". This is probably a compiler bug.")
                    e' <- foldM (\e0 (mp,(x,t)) -> reThrow (error "") $ maximalPrefixSubst t mp x e0) e (zip vs hg)
                    -- lift $ putStrLn $ "Core term: " ++ pp e ++ " for running function " ++ pp f ++ " on " ++ pp rho
                    case doEval (eval e') rho of
                        Right (p',_) -> do
                            lift (putStrLn $ "Result of executing " ++ pp f ++ " on " ++ pp rho ++ ": " ++ pp p')
                            () <- hasTypeB p' t >>= (\b -> if b then return () else error ("Output: " ++ pp p' ++ " does not have type "++ pp t))
                            return ()
                        Left err -> error $ ("\nRuntime Error: " ++ pp err)
        go (RunStepCommand f vs rho) = do
            lift (putStrLn "\n")
            fs <- gets (M.lookup f) >>= maybe (error ("Runtime Error: Tried to execute unbound function " ++ pp f)) return
            case fs of
                PolymorphicDefn {} -> error ("Runtime error: Cannot run un-specialized function " ++ pp f)
                SpecTerm e hg g s -> do
                    when (length hg /= length hg) $ error ("Runtime error: unsaturated historical arguments for function " ++ pp f ++ ". This is probably a compiler bug.")
                    e' <- foldM (\e0 (mp,(x,t)) -> reThrow (error $ "Failed to prefix substitute " ++ pp mp ++ " for " ++ pp x ++ " into " ++ pp e0) $ maximalPrefixSubst t mp x e0) e (zip vs hg)
                    -- lift $ putStrLn $ "Core term: " ++ pp e ++ " for step-running functon " ++ pp f ++ " on " ++ pp rho ++ ", and histargs: " ++ (intercalate "," (map pp vs))
                    case doEval (eval e') rho of
                        Right (p',e'') -> do
                            lift (putStrLn $ "Result of executing " ++ pp f ++ " on " ++ pp rho ++ ": " ++ pp p')
                            -- lift (putStrLn $ "Final core term (stepping): " ++  pp e'')
                            () <- runExceptT (hasType p' s) >>= either (error . pp) return
                            g' <- doDeriv rho g
                            s' <- doDeriv p' s
                            modify (M.insert f (SpecTerm e'' [] g' s'))
                        Left err -> error $ "Runtime Error: " ++ pp err

        go (QuickCheckCommand f) = error "Not currently implemented."
            -- do
            -- lift (putStrLn "\n")
            -- fs <- gets (M.lookup f) >>= maybe (error ("Runtime Error: Tried to QuickCheck unbound function " ++ pp f)) return
            -- case fs of
            --     PolymorphicDefn {} -> error ("Cannot run un-specialized function " ++ pp f)
            --     SpecTerm e g t -> lift $ do
            --         putStrLn $ "Quickchecking: " ++ pp e
            --         putStrLn $ "Input context: " ++ pp g
            --         verboseCheck (testSem e g t)

-- testSem e g t = forAll (genOf g) $ \rho -> monadicIO $ do
--     tevs <- lift (reThrowIO (envToEvents g rho))
--     !()<- trace ("Events in: [" ++ intercalate "," (map show tevs) ++ "]") (return ())
--     let e' = (bufMap (const emptyBuf) e :: Term EventSem.EventBuf)
--     evs <- lift (EventSem.doEvalMany e' tevs)
--     !() <- trace ("Events out: " ++ intercalate "," (map show evs)) (return ())
--     case doEval (eval e) rho of
--         Left e -> lift (error (pp e))
--         Right (p,_) -> do
--             !()<- trace ("Env in: " ++ pp rho) (return ())
--             !() <- trace ("Prefix out: " ++ show p) (return ())
--             p' <- lift $ reThrowIO (eventsToPrefix t evs) 
--             !() <- trace ("Events, converted to prefix out: " ++ show p') (return ())
--             return (p === p')



-- testSemN :: Term EnvBuf -> [Env Var.Var Prefix] -> Property
-- testSemN e rhos = monadicIO $ do
--     case (doEvalN e rhos, embed (denote e) rhos) of
--         (Left e,Left e') -> do
--             lift (putStrLn ("Small-Step failed with " ++ pp e))
--             lift (putStrLn ("Denotation failed with " ++ pp e'))
--             return (property False)
--         (Left e,Right v) -> do
--             lift (putStrLn ("Small-Step failed with " ++ pp e))
--             lift (putStrLn ("Denotation got " ++ intercalate "," (map pp v)))
--             return (property False)
--         (Right ps, Left e') -> do
--             lift (putStrLn ("Small-Step got " ++ intercalate "," (map pp ps)))
--             lift (putStrLn ("Denotation failed with " ++ pp e'))
--             return (property False)
--         (Right ps, Right ps') -> return (ps === ps')


evalSingle e xs = runIdentity (runExceptT (runReaderT (eval e) (bindAllEnv (map (Data.Bifunctor.first var) xs) emptyEnv)))

semTests :: Test
semTests = TestList [
        semTest (TmLitR (LInt 3)) [] (LitPFull (LInt 3)) TmEpsR,
        semTest TmEpsR [] EpsP TmEpsR,
        semTest (TmVar $ var "x") [("x",CatPA (LitPFull (LInt 4)))] (CatPA (LitPFull (LInt 4))) (TmVar $ var "x"),
        semTest (TmCatL TyInt (var "x") (var "y") (var "z") (TmVar (var "x"))) [("z",CatPA LitPEmp)] LitPEmp (TmCatL TyInt (var "x") (var "y") (var "z") (TmVar (var "x"))),
        semTest (TmCatL TyInt (var "x") (var "y") (var "z") (TmVar (var "x"))) [("z",CatPA (LitPFull (LInt 3)))] (LitPFull (LInt 3)) (TmCatL TyInt (var "x") (var "y") (var "z") (TmVar (var "x"))),
        semTest (TmCatL TyInt (var "x") (var "y") (var "z") (TmVar (var "x"))) [("z",CatPB (LitPFull (LInt 3)) LitPEmp)] (LitPFull (LInt 3)) TmEpsR,

        semTest (TmCatL TyInt (var "x") (var "y") (var "z") (TmVar (var "y"))) [("z",CatPA LitPEmp)] LitPEmp (TmCatL TyInt (var "x") (var "y") (var "z") (TmVar (var "y"))),
        semTest (TmCatL TyInt (var "x") (var "y") (var "z") (TmVar (var "y"))) [("z",CatPA (LitPFull (LInt 3)))] LitPEmp (TmCatL TyInt (var "x") (var "y") (var "z") (TmVar (var "y"))),
        semTest (TmCatL (TyCat TyInt TyInt) (var "x") (var "y") (var "z") (TmVar (var "y"))) [("z",CatPA (LitPFull (LInt 3)))] (CatPA LitPEmp) (TmCatL (TyCat TyInt TyInt) (var "x") (var "y") (var "z") (TmVar (var "y"))),
        semTest (TmCatL TyInt (var "x") (var "y") (var "z") (TmVar (var "y"))) [("z",CatPB (LitPFull (LInt 3)) (LitPFull (LInt 4)))] (LitPFull (LInt 4)) (TmVar (var "z")),

        semTest (TmCatR undefined (TmVar $ var "x") (TmVar $ var "y")) [("x",LitPEmp),("y",LitPEmp)] (CatPA LitPEmp) (TmCatR undefined (TmVar $ var "x") (TmVar $ var "y")),
        semTest (TmCatR undefined (TmLitR (LBool False)) (TmVar $ var "y")) [("y",LitPEmp)] (CatPB (LitPFull $ LBool False) LitPEmp) (TmVar (var "y")),

        semTest (TmPlusCase emptyEnv TyInt (var "z") (var "z0") (TmVar (var "u")) (var "z1") (TmVar (var "z1"))) [("u", LitPEmp), ("z",SumPEmp)] LitPEmp (TmPlusCase (env [(var "u",LitPEmp),(var "z",SumPEmp)]) TyInt (var "z") (var "z0") (TmVar (var "u")) (var "z1") (TmVar (var "z1"))),
        semTest (TmPlusCase emptyEnv TyInt (var "z") (var "z0") (TmVar (var "u")) (var "z1") (TmVar (var "z1"))) [("u", LitPFull (LInt 3)), ("z",SumPEmp)] LitPEmp (TmPlusCase (env [(var "u",LitPFull (LInt 3)),(var "z",SumPEmp)]) TyInt (var "z") (var "z0") (TmVar (var "u")) (var "z1") (TmVar (var "z1"))),
        semTest (TmPlusCase (env [(var "u",LitPFull (LInt 3)),(var "z",SumPEmp)]) TyInt (var "z") (var "z0") (TmVar (var "u")) (var "z1") (TmVar (var "z1"))) [("u", EpsP), ("z",SumPA EpsP)] (LitPFull (LInt 3)) (TmVar (var "u")),
        semTest (TmPlusCase emptyEnv TyInt (var "z") (var "z0") (TmVar (var "u")) (var "z1") (TmVar (var "z1"))) [("u", LitPFull (LInt 3)), ("z",SumPA EpsP)] (LitPFull (LInt 3)) (TmVar (var "u")),
        semTest (TmPlusCase emptyEnv TyInt (var "z") (var "z0") (TmVar (var "u")) (var "z1") (TmVar (var "z1"))) [("u", LitPFull (LInt 3)), ("z",SumPB LitPEmp)] LitPEmp (TmVar (var "z")),
        semTest (TmPlusCase emptyEnv TyInt (var "z") (var "z0") (TmVar (var "u")) (var "z1") (TmVar (var "z1"))) [("u", LitPFull (LInt 3)), ("z",SumPB (LitPFull (LInt 4)))] (LitPFull (LInt 4)) (TmVar (var "z"))
    ]
    where
        semTest e xs p e' = TestCase $ do
            case evalSingle e xs of
                Left err -> assertFailure (pp err)
                Right (p',e'') -> do
                    assertEqual ("Prefixes should be equal when running " ++ pp e) p p'
                    assertEqual ("Output terms should be equal when running " ++ pp e) e' e''
        semTestPfx e xs p = TestCase $ do
            case evalSingle e xs of
                Left err -> assertFailure (pp err)
                Right (p',_) -> assertEqual "Prefixes should be equal" p p'
        env xs = bindAllEnv xs emptyEnv

var = Var.Var


-- Accumulates inputs until the total combined input (with comb) passes the predicate. Then, we run the continuation,
-- first with the combined input, then with whatever comes in from then on.
bufferUntil :: (Monad m) => (a -> a -> m a) -> (a -> m (Maybe c)) -> a -> b -> (c -> MSF m a b) -> MSF m a b
bufferUntil comb pred init out m = switch (feedback init (arrM accum)) (\(old,c) -> applyToFirstM (comb old) return (m c))
    where
        accum (new,old) = do
            new' <- comb old new
            mc <- pred new'
            return ((out,(old,) <$> mc),new')

-- >>> (embed (bufferUntil (\x y -> return (x + y)) (\n -> return (if n > 5 then Just () else Nothing)) 0 99 (const (arr id))) [1,2,9,150,150] :: Identity [Int])
-- Identity [99,99,12,150,150]

msfLookupEnv :: (MonadError SemError m) => Var.Var -> MSF m (Env Var.Var Prefix) Prefix
msfLookupEnv x = arrM (maybe (throwError (VarLookupFailed x)) return . lookupEnv x)

msfBindEnv :: (Monad m) => Var.Var -> Prefix -> MSF m (Env Var.Var Prefix) (Env Var.Var Prefix)
msfBindEnv x p = arrM (return . bindEnv x p)

msfBindAllEnv :: (Monad m) => [(Var.Var, Prefix)] -> MSF m (Env Var.Var Prefix) (Env Var.Var Prefix)
msfBindAllEnv xps = arrM (return . bindAllEnv xps)

msfUnionEnv :: (MonadError SemError m) => MSF m (Env Var.Var Prefix, Env Var.Var Prefix) (Env Var.Var Prefix)
msfUnionEnv = arrM $ \(rho,rho') -> reThrow r (unionDisjointEnv rho rho')
    where
        r (x,p,p') = UnionEnvError x p p'

-- denote :: (MonadError SemError m) => Term EnvBuf -> MSF m (Env Var.Var Prefix) Prefix
-- denote (TmLitR v) = arr (const (LitPFull v)) `dThen` denote TmEpsR
-- denote TmEpsR = arr (const EpsP)
-- denote (TmVar x) = msfLookupEnv x
-- denote (TmCatR _ e1 e2) = switch (denote e1 >>^ maximalPass) (\p -> applyToFirst id (CatPB p) (denote e2))
--     where
--         maximalPass p = (CatPA p,if isMaximal p then Just p else Nothing)

-- denote (TmCatL t x y z e) = switch bindX (\(p,p') -> dSwitch (bindXY p p') closeXRebindY) >>> denote e
--     where
--         -- First, we just bind p to x and emp(t) to y.
--         -- Once we get a CatPB, we immediately switch to running with x |-> p, y |-> p'
--         bindX = arrM $ \rho ->
--             case lookupEnv z rho of
--                 Just (CatPA p) -> return (bindAllEnv [(x,p),(y,emptyPrefix t)] rho, Nothing)
--                 Just (CatPB p p') -> return (rho,Just (p,p'))
--                 Just p -> throwError (NotCatPrefix z p)
--                 Nothing -> throwError (VarLookupFailed z)
--         bindXY p p' = arrM $ \rho ->
--             case maximalLift p of
--                 Just mp -> return (bindAllEnv [(x,p),(y,p')] rho, Just (sinkPrefix mp))
--                 _ -> throwError (MaximalPrefixError p)
--         -- Once we've done that once, we continue by running with x |-> sink(p'), y |-> rho(z)
--         closeXRebindY xBind = arrM $ \rho ->
--             case lookupEnv z rho of
--                 Just p -> return $ bindAllEnv [(x,xBind),(y,p)] rho
--                 Nothing -> throwError (VarLookupFailed z)


-- denote (TmParR e1 e2) = denote e1 &|& denote e2 >>^ uncurry ParP
-- denote (TmParL x y z e) = msfLookupEnv z &&& arr id >>> arrM rebind >>> denote e
--     where
--         rebind (ParP p1 p2,rho) = return (bindAllEnv [(x,p1),(y,p2)] rho)
--         rebind (p,_) = throwError (NotParPrefix z p)

-- denote (TmCut x e1 e2) = (denote e1 &&& arr id >>^ uncurry (bindEnv x)) >>> denote e2
-- denote (TmInl e) = applyToFirst id SumPA (denote e)
-- denote (TmInr e) = applyToFirst id SumPB (denote e)
-- denote e@(TmIte rho' t z e1 e2) = bufferUntil (concatEnvM e) boolLit rho' (emptyPrefix t) go
--     where
--         boolLit rho =
--             case lookupEnv z rho of
--                 Just LitPEmp -> return Nothing
--                 Just (LitPFull (LBool True)) -> return (Just True)
--                 Just (LitPFull (LBool False)) -> return (Just False)
--                 Just p -> throwError (NotBoolPrefix z p)
--                 _ -> throwError (VarLookupFailed z)
--         go True = denote e1
--         go False = denote e2

-- denote e@(TmPlusCase rho' t z x e1 y e2) = bufferUntil (concatEnvM e) nonEmptyPlus rho' (emptyPrefix t) go
--     where
--         nonEmptyPlus rho =
--             case lookupEnv z rho of
--                 Just SumPEmp -> return Nothing
--                 Just (SumPA p) -> return (Just (Left p))
--                 Just (SumPB p) -> return (Just (Right p))
--                 Just p -> throwError (NotPlusPrefix z p)
--                 Nothing -> throwError (VarLookupFailed z)

--         go :: (MonadError SemError m) => Either Prefix Prefix -> MSF m (Env Var.Var Prefix) Prefix
--         go (Left p) = (msfBindEnv x p `dThen` rebind x z) >>> denote e1
--         go (Right p) = (msfBindEnv y p `dThen` rebind y z) >>> denote e2

--         rebind x z = arrM $ \rho ->
--             case lookupEnv z rho of
--                 Just p -> return (unbindEnv z (bindEnv x p rho))
--                 Nothing -> throwError (VarLookupFailed z)

-- denote TmNil = arr (const StpDone) `dThen` denote TmEpsR
-- denote (TmCons _ e1 e2) = switch (denote e1 >>^ maximalPass) (\p -> applyToFirst id (StpB p) (denote e2))
--     where
--         maximalPass p = (StpA p,if isMaximal p then Just p else Nothing)

-- denote e@(TmStarCase rho' r s z e1 x xs e2) = bufferUntil (concatEnvM e) nonEmptyStar rho' (emptyPrefix r) go
--     where
--         nonEmptyStar rho =
--             case lookupEnv z rho of
--                 Just StpEmp -> return Nothing
--                 Just StpDone -> return (Just (Left ()))
--                 Just (StpA p) -> return (Just (Right (Left p)))
--                 Just (StpB p p') -> return (Just (Right (Right (p,p'))))
--                 Just p -> throwError (NotStarPrefix z p)
--                 Nothing -> throwError (VarLookupFailed z)

--         go (Left ()) = denote e1
--         go (Right (Left p)) = (msfBindAllEnv [(x,p),(xs,StpEmp)] `dThen` rebind xs z {- WRONG!! -}) >>> denote e2
--         go (Right (Right (p,p'))) = (msfBindAllEnv [(x,p),(xs,p')] `dThen` rebind xs z) >>> denote e2

--         rebind x z = arrM $ \rho ->
--             case lookupEnv z rho of
--                 Just p -> return (unbindEnv z (bindEnv x p rho))
--                 Nothing -> throwError (VarLookupFailed z)

-- denote (TmWait rho' t s x e) = bufferUntil (concatEnvM e) (maximalOn x) rho' (emptyPrefix t) go
--     where
--         maximalOn x rho =
--             case lookupEnv x rho of
--                 Just p -> return (maximalLift p)
--                 Nothing -> throwError (VarLookupFailed x)
--         go mp = case runIdentity (runExceptT (maximalPrefixSubst s mp x e)) of
--                   Left (x,s,p,e) -> arrM (const (throwError (MaximalPrefixSubstErr x s p e)))
--                   Right e' -> denote e'

-- denote (TmHistPgm s he) = dSwitch emit sink
--     where
--         emit = arrM $ \_ -> do
--             mp <- reThrow (handleHistEvalErr he) $ do
--                 v <- Hist.eval he
--                 Hist.valueToMaximalPrefix s v
--             return (maximalDemote mp, Just mp)
--         sink mp = arr (const (sinkPrefix mp))


-- denote (TmRec _) = error "imposible"

-- denote (TmFix args g t e) = denoteArgs args g >>> denote (fixSubst g t e e)

-- denote (TmArgsCut {}) = error "unimplemented"

-- denoteArgs EmpCtx EmpCtx = arr id
-- denoteArgs (SngCtx e) (SngCtx (CE x _)) = denote e >>> arrM (return . singletonEnv x)
-- denoteArgs (CommaCtx g1 g2) (CommaCtx g1' g2') = denoteArgs g1 g1' &&& denoteArgs g2 g2' >>> msfUnionEnv
-- denoteArgs (SemicCtx g1 g2) (SemicCtx g1' g2') = denoteArgs g1 g1' &&& denoteArgs g2 g2' >>> msfUnionEnv
-- denoteArgs g g' = arrM (const (throwError (NonMatchingArgs g' g)))


