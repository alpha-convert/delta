{-# LANGUAGE FlexibleContexts, BangPatterns, FlexibleInstances, TupleSections #-}
module Backend.EnvSemantics where

import CoreSyntax
    ( Term(..), Program, Cmd(..), substVar, sinkTm, maximalPrefixSubst, fixSubst, cutArgs)
import qualified Data.Map as M
import Control.Monad.Reader
    ( Monad(return), sequence, MonadReader(ask, local), ReaderT (runReaderT), guard, asks )
import Control.Monad.Identity (Identity (runIdentity))
import Control.Monad.Except ( ExceptT, runExceptT, MonadError(throwError) )
import Prelude
import Types (emptyPrefix, TyF (..), Ty, CtxStruct(..), Ctx, ValueLike (..), CtxEntry (..), genSequenceOf)
import Values (Prefix (..), Env, isMaximal, bindAllEnv, bindEnv, bindAllEnv, lookupEnv, prefixConcat, concatEnv, emptyEnv, Lit (..), maximalLift, MaximalPrefix, maximalDemote, unbindEnv, sinkPrefix, unionDisjointEnv)
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
import Backend.Monomorphizer
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
import Util.ErrUtil (reThrow)

type EnvBuffer = Env Var.Var Prefix

instance Buffer EnvBuffer where

data SemError =
      VarLookupFailed Var.Var
    | NotCatPrefix Var.Var Prefix
    | NotParPrefix Var.Var Prefix
    | NotPlusPrefix Var.Var Prefix
    | NotBoolPrefix Var.Var Prefix
    | ConcatError (Term EnvBuffer) Var.Var Prefix Prefix
    | RuntimeCutError Var.Var (Term EnvBuffer) (Term EnvBuffer)
    | SinkError Prefix
    | MaximalPrefixSubstErr Var.Var Values.MaximalPrefix (Term EnvBuffer)
    | MaximalPrefixError Prefix
    | HistSemErr Hist.SemErr Hist.Term
    | NonMatchingArgs (Ctx Var.Var Ty) (CtxStruct (Term EnvBuffer))
    | UnionEnvError Var.Var Prefix Prefix
    deriving (Eq, Ord, Show)

instance PrettyPrint SemError where
    pp (VarLookupFailed (Var.Var x)) = concat ["Variable ",x," is unbound. This is a compiler bug."]
    pp (NotCatPrefix (Var.Var z) p) = concat ["Expected variable ",z," to be a cat-prefix. Instead got: ",pp p]
    pp (NotParPrefix (Var.Var z) p) = concat ["Expected variable ",z," to be a par-prefix. Instead got: ",pp p]
    pp (NotPlusPrefix (Var.Var z) p) = concat ["Expected variable ",z," to be a plus-prefix. Instead got: ",pp p]
    pp (NotBoolPrefix (Var.Var z) p) = concat ["Expected variable ",z," to be a bool-prefix. Instead got: ",pp p]
    pp (ConcatError e x p p') = concat ["Tried to concatenate prefixes ", pp p," and ",pp p', " for variable ", pp x, " in term ", pp e]
    pp (RuntimeCutError x e e') = concat ["Error occurred when trying to cut ",pp x," = ",pp e, " in ", pp e',". This is a bug."]
    pp (SinkError p) = concat ["Tried to build sink term for prefix ", pp p, ". This is a bug."]
    pp (MaximalPrefixSubstErr x p e) = concat ["Failed to substitute prefix ", pp p," for ", pp x, " in term ", pp e]
    pp (MaximalPrefixError p) = concat ["Expected prefix ", pp p," to be maximal."]
    pp (HistSemErr err he) = concat ["Encountered error while evaluating historical term ", pp he, ": ", pp err]
    pp (NonMatchingArgs g g') = concat ["Arguments ", pp g', " do not match ", pp g]
    pp (UnionEnvError x p p') = concat ["Variable ", pp x, " has two different bindings: ", pp p, " and ", pp p']

handleConcatError :: Term EnvBuffer -> (Var.Var,Prefix, Prefix) -> SemError
handleConcatError e (x,p,p') = ConcatError e x p p'

handleRuntimeCutError :: (Var.Var, Term EnvBuffer, Term EnvBuffer) -> SemError
handleRuntimeCutError (x,e,e') = RuntimeCutError x e e'

handlePrefixSubstError :: (Var.Var,Values.MaximalPrefix, Term EnvBuffer) -> SemError
handlePrefixSubstError (x,p,e) = MaximalPrefixSubstErr x p e

handleHistEvalErr :: Hist.Term -> Hist.SemErr -> SemError
handleHistEvalErr e err = HistSemErr err e


class (MonadReader EnvBuffer m, MonadError SemError m) => EvalM m where

instance EvalM (ReaderT EnvBuffer (ExceptT SemError Identity)) where

doEval :: ReaderT (Env Var.Var Prefix) (ExceptT SemError Identity) a -> Env Var.Var Prefix -> Either SemError a
doEval x rho = runIdentity (runExceptT (runReaderT x rho))

doEvalN :: Term EnvBuffer -> [Env Var.Var Prefix] -> Either SemError [Prefix]
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

eval :: (EvalM m) => Term EnvBuffer -> m (Prefix,Term EnvBuffer)
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

eval (TmCatR e1 e2) = do
    (p,e1') <- eval e1
    if not (isMaximal p) then
        return (CatPA p, TmCatR e1' e2)
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
                (p'',e1') <- withEnv (bindEnv x p' . unbindEnv z) (eval e1)
                return (p'', substVar e1' z x)
            SumPB p' -> do
                (p'',e2') <- withEnv (bindEnv y p' . unbindEnv z) (eval e2)
                return (p'', substVar e2' z y)
            _ -> throwError (NotPlusPrefix z p))

eval e@(TmIte rho' r z e1 e2) = do
    withEnvM (concatEnvM e rho') $ do
        p <- lookupVar z
        case p of
            LitPEmp -> do
                rho'' <- ask
                return (emptyPrefix r, TmIte rho'' r z e1 e2)
            (LitPFull (LBool True)) -> do
             (p',e1') <- eval e1
            --  e1'' <- reThrow handleRuntimeCutError (cut z TmEpsR e1')
             return (p', TmCut z TmEpsR e1')
            (LitPFull (LBool False)) -> do
                (p',e2') <- eval e2
                -- e2'' <- reThrow handleRuntimeCutError (cut z TmEpsR e2')
                return (p', TmCut z TmEpsR e2')
            _ -> throwError (NotBoolPrefix z p)

eval TmNil = return (StpDone,TmEpsR)

eval (TmCons e1 e2) = do
    (p,e1') <- eval e1
    if not (isMaximal p) then
        return (StpA p, TmCatR e1' e2)
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
            _ -> throwError (NotPlusPrefix z p))

eval (TmCut x e1 e2) = do
    (p,e1') <- eval e1
    withEnv (bindEnv x p) $ do
        (p',e2') <- eval e2
        -- e' <- reThrow handleRuntimeCutError (cut x e1' e2')
        return (p',TmCut x e1' e2')
        -- return (p',e')

eval (TmFix args g s e) = reThrow (uncurry NonMatchingArgs) (cutArgs g args (fixSubst g s e e)) >>= eval


eval (TmRec _) = error "Impossible."

eval e@(TmWait rho' r x e') = do
    withEnvM (concatEnvM e rho') $ do
        p <- lookupVar x
        case maximalLift p of
            Just p' -> do
                e'' <- reThrow handlePrefixSubstError $ maximalPrefixSubst p' x e'
                withEnv (unbindEnv x) (eval e'')
            Nothing -> do
                rho'' <- ask
                return (emptyPrefix r, TmWait rho'' r x e')

eval (TmHistPgm s he) = do
    p <- reThrow (handleHistEvalErr he) $ do
        v <- Hist.eval he
        mp <- Hist.valueToMaximalPrefix s v
        return (maximalDemote mp)
    e <- reThrow SinkError (sinkTm p)
    return (p,e)

-- A function can be in one of two states. It can have been defined (and not yet specialized), or specialized.
-- An unspecialized function is a monomorphizer, accepting type varibles matching its required type arguments.
data FunState =
      PolymorphicDefn [Var.TyVar] (Mono (Term EnvBuffer)) (Mono (Ctx Var.Var Ty)) (Mono Ty)
    | SpecTerm (Term EnvBuffer) (Ctx Var.Var Ty) Ty

type TopLevel = M.Map Var.FunVar FunState

doRunPgm :: Program EnvBuffer -> IO ()
doRunPgm p = do
    !_ <- runStateT (mapM go p) M.empty
    return ()
    where
        go :: Cmd EnvBuffer -> StateT TopLevel IO ()
        go (FunDef f tvs g s e) = modify' (M.insert f (PolymorphicDefn tvs e g s))
        go (SpecializeCommand f ts) = do
            lift (putStrLn "\n")
            fs <- gets (M.lookup f) >>= maybe (error ("Runtime Error: Tried to execute unbound function " ++ pp f)) return
            case fs of
                SpecTerm {} -> error ("Cannot re-specialize function " ++ pp f)
                PolymorphicDefn tvs me mg ms -> do
                    when (length ts /= length tvs) $ error ("Unsaturated type arguments when specializing " ++ pp f)
                    -- Build the map from type variables to closed types being applied
                    let monomap = foldr (uncurry M.insert) M.empty (zip tvs ts)
                    let monoAll = do {e <- me; g <- mg; s <- ms; return (e,g,s)}
                    -- Monomorphize everything, then insert it as a specialized term into the file info.
                    case runMono monoAll monomap of
                        Left err -> error (pp err)
                        Right (e,g,s) -> modify' (M.insert f (SpecTerm e g s))
        go (RunCommand f rho) = do
            lift (putStrLn "\n")
            fs <- gets (M.lookup f) >>= maybe (error ("Runtime Error: Tried to execute unbound function " ++ pp f)) return
            case fs of
                PolymorphicDefn {} -> error ("Cannot run un-specialized function " ++ pp f)
                SpecTerm e _ t -> do
                    lift $ putStrLn $ "Core term: " ++ pp e ++ " for running function " ++ pp f ++ " on " ++ pp rho
                    case doEval (eval e) rho of
                        Right (p',_) -> do
                            lift (putStrLn $ "Result of executing " ++ pp f ++ " on " ++ pp rho ++ ": " ++ pp p')
                            () <- hasTypeB p' t >>= (\b -> if b then return () else error ("Output: " ++ pp p' ++ " does not have type "++ pp t))
                            return ()
                        Left err -> error $ ("\nRuntime Error: " ++ pp err)

        go (RunStepCommand f rho) = do
            lift (putStrLn "\n")
            fs <- gets (M.lookup f) >>= maybe (error ("Runtime Error: Tried to execute unbound function " ++ pp f)) return
            case fs of
                PolymorphicDefn {} -> error ("Cannot run un-specialized function " ++ pp f)
                SpecTerm e g s -> do
                    lift $ putStrLn $ "Core term: " ++ pp e ++ " for step-running functon " ++ pp f ++ " on " ++ pp rho
                    case doEval (eval e) rho of
                        Right (p',e') -> do
                            lift (putStrLn $ "Result of executing " ++ pp f ++ " on " ++ pp rho ++ ": " ++ pp p')
                            lift (putStrLn $ "Final core term (stepping): " ++  pp e')
                            () <- runExceptT (hasType p' s) >>= either (error . pp) return
                            g' <- doDeriv rho g
                            s' <- doDeriv p' s
                            modify (M.insert f (SpecTerm e' g' s'))
                        Left err -> error $ "Runtime Error: " ++ pp err


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

        semTest (TmCatR (TmVar $ var "x") (TmVar $ var "y")) [("x",LitPEmp),("y",LitPEmp)] (CatPA LitPEmp) (TmCatR (TmVar $ var "x") (TmVar $ var "y")),
        semTest (TmCatR (TmLitR (LBool False)) (TmVar $ var "y")) [("y",LitPEmp)] (CatPB (LitPFull $ LBool False) LitPEmp) (TmVar (var "y")),

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


-- prop_denote_correct :: Ctx Var.Var Ty -> Term -> Property
-- prop_denote_correct g e = forAll (genSequenceOf 10 g) $ \rhos -> embed (denote e) rhos == doEvalN e rhos

dThen :: (Monad m) => MSF m a b -> MSF m a b -> MSF m a b
dThen m m' = dSwitch (m >>> arr (,Just ())) (const m')

applyOnce :: (Monad m) => (a -> a) -> MSF m a a
applyOnce f = dSwitch (arr ((,Just ()) . f)) (const (arr id))

applyOnceM :: (Monad m) => (a -> m a) -> MSF m a a
applyOnceM f = dSwitch (arrM ((fmap (,Just ())) . f)) (const (arr id))

applyToFirst :: (Monad m) => (a -> a) -> (b -> b) -> MSF m a b -> MSF m a b
applyToFirst f g m = applyOnce f >>> m >>> applyOnce g

applyToFirstM :: (Monad m) => (a -> m a) -> (b -> m b) -> MSF m a b -> MSF m a b
applyToFirstM f g m = applyOnceM f >>> m >>> applyOnceM g

--- Run with the second input, and then the first for the rest of the time
switchInputs :: (Monad m) => MSF m a b -> MSF m (a,a) b
switchInputs m = dSwitch (arr $ \(x,_) -> (x,Just ())) (const (arr snd)) >>> m

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

msfUnionEnv :: (MonadError SemError m) => MSF m (Env Var.Var Prefix, Env Var.Var Prefix) (Env Var.Var Prefix)
msfUnionEnv = arrM (reThrow (\(x,p,p') -> UnionEnvError x p p') . uncurry unionDisjointEnv)

denote :: (MonadError SemError m) => Term EnvBuffer -> MSF m (Env Var.Var Prefix) Prefix
denote (TmLitR v) = dSwitch (arr (const (LitPFull v, Just ()))) (const (denote TmEpsR))
denote TmEpsR = dSwitch (arr (const (EpsP, Just ()))) (const (denote TmEpsR))
denote (TmVar x) = msfLookupEnv x
denote (TmCatR e1 e2) = switch (denote e1 >>^ maximalPass) (\p -> applyToFirst id (CatPB p) (denote e2))
    where
        maximalPass p = (CatPA p,if isMaximal p then Just p else Nothing)

denote (TmCatL t x y z e) = switch bindX (\(p,p') -> dSwitch (bindXY p p') closeXRebindY) >>> denote e
    where
        -- First, we just bind p to x and emp(t) to y.
        -- Once we get a CatPB, we immediately switch to running with x |-> p, y |-> p'
        bindX = arrM $ \rho ->
            case lookupEnv z rho of
                Just (CatPA p) -> return (bindAllEnv [(x,p),(y,emptyPrefix t)] rho, Nothing)
                Just (CatPB p p') -> return (rho,Just (p,p'))
                Just p -> throwError (NotCatPrefix z p)
                Nothing -> throwError (VarLookupFailed z)
        bindXY p p' = arrM $ \rho -> 
            case maximalLift p of
                Just mp -> return (bindAllEnv [(x,p),(y,p')] rho, Just (sinkPrefix mp))
                _ -> throwError (MaximalPrefixError p)
        -- Once we've done that once, we continue by running with x |-> sink(p'), y |-> rho(z)
        closeXRebindY xBind = arrM $ \rho ->
            case lookupEnv z rho of
                Just p -> return $ bindAllEnv [(x,xBind),(y,p)] rho
                Nothing -> throwError (VarLookupFailed z)


denote (TmParR e1 e2) = denote e1 &|& denote e2 >>^ uncurry ParP
denote (TmParL x y z e) = msfLookupEnv z &&& arr id >>> arrM rebind >>> denote e
    where
        rebind (ParP p1 p2,rho) = return (bindAllEnv [(x,p1),(y,p2)] rho)
        rebind (p,_) = throwError (NotParPrefix z p)

denote (TmCut x e1 e2) = (denote e1 &&& arr id >>^ uncurry (bindEnv x)) >>> denote e2
denote (TmInl e) = applyToFirst id SumPA (denote e)
denote (TmInr e) = applyToFirst id SumPB (denote e)
denote e@(TmIte rho' t z e1 e2) = bufferUntil (concatEnvM e) boolLit rho' (emptyPrefix t) go
    where
        boolLit rho =
            case lookupEnv z rho of
                Just LitPEmp -> return Nothing
                Just (LitPFull (LBool True)) -> return (Just True)
                Just (LitPFull (LBool False)) -> return (Just False)
                Just p -> throwError (NotBoolPrefix z p)
                _ -> throwError (VarLookupFailed z)
        go True = denote e1
        go False = denote e2

denote e@(TmPlusCase rho' t z x e1 y e2) = bufferUntil (concatEnvM e) nonEmptyPlus rho' (emptyPrefix t) go
    where
        nonEmptyPlus rho =
            case lookupEnv z rho of
                Just SumPEmp -> return Nothing
                Just (SumPA p) -> return (Just (Left p))
                Just (SumPB p) -> return (Just (Right p))
                Just p -> throwError (NotPlusPrefix z p)
                Nothing -> throwError (VarLookupFailed z)

        go :: (MonadError SemError m) => Either Prefix Prefix -> MSF m (Env Var.Var Prefix) Prefix
        go (Left p) = (msfBindEnv x p `dThen` rebind x z) >>> denote e1
        go (Right p) = (msfBindEnv y p `dThen` rebind y z) >>> denote e2

        rebind x z = arrM $ \rho ->
            case lookupEnv z rho of
                Just p -> return (unbindEnv z (bindEnv x p rho))
                Nothing -> throwError (VarLookupFailed z)

denote TmNil = arr (const StpDone) `dThen` denote TmEpsR
denote (TmCons e1 e2) = switch (denote e1 >>^ maximalPass) (\p -> applyToFirst id (StpB p) (denote e2))
    where
        maximalPass p = (StpA p,if isMaximal p then Just p else Nothing)

denote (TmStarCase {}) = undefined

denote (TmWait rho' t x e) = bufferUntil (concatEnvM e) (maximalOn x) rho' (emptyPrefix t) go
    where
        maximalOn x rho =
            case lookupEnv x rho of
                Just p -> return (maximalLift p)
                Nothing -> throwError (VarLookupFailed x)
        go mp = case runIdentity (runExceptT (maximalPrefixSubst mp x e)) of
                  Left (x,p,e) -> arrM (const (throwError (MaximalPrefixSubstErr x p e)))
                  Right e' -> denote e'

denote (TmHistPgm s he) = dSwitch emit sink
    where
        emit = arrM $ \_ -> do
            mp <- reThrow (handleHistEvalErr he) $ do
                v <- Hist.eval he
                Hist.valueToMaximalPrefix s v
            return (maximalDemote mp, Just mp)
        sink mp = arr (const (sinkPrefix mp))


denote (TmRec _) = error "imposible"

denote (TmFix args g t e) =
    let e' = fixSubst g t e e in
    denoteArgs args g >>> denote e'

denoteArgs EmpCtx EmpCtx = arr id
denoteArgs (SngCtx e) (SngCtx (CE x _)) = denote e &&& arr id >>> arrM (\(p,rho) -> return (bindEnv x p rho))
denoteArgs (CommaCtx g1 g2) (CommaCtx g1' g2') = denoteArgs g1 g1' &&& denoteArgs g2 g2' >>> msfUnionEnv
denoteArgs (SemicCtx g1 g2) (SemicCtx g1' g2') = denoteArgs g1 g1' &&& denoteArgs g2 g2' >>> msfUnionEnv
denoteArgs g g' = arrM (const (throwError (NonMatchingArgs g' g)))


