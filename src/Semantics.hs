{-# LANGUAGE FlexibleContexts, BangPatterns, FlexibleInstances #-}
module Semantics where

import CoreSyntax
import qualified Data.Map as M
import Control.Monad.Reader
    ( Monad(return), sequence, MonadReader(ask, local), ReaderT (runReaderT), guard )
import Control.Monad.Identity (Identity (runIdentity))
import Control.Monad.Except ( ExceptT, runExceptT, MonadError(throwError) )
import Prelude
import Types (emptyPrefix, Ty (..), Ctx (SngCtx), ValueLike (..))
import Values (Prefix (..), Env, isMaximal, bindAllEnv, bindEnv, bindAllEnv, lookupEnv, prefixConcat, concatEnv, emptyEnv, Lit (..))
import Data.Map (Map, unionWith)
import Control.Applicative (Applicative(liftA2))
import Control.Monad.State (runStateT, StateT, modify', gets, get, lift)
import Util.PrettyPrint (PrettyPrint (pp))

import qualified Var (Var(..))
import Frontend.Typecheck (doCheckCoreTm)
import Test.HUnit
import qualified Debug.Trace as Debug

data SemError =
      VarLookupFailed Var.Var
    | NotCatPrefix Var.Var Prefix
    | NotPlusPrefix Var.Var Prefix
    | ConcatError Prefix Prefix
    | RuntimeCutError Var.Var Term Term
    | SinkError Var.Var Prefix
    deriving (Eq, Ord, Show)

instance PrettyPrint SemError where
    pp (VarLookupFailed (Var.Var x)) = concat ["Variable ",x," is unbound. This is a compiler bug."]
    pp (NotCatPrefix (Var.Var z) p) = concat ["Expected variable ",z," to be a cat-prefix. Instead got: ",pp p]
    pp (NotPlusPrefix (Var.Var z) p) = concat ["Expected variable ",z," to be a plus-prefix. Instead got: ",pp p]
    pp (ConcatError p p') = concat ["Tried to concatenate prefixes ", pp p," and ",pp p']
    pp (RuntimeCutError x e e') = concat ["Error occurred when trying to cut ",pp x," = ",pp e, " in ", pp e',". This is a bug."]
    pp (SinkError x p) = concat ["Tried to build sink term for prefix ", pp p, "while substituting for ", pp x, ". This is a bug."]

class (MonadReader (Env Var.Var) m, MonadError SemError m) => EvalM m where

instance EvalM (ReaderT (Env Var.Var) (ExceptT SemError Identity)) where

reThrow :: (EvalM m) => (e -> SemError) -> ExceptT e m a -> m a
reThrow k x = runExceptT x >>= either (throwError . k) return

withEnv :: (EvalM m) => (Env Var.Var -> Env Var.Var) -> m a -> m a
withEnv = local

withEnvM :: (EvalM m) => (Env Var.Var -> m (Env Var.Var)) -> m a -> m a
withEnvM f m = do
    e <- ask
    e' <- f e
    local (const e') m


lookupVar :: (EvalM m) => Var.Var -> m Prefix
lookupVar x = do
    rho <- ask
    case Values.lookupEnv x rho of
        Nothing -> throwError (VarLookupFailed x)
        Just p -> return p

eval :: (EvalM m) => Term -> m (Prefix,Term)
eval (TmLitR v) = return (LitPFull v,TmEpsR)

eval TmEpsR = return (EpsP,TmEpsR)

eval (TmVar x) = do
    p <- lookupVar x
    return (p, TmVar x)

eval (TmCatL t x y z e) = do
    p <- lookupVar z
    case p of
        CatPA p1 -> do
            (p',e') <- withEnv (bindAllEnv [(x,p1),(y,emptyPrefix t)]) (eval e)
            return (p',TmCatL t x y z e')
        CatPB p1 p2 -> do
            (p',e') <- withEnv (bindAllEnv [(x,p1),(y,p2)]) (eval e)
            let e'' = substVar e' z y
            sink <- reThrow (SinkError x) (sinkTm p1)
            return (p', TmCut x sink e'')
        _ -> throwError (NotCatPrefix z p)

eval (TmCatR e1 e2) = do
    (p,e1') <- eval e1
    if not (isMaximal p) then
        return (CatPA p, TmCatR e1' e2)
    else do
        (p',e2') <- eval e2
        return (CatPB p p',e2')

eval (TmInl e) = do
    (p,e') <- eval e
    return (SumPA p, e')

eval (TmInr e) = do
    (p,e') <- eval e
    return (SumPB p, e')

eval (TmPlusCase rho' r z x e1 y e2) = do
    withEnvM (reThrow (uncurry ConcatError) . concatEnv rho') $ do
        p <- lookupVar z
        (case p of
            SumPEmp -> do
                rho'' <- ask
                return (emptyPrefix r, TmPlusCase rho'' r z x e1 y e2)
            SumPA p' -> do
                (p'',e1') <- withEnv (bindEnv x p') (eval e1)
                return (p'', substVar e1' z x)
            SumPB p' -> do
                (p'',e2') <- withEnv (bindEnv y p') (eval e2)
                return (p'', substVar e2' z y)
            _ -> throwError (NotPlusPrefix z p))

eval TmNil = return (StpDone,TmEpsR)

eval (TmCons e1 e2) = do
    (p,e1') <- eval e1
    if not (isMaximal p) then
        return (StpA p, TmCatR e1' e2)
    else do
        (p',e2') <- eval e2
        return (StpB p p',e2')

eval (TmStarCase rho' r s z e1 x xs e2) = do
    withEnvM (reThrow (uncurry ConcatError) . concatEnv rho') $ do
        p <- lookupVar z
        (case p of
            StpEmp -> do
                rho'' <- ask
                return (emptyPrefix r, TmStarCase rho'' r s z e1 x xs e2)
            StpDone -> eval e1
            StpA p' -> do
                (p'',e2') <- withEnv (bindAllEnv [(x,p'),(xs,StpEmp)]) (eval e2)
                return (p'', TmCatL (TyStar s) x xs z e2')
            StpB p1 p2 -> do
                (p'',e2') <- withEnv (bindAllEnv [(x,p1),(xs,p2)]) (eval e2)
                sink <- reThrow (SinkError x) (sinkTm p1)
                return (p'', substVar (TmCut x sink e2') z xs)
            _ -> throwError (NotPlusPrefix z p))

eval (TmCut x e1 e2) = do
    (p,e1') <- eval e1
    withEnv (bindEnv x p) $ do
        (p',e2') <- eval e2
        return (p',TmCut x e1' e2')

eval (TmFix g s e) = do
    let e' = fixSubst (TmFix g s e) e -- this is extremely broken, most likeliy.
    !_ <- Debug.trace ("Unfolded: " ++ pp e' ++ "\n") (return ())
    eval e'
eval TmRec = error "Impossible."

fixSubst :: Term -> Term -> Term
fixSubst e = go
    where
        go TmEpsR = TmEpsR
        go (TmLitR l) = TmLitR l
        go (TmVar x) = TmVar x
        go (TmCatL t x y z e') = TmCatL t x y z (go e')
        go (TmCatR e1 e2) = TmCatR (go e1) (go e2)
        go (TmInl e') = TmInl (go e')
        go (TmInr e') = TmInr (go e')
        go (TmPlusCase rho r z x e1 y e2) = TmPlusCase rho r z x (go e1) y (go e2)
        go TmNil = TmNil
        go (TmCons e1 e2) = TmCons (go e1) (go e2)
        go (TmStarCase rho r t z e1 y ys e2) = TmStarCase rho r t z (go e1) y ys (go e2)
        go (TmFix g s _) = TmFix g s e
        go TmRec = e
        go (TmCut x e1 e2) = TmCut x (go e1) (go e2)

handleRuntimeCutError :: (Var.Var, Term, Term) -> SemError
handleRuntimeCutError (x,e,e') = RuntimeCutError x e e'


type TopLevel = M.Map String (Term, Ctx Var.Var, Ty)


doRunPgm :: Program -> IO ()
doRunPgm p = do
    !_ <- runStateT (mapM go p) M.empty
    return ()
    where
        go :: Either FunDef RunCmd -> StateT TopLevel IO ()
        go (Left (FD f g s e)) = modify' (M.insert f (e,g,s))
        go (Right (RC f rho)) = do
            tl <- get
            case M.lookup f tl of
                Just (e,g,s) -> case runIdentity $ runExceptT $ runReaderT (eval e) rho of
                                    Right (p',e') -> do
                                        lift (print $ "Result of executing " ++ f)
                                        lift (print p')
                                        lift (print e')
                                        () <- hasTypeB p' s >>= guard
                                        g' <- doDeriv rho g 
                                        s' <- doDeriv p' s
                                        () <- doCheckCoreTm g' s' e'
                                        return ()
                                    Left err -> error $ "Runtime Error: " ++ pp err
                Nothing -> error ("Runtime Error: Tried to execute unbound function " ++ f)

evalSingle e xs = runIdentity (runExceptT (runReaderT (eval e) (bindAllEnv (map (\(x,p) -> (var x, p)) xs) emptyEnv)))

semTests :: Test
semTests = TestList [
        semTest (TmLitR (LInt 3)) [] (LitPFull (LInt 3)) TmEpsR,
        semTest TmEpsR [] EpsP TmEpsR,
        semTest (TmVar $ var "x") [("x",CatPA (LitPFull (LInt 4)))] (CatPA (LitPFull (LInt 4))) (TmVar $ var "x"),
        semTest (TmCatL TyInt (var "x") (var "y") (var "z") (TmVar (var "x"))) [("z",CatPA LitPEmp)] LitPEmp (TmCatL TyInt (var "x") (var "y") (var "z") (TmVar (var "x"))),
        semTest (TmCatL TyInt (var "x") (var "y") (var "z") (TmVar (var "x"))) [("z",CatPA (LitPFull (LInt 3)))] (LitPFull (LInt 3)) (TmCatL TyInt (var "x") (var "y") (var "z") (TmVar (var "x"))),
        semTest (TmCatL TyInt (var "x") (var "y") (var "z") (TmVar (var "x"))) [("z",CatPB (LitPFull (LInt 3)) LitPEmp)] (LitPFull (LInt 3)) (TmCut (var "x") TmEpsR (TmVar (var "x"))),

        semTest (TmCatL TyInt (var "x") (var "y") (var "z") (TmVar (var "y"))) [("z",CatPA LitPEmp)] LitPEmp (TmCatL TyInt (var "x") (var "y") (var "z") (TmVar (var "y"))),
        semTest (TmCatL TyInt (var "x") (var "y") (var "z") (TmVar (var "y"))) [("z",CatPA (LitPFull (LInt 3)))] LitPEmp (TmCatL TyInt (var "x") (var "y") (var "z") (TmVar (var "y"))),
        semTest (TmCatL (TyCat TyInt TyInt) (var "x") (var "y") (var "z") (TmVar (var "y"))) [("z",CatPA (LitPFull (LInt 3)))] (CatPA LitPEmp) (TmCatL (TyCat TyInt TyInt) (var "x") (var "y") (var "z") (TmVar (var "y"))),
        semTest (TmCatL TyInt (var "x") (var "y") (var "z") (TmVar (var "y"))) [("z",CatPB (LitPFull (LInt 3)) (LitPFull (LInt 4)))] (LitPFull (LInt 4)) (TmCut (var "x") TmEpsR $ TmVar (var "z")),

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

-- >>> evalSingle (TmFix _)
-- >>> evalSingle (TmCatL TyInt (var "x") (var "y") (var "z") (TmVar (var "x"))) [("z",CatPA LitPEmp)]
-- Found hole: _ :: Ctx Var
-- In the first argument of `TmFix', namely `_'
-- In the first argument of `evalSingle', namely `(TmFix _)'
-- In the expression: evalSingle (TmFix _)
-- Relevant bindings include
--   it_a71b6 :: [(String, Prefix)] -> Either SemError (Prefix, Term)
--     (bound at /Users/jwc/Documents/research/Creek/src/Semantics.hs:222:2)
-- Valid refinement hole fits include
--   head _
--   minimum _
--   last _
--   maximum _
--   id _
--   ask _
--   runIdentity _
-- Couldn't match expected type `Term'
--             with actual type `Ty -> Term -> Term'
-- Probable cause: `TmFix' is applied to too few arguments
-- In the first argument of `evalSingle', namely `(TmFix _)'
-- In the expression: evalSingle (TmFix _)
-- In an equation for `it_a71b6': it_a71b6 = evalSingle (TmFix _)
