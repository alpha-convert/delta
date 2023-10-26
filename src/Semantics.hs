{-# LANGUAGE FlexibleContexts, BangPatterns, FlexibleInstances #-}
module Semantics where

import qualified CoreSyntax as Core
import qualified Data.Map as M
import Control.Monad.Reader
    ( Monad(return), sequence, MonadReader(ask, local), ReaderT (runReaderT), guard )
import Control.Monad.Identity (Identity (runIdentity))
import Control.Monad.Except ( ExceptT, runExceptT, MonadError(throwError) )
import Prelude
import Types (emptyPrefix, Ty (..), Ctx, ValueLike (..))
import Values (Prefix (..), Env, isMaximal, bindAllEnv, bindEnv, bindAllEnv, lookupEnv, prefixConcat, concatEnv)
import Data.Map (Map, unionWith)
import Control.Applicative (Applicative(liftA2))
import Control.Monad.State (runStateT, StateT, modify', gets, get, lift)
import Util.PrettyPrint (PrettyPrint (pp))

import qualified Var (Var(..))
import Frontend.Typecheck (doCheckCoreTm)

data SemError =
      VarLookupFailed Var.Var
    | NotCatPrefix Var.Var Prefix
    | NotPlusPrefix Var.Var Prefix
    | ConcatError Prefix Prefix
    | RuntimeCutError Var.Var Core.Term Core.Term
    | SinkError Var.Var Prefix

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

eval :: (EvalM m) => Core.Term -> m (Prefix,Core.Term)
eval (Core.TmLitR v) = return (LitPFull v,Core.TmEpsR)

eval Core.TmEpsR = return (LitPEmp,Core.TmEpsR)

eval (Core.TmVar x) = do
    p <- lookupVar x
    return (p, Core.TmVar x)

eval (Core.TmCatL t x y z e) = do
    p <- lookupVar z
    case p of
        CatPA p1 -> do
            (p',e') <- withEnv (bindAllEnv [(x,p1),(y,emptyPrefix t)]) (eval e)
            return (p',Core.TmCatL t x y z e')
        CatPB p1 p2 -> do
            (p',e') <- withEnv (bindAllEnv [(x,p1),(y,p2)]) (eval e)
            let e'' = Core.substVar e' z y
            sink <- reThrow (SinkError x) (Core.sinkTm p1)
            e''' <- reThrow handleRuntimeCutError (Core.cut x sink e'')
            return (p', e''')
        _ -> throwError (NotCatPrefix z p)

eval (Core.TmCatR e1 e2) = do
    (p,e1') <- eval e1
    if not (isMaximal p) then
        return (CatPA p, Core.TmCatR e1' e2)
    else do
        (p',e2') <- eval e2
        return (CatPB p p',e2')

eval (Core.TmInl e) = do
    (p,e') <- eval e
    return (SumPA p, e')

eval (Core.TmInr e) = do
    (p,e') <- eval e
    return (SumPB p, e')

eval (Core.TmPlusCase rho' r z x e1 y e2) = do
    withEnvM (reThrow (uncurry ConcatError) . concatEnv rho') $ do
        p <- lookupVar z
        (case p of
            SumPEmp -> do
                rho'' <- ask
                return (emptyPrefix r, Core.TmPlusCase rho'' r z x e1 y e2)
            SumPA p' -> do
                (p'',e1') <- withEnv (bindEnv x p') (eval e1)
                return (p'', Core.substVar e1' z x)
            SumPB p' -> do
                (p'',e2') <- withEnv (bindEnv y p') (eval e2)
                return (p'', Core.substVar e2' z y)
            _ -> throwError (NotPlusPrefix z p))

eval Core.TmNil = return (StpDone,Core.TmEpsR)

eval (Core.TmCons e1 e2) = do
    (p,e1') <- eval e1
    if not (isMaximal p) then
        return (StpA p, Core.TmCatR e1' e2)
    else do
        (p',e2') <- eval e2
        return (StpB p p',e2')

eval (Core.TmStarCase rho' r s z e1 x xs e2) = do
    withEnvM (reThrow (uncurry ConcatError) . concatEnv rho') $ do
        p <- lookupVar z
        (case p of
            StpEmp -> do
                rho'' <- ask
                return (emptyPrefix r, Core.TmStarCase rho'' r s z e1 x xs e2)
            StpDone -> eval e1
            StpA p' -> do
                (p'',e2') <- withEnv (bindAllEnv [(x,p'),(xs,StpEmp)]) (eval e2)
                return (p'', Core.TmCatL (TyStar s) x xs z e2')
            StpB p1 p2 -> do
                (p'',e2') <- withEnv (bindAllEnv [(x,p1),(xs,p2)]) (eval e2)
                sink <- reThrow (SinkError x) (Core.sinkTm p1)
                e2'' <- reThrow handleRuntimeCutError (Core.cut x sink e2')
                return (p'', Core.substVar e2'' z xs)
            _ -> throwError (NotPlusPrefix z p))

handleRuntimeCutError :: (Var.Var, Core.Term, Core.Term) -> SemError
handleRuntimeCutError (x,e,e') = RuntimeCutError x e e'


type TopLevel = M.Map String (Core.Term, Ctx Var.Var, Ty)

doRunPgm :: Core.Program -> IO ()
doRunPgm p = do
    !_ <- runStateT (mapM go p) M.empty
    return ()
    where
        go :: Either Core.FunDef Core.RunCmd -> StateT TopLevel IO ()
        go (Left (Core.FD f g s e)) = modify' (M.insert f (e,g,s))
        go (Right (Core.RC f rho)) = do
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
                                        -- () <- doCheckCoreTm g' s' e'
                                        return ()
                                    Left err -> error $ "Runtime Error: " ++ pp err
                Nothing -> error ("Runtime Error: Tried to execute unbound function " ++ f)