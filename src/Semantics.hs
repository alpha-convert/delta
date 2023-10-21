{-# LANGUAGE FlexibleContexts #-}
module Semantics where

import qualified CoreSyntax as Core
import qualified Data.Map as M
import Control.Monad.Reader
import Control.Monad.Identity ()
import Control.Monad.Except
import Prelude
import Types
import Values (Prefix (..), Env (..), isMaximal, bindAll, emptyPrefix, bind)
import Data.Map (Map, unionWith)
import Control.Applicative (Applicative(liftA2))

data SemError = VarLookupFailed Core.Var | NotCatPrefix Prefix | NotPlusPrefix Prefix | ConcatError Prefix Prefix

class (MonadReader (Env Core.Var) m, MonadError SemError m) => EvalM m where

withEnv :: (EvalM m) => (Env Core.Var -> Env Core.Var) -> m a -> m a
withEnv = local

withEnvM :: (EvalM m) => (Env Core.Var -> m (Env Core.Var)) -> m a -> m a
withEnvM f m = do
    e <- ask
    e' <- f e
    local (const e') m

prefixConcat :: (EvalM m) => Prefix -> Prefix -> m Prefix
prefixConcat LitPEmp LitPEmp = return LitPEmp
prefixConcat LitPEmp (LitPFull l) = return (LitPFull l)
prefixConcat (LitPFull l) EpsP = return (LitPFull l)
prefixConcat EpsP EpsP = return EpsP
prefixConcat (CatPA p) (CatPA p') = CatPA <$> prefixConcat p p'
prefixConcat (CatPA p) (CatPB p1 p2) = do
    p1' <- prefixConcat p p1
    return (CatPB p1' p2)
prefixConcat (CatPB p1 p2) p = do
    p2' <- prefixConcat p2 p
    return (CatPB p1 p2')
prefixConcat SumPEmp SumPEmp = return SumPEmp
prefixConcat SumPEmp (SumPA p) = return (SumPA p)
prefixConcat SumPEmp (SumPB p) = return (SumPB p)
prefixConcat (SumPA p) p' = SumPA <$> prefixConcat p p'
prefixConcat (SumPB p) p' = SumPB <$> prefixConcat p p'
prefixConcat p p' = throwError (ConcatError p p')

unionWithM :: (Monad m, Ord k) => (v -> v -> m v) -> Map k v -> Map k v -> m (Map k v)
unionWithM f m m' = sequence (unionWith (bindM2 f) (return <$> m) (return <$> m'))
    where
        bindM2 g a b = do {x <- a; y <- b; g x y}

envConcat :: (EvalM m) => Env Core.Var -> Env Core.Var -> m (Env Core.Var)
envConcat (Env m1) (Env m2) = Env <$> unionWithM prefixConcat m1 m2


lookupVar :: (EvalM m) => Core.Var -> m Prefix
lookupVar x = do
    (Env m) <- ask
    case M.lookup x m of
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
            (p',e') <- withEnv (bindAll [(x,p1),(y,emptyPrefix t)]) (eval e)
            return (p',Core.TmCatL t x y z e')
        CatPB p1 p2 -> do
            (p',e') <- withEnv (bindAll [(x,p1),(y,p2)]) (eval e)
            return (p', Core.substVar e' z y)
        _ -> throwError (NotCatPrefix p)

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
    withEnvM (envConcat rho') $ do
        p <- lookupVar z
        (case p of
            SumPEmp -> do
                rho'' <- ask
                return (emptyPrefix r, Core.TmPlusCase rho'' r z x e1 y e2)
            SumPA p' -> do
                (p'',e1') <- withEnv (bind x p') (eval e1)
                return (p'', Core.substVar e1' z x)
            SumPB p' -> do
                (p'',e2') <- withEnv (bind y p') (eval e2)
                return (p'', Core.substVar e2' z y)
            _ -> throwError (NotPlusPrefix p))