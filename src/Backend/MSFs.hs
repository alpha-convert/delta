{-# LANGUAGE TupleSections, FlexibleContexts #-}
module Backend.MSFs where

import Data.MonadicStreamFunction
import qualified Var
import Values
import CoreSyntax
import Types
import Control.Monad.Except (MonadError, throwError, runExceptT)
import Backend.SemError
import Control.Monad.Trans.MSF.Except (dSwitch, switch)
import qualified HistPgm as Hist
import Data.MonadicStreamFunction.Parallel ((&|&))
import Control.Monad.Identity (runIdentity)


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

concatEnvM e rho' rho = reThrow (handleConcatError e) (concatEnv rho' rho)

msfLookupEnv :: (MonadError SemError m) => Var.Var -> MSF m (Env Var.Var Prefix) Prefix
msfLookupEnv x = arrM (maybe (throwError (VarLookupFailed x)) return . lookupEnv x)

msfBindEnv :: (Monad m) => Var.Var -> Prefix -> MSF m (Env Var.Var Prefix) (Env Var.Var Prefix)
msfBindEnv x p = arrM (return . bindEnv x p)

msfUnionEnv :: (MonadError SemError m) => MSF m (Env Var.Var Prefix, Env Var.Var Prefix) (Env Var.Var Prefix)
msfUnionEnv = arrM (reThrow (\(x,p,p') -> UnionEnvError x p p') . uncurry unionDisjointEnv)

denote :: (MonadError SemError m) => Term -> MSF m (Env Var.Var Prefix) Prefix
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
denote e@(TmIte _ rho' t z e1 e2) = bufferUntil (concatEnvM e) boolLit rho' (emptyPrefix t) go
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

denote e@(TmPlusCase _ rho' t z x e1 y e2) = bufferUntil (concatEnvM e) nonEmptyPlus rho' (emptyPrefix t) go
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


