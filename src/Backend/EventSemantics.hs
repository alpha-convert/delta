{-# LANGUAGE FlexibleInstances, FlexibleContexts, Arrows #-}
module Backend.EventSemantics where
import Event (TaggedEvent(..), Event(..), isMaximal, maximalLift)

import CoreSyntax
import Buffer
import Values
import qualified HistPgm as Hist
import Types (Ty,TyF(TyStar), deriv, ValueLikeErr (IllTyped), CtxStruct, Ctx)
import Util.ErrUtil
import Control.Monad.Except (MonadError (throwError))
import Data.Maybe (mapMaybe, maybeToList)
import Data.Either
import qualified Var
import Data.MonadicStreamFunction
import Util.MSFUtil
import Control.Monad.Trans.MSF.Except (switch, dSwitch)
import Util.Shuffle


tagWith :: Var -> Event -> TaggedEvent
tagWith = TE

isTaggedFor :: TaggedEvent -> Var -> Maybe Event
(TE y ev) `isTaggedFor` x = if x == y then Just ev else Nothing

type EventBuf = [TaggedEvent]

instance Buffer EventBuf where
    rebindBuf = undefined
    unbindBuf x = snd . bufferPartition x
    emptyBufOfType _ = return []
    emptyBuf = []

bufferAt :: Var -> EventBuf -> [Event]
bufferAt x = mapMaybe (`isTaggedFor` x)

{-Split a buffer into the events tagged for a variable, and the rest.-}
bufferPartition :: Var -> EventBuf -> ([Event],EventBuf)
bufferPartition x = partitionEithers . map untag
    where
        untag tev@(TE y ev) = if x == y then Left ev else Right tev
    

data SemError =
      NotCatEv Var.Var Event
    | NotParEv Var.Var Event
    | NotPlusEv Var.Var Event
    | NotStarEv Var.Var Event
    | NotBoolEv Var.Var Event
    | IllTypedEvents [Event] Ty (Term EventBuf)
    | MaximalPrefixSubstErr Var.Var Ty Values.MaximalPrefix (Term EventBuf)
    | NonMatchingArgs (Ctx Var.Var Ty) (CtxStruct (Term EventBuf))
    | HistSemErr Hist.Term Hist.SemErr 


handleValueLikeErr :: Term EventBuf -> Types.ValueLikeErr [Event] Ty -> SemError
handleValueLikeErr e (IllTyped evs t) = IllTypedEvents evs t e

handlePrefixSubstError :: (Var.Var,Ty,Values.MaximalPrefix, Term EventBuf) -> SemError
handlePrefixSubstError (x,s,p,e) = MaximalPrefixSubstErr x s p e

eval :: (MonadError SemError m, MonadShuffle m) => Term EventBuf -> TaggedEvent -> m ([Event], Term EventBuf)
eval TmEpsR _ = return ([],TmEpsR)
eval (TmLitR v) _ = return ([LitEv v],TmEpsR)
eval (TmVar x) tev =
    case tev `isTaggedFor` x of
        Just ev -> return ([ev],TmVar x)
        Nothing -> return ([], TmVar x)

eval (TmCatL t x y z e) tev =
    case tev `isTaggedFor` z of
        Nothing -> do
            (evs,e') <- eval e tev
            return (evs,TmCatL t x y z e')
        Just (CatEvA ev) -> do
            (evs,e') <- eval e (tagWith x ev)
            return (evs,TmCatL t x y z e')
        Just CatPunc -> do
            let e' = substVar e z y
            sink <- undefined
            return ([], TmCut x sink e')
        Just ev -> throwError (NotCatEv z ev)


eval e@(TmCatR s e1 e2) tev = do
    (evs,e1') <- eval e1 tev
    if Event.isMaximal s evs then
        return (CatEvA <$> evs ++ [CatPunc],e2)
    else do
        s' <- reThrow (handleValueLikeErr e) (deriv evs s)
        return (CatEvA <$> evs, TmCatR s' e1' e2)

eval (TmParL x y z e) tev = do
    tev' <- case tev `isTaggedFor` z of
                 Nothing -> return tev
                 Just (ParEvA ev) -> return (tagWith x ev)
                 Just (ParEvB ev) -> return (tagWith y ev)
                 Just ev -> throwError (NotParEv z ev)
    (evs,e') <- eval e tev'
    return (evs, TmParL x y z e')

eval (TmParR e1 e2) ev = do
    (evs1,e1') <- eval e1 ev
    (evs2,e2') <- eval e2 ev
    evs <- shuffleM (fmap ParEvA evs1) (fmap ParEvB evs2)
    return (evs, TmParR e1' e2')

eval (TmCut x e1 e2) ev = do
    (evs,e1') <- eval e1 ev
    (evs_out,e2') <- evalMany e2 (tagWith x <$> evs)
    return (evs_out, TmCut x e1' e2')

eval (TmInl e) ev = do
    (evs,e') <- eval e ev
    return (PlusPuncA : evs,e')

eval (TmInr e) ev = do
    (evs,e') <- eval e ev
    return (PlusPuncB : evs,e')

-- I'm not sure that the environment and event semantics agree: The environment
-- semantics is a bit more eager: Consider the case where the first thing we get
-- is (SumPA emp). In the environment semantics, this *runs* the first branch,
-- potentially emitting constants. In the event semantics, this just steps to
-- the first branch without running it (the buf is empty.)
eval (TmPlusCase buf r z x e1 y e2) tev =
    case tev `isTaggedFor` z of
        Nothing -> return ([], TmPlusCase (buf ++ [tev]) r z x e1 y e2)
        Just PlusPuncA -> evalMany (substVar e1 z x) buf -- ????
        Just PlusPuncB -> evalMany (substVar e2 z y) buf -- ???
        Just ev -> throwError (NotPlusEv z ev)


eval TmNil _ = return ([PlusPuncA],TmEpsR)
eval e@(TmCons s e1 e2) tev = do
    (evs,e1') <- eval e1 tev
    if Event.isMaximal s evs then
        return (PlusPuncB : (CatEvA <$> evs ++ [CatPunc]),e2)
    else do
        s' <- reThrow (handleValueLikeErr e) (deriv evs s)
        return (PlusPuncB : (CatEvA <$> evs), TmCatR s' e1' e2)

eval (TmStarCase buf r s z e1 x xs e2) tev =
    case tev `isTaggedFor` z of
        Nothing -> return ([], TmStarCase (buf ++ [tev]) r s z e1 x xs e2)
        Just PlusPuncA -> evalMany e1 buf
        Just PlusPuncB -> evalMany (TmCatL (TyStar s) x xs z e2) buf
        Just ev -> throwError (NotStarEv z ev)

eval (TmIte buf t z e1 e2) tev =
    case tev `isTaggedFor` z of
        Nothing -> return ([], TmIte (buf ++ [tev]) t z e1 e2)
        Just (LitEv (LBool True)) -> evalMany (TmCut z TmEpsR e1) buf
        Just (LitEv (LBool False)) -> evalMany (TmCut z TmEpsR e2) buf
        Just ev -> throwError (NotBoolEv z ev)

eval (TmFix args g s e) tev = do
    e' <- reThrow (uncurry NonMatchingArgs)  (cutArgs g args (fixSubst g s e e))
    eval e' tev

eval (TmRec {}) _ = error "Impossible."

eval (TmWait buf r s x e) tev =
    let buf' = buf ++ [tev] in
    let (bx,brest) = bufferPartition x buf' in
    case Event.maximalLift s bx of
        Nothing -> return ([], TmWait buf' r s x e)
        Just p -> do
            e' <- reThrow handlePrefixSubstError $ maximalPrefixSubst s p x e
            evalMany e' brest


eval (TmHistPgm s he) _ = do
    evs <- reThrow (HistSemErr he) (Hist.eval he >>= Hist.valueToEventList s)
    return (evs,undefined)

evalMany :: (MonadError SemError m, MonadShuffle m) => Term EventBuf -> [TaggedEvent] -> m ([Event], Term EventBuf)
evalMany e [] = return ([],e)
evalMany e (ev:evs_in) = do
    (evs_out,e') <- eval e ev
    (evs_out',e'') <- evalMany e' evs_in
    return (evs_out ++ evs_out',e'')

msfDeriv :: MonadError SemError m => MSF m ([Event],Ty) Ty
msfDeriv = undefined

denote :: (MonadError SemError m, MonadShuffle m) => Term EventBuf -> MSF m TaggedEvent [Event]
denote (TmLitR v) = arr (const [LitEv v]) `dThen` denote TmEpsR
denote TmEpsR = arr (const [])
denote (TmVar x) = arr (maybeToList . (`isTaggedFor` x))
denote (TmCatR s e1 e2) = dSwitch (feedback s ((denote e1 *** returnA) >>> (maximalCheck &&& msfDeriv))) (const (denote e2))
    where
        maximalCheck = arrM $ \(evs,s') ->
            if Event.isMaximal s' evs then
                return (CatEvA <$> evs ++ [CatPunc], Just ())
            else
                return (CatEvA <$> evs, Nothing)

denote (TmCatL t x y z e) = undefined

-- eval (TmCatL t x y z e) tev =
--     case tev `isTaggedFor` z of
--         Nothing -> do
--             (evs,e') <- eval e tev
--             return (evs,TmCatL t x y z e')
--         Just (CatEvA ev) -> do
--             (evs,e') <- eval e (tagWith x ev)
--             return (evs,TmCatL t x y z e')
--         Just CatPunc -> do
--             let e' = substVar e z y
--             sink <- undefined
--             return ([], TmCut x sink e')
--         Just ev -> throwError (NotCatEv z ev)

denote (TmParL x y z e) = arrM reTag >>> denote e
    where
        reTag tev =
           case tev `isTaggedFor` z of
             Nothing -> return tev
             Just (ParEvA ev) -> return (tagWith x ev)
             Just (ParEvB ev) -> return (tagWith y ev)
             Just ev -> throwError (NotParEv z ev)

denote (TmParR e1 e2) = (denote e1 &&& denote e2) >>> (arr (fmap ParEvA) *** arr (fmap ParEvB)) >>> arrM (uncurry shuffleM)

denote (TmInl e) = applyToFirst id (PlusPuncA:) (denote e)
denote (TmInr e) = applyToFirst id (PlusPuncB:) (denote e)

denote (TmPlusCase {}) = undefined
denote (TmIte {}) = undefined
denote TmNil = arr (const [PlusPuncA]) `dThen` denote TmEpsR

denote _ = undefined