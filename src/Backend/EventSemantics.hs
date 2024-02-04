{-# LANGUAGE FlexibleInstances, FlexibleContexts, Arrows, TupleSections #-}
{-# LANGUAGE LambdaCase, BangPatterns #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
module Backend.EventSemantics where
import Event (TaggedEvent(..), Event(..), isMaximal, maximalLift)

import CoreSyntax
import Buffer
import Values
import qualified HistPgm as Hist
import Types (Ty,TyF(TyStar), deriv, ValueLikeErr (IllTyped), CtxStruct, Ctx)
import Util.ErrUtil
import Control.Monad.Except (MonadError (throwError), runExceptT, ExceptT (ExceptT))
import Data.Maybe (mapMaybe, maybeToList)
import Data.Either
import qualified Var
import Data.MonadicStreamFunction
import Util.MSFUtil
import Control.Monad.Trans.MSF.Except (switch, dSwitch)
import Util.Shuffle
import Data.MonadicStreamFunction.InternalCore
import Control.Monad.Random (runRandT,runRand, MonadRandom, weighted)
import Control.Monad.IO.Class (MonadIO)
import qualified Data.Functor
import qualified Debug.Trace as Debug
import Data.List (intercalate)

tagSubst :: Var -> Var -> TaggedEvent -> TaggedEvent
tagSubst x y (TE z ev) | z == y = TE x ev
tagSubst _ _ tev       | otherwise = tev

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
    | IllTypedEvents [Event] Ty
    | MaximalPrefixSubstErr Var.Var Ty Values.MaximalPrefix (Term EventBuf)
    | NonMatchingArgs (Ctx Var.Var Ty) (CtxStruct (Term EventBuf))
    | HistSemErr Hist.Term Hist.SemErr
    deriving (Eq,Ord,Show)


handleValueLikeErr :: Types.ValueLikeErr [Event] Ty -> SemError
handleValueLikeErr (IllTyped evs t) = IllTypedEvents evs t

handlePrefixSubstError :: (Var.Var,Ty,Values.MaximalPrefix, Term EventBuf) -> SemError
handlePrefixSubstError (x,s,p,e) = MaximalPrefixSubstErr x s p e

poke :: (MonadError SemError m, MonadShuffle m) => Term EventBuf -> m ([Event], Term EventBuf)
poke TmEpsR = return ([], TmEpsR)
poke (TmLitR v) = return ([LitEv v], TmEpsR)
poke (TmVar x) = return ([], TmVar x)
poke (TmCatL t x y z e) = do
    (evs,e') <- poke e
    return (evs, TmCatL t x y z e')
poke e@(TmCatR s e1 e2) = do
    (evs,e1') <- poke e1
    if Event.isMaximal s evs then do
        (evs', e2') <- poke e2
        return (fmap CatEvA evs ++ [CatPunc] ++ evs',e2')
    else do
        s' <- reThrow handleValueLikeErr (deriv evs s)
        return (CatEvA <$> evs, TmCatR s' e1' e2)
poke (TmParR e1 e2) = do
    (evs1,e1') <- poke e1
    (evs2,e2') <- poke e2
    evs <- shuffleM (fmap ParEvA evs1) (fmap ParEvB evs2)
    return (evs, TmParR e1' e2')
poke (TmParL x y z e) = do
    (evs,e') <- poke e
    return (evs, TmParL x y z e')
poke (TmInl e) = do
    (evs,e') <- poke e
    return (PlusPuncA : evs,e')
poke (TmInr e) = do
    (evs,e') <- poke e
    return (PlusPuncB : evs,e')
poke e@(TmPlusCase {}) = return ([], e)
poke e@(TmIte {}) = return ([],e)
poke TmNil = return ([PlusPuncA],TmEpsR)
poke (TmCons s e1 e2) = do
    (evs,e1') <- poke e1
    if Event.isMaximal s evs then do
        (evs', e2') <- poke e2
        return (PlusPuncB : fmap CatEvA evs ++ [CatPunc] ++ evs',e2')
    else do
        s' <- reThrow handleValueLikeErr (deriv evs s)
        return (PlusPuncB : fmap CatEvA evs, TmCatR s' e1' e2)
poke e@(TmStarCase {}) = return ([],e)
{- UHHHHHHHHHHHHHHH is this allowed -}
poke (TmFix args g s e) = do
    e' <- reThrow (uncurry NonMatchingArgs)  (cutArgs g args (fixSubst g s e e))
    poke e'
-- poke e@(TmFix {}) = return([],e)
poke (TmRec {}) = error "impossible"
poke e@(TmWait {}) = return ([],e)
poke (TmCut x e1 e2) = do
    (evs,e1') <- poke e1
    (evs',e2') <- evalMany e2 (tagWith x <$> evs)
    return (evs', TmCut x e1' e2')
poke (TmHistPgm s he) = do
    evs <- reThrow (HistSemErr he) (Hist.eval he >>= Hist.valueToEventList s)
    return (evs,TmEpsR)

poke (TmArgsCut {}) = undefined


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
            return ([], TmCut x TmEpsR e')
        Just ev -> throwError (NotCatEv z ev)


eval e@(TmCatR s e1 e2) tev = do
    (evs,e1') <- eval e1 tev
    if Event.isMaximal s evs then
        return (fmap CatEvA evs ++ [CatPunc],e2)
    else do
        s' <- reThrow handleValueLikeErr (deriv evs s)
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

{-
BUG!!! This isn't equivalent to the prefix semantics!  If e1 outputs nothing,
then e2 doesn't get run, by the defn of evalMany. The whole event semantics is irreperably broken.
-}
eval (TmCut x e1 e2) tev = do
    (evs,e1') <- eval e1 tev
    (evs_out,e2') <- evalMany e2 (tev : (tagWith x <$> evs))
    return (evs_out, TmCut x e1' e2')

eval (TmInl e) ev = do
    (evs,e') <- eval e ev
    return (PlusPuncA : evs,e')

eval (TmInr e) ev = do
    (evs,e') <- eval e ev
    return (PlusPuncB : evs,e')

eval (TmPlusCase buf r z x e1 y e2) tev =
    case tev `isTaggedFor` z of
        Nothing -> return ([], TmPlusCase (buf ++ [tev]) r z x e1 y e2)
        Just PlusPuncA -> evalMany (substVar e1 z x) buf
        Just PlusPuncB -> evalMany (substVar e2 z y) buf
        Just ev -> throwError (NotPlusEv z ev)


eval TmNil _ = return ([PlusPuncA],TmEpsR)
eval e@(TmCons s e1 e2) tev = do
    (evs,e1') <- eval e1 tev
    if Event.isMaximal s evs then
        return (PlusPuncB : (fmap CatEvA evs ++ [CatPunc]),e2)
    else do
        s' <- reThrow handleValueLikeErr (deriv evs s)
        return (PlusPuncB : fmap CatEvA evs, TmCatR s' e1' e2)

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
    !() <- Debug.trace ("**Running: " ++ show e' ++ " with tev: " ++ show tev) (return ())
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
    return (evs,TmEpsR) -- This isn't type safe, but it's semantically typesafe... TmEpsR never emits anything.

eval (TmArgsCut {}) _ = error "unimplemented"

evalMany :: (MonadError SemError m, MonadShuffle m) => Term EventBuf -> [TaggedEvent] -> m ([Event], Term EventBuf)
evalMany e [] = poke e
evalMany e (ev:evs_in) = do
    (evs_out,e') <- eval e ev
    (evs_out',e'') <- evalMany e' evs_in
    return (evs_out ++ evs_out',e'')


doEvalMany ::  Term EventBuf -> [TaggedEvent] -> IO [Event]
doEvalMany e evts = do
    reThrowIO (evalMany e evts :: ExceptT SemError IO ([Event], Term EventBuf)) Data.Functor.<&> fst


msfDeriv :: MonadError SemError m => MSF m ([Event],Ty) Ty
msfDeriv = arrM (uncurry go)
    where
        go evs t = reThrow handleValueLikeErr (deriv evs t)

msfIterate :: (Monad m) => MSF m a [b] -> MSF m [a] [b]
msfIterate f = MSF $ \case
                        [] -> return ([], msfIterate f)
                        y:ys -> do
                            (bs,f') <- unMSF f y
                            (bs',f'') <- unMSF (msfIterate f') ys
                            return (bs ++ bs', f'')

-- msfCatchUp xs f runs f on xs at the first step (ignoring the first input), then continues to behave normally after.
msfCatchUp :: (Monad m) => [a] -> MSF m a [b] -> MSF m a [b]
msfCatchUp xs f = (arr (const xs) `dThen` arr pure) >>> msfIterate f

--

bufferUntil :: (Monad m) => ([a] -> a -> m (Maybe c)) -> (c -> MSF m a [b]) -> MSF m a [b]
bufferUntil p m = switch (feedback [] (arrM acc)) (\(c,buf) -> msfCatchUp buf (m c))
    where
        acc (ev,buf) = do
            let buf' = buf ++ [ev]
            mc <- p buf ev
            return (([],(,buf) <$> mc),buf')

catSwitch :: (MonadError SemError m) => Ty -> MSF m TaggedEvent [Event] -> MSF m TaggedEvent [Event] -> MSF m TaggedEvent [Event]
catSwitch s m1 m2 = dSwitch (feedback s ((m1 *** returnA) >>> (maximalCheck &&& msfDeriv))) (const m2)
    where
        maximalCheck = arrM $ \(evs,s') ->
                if Event.isMaximal s' evs then
                    return (fmap CatEvA evs ++ [CatPunc], Just ())
                else
                    return (fmap CatEvA evs, Nothing)

denote :: (MonadError SemError m, MonadShuffle m) => Term EventBuf -> MSF m TaggedEvent [Event]
denote (TmLitR v) = arr (const [LitEv v]) `dThen` denote TmEpsR
denote TmEpsR = arr (const [])
denote (TmVar x) = arr (maybeToList . (`isTaggedFor` x))
denote (TmCatR s e1 e2) = catSwitch s (denote e1) (denote e2)

denote (TmCatL _ x y z e) = foo >>> denote e
    where
        foo = dSwitch (arrM f) (const (arr (tagSubst y z)))
        f tev = case tev `isTaggedFor` z of
                  Nothing -> return (tev,Nothing)
                  Just (CatEvA ev) -> return (tagWith x ev,Nothing)
                  Just CatPunc -> return (tev,Just ())
                  Just ev -> throwError (NotCatEv z ev)


denote (TmParL x y z e) = arrM go >>> denote e
    where
        go tev =
           case tev `isTaggedFor` z of
             Nothing -> return tev
             Just (ParEvA ev) -> return (tagWith x ev)
             Just (ParEvB ev) -> return (tagWith y ev)
             Just ev -> throwError (NotParEv z ev)

denote (TmParR e1 e2) = ((denote e1 >>> arr (fmap ParEvA)) &&& (denote e2 >>> arr (fmap ParEvB))) >>> arrM (uncurry shuffleM)-- (arr (fmap ParEvA) *** arr (fmap ParEvB)) >>> arrM (uncurry shuffleM)

denote (TmInl e) = applyToFirst id (PlusPuncA:) (denote e)
denote (TmInr e) = applyToFirst id (PlusPuncB:) (denote e)

denote (TmPlusCase _ _ z x e1 y e2) = bufferUntil isPunc go
    where
        isPunc _ tev = case tev `isTaggedFor` z of
                         Nothing -> return Nothing
                         Just PlusPuncA -> return (Just (Left ()))
                         Just PlusPuncB -> return (Just (Right ()))
                         Just ev -> throwError (NotCatEv z ev)
        go (Left _) = arr (tagSubst x z) >>> denote e1
        go (Right _) = arr (tagSubst y z) >>> denote e2

denote (TmIte _ _ z e1 e2) = bufferUntil isBool go
    where
        isBool _ tev = case tev `isTaggedFor` z of
                         Nothing -> return Nothing
                         Just (LitEv (LBool b)) -> return (Just b)
                         Just ev -> throwError (NotBoolEv z ev)
        go True = denote e1
        go False = denote e2

denote TmNil = arr (const [PlusPuncA]) `dThen` denote TmEpsR

-- denote e@(TmCatR s e1 e2) = dSwitch (feedback s ((denote e1 *** returnA) >>> (maximalCheck &&& msfDeriv e))) (const (denote e2))
--     where
--         maximalCheck = arrM $ \(evs,s') ->
--             if Event.isMaximal s' evs then
--                 return (CatEvA <$> evs ++ [CatPunc], Just ())
--             else
--                 return (CatEvA <$> evs, Nothing)

denote (TmCons s e1 e2) = applyToFirst id (PlusPuncB:) (catSwitch s (denote e1) (denote e2))

denote (TmStarCase _ _ s z e1 x xs e2) = bufferUntil isPunc go
    where
        isPunc _ tev = case tev `isTaggedFor` z of
                         Nothing -> return Nothing
                         Just PlusPuncA -> return (Just (Left ()))
                         Just PlusPuncB -> return (Just (Right ()))
                         Just ev -> throwError (NotPlusEv z ev)
        go (Left ()) = denote e1
        go (Right ()) = denote (TmCatL (TyStar s) x xs z e2)

denote (TmCut x e1 e2) = denote e1 >>> arr (tagWith x <$>) >>> msfIterate (denote e2)

denote (TmHistPgm t he) = undefined

denote (TmWait buf r s x e) = bufferUntil mLift undefined
    where
        mLift buf' tev =
            let buf'' = buf' ++ [tev] in
            let (bx,_) = bufferPartition x buf'' in
            case Event.maximalLift s bx of
                Nothing -> return Nothing
                Just mp -> return (Just mp)


denote (TmFix _ _ _ _) = undefined
denote (TmRec _) = undefined

denote (TmArgsCut {}) = undefined

-- denote (TmStar)

var = Var.Var

--- >>> runRand $ embed (denote (TmPlusCase [] undefined (var "z") (var "x") (TmVar (var "x")) (var "y") (TmVar (var "y")))) [TE (var "z") CatPunc]
-- Variable not in scope:
--   runExceptT :: m0_a1AuTE[tau:1] [[Event]] -> b_a1AuTC[sk:1]

-- E.denote (C.TmPlusCase [] undefined (var "z") (var "x") (C.TmVar (var "x")) (var "y") (C.TmVar (var "y")))
