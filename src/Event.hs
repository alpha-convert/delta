{-# LANGUAGE  MultiParamTypeClasses, FlexibleInstances #-}
module Event where

import Values (Lit(..), Prefix(..), MaximalPrefix (..), prefixConcat, Env, lookupEnv)
import Types ( TyF(..), Ty, TypeLike(..), ValueLike(..), ValueLikeErr(..), GenValueLike(..), emptyPrefix, Ctx, CtxStruct (..), CtxEntry (..))
import Control.Monad.Except(ExceptT, MonadError (..), withExceptT, MonadTrans (lift), runExceptT)
import Util.ErrUtil(guard, reThrow)
import Var (Var)
import Data.Maybe (isJust, mapMaybe)
import Data.Void (absurd)
import Data.Either (partitionEithers)
import Util.Shuffle
import Test.QuickCheck (forAll, quickCheck, Property, Gen, property, arbitrary, frequency, (===))
import Test.QuickCheck.Monadic (monadicIO)
import Control.Monad.Identity(runIdentity)

data Event =
      LitEv Lit
    | PlusPuncA
    | PlusPuncB
    | CatPunc
    | CatEvA Event
    | ParEvA Event
    | ParEvB Event
    deriving (Eq,Ord,Show)

data TaggedEvent = TE Var Event deriving (Eq,Ord,Show)

instance ValueLike Event Ty where
    hasType p t@TyEps = throwError (IllTyped p t)
    hasType _ (TyVar a) = absurd a

    hasType (LitEv (LInt _)) TyInt = return ()
    hasType p t@TyInt = throwError (IllTyped p t)

    hasType (LitEv (LBool _)) TyBool = return ()
    hasType p t@TyBool = throwError (IllTyped p t)

    hasType PlusPuncA (TyPlus _ _) = return ()
    hasType PlusPuncB (TyPlus _ _) = return ()
    hasType p t@(TyPlus _ _) = throwError (IllTyped p t)

    hasType p@CatPunc t@(TyCat s _) = guard (isNull s) (IllTyped p t)
    hasType (CatEvA x) (TyCat s _) = hasType x s
    hasType p t@(TyCat {}) = throwError (IllTyped p t)

    hasType (ParEvA x) (TyPar s _) = hasType x s
    hasType (ParEvB x) (TyPar _ t) = hasType x t
    hasType p t@(TyPar {}) = throwError (IllTyped p t)

    hasType PlusPuncA (TyStar _) = return ()
    hasType PlusPuncB (TyStar _) = return ()
    hasType p t@(TyStar _) = throwError (IllTyped p t)


    deriv p t@TyEps = throwError (IllTyped p t)
    deriv _ (TyVar a) = absurd a

    deriv (LitEv (LInt _)) TyInt = return TyEps
    deriv p t@TyInt = throwError (IllTyped p t)

    deriv (LitEv (LBool _)) TyBool = return TyEps
    deriv p t@TyBool = throwError (IllTyped p t)

    deriv PlusPuncA (TyPlus s _) = return s
    deriv PlusPuncB (TyPlus _ t) = return t
    deriv p t@(TyPlus {}) = throwError (IllTyped p t)

    deriv CatPunc (TyCat _ t) = return t

    deriv (CatEvA x) (TyCat s t) = do
        s' <- deriv x s
        return (TyCat s' t)
    deriv p t@(TyCat {}) = throwError (IllTyped p t)

    deriv (ParEvA x) (TyPar s t) = do
        s' <- deriv x s
        return (TyPar s' t)

    deriv (ParEvB x) (TyPar s t) = do
        t' <- deriv x t
        return (TyPar s t')
    deriv p t@(TyPar {}) = throwError (IllTyped p t)

    deriv PlusPuncA (TyStar _) = return TyEps
    deriv PlusPuncB (TyStar s) = return (TyCat s (TyStar s))
    deriv p t@(TyStar _) = throwError (IllTyped p t)

genMaximalEventsOfTy :: Ty -> Gen [Event]
genMaximalEventsOfTy TyEps = return []
genMaximalEventsOfTy TyInt = (:[]) . LitEv . LInt <$> arbitrary
genMaximalEventsOfTy TyBool = (:[]) . LitEv . LBool <$> arbitrary
genMaximalEventsOfTy (TyVar a) = absurd a
genMaximalEventsOfTy (TyCat s t) = do
    evs1 <- genMaximalEventsOfTy s
    evs2 <- genMaximalEventsOfTy t
    return $ fmap CatEvA evs1 ++ [CatPunc] ++ evs2
genMaximalEventsOfTy (TyPar s t) = do
    evs1 <- genMaximalEventsOfTy s
    evs2 <- genMaximalEventsOfTy t
    shuffleM (ParEvA <$> evs1) (ParEvB <$> evs2)
genMaximalEventsOfTy (TyPlus s t) = frequency [(1, (PlusPuncA:) <$> genMaximalEventsOfTy s), (1, (PlusPuncB:) <$> genMaximalEventsOfTy t)]
genMaximalEventsOfTy (TyStar s) = frequency [(1, return [PlusPuncA]), (2, (PlusPuncB:) <$> genMaximalEventsOfTy (TyCat s (TyStar s)))]


genEventsOfTy :: Ty -> Gen [Event]
genEventsOfTy TyEps = return []
genEventsOfTy TyInt = frequency [(1,return []),(2, genMaximalEventsOfTy TyInt)]
genEventsOfTy TyBool = frequency [(1,return []),(2, genMaximalEventsOfTy TyBool)]
genEventsOfTy (TyVar a) = absurd a
genEventsOfTy (TyCat s t) = do
    b <- frequency [(1, return True), (2, return False)]
    if b then do
        evs1 <- genMaximalEventsOfTy s
        evs2 <- genEventsOfTy t
        return $ fmap CatEvA evs1 ++ [CatPunc] ++ evs2
    else do
        evs <- genEventsOfTy s
        return $ fmap CatEvA evs
genEventsOfTy (TyPar s t) = do
    evs1 <- genEventsOfTy s
    evs2 <- genEventsOfTy t
    shuffleM (ParEvA <$> evs1) (ParEvB <$> evs2)
genEventsOfTy (TyPlus s t) = frequency [(1, (PlusPuncA:) <$> genEventsOfTy s), (1, (PlusPuncB:) <$> genEventsOfTy t)]
genEventsOfTy (TyStar s) = 
    frequency [
        (1,return [PlusPuncA]),
        (2, (PlusPuncB:) <$> genEventsOfTy (TyCat s (TyStar s)))
    ]

instance GenValueLike [Event] Ty where
    genOf = genEventsOfTy

-- prop_genOf_hasType :: Ty -> Property
-- prop_genOf_hasType t = forAll (genOf t :: Gen [Event]) $ \ev -> property (runIdentity (hasTypeB ev t))
-- t0' = quickCheck prop_genOf_hasType

promote xs = withExceptT (errCons xs)
errCons xs (IllTyped x t) = IllTyped (x:xs) t

instance ValueLike [Event] Ty where
    hasType [] _ = return ()
    hasType (x:xs) t = do
        promote xs (hasType x t)
        t' <- promote xs (deriv x t)
        hasType xs t'

    deriv [] s = return s
    deriv (x:xs) s = do
        s' <- promote xs (deriv x s)
        deriv xs s'

partitionPar :: [Event] -> Maybe ([Event], [Event])
partitionPar evs = partitionEithers <$> mapM go evs
    where
        go (ParEvA x) = Just (Left x)
        go (ParEvB x) = Just (Right x)
        go _ = Nothing

partitionCat [] = Nothing
partitionCat (CatPunc : evs) = Just ([],evs)
partitionCat (CatEvA x : evs) = do
    (evs1,evs2) <- partitionCat evs
    return (x:evs1,evs2)
partitionCat _ = Nothing


maximalLift :: Ty -> [Event] -> Maybe MaximalPrefix
maximalLift TyEps [] = Just EpsMP
maximalLift TyEps _ = Nothing
maximalLift TyInt [LitEv l@(LInt _)] = Just (LitMP l)
maximalLift TyInt _ = Nothing
maximalLift TyBool [LitEv l@(LBool _)] = Just (LitMP l)
maximalLift TyBool _ = Nothing
maximalLift (TyVar v) _ = absurd v
maximalLift (TyCat s t) evs = do
    (evs1,evs2) <- partitionCat evs
    p1 <- maximalLift s evs1
    p2 <- maximalLift t evs2
    return (CatMP p1 p2)
maximalLift (TyPar s t) evs = do
    (evs1,evs2) <- partitionPar evs
    p1 <- maximalLift s evs1
    p2 <- maximalLift t evs2
    return (ParMP p1 p2)
maximalLift (TyPlus s _) (PlusPuncA : evs) = SumMPA <$> maximalLift s evs
maximalLift (TyPlus _ t) (PlusPuncB : evs) = SumMPB <$> maximalLift t evs
maximalLift (TyPlus {}) _ = Nothing
maximalLift (TyStar s) evs = StMP <$> go evs
    where
        go [PlusPuncA] = Just []
        go (PlusPuncB:evs') = do
            (evs1,evs2) <- partitionCat evs'
            p1 <- maximalLift s evs1
            p2 <- go evs2
            return (p1:p2)
        go _ = Nothing


isMaximal :: Ty -> [Event] -> Bool
isMaximal t evs = isJust (maximalLift t evs)

prefixToEvents :: (MonadShuffle m) => Prefix -> m [Event]
prefixToEvents LitPEmp = return []
prefixToEvents (LitPFull l) = return [LitEv l]
prefixToEvents EpsP = return []
prefixToEvents (CatPA p) = fmap CatEvA <$> prefixToEvents p
prefixToEvents (CatPB p p') = do
    evs1 <- prefixToEvents p
    evs2 <- prefixToEvents p'
    return (fmap CatEvA evs1 ++ [CatPunc] ++ evs2)
prefixToEvents (ParP p p') = do
    evs1 <- prefixToEvents p
    evs2 <- prefixToEvents p'
    shuffleM (ParEvA <$> evs1) (ParEvB <$> evs2)
prefixToEvents SumPEmp = return []
prefixToEvents (SumPA p) = (PlusPuncA:) <$> prefixToEvents p
prefixToEvents (SumPB p) = (PlusPuncB:) <$> prefixToEvents p
prefixToEvents StpEmp = return []
prefixToEvents StpDone = return [PlusPuncA]
prefixToEvents (StpA p) = (PlusPuncB:) . fmap CatEvA <$> prefixToEvents p
prefixToEvents (StpB p p') = do
    evs1 <- prefixToEvents p
    evs2 <- prefixToEvents p'
    return $ PlusPuncB : (CatEvA <$> evs1) ++ (CatPunc : evs2)


p2e_correct :: Ty -> Property
p2e_correct t = forAll (genOf t) $ \p -> monadicIO $ do
    evs <- lift (prefixToEvents p)
    hasTypeB evs t

p2e_deriv :: Ty -> Property
p2e_deriv t = forAll (genOf t) $ \p -> monadicIO $ do
    evs <- lift (prefixToEvents p)
    t1 <- doDeriv p t
    t2 <- doDeriv evs t
    return (t1 === t2)

envToEvents :: (MonadShuffle m) => Ctx Var Ty -> Env Var Prefix -> ExceptT (ValueLikeErr (Ctx Var Ty) (Env Var Prefix)) m [TaggedEvent]
envToEvents EmpCtx rho = return []
envToEvents g@(SngCtx (CE x _)) rho =
    case lookupEnv x rho of
        Nothing -> throwError (IllTyped g rho)
        Just p -> fmap (TE x) <$> lift (prefixToEvents p)
envToEvents (CommaCtx g1 g2) rho = do
    evs1 <- envToEvents g1 rho
    evs2 <- envToEvents g2 rho
    lift (shuffleM evs1 evs2)
envToEvents (SemicCtx g1 g2) rho = do
    evs1 <- envToEvents g1 rho
    evs2 <- envToEvents g2 rho
    return (evs1 ++ evs2)


eventToPrefix :: (Monad m) => Ty -> Event -> ExceptT (ValueLikeErr Event Ty) m Prefix
eventToPrefix (TyVar a) _ = absurd a
eventToPrefix t@TyEps ev = throwError (IllTyped ev t)
eventToPrefix TyInt (LitEv l@(LInt _)) = return (LitPFull l)
eventToPrefix t@TyInt ev = throwError (IllTyped ev t)
eventToPrefix TyBool (LitEv l@(LBool _)) = return (LitPFull l)
eventToPrefix t@TyBool ev = throwError (IllTyped ev t)
eventToPrefix (TyCat s _) (CatEvA ev) = CatPA <$> eventToPrefix s ev
eventToPrefix t0@(TyCat s t) ev@CatPunc = do
    guard (isNull s) (IllTyped ev t0)
    return (CatPB (emptyPrefix s) (emptyPrefix t))
eventToPrefix t@(TyCat {}) ev = throwError (IllTyped ev t)
eventToPrefix (TyPar s t) (ParEvA ev) = do
    p <- eventToPrefix s ev
    return (ParP p (emptyPrefix t))
eventToPrefix (TyPar s t) (ParEvB ev) = do
    p <- eventToPrefix t ev
    return (ParP (emptyPrefix s) p)
eventToPrefix t@(TyPar {}) ev = throwError (IllTyped ev t)
eventToPrefix (TyPlus s _) PlusPuncA = return (SumPA (emptyPrefix s))
eventToPrefix (TyPlus _ t) PlusPuncB = return (SumPB (emptyPrefix t))
eventToPrefix t@(TyPlus {}) ev = throwError (IllTyped ev t)
eventToPrefix (TyStar _) PlusPuncA = return StpDone
eventToPrefix (TyStar s) PlusPuncB = return (StpA (emptyPrefix s))
eventToPrefix t@(TyStar _) ev = throwError (IllTyped ev t)

eventsToPrefix :: (Monad m) => Ty -> [Event] -> ExceptT (ValueLikeErr [Event] Ty) m Prefix
eventsToPrefix t [] = return (emptyPrefix t)
eventsToPrefix t (ev:evs) = do
    p <- promote evs (eventToPrefix t ev)
    t' <- promote evs (deriv ev t)
    p' <- eventsToPrefix t' evs
    reThrow (error . show) $ prefixConcat p p'

es2p_correct :: Ty -> Property
es2p_correct t = forAll (genOf t) $ \evs -> monadicIO $ do
    mp <- runExceptT (eventsToPrefix t evs)
    case mp of
        Left u -> error (show u)
        Right p -> hasTypeB p t
    
es2p_deriv :: Ty -> Property
es2p_deriv t = forAll (genOf t) $ \evs -> monadicIO $ do
    mp <- runExceptT (eventsToPrefix t evs)
    case mp of
        Left u -> error (show u)
        Right p -> do
            t1 <- doDeriv p t
            t2 <- doDeriv evs t
            return (t1 === t2)
