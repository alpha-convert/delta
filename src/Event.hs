{-# LANGUAGE  MultiParamTypeClasses, FlexibleInstances #-}
module Event where

import Values (Lit(..), Prefix(..), MaximalPrefix (..))
import Types ( TyF(..), Ty, TypeLike(..), ValueLike(..), ValueLikeErr(..))
import Control.Monad.Except(ExceptT, MonadError (..), withExceptT)
import Util.ErrUtil(guard)
import Var (Var)
import Data.Maybe (isJust, mapMaybe)
import Data.Void (absurd)

data Event =
      LitEv Lit
    | PlusPuncA
    | PlusPuncB
    | CatPunc
    | CatEvA Event
    | ParEvA Event
    | ParEvB Event

data TaggedEvent = TE Var Event

instance ValueLike Event Ty where
    hasType (LitEv (LInt _)) TyInt = return ()
    hasType p@(LitEv (LInt _)) t = throwError (IllTyped p t)

    hasType (LitEv (LBool _)) TyBool = return ()
    hasType p@(LitEv (LBool _)) t = throwError (IllTyped p t)

    hasType PlusPuncA (TyPlus _ _) = return ()
    hasType p@PlusPuncA t = throwError (IllTyped p t)
    hasType PlusPuncB (TyPlus _ _) = return ()
    hasType p@PlusPuncB t = throwError (IllTyped p t)

    hasType p@CatPunc t@(TyCat s _) = guard (isNull s) (IllTyped p t)
    hasType p@CatPunc t = throwError (IllTyped p t)

    hasType (CatEvA x) (TyCat s _) = hasType x s
    hasType p@(CatEvA _) t = throwError (IllTyped p t)

    hasType (ParEvA x) (TyPar s _) = hasType x s
    hasType p@(ParEvA _) t = throwError (IllTyped p t)

    hasType (ParEvB x) (TyPar _ t) = hasType x t
    hasType p@(ParEvB _) t = throwError (IllTyped p t)

    deriv (LitEv (LInt _)) TyInt = return TyEps
    deriv p@(LitEv (LInt _)) t = throwError (IllTyped p t)

    deriv (LitEv (LBool _)) TyInt = return TyEps
    deriv p@(LitEv (LBool _)) t = throwError (IllTyped p t)

    deriv PlusPuncA (TyPlus s _) = return s
    deriv p@PlusPuncA t = throwError (IllTyped p t)

    deriv PlusPuncB (TyPlus _ t) = return t
    deriv p@PlusPuncB t = throwError (IllTyped p t)

    deriv CatPunc (TyCat _ t) = return t
    deriv p@CatPunc t = throwError (IllTyped p t)

    deriv (CatEvA x) (TyCat s t) = do
        s' <- deriv x s
        return (TyCat s' t)
    deriv p@(CatEvA _) t = throwError (IllTyped p t)

    deriv (ParEvA x) (TyPar s t) = do
        s' <- deriv x s
        return (TyPar s' t)
    deriv p@(ParEvA _) t = throwError (IllTyped p t)

    deriv (ParEvB x) (TyPar s t) = do
        t' <- deriv x t
        return (TyPar s t')
    deriv p@(ParEvB _) t = throwError (IllTyped p t)

promote xs = withExceptT (errCons xs)
errCons xs (IllTyped x t) = IllTyped (x:xs) t

instance ValueLike [Event] Ty where
    hasType [] _ = return ()
    hasType (x:xs) t = promote xs (hasType x t) >> promote xs (deriv x t) >>= hasType xs

    deriv [] s = return s
    deriv (x:xs) s = do
        s' <- promote xs (deriv x s)
        deriv xs s'

partitionPar [] = return ([],[])
partitionPar (ev : evs) = do
    (evs1,evs2) <- partitionPar evs
    case ev of
        ParEvA x -> return (x:evs1,evs2)
        ParEvB x -> return (evs1,x:evs2)
        _ -> Nothing

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
        go (PlusPuncB:evs) = do
            (evs1,evs2) <- partitionCat evs
            p1 <- maximalLift s evs1
            p2 <- go evs2
            return (p1:p2)
        go _ = Nothing


isMaximal :: Ty -> [Event] -> Bool
isMaximal t evs = isJust (maximalLift t evs)