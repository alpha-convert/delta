{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
module Backend.EventSemantics where
import Event (TaggedEvent(..), Event(..))

import CoreSyntax
import Buffer
import Values
import qualified HistPgm as Hist
import Types (TyF(TyStar))
import Util.ErrUtil
import Control.Monad.Except (MonadError (throwError))


tagWith :: Var -> Event -> TaggedEvent
tagWith = TE

(TE y ev) `isTaggedFor` x = if x == y then Just ev else Nothing

type EventBuf = [TaggedEvent]

instance Buffer EventBuf where

data SemErr

eval :: (MonadError SemErr m) => Term EventBuf -> TaggedEvent -> m ([Event], Term EventBuf)
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
        Just _ -> throwError undefined
        

-- Maximality depends on the type!
eval (TmCatR e1 e2) ev = undefined

eval (TmParL x y z e) tev = do
    tev' <- case tev `isTaggedFor` z of
                 Nothing -> return tev
                 Just (ParEvA ev) -> return (tagWith x ev)
                 Just (ParEvB ev) -> return (tagWith y ev)
                 Just _ -> throwError undefined
    (evs,e') <- eval e tev'
    return (evs, TmParL x y z e')

eval (TmParR e1 e2) ev = do
    (evs1,e1') <- eval e1 ev
    (evs2,e2') <- eval e2 ev
    return (fmap ParEvA evs1 ++ fmap ParEvB evs2, TmParR e1' e2')

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
        Just _ -> throwError undefined


eval TmNil _ = return ([PlusPuncA],TmEpsR)
eval (TmCons e1 e2) ev = undefined

eval (TmStarCase buf r s z e1 x xs e2) tev =
    case tev `isTaggedFor` z of
        Nothing -> return ([], TmStarCase (buf ++ [tev]) r s z e1 x xs e2)
        Just PlusPuncA -> evalMany e1 buf
        Just PlusPuncB -> evalMany (TmCatL (TyStar s) x xs z e2) buf
        Just _ -> throwError undefined

eval (TmIte buf t z e1 e2) tev =
    case tev `isTaggedFor` z of
        Nothing -> return ([], TmIte (buf ++ [tev]) t z e1 e2)
        Just (LitEv (LBool True)) -> evalMany (TmCut z TmEpsR e1) buf
        Just (LitEv (LBool False)) -> evalMany (TmCut z TmEpsR e2) buf
        Just _ -> throwError undefined

eval (TmFix args g s e) tev = do
    e' <- reThrow undefined (cutArgs g args (fixSubst g s e e)) 
    eval e' tev

eval (TmRec {}) _ = throwError undefined

eval (TmWait buf r x e) tev = undefined

eval (TmHistPgm s he) _ = do
    evs <- reThrow undefined (Hist.eval he >>= Hist.valueToEventList s)
    return (evs,undefined)


evalMany :: (MonadError SemErr m) => Term EventBuf -> [TaggedEvent] -> m ([Event], Term EventBuf)
evalMany e [] = return ([],e)
evalMany e (ev:evs_in) = do
    (evs_out,e') <- eval e ev
    (evs_out',e'') <- evalMany e' evs_in
    return (evs_out ++ evs_out',e'')