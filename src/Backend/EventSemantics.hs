module Backend.EventSemantics where
import Event (TaggedEvent(..), Event(..))

import CoreSyntax
import Buffer

tagWith :: Var -> Event -> TaggedEvent
tagWith = TE

type EventBuf = [TaggedEvent]

instance Buffer EventBuf where

eval :: (Monad m) => Term EventBuf -> TaggedEvent -> m ([Event], Term EventBuf)
eval TmEpsR _ = return ([],TmEpsR)
eval (TmLitR v) _ = return ([LitEv v],TmEpsR)
eval (TmVar x) (TE y ev) = return (if x == y then [ev] else [],TmVar x)

eval (TmCatL t x y z e) (TE z' ev) | z == z' =
    case ev of
        CatEvA ev' -> do
            (evs,e') <- eval e (tagWith x ev')
            return (evs,TmCatL t x y z e')
        CatPunc -> do
            let e' = substVar e z y
            sink <- undefined
            return ([], TmCut x sink e')
        _ -> undefined

eval (TmCatL t x y z e) ev = do
    (evs,e') <- eval e ev
    return (evs,TmCatL t x y z e')

-- Maximality depends on the type!
eval (TmCatR e1 e2) ev = undefined

eval (TmParL x y z e) ev = undefined
eval (TmParR e1 e2) ev = do
    (evs1,e1') <- eval e1 ev
    (evs2,e2') <- eval e2 ev
    return (fmap ParEvA evs1 ++ fmap ParEvB evs2, TmParR e1' e2')

eval (TmInl e) ev = do
    (evs,e') <- eval e ev
    return (PlusPuncA : evs,e')

eval (TmInr e) ev = do
    (evs,e') <- eval e ev
    return (PlusPuncB : evs,e')

eval (TmPlusCase _ _ _ _ _ _ _) _ = undefined

eval (TmCut x e1 e2) ev = do
    (evs,e1') <- eval e1 ev
    (evs_out,e2') <- evalMany e2 (tagWith x <$> evs)
    return (evs_out, TmCut x e1' e2')

eval TmNil _ = return ([PlusPuncA],TmEpsR)

eval (TmCons e1 e2) ev = undefined

eval _ _ = undefined


evalMany :: (Monad m) => Term EventBuf -> [TaggedEvent] -> m ([Event], Term EventBuf)
evalMany e [] = return ([],e)
evalMany e (ev:evs_in) = do
    (evs_out,e') <- eval e ev
    (evs_out',e'') <- evalMany e' evs_in
    return (evs_out ++ evs_out',e'')