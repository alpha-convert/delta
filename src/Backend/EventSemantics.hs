module Backend.EventSemantics where
import Event (TaggedEvent(..), Event(..))

import CoreSyntax
import Buffer

tagWith :: Var -> Event -> TaggedEvent
tagWith = TE

data EventBuf = EB [TaggedEvent]

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

eval (TmCatR e1 e2) ev = undefined

eval (TmParL x y z e) ev = undefined
eval (TmParR e1 e2) ev = undefined

eval (TmInl e) ev = undefined
eval (TmInr e) ev = undefined

eval (TmPlusCase _ _ _ _ _ _ _ _) _ = undefined

eval (TmCut x e1 e2) ev = do
    (evs,e1') <- eval e1 ev
    (evs_out,e2') <- evalMany e2 (tagWith x <$> evs)
    return (evs_out, TmCut x e1' e2')

eval _ _ = undefined


evalMany :: (Monad m) => Term EventBuf -> [TaggedEvent] -> m ([Event], Term EventBuf)
evalMany e [] = return ([],e)
evalMany e (ev:evs_in) = do
    (evs_out,e') <- eval e ev
    (evs_out',e'') <- evalMany e' evs_in
    return (evs_out ++ evs_out',e'')