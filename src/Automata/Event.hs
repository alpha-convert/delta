{-# LANGUAGE  MultiParamTypeClasses, FlexibleInstances #-}
module Automata.Event() where

import Values (Lit(..), Prefix(..))
import Types ( Ty(..), TypeLike(..), ValueLike(..), ValueLikeErr(..))
import Control.Monad.Except(ExceptT, MonadError (..), withExceptT)
import Util.ErrUtil(guard)

data Event = LitEv Lit | PlusPuncA | PlusPuncB | CatPunc | CatEvA Event

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

promote xs = withExceptT (errCons xs)
errCons xs (IllTyped x t) = IllTyped (x:xs) t

instance ValueLike [Event] Ty where
    hasType [] _ = return ()
    hasType (x:xs) t = promote xs (hasType x t) >> promote xs (deriv x t) >>= hasType xs

    deriv [] s = return s
    deriv (x:xs) s = do
        s' <- promote xs (deriv x s)
        deriv xs s'