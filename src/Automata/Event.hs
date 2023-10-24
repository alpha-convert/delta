{-# LANGUAGE  MultiParamTypeClasses #-}
module Automata.Event where
import Values (Lit(..))
import Types ( Ty(..), TypeLike(..), ValueLike(..), DerivErr(..), HasTypeErr(..))
import Control.Monad.Except(ExceptT, MonadError (..))
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

    deriv = undefined

-- instance ValueLike [Event] Ty where
--     hasType = _
