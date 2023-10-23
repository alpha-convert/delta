{-# LANGUAGE  MultiParamTypeClasses #-}
module Automata.Event where
import Values (Lit)
import Types ( Ty, Derivative(..), DerivErr)
import Control.Monad.Except(ExceptT)

data Event = LitEv Lit | PlusPuncA | PlusPuncB | CatPunc | CatEvA Event

instance Derivative Event Ty where
    hasType = undefined
    deriv = undefined
