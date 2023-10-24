module Automata.Compile where

import CoreSyntax
import Automata.Automata (Autom)
import Automata.Event (Event)
import Control.Monad.Identity (Identity)

import Control.Monad.State (StateT (runStateT), State)

data AutomState = AS {}
