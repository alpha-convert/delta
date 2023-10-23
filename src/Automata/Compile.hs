module Automata.Compile where

import CoreSyntax
import Automata.Automata (Autom)

class (Monad m) => CompileM m where

