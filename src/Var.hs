{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use newtype instead of data" #-}
module Var(Var(..)) where
import Util.PrettyPrint (PrettyPrint (..))

data Var = Var String deriving (Eq, Ord, Show)

instance PrettyPrint Var where
    pp (Var x) = x