module Util.PrettyPrint(PrettyPrint, pp) where

class PrettyPrint a where
    pp :: a -> String