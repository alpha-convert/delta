module Util.PrettyPrint where

class PrettyPrint a where
    pp :: a -> String