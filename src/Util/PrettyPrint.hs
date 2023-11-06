{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
module Util.PrettyPrint(PrettyPrint, pp) where
import qualified Data.Map as M
import Data.List (intercalate)

class PrettyPrint a where
    pp :: a -> String

instance (PrettyPrint k, PrettyPrint v) => PrettyPrint (M.Map k v) where
    pp m = "{" ++ intercalate "," (go <$> M.assocs m) ++ "}"
        where
            go (k,v) = pp k ++ " = " ++ pp v

instance PrettyPrint String where
    pp s = s

instance PrettyPrint Int where
    pp = show

instance PrettyPrint Bool where
    pp = show