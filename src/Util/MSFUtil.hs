{-# LANGUAGE TupleSections #-}
module Util.MSFUtil where
import Data.MonadicStreamFunction
import Control.Monad.Trans.MSF (dSwitch)

dThen :: (Monad m) => MSF m a b -> MSF m a b -> MSF m a b
dThen m m' = dSwitch (m >>> arr (,Just ())) (const m')

applyOnce :: (Monad m) => (a -> a) -> MSF m a a
applyOnce f = dSwitch (arr ((,Just ()) . f)) (const (arr id))

applyOnceM :: (Monad m) => (a -> m a) -> MSF m a a
applyOnceM f = dSwitch (arrM ((fmap (,Just ())) . f)) (const (arr id))

applyToFirst :: (Monad m) => (a -> a) -> (b -> b) -> MSF m a b -> MSF m a b
applyToFirst f g m = applyOnce f >>> m >>> applyOnce g

applyToFirstM :: (Monad m) => (a -> m a) -> (b -> m b) -> MSF m a b -> MSF m a b
applyToFirstM f g m = applyOnceM f >>> m >>> applyOnceM g

