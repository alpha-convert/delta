{-# LANGUAGE UndecidableInstances, FlexibleInstances #-}
module Util.Shuffle where
import Test.QuickCheck (Gen)
import Control.Monad.Random

class MonadShuffle m where
    shuffleM :: [a] -> [a] -> m [a]

instance MonadRandom m => MonadShuffle m where
    shuffleM [] ys = return ys
    shuffleM xs [] = return xs
    shuffleM (x:xs) (y:ys) = do
        b <- getRandom
        if b then do
            zs <- shuffleM xs (y:ys)
            return (x:zs)
        else do
            zs <- shuffleM (x:xs) ys
            return (y:zs)
