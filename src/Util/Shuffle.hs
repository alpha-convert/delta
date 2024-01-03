module Util.Shuffle where
import Test.QuickCheck (Gen, Arbitrary (arbitrary))
import Control.Monad.Random
import Control.Monad.Except (ExceptT)

class Monad m => MonadShuffle m where
    shuffleM :: [a] -> [a] -> m [a]

instance MonadShuffle IO where
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

instance MonadShuffle Gen where
    shuffleM [] ys = return ys
    shuffleM xs [] = return xs
    shuffleM (x:xs) (y:ys) = do
        b <- arbitrary
        if b then do
            zs <- shuffleM xs (y:ys)
            return (x:zs)
        else do
            zs <- shuffleM (x:xs) ys
            return (y:zs)

instance MonadShuffle m => MonadShuffle (ExceptT e m) where
    shuffleM xs ys = lift (shuffleM xs ys)