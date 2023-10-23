module Automata.Automata where
import Control.Monad.State (StateT (runStateT))

newtype Autom m f a b = A (a -> m (f b, Autom m f a b))

fromState :: (Monad m) => (a -> StateT s m (f b)) -> s -> Autom m f a b
fromState f s = A $ \x -> do
    (fb,s') <- runStateT (f x) s
    return (fb,fromState f s')