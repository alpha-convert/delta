module Util.ErrUtil (
    guard,
    reThrow
) where
import Control.Monad.Except (MonadError, throwError, ExceptT, runExceptT)

guard :: (MonadError e m) => Bool -> e -> m ()
guard b e = if b then return () else throwError e

reThrow :: (MonadError e' m) => (e -> e') -> ExceptT e m a -> m a
reThrow k x = runExceptT x >>= either (throwError . k) return