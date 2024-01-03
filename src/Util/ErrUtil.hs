module Util.ErrUtil (
    guard,
    reThrow,
    reThrowIO
) where
import Control.Monad.Except (MonadError, throwError, ExceptT, runExceptT)
import Control.Monad.IO.Class (MonadIO)

guard :: (MonadError e m) => Bool -> e -> m ()
guard b e = if b then return () else throwError e

reThrow :: (MonadError e' m) => (e -> e') -> ExceptT e m a -> m a
reThrow k x = runExceptT x >>= either (throwError . k) return

reThrowIO :: (MonadIO m, Show e) => ExceptT e m a -> m a
reThrowIO x = runExceptT x >>= either (error . show) return