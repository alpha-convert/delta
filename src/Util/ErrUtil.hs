module Util.ErrUtil(guard) where
import Control.Monad.Except (MonadError, throwError)

guard :: (MonadError e m) => Bool -> e -> m ()
guard b e = if b then return () else throwError e