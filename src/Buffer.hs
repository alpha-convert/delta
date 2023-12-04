module Buffer where

import Var
import Data.Map
import Types
import Backend.Template (Template)

class Buffer buf where
  rebindBuf :: buf -> Var -> Var -> buf
  unbindBuf :: Var -> buf -> buf
  emptyBufOfType :: Map Var OpenTy -> Template buf
  emptyBuf :: buf