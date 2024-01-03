module Buffer where

import Var
import Data.Map
import Types
import Backend.Template (Template)

class Buffer buf where
  rebindBuf :: buf -> Var -> Var -> buf
  unbindBuf :: Var -> buf -> buf
  emptyBuf :: buf
  emptyBufOfType :: Map Var OpenTy -> Template buf