module Buffer where

import Var
import Data.Map
import Types
import Backend.Monomorphizer (Mono)

class Buffer buf where
  rebindBuf :: buf -> Var -> Var -> buf
  unbindBuf :: Var -> buf -> buf
  emptyBufOfType :: Map Var OpenTy -> Mono buf
  emptyBuf :: buf