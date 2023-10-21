module Values where

import Types
import qualified Data.Map as M

data Lit = LInt Int | LBool Bool deriving (Eq, Ord, Show)

data Prefix =
      LitPEmp
    | LitPFull Lit
    | EpsP
    | CatPA Prefix
    | CatPB Prefix Prefix
    | SumPEmp
    | SumPA Prefix
    | SumPB Prefix
    deriving (Eq, Ord, Show)

 
emptyPrefix :: Ty -> Prefix
emptyPrefix t = undefined

isMaximal :: Prefix -> Bool
isMaximal p = undefined

data Env v = Env (M.Map v Prefix) deriving (Eq, Ord, Show)

composeEnv :: (Ord v) => Env v -> Env v -> Env v
composeEnv (Env m) (Env m') = Env (M.unionWith (flip const) m m')

singletonEnv :: v -> Prefix -> Env v
singletonEnv x p = Env (M.singleton x p)

bind :: (Ord v) => v -> Prefix -> Env v -> Env v
bind x p rho = composeEnv rho (singletonEnv x p)

bindAll :: (Ord v) => [(v,Prefix)] -> Env v -> Env v
bindAll xs rho = foldr (uncurry bind) rho xs