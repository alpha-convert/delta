module Values where

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


isMaximal :: Prefix -> Bool
isMaximal LitPEmp = False
isMaximal (LitPFull _) = True
isMaximal EpsP = True
isMaximal (CatPA _) = False
isMaximal (CatPB _ p) = isMaximal p
isMaximal SumPEmp = False
isMaximal (SumPA p) = isMaximal p
isMaximal (SumPB p) = isMaximal p

isEmpty :: Prefix -> Bool
isEmpty LitPEmp = True
isEmpty (LitPFull _) = False
isEmpty EpsP = True
isEmpty (CatPA p) = isEmpty p
isEmpty (CatPB _ _) = False
isEmpty SumPEmp = True
isEmpty (SumPA _) = False
isEmpty (SumPB _) = False

data Env v = Env (M.Map v Prefix) deriving (Eq, Ord, Show)


composeEnv :: (Ord v) => Env v -> Env v -> Env v
composeEnv (Env m) (Env m') = Env (M.unionWith (\ _ x -> x) m m')

singletonEnv :: v -> Prefix -> Env v
singletonEnv x p = Env (M.singleton x p)

bind :: (Ord v) => v -> Prefix -> Env v -> Env v
bind x p rho = composeEnv rho (singletonEnv x p)

bindAll :: (Ord v) => [(v,Prefix)] -> Env v -> Env v
bindAll xs rho = foldr (uncurry bind) rho xs