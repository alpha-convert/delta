module Values(
  Lit(..),
  Prefix(..),
  isMaximal,
  isEmpty,
  Env,
  bindEnv,
  bindAllEnv,
  lookupEnv,
  emptyEnv,
  composeEnv,
  unbindEnv,
  prefixConcat,
  concatEnv,
  allEnv,
  unionDisjointEnv
) where

import qualified Data.Map as M
import Util.PrettyPrint (PrettyPrint(..))
import Control.Monad.Except
import Data.IntMap (unionWith)

data Lit = LInt Int | LBool Bool deriving (Eq, Ord, Show)

instance PrettyPrint Lit where
  pp (LInt n) = show n
  pp (LBool b) = show b

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

instance PrettyPrint Prefix where
  pp LitPEmp = "litemp"
  pp (LitPFull l) = pp l
  pp EpsP = "epsemp"
  pp (CatPA p) = concat ["(",pp p,";)"]
  pp (CatPB p p') = concat ["(",pp p,";",pp p',")"]
  pp SumPEmp = "sumemp"
  pp (SumPA p) = concat ["inl(",pp p,")"]
  pp (SumPB p) = concat ["inr(",pp p,")"]

prefixConcat :: (Monad m) => Prefix -> Prefix -> ExceptT (Prefix,Prefix) m Prefix
prefixConcat LitPEmp LitPEmp = return LitPEmp
prefixConcat LitPEmp (LitPFull l) = return (LitPFull l)
prefixConcat (LitPFull l) EpsP = return (LitPFull l)
prefixConcat EpsP EpsP = return EpsP
prefixConcat (CatPA p) (CatPA p') = CatPA <$> prefixConcat p p'
prefixConcat (CatPA p) (CatPB p1 p2) = do
    p1' <- prefixConcat p p1
    return (CatPB p1' p2)
prefixConcat (CatPB p1 p2) p = do
    p2' <- prefixConcat p2 p
    return (CatPB p1 p2')
prefixConcat SumPEmp SumPEmp = return SumPEmp
prefixConcat SumPEmp (SumPA p) = return (SumPA p)
prefixConcat SumPEmp (SumPB p) = return (SumPB p)
prefixConcat (SumPA p) p' = SumPA <$> prefixConcat p p'
prefixConcat (SumPB p) p' = SumPB <$> prefixConcat p p'
prefixConcat p p' = throwError (p,p')


unionWithM :: (Monad m, Ord k) => (v -> v -> m v) -> M.Map k v -> M.Map k v -> m (M.Map k v)
unionWithM f m m' = sequence (M.unionWith (bindM2 f) (return <$> m) (return <$> m'))
    where
        bindM2 g a b = do {x <- a; y <- b; g x y}

unionWithkM :: (Monad m, Ord k) => (k -> v -> v -> m v) -> M.Map k v -> M.Map k v -> m (M.Map k v)
unionWithkM f m m' = sequence (M.unionWithKey (\k a b -> do {x <- a; y <- b; f k x y}) (return <$> m) (return <$> m'))

concatEnv :: (Monad m, Ord v) => Env v -> Env v -> ExceptT (Prefix,Prefix) m (Env v)
concatEnv (Env m1) (Env m2) = Env <$> unionWithM prefixConcat m1 m2

unionDisjointEnv :: (Monad m, Ord v) => Env v -> Env v -> ExceptT (v,Prefix,Prefix) m (Env v)
unionDisjointEnv (Env m1) (Env m2) = Env <$> unionWithkM (\v p p' -> throwError (v,p,p')) m1 m2

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

lookupEnv :: (Ord v) => v -> Env v -> Maybe Prefix
lookupEnv x (Env m) = M.lookup x m

composeEnv :: (Ord v) => Env v -> Env v -> Env v
composeEnv (Env m) (Env m') = Env (M.unionWith (\ _ x -> x) m m')

emptyEnv :: Env v
emptyEnv = Env M.empty

singletonEnv :: v -> Prefix -> Env v
singletonEnv x p = Env (M.singleton x p)

bindEnv :: (Ord v) => v -> Prefix -> Env v -> Env v
bindEnv x p rho = composeEnv rho (singletonEnv x p)

bindAllEnv :: (Ord v) => [(v,Prefix)] -> Env v -> Env v
bindAllEnv xs rho = foldr (uncurry bindEnv) rho xs

unbindEnv :: (Ord v) => v -> Env v -> Env v
unbindEnv x (Env m) = Env (M.delete x m)

allEnv :: (Prefix -> Bool) -> Env v -> Bool
allEnv p (Env m) = all p m