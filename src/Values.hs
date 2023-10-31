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
  singletonEnv,
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
import Data.List (intersperse)

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
    | StpEmp
    | StpDone
    | StpA Prefix
    | StpB Prefix Prefix
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
  pp StpEmp = "stpemp"
  pp StpDone = "[]"
  pp (StpA p) = concat ["[",pp p,";)"]
  pp (StpB p p') = concat ["[",pp p,";",pp p',";)"]

prefixConcat :: (Monad m) => Prefix -> Prefix -> ExceptT (Prefix,Prefix) m Prefix
prefixConcat LitPEmp LitPEmp = return LitPEmp
prefixConcat LitPEmp (LitPFull l) = return (LitPFull l)
prefixConcat p@LitPEmp p' = throwError (p,p')
prefixConcat (LitPFull l) EpsP = return (LitPFull l)
prefixConcat p@(LitPFull _) p' = throwError (p,p')
prefixConcat EpsP EpsP = return EpsP
prefixConcat p@EpsP p' = throwError (p,p')
prefixConcat (CatPA p) (CatPA p') = CatPA <$> prefixConcat p p'
prefixConcat (CatPA p) (CatPB p1 p2) = do
    p1' <- prefixConcat p p1
    return (CatPB p1' p2)
prefixConcat p@(CatPA _) p' = throwError (p,p')
prefixConcat (CatPB p1 p2) p = do
    p2' <- prefixConcat p2 p
    return (CatPB p1 p2')
prefixConcat SumPEmp SumPEmp = return SumPEmp
prefixConcat SumPEmp (SumPA p) = return (SumPA p)
prefixConcat SumPEmp (SumPB p) = return (SumPB p)
prefixConcat p@SumPEmp p' = throwError (p,p')
prefixConcat (SumPA p) p' = SumPA <$> prefixConcat p p'
prefixConcat (SumPB p) p' = SumPB <$> prefixConcat p p'
prefixConcat StpEmp StpEmp = return StpEmp
prefixConcat StpEmp StpDone = return StpDone
prefixConcat StpEmp (StpA p) = return (StpA p)
prefixConcat StpEmp (StpB p p') = return (StpB p p')
prefixConcat p@StpEmp p' = throwError (p,p')
prefixConcat StpDone EpsP = return StpDone
prefixConcat p@StpDone p' = throwError (p,p')
prefixConcat (StpA p) (CatPA p') = StpA <$> prefixConcat p p'
prefixConcat (StpA p1) (CatPB p1' p2) = do
  p1'' <- prefixConcat p1 p1'
  return (StpB p1'' p2)
prefixConcat p@(StpA _) p' = throwError (p,p')
prefixConcat (StpB p1 p2) p' = do
  p2' <- prefixConcat p2 p'
  return (StpB p1 p2')



unionWithM :: (Monad m, Ord k) => (v -> v -> m v) -> M.Map k v -> M.Map k v -> m (M.Map k v)
unionWithM f m m' = sequence (M.unionWith (bindM2 f) (return <$> m) (return <$> m'))
    where
        bindM2 g a b = do {x <- a; y <- b; g x y}

unionWithkM :: (Monad m, Ord k) => (k -> v -> v -> m v) -> M.Map k v -> M.Map k v -> m (M.Map k v)
unionWithkM f m m' = sequence (M.unionWithKey (\k a b -> do {x <- a; y <- b; f k x y}) (return <$> m) (return <$> m'))

concatEnv :: (Monad m, Ord v) => Env v Prefix -> Env v Prefix -> ExceptT (Prefix,Prefix) m (Env v Prefix)
concatEnv (Env m1) (Env m2) = Env <$> unionWithM prefixConcat m1 m2

unionDisjointEnv :: (Monad m, Ord v) => Env v Prefix -> Env v Prefix -> ExceptT (v,Prefix,Prefix) m (Env v Prefix)
unionDisjointEnv (Env m1) (Env m2) = Env <$> unionWithkM (\v p p' -> throwError (v,p,p')) m1 m2

isMaximal :: Prefix -> Bool
isMaximal LitPEmp = False
isMaximal (LitPFull _) = True
isMaximal EpsP = True
isMaximal (CatPA _) = False
isMaximal (CatPB p p') = isMaximal p && isMaximal p'
isMaximal SumPEmp = False
isMaximal (SumPA p) = isMaximal p
isMaximal (SumPB p) = isMaximal p
isMaximal StpEmp = False
isMaximal StpDone = True
isMaximal (StpA _) = False
isMaximal (StpB p p') = isMaximal p && isMaximal p'

isEmpty :: Prefix -> Bool
isEmpty LitPEmp = True
isEmpty (LitPFull _) = False
isEmpty EpsP = True
isEmpty (CatPA p) = isEmpty p
isEmpty (CatPB {}) = False
isEmpty SumPEmp = True
isEmpty (SumPA _) = False
isEmpty (SumPB _) = False
isEmpty StpEmp = True
isEmpty StpDone = False
isEmpty (StpA _) = False
isEmpty (StpB {}) = False

data Env v p = Env (M.Map v p) deriving (Eq, Ord, Show)

instance (PrettyPrint p, PrettyPrint v) => PrettyPrint (Env v p) where
  pp (Env m) = "{" ++ concat (intersperse "," $ map go $ M.assocs m) ++ "}"
    where
      go (x,p) = pp x ++ " = " ++ pp p

lookupEnv :: (Ord v) => v -> Env v p -> Maybe p
lookupEnv x (Env m) = M.lookup x m

composeEnv :: (Ord v) => Env v p -> Env v p -> Env v p
composeEnv (Env m) (Env m') = Env (M.unionWith (\ _ x -> x) m m')

emptyEnv :: Env v p
emptyEnv = Env M.empty

singletonEnv :: v -> p -> Env v p
singletonEnv x p = Env (M.singleton x p)

bindEnv :: (Ord v) => v -> p -> Env v p -> Env v p
bindEnv x p rho = composeEnv rho (singletonEnv x p)

bindAllEnv :: (Ord v) => [(v,p)] -> Env v p -> Env v p
bindAllEnv xs rho = foldr (uncurry bindEnv) rho xs

unbindEnv :: (Ord v) => v -> Env v p -> Env v p
unbindEnv x (Env m) = Env (M.delete x m)

allEnv :: (p -> Bool) -> Env v p -> Bool
allEnv p (Env m) = all p m