module Values(
  Lit(..),
  Prefix(..),
  MaximalPrefix(..),
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
  unionDisjointEnv,
  rebindEnv,
  maximalLift,
  maximalDemote,
  sinkPrefix
) where

import qualified Data.Map as M
import Util.PrettyPrint (PrettyPrint(..))
import Control.Monad.Except
import Data.IntMap (unionWith)
import Data.List (intersperse, intercalate)
import Data.Semigroup (Max)

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
    | ParP Prefix Prefix
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
  pp (ParP p p') = concat ["(",pp p,",", pp p',")"]
  pp SumPEmp = "sumemp"
  pp (SumPA p) = concat ["inl(",pp p,")"]
  pp (SumPB p) = concat ["inr(",pp p,")"]
  pp StpEmp = "stpemp"
  pp StpDone = "[]"
  pp (StpA p) = concat ["[",pp p,";)"]
  pp (StpB p p') = concat ["[",pp p,";",pp p',")"]

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
prefixConcat (ParP p1 p2) (ParP p1' p2') = do 
  p1'' <- prefixConcat p1 p1'
  p2'' <- prefixConcat p2 p2'
  return (ParP p1'' p2'')
prefixConcat p@(ParP {}) p' = throwError (p,p')

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



unionWithM :: (Monad m, Ord k) => (k -> v -> v -> m v) -> M.Map k v -> M.Map k v -> m (M.Map k v)
unionWithM f m m' = sequence (M.unionWithKey g (return <$> m) (return <$> m'))
    where
        g k a b = do {x <- a; y <- b; f k x y}

unionWithkM :: (Monad m, Ord k) => (k -> v -> v -> m v) -> M.Map k v -> M.Map k v -> m (M.Map k v)
unionWithkM f m m' = sequence (M.unionWithKey (\k a b -> do {x <- a; y <- b; f k x y}) (return <$> m) (return <$> m'))

concatEnv :: (Monad m, Ord v) => Env v Prefix -> Env v Prefix -> ExceptT (v,Prefix,Prefix) m (Env v Prefix)
concatEnv (Env m1) (Env m2) = Env <$> unionWithM go m1 m2
  where
    go v p1 p2 = withExceptT (\(p1',p2') -> (v,p1',p2')) (prefixConcat p1 p2)

unionDisjointEnv :: (Monad m, Ord v) => Env v Prefix -> Env v Prefix -> ExceptT (v,Prefix,Prefix) m (Env v Prefix)
unionDisjointEnv (Env m1) (Env m2) = Env <$> unionWithkM (\v p p' -> throwError (v,p,p')) m1 m2

isMaximal :: Prefix -> Bool
isMaximal LitPEmp = False
isMaximal (LitPFull _) = True
isMaximal EpsP = True
isMaximal (CatPA _) = False
isMaximal (CatPB p p') = isMaximal p && isMaximal p'
isMaximal (ParP p p') = isMaximal p && isMaximal p'
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
isEmpty (ParP p p') = isEmpty p && isEmpty p'
isEmpty SumPEmp = True
isEmpty (SumPA _) = False
isEmpty (SumPB _) = False
isEmpty StpEmp = True
isEmpty StpDone = False
isEmpty (StpA _) = False
isEmpty (StpB {}) = False

data Env v p = Env (M.Map v p) deriving (Eq, Ord, Show)

instance (PrettyPrint p, PrettyPrint v) => PrettyPrint (Env v p) where
  pp (Env m) = "{" ++ intercalate "," (map go $ M.assocs m) ++ "}"
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

-- rebindEnv m x y = m[x/y]
rebindEnv :: (Ord v) => Env v p -> v -> v -> Env v p
rebindEnv m x y =
  case lookupEnv y m of
    Nothing -> m
    Just p -> bindEnv x p (unbindEnv y m)

data MaximalPrefix =
      LitMP Lit
    | EpsMP
    | CatMP MaximalPrefix MaximalPrefix
    | ParMP MaximalPrefix MaximalPrefix
    | SumMPA MaximalPrefix
    | SumMPB MaximalPrefix
    | StMP [MaximalPrefix]
    deriving (Eq, Ord, Show)

maximalDemote :: MaximalPrefix -> Prefix
maximalDemote (LitMP l) = LitPFull l
maximalDemote EpsMP = EpsP
maximalDemote (CatMP p1 p2) = CatPB (maximalDemote p1) (maximalDemote p2)
maximalDemote (ParMP p1 p2) = ParP (maximalDemote p1) (maximalDemote p2)
maximalDemote (SumMPA p) = SumPA (maximalDemote p)
maximalDemote (SumMPB p) = SumPB (maximalDemote p)
maximalDemote (StMP ps) = go ps
  where
    go [] = StpDone
    go (p:ps') = StpB (maximalDemote p) (go ps')

instance PrettyPrint MaximalPrefix where
  pp (LitMP l) = pp l
  pp EpsMP = "()"
  pp (CatMP p1 p2) = "(" ++ pp p1 ++ ";" ++ pp p2 ++ ")"
  pp (ParMP p1 p2) = "(" ++ pp p1 ++ "," ++ pp p2 ++ ")"
  pp (SumMPA p) = "inl " ++ pp p
  pp (SumMPB p) = "inr " ++ pp p
  pp (StMP p) = "[" ++ intercalate ";" (map pp p) ++ "]"

maximalLift :: Prefix -> Maybe MaximalPrefix
maximalLift LitPEmp = Nothing
maximalLift (LitPFull l) = return (LitMP l)
maximalLift EpsP = return EpsMP
maximalLift (CatPA _) = Nothing
maximalLift (CatPB p1 p2) = do
  p1' <- maximalLift p1
  p2' <- maximalLift p2
  return (CatMP p1' p2')
maximalLift (ParP p1 p2) = do
  p1' <- maximalLift p1
  p2' <- maximalLift p2
  return (ParMP p1' p2')
maximalLift SumPEmp = Nothing
maximalLift (SumPA p) = SumMPA <$> maximalLift p
maximalLift (SumPB p) = SumMPB <$> maximalLift p
maximalLift StpEmp = Nothing
maximalLift StpDone = return (StMP [])
maximalLift (StpA _) = Nothing
maximalLift (StpB p1 p2) = do
  p1' <- maximalLift p1
  p2' <- maximalLift p2
  case p2' of
    StMP ps -> return (StMP (p1' : ps))
    _ -> Nothing

sinkPrefix :: MaximalPrefix -> Prefix
sinkPrefix (LitMP _) = EpsP
sinkPrefix EpsMP = EpsP
sinkPrefix (CatMP _ p) = sinkPrefix p
sinkPrefix (ParMP p p') = ParP (sinkPrefix p) (sinkPrefix p')
sinkPrefix (SumMPA p) = sinkPrefix p
sinkPrefix (SumMPB p) = sinkPrefix p
sinkPrefix (StMP _) = EpsP