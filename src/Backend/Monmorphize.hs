module Backend.Monmorphize where
import qualified Var
import Util.PrettyPrint
import Types
import qualified Data.Map as M

data MonomorphizeErr t =
    TyVarNotFound t

instance PrettyPrint t => PrettyPrint (MonomorphizeErr t) where
    pp (TyVarNotFound v) = "Could not find binding for type variable " ++ pp v ++ " while monomorphizing."

class Monomorphizable f where
    mapTyVars :: (t -> Either (MonomorphizeErr t) (TyF t')) -> f t -> Either (MonomorphizeErr t) (f t')

instance Monomorphizable TyF where
    mapTyVars f (TyVar x) = f x
    mapTyVars f TyEps = return TyEps
    mapTyVars f TyInt = return TyInt
    mapTyVars f TyBool = return TyBool
    mapTyVars f (TyCat s t) = do
        s' <- mapTyVars f s
        t' <- mapTyVars f t
        return (TyCat s' t')
    mapTyVars f (TyPar s t) = do
        s' <- mapTyVars f s
        t' <- mapTyVars f t
        return (TyPar s' t')
    mapTyVars f (TyPlus s t) = do
        s' <- mapTyVars f s
        t' <- mapTyVars f t
        return (TyPlus s' t')
    mapTyVars f (TyStar s) = TyStar <$> mapTyVars f s

reparameterize :: (Monomorphizable f) => M.Map Var.TyVar t' -> f t -> Either (MonomorphizeErr t) (f t')
reparameterize m = undefined