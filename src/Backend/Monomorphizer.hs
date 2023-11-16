module Backend.Monomorphizer (
    Mono,
    MonomorphErr(..),
    monomorphizeTy,
    monomorphizeCtx,
    precomposeMono,
    runMono
)
where
import Control.Monad.Reader (ReaderT (runReaderT), asks, runReader, MonadReader (ask), withReaderT)
import qualified Data.Map as M
import Types
import Control.Monad.Except (Except, MonadError (throwError), runExcept, runExceptT, ExceptT)
import qualified Var
import Control.Monad.Identity (Identity(runIdentity))
import Util.PrettyPrint (PrettyPrint,pp)

data MonomorphErr =
    TyVarNotFound Var.TyVar

instance PrettyPrint MonomorphErr where
    pp (TyVarNotFound v) = "Could not find binding for type variable " ++ pp v ++ " while monomorphizing."

type Mono = ReaderT (M.Map Var.TyVar Ty) (Except MonomorphErr)

precomposeMono :: M.Map Var.TyVar OpenTy -> Mono a -> Mono a
precomposeMono m = withReaderT (\m' -> M.map (\ot -> either (error . (++" missing var") . pp) id $ runIdentity $ runExceptT $ (reparameterizeTy m' ot :: ExceptT Var.TyVar Identity Ty)) m)

-- (m :: v -> TyF v)
-- (m' :: v -> Ty )

monomorphizeTy :: OpenTy -> Mono Ty
monomorphizeTy TyEps = return TyEps
monomorphizeTy TyInt = return TyInt
monomorphizeTy TyBool = return TyBool
monomorphizeTy (TyCat s t) = TyCat <$> monomorphizeTy s <*> monomorphizeTy t
monomorphizeTy (TyPar s t) = TyPar <$> monomorphizeTy s <*> monomorphizeTy t
monomorphizeTy (TyPlus s t) = TyPlus <$> monomorphizeTy s <*> monomorphizeTy t
monomorphizeTy (TyStar s) = TyStar <$> monomorphizeTy s
monomorphizeTy (TyVar x) = asks (M.lookup x) >>= maybe (throwError (TyVarNotFound x)) return

monomorphizeCtx :: Ctx Var.Var OpenTy -> Mono (Ctx Var.Var Ty)
monomorphizeCtx EmpCtx = return EmpCtx
monomorphizeCtx (SngCtx (CE x s)) =  SngCtx . CE x <$> monomorphizeTy s
monomorphizeCtx (CommaCtx g g') =  CommaCtx <$> monomorphizeCtx g <*> monomorphizeCtx g'
monomorphizeCtx (SemicCtx g g') =  SemicCtx <$> monomorphizeCtx g <*> monomorphizeCtx g'

runMono :: Mono a -> M.Map Var.TyVar Ty -> Either MonomorphErr a
runMono x m = runIdentity (runExceptT (runReaderT x m))