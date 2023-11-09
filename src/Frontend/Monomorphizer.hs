module Frontend.Monomorphizer (
    Mono,
    MonomorphErr(..),
    monomorphizeTy,
    monomorphizeCtx,
    runMono
)
where
import Control.Monad.Reader (ReaderT (runReaderT), asks, runReader)
import qualified Data.Map as M
import Types
import Control.Monad.Except (Except, MonadError (throwError), runExcept, runExceptT)
import qualified Var
import Control.Monad.Identity (Identity(runIdentity))
import Util.PrettyPrint (PrettyPrint,pp)

data MonomorphErr v =
    TyVarNotFound v

instance PrettyPrint v => PrettyPrint (MonomorphErr v) where
    pp (TyVarNotFound v) = "Could not find binding for type variable " ++ pp v ++ " while monomorphizing."

type Mono v = ReaderT (M.Map v Ty) (Except (MonomorphErr v))

monomorphizeTy :: Ord v => TyF v -> Mono v Ty
monomorphizeTy TyEps = return TyEps
monomorphizeTy TyInt = return TyInt
monomorphizeTy TyBool = return TyBool
monomorphizeTy (TyCat s t) = TyCat <$> monomorphizeTy s <*> monomorphizeTy t
monomorphizeTy (TyPar s t) = TyPar <$> monomorphizeTy s <*> monomorphizeTy t
monomorphizeTy (TyPlus s t) = TyPlus <$> monomorphizeTy s <*> monomorphizeTy t
monomorphizeTy (TyStar s) = TyStar <$> monomorphizeTy s
monomorphizeTy (TyVar x) = asks (M.lookup x) >>= maybe (throwError (TyVarNotFound x)) return

monomorphizeCtx :: Ord v => Ctx Var.Var (TyF v) -> Mono v (Ctx Var.Var Ty)
monomorphizeCtx EmpCtx = return EmpCtx
monomorphizeCtx (SngCtx (CE x s)) =  SngCtx . CE x <$> monomorphizeTy s
monomorphizeCtx (CommaCtx g g') =  CommaCtx <$> monomorphizeCtx g <*> monomorphizeCtx g'
monomorphizeCtx (SemicCtx g g') =  SemicCtx <$> monomorphizeCtx g <*> monomorphizeCtx g'

runMono :: Mono v a -> M.Map v Ty -> Either (MonomorphErr v) a
runMono x m = runIdentity (runExceptT (runReaderT x m))