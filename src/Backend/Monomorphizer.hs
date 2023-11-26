module Backend.Monomorphizer (
    Mono,
    MonomorphErr(..),
    monomorphizeTy,
    monomorphizeCtx,
    reparameterizeMono,
    runMono
)
where
import Control.Monad.Reader (ReaderT (runReaderT), asks, runReader, MonadReader (ask, local), withReaderT)
import qualified Data.Map as M
import Types
import Control.Monad.Except (Except, MonadError (throwError), runExcept, runExceptT, ExceptT)
import qualified Var
import Control.Monad.Identity (Identity(runIdentity))
import Util.PrettyPrint (PrettyPrint,pp)
import Data.Void (Void)

data MonomorphErr =
    TyVarNotFound Var.TyVar
  | ReparErr Var.TyVar

instance PrettyPrint MonomorphErr where
    pp (TyVarNotFound v) = "Could not find binding for type variable " ++ pp v ++ " while monomorphizing."
    pp (ReparErr v) = "Reparamaterize error: " ++ pp v ++ "."

type Mono = ReaderT (M.Map Var.TyVar Ty) (Except MonomorphErr)

getTy :: Var.TyVar -> Mono Ty
getTy alpha = ask >>= maybe (throwError (TyVarNotFound alpha)) return . M.lookup alpha

reThrowReparErr :: ExceptT Var.TyVar Mono a -> Mono a
reThrowReparErr x = runExceptT x >>= either (throwError . ReparErr) return


-- Given a monomorphizer m :: ((TyVar -> Ty) -> a) and a map f :: (TyVar -> OpenTy),
-- construct the monomorphizer (\f' -> m (f' . f))
reparameterizeMono :: M.Map Var.TyVar OpenTy -> Mono a -> Mono a
reparameterizeMono f m = do
    f' <- ask
    f'' <- mapM (reThrowReparErr . reparameterizeTy f') f
    local (const f'') m

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