module Backend.Template (
    Template,
    TemplateErr(..),
    monomorphizeTy,
    monomorphizeCtx,
    reparameterizeTemplate,
    runTemplate
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

data TemplateErr =
    TyVarNotFound Var.TyVar
  | ReparErr Var.TyVar

instance PrettyPrint TemplateErr where
    pp (TyVarNotFound v) = "Could not find binding for type variable " ++ pp v ++ " while monomorphizing."
    pp (ReparErr v) = "Reparamaterize error: " ++ pp v ++ "."

type Template = ReaderT (M.Map Var.TyVar Ty) (Except TemplateErr)

getTy :: Var.TyVar -> Template Ty
getTy alpha = ask >>= maybe (throwError (TyVarNotFound alpha)) return . M.lookup alpha

reThrowReparErr :: ExceptT Var.TyVar Template a -> Template a
reThrowReparErr x = runExceptT x >>= either (throwError . ReparErr) return


-- Given a monomorphizer m :: ((TyVar -> Ty) -> a) and a map f :: (TyVar -> OpenTy),
-- construct the monomorphizer (\f' -> m (f' . f))
reparameterizeTemplate :: M.Map Var.TyVar OpenTy -> Template a -> Template a
reparameterizeTemplate f m = do
    f' <- ask
    f'' <- mapM (reThrowReparErr . reparameterizeTy f') f
    local (const f'') m

monomorphizeTy :: OpenTy -> Template Ty
monomorphizeTy TyEps = return TyEps
monomorphizeTy TyInt = return TyInt
monomorphizeTy TyBool = return TyBool
monomorphizeTy (TyCat s t) = TyCat <$> monomorphizeTy s <*> monomorphizeTy t
monomorphizeTy (TyPar s t) = TyPar <$> monomorphizeTy s <*> monomorphizeTy t
monomorphizeTy (TyPlus s t) = TyPlus <$> monomorphizeTy s <*> monomorphizeTy t
monomorphizeTy (TyStar s) = TyStar <$> monomorphizeTy s
monomorphizeTy (TyVar x) = asks (M.lookup x) >>= maybe (throwError (TyVarNotFound x)) return

monomorphizeCtx :: Ctx Var.Var OpenTy -> Template (Ctx Var.Var Ty)
monomorphizeCtx EmpCtx = return EmpCtx
monomorphizeCtx (SngCtx (CE x s)) =  SngCtx . CE x <$> monomorphizeTy s
monomorphizeCtx (CommaCtx g g') =  CommaCtx <$> monomorphizeCtx g <*> monomorphizeCtx g'
monomorphizeCtx (SemicCtx g g') =  SemicCtx <$> monomorphizeCtx g <*> monomorphizeCtx g'

runTemplate :: Template a -> M.Map Var.TyVar Ty -> Either TemplateErr a
runTemplate x m = runIdentity (runExceptT (runReaderT x m))