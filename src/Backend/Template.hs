module Backend.Template (
    Template,
    TemplateErr(..),
    monomorphizeTy,
    monomorphizeCtx,
    monomorphizeCtxStruct,
    reparameterizeTemplate,
    getMacParamReplacement,
    getMacParamReplacement',
    withMacParamReplacement,
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
  | MissingMacParamReplacement

instance PrettyPrint TemplateErr where
    pp (TyVarNotFound v) = "Could not find binding for type variable " ++ pp v ++ " while monomorphizing."
    pp (ReparErr v) = "Reparamaterize error: " ++ pp v ++ "."
    pp (MissingMacParamReplacement) = "Expected the template to recieve a macro param replacement."

data TempData a = TD { tyMap :: M.Map Var.TyVar Ty, macParamReplacement :: Maybe a }

type Template a = ReaderT (TempData a) (Except TemplateErr)

withMacParamReplacement :: t -> Template t a -> Template t a
withMacParamReplacement e m = local (\(TD tm _) -> TD tm (Just e)) m

getTy :: Var.TyVar -> Template t Ty
getTy alpha = asks tyMap >>= maybe (throwError (TyVarNotFound alpha)) return . M.lookup alpha

getMacParamReplacement :: Template a (Maybe a)
getMacParamReplacement = asks macParamReplacement

getMacParamReplacement' :: Template a a
getMacParamReplacement' = asks macParamReplacement >>= maybe (throwError MissingMacParamReplacement) return


reThrowReparErr :: ExceptT Var.TyVar (Template t) a -> Template t a
reThrowReparErr x = runExceptT x >>= either (throwError . ReparErr) return


-- Given a monomorphizer m :: ((TyVar -> Ty) -> a) and a map f :: (TyVar -> OpenTy),
-- construct the monomorphizer (\f' -> m (f' . f))
reparameterizeTemplate :: M.Map Var.TyVar OpenTy -> Template t a -> Template t a
reparameterizeTemplate f m = do
    f' <- asks tyMap
    f'' <- mapM (reThrowReparErr . reparameterizeTy f') f
    local (\(TD _ far) -> (TD f'' far)) m

monomorphizeTy :: OpenTy -> Template t Ty
monomorphizeTy TyEps = return TyEps
monomorphizeTy TyInt = return TyInt
monomorphizeTy TyBool = return TyBool
monomorphizeTy (TyCat s t) = TyCat <$> monomorphizeTy s <*> monomorphizeTy t
monomorphizeTy (TyPar s t) = TyPar <$> monomorphizeTy s <*> monomorphizeTy t
monomorphizeTy (TyPlus s t) = TyPlus <$> monomorphizeTy s <*> monomorphizeTy t
monomorphizeTy (TyStar s) = TyStar <$> monomorphizeTy s
monomorphizeTy (TyVar x) = asks (M.lookup x . tyMap) >>= maybe (throwError (TyVarNotFound x)) return

monomorphizeCtx :: Ctx Var.Var OpenTy -> Template t (Ctx Var.Var Ty)
monomorphizeCtx EmpCtx = return EmpCtx
monomorphizeCtx (SngCtx (CE x s)) =  SngCtx . CE x <$> monomorphizeTy s
monomorphizeCtx (CommaCtx g g') =  CommaCtx <$> monomorphizeCtx g <*> monomorphizeCtx g'
monomorphizeCtx (SemicCtx g g') =  SemicCtx <$> monomorphizeCtx g <*> monomorphizeCtx g'

monomorphizeCtxStruct :: (a -> Template t b) -> CtxStruct a -> Template t (CtxStruct b)
monomorphizeCtxStruct _ EmpCtx = return EmpCtx
monomorphizeCtxStruct f (SngCtx x) =  f x >>= (return . SngCtx)
monomorphizeCtxStruct f (CommaCtx g g') =  CommaCtx <$> monomorphizeCtxStruct f g <*> monomorphizeCtxStruct f g'
monomorphizeCtxStruct f (SemicCtx g g') =  SemicCtx <$> monomorphizeCtxStruct f g <*> monomorphizeCtxStruct f g'

runTemplate :: Template t a -> M.Map Var.TyVar Ty -> Maybe t -> Either TemplateErr a
runTemplate x m mt = runIdentity (runExceptT (runReaderT x td_init))
    where
        td_init = TD m mt