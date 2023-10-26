{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
module Frontend.ElabSyntax (doElab, Term(..), Program, FunDef(..), RunCmd(..)) where

import Values ( Lit(..) )
import Var (Var(..))
import Control.Monad.State (MonadState (put), get, StateT (runStateT))
import Control.Monad.Except (MonadError (throwError), ExceptT, runExceptT)
import Types

import qualified Frontend.SurfaceSyntax as Surf
import Control.Monad.Identity (Identity (runIdentity))
import Util.PrettyPrint (PrettyPrint(..))
import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad.RWS.Strict (MonadReader (local, ask))
import Control.Monad.Reader (ReaderT (runReaderT))

data Term =
      TmLitR Lit
    | TmEpsR
    | TmVar Var
    | TmCatL Var Var Var Term
    | TmCatR Term Term
    | TmInl Term
    | TmInr Term
    | TmPlusCase Var Var Term Var Term
    | TmCut Var Term Term
    deriving (Eq, Ord, Show)

instance PrettyPrint Term where
    pp = go False
        where
            go _ (TmLitR l) = pp l
            go _ TmEpsR = "sink"
            go _ (TmVar (Var x)) = x
            go _ (TmCatR e1 e2) = concat ["(",go False e1,";",go False e2,")"]
            go True e = concat ["(", go False e, ")"]
            go False (TmCatL (Var x) (Var y) (Var z) e) = concat ["let (",x,";",y,") = ",z," in ",go False e]
            go False (TmInl e) = "inl " ++ go True e
            go False (TmInr e) = "inl " ++ go True e
            go False (TmPlusCase (Var z) (Var x) e1 (Var y) e2) = concat ["case ",z," of inl ",x," => ",go True e1," | inr",y," => ",go True e2]
            go False (TmCut (Var x) e1 e2) = concat ["let ",x," = ",go True e1," in ",go True e2]

data ElabState = ES { nextVar :: Int }

data ElabErr = UnboundVar Var

instance PrettyPrint ElabErr where
    pp (UnboundVar (Var x)) = concat ["Variable ",x," not bound. This is a compiler bug."]

class (MonadState ElabState m, MonadReader (M.Map Var Var) m, MonadError ElabErr m) => ElabM m where

freshElabVar :: (ElabM m) => m Var
freshElabVar = do
    es <- get
    put $ ES (nextVar es + 1)
    return $ Var.Var $ "__x" ++ show (nextVar es)

withUnshadow :: (ElabM m) => Maybe Var -> m a -> m (a,Var)
withUnshadow Nothing u = do
    x <- freshElabVar
    a <- local (M.insert x x) u
    return (a,x)
withUnshadow (Just x) u = do
    sm <- ask
    if M.member x sm then do
        y <- freshElabVar
        a <- local (M.insert x y) u
        return (a,y)
    else do
        a <- local (M.insert x x) u
        return (a,x)

unshadow :: (ElabM m) => Var -> m Var
unshadow x = do
    sm <- ask
    case M.lookup x sm of
        Just y -> return y
        Nothing -> throwError (UnboundVar x)
    

elab :: (ElabM m) => Surf.Term -> m Term
elab (Surf.TmLitR l) = return (TmLitR l)
elab Surf.TmEpsR = return TmEpsR
elab (Surf.TmVar x) = TmVar <$> unshadow x
elab (Surf.TmCatL mx my e1 e2) = do
    e1' <- elab e1
    ((e2',y),x) <- withUnshadow mx $ withUnshadow my $ elab e2
    z <- freshElabVar
    return $ TmCut z e1' (TmCatL x y z e2')
elab (Surf.TmCatR e1 e2) = do
    e1' <- elab e1
    e2' <- elab e2
    return (TmCatR e1' e2')
elab (Surf.TmInl e) = TmInl <$> elab e
elab (Surf.TmInr e) = TmInr <$> elab e
elab (Surf.TmPlusCase e mx e1 my e2) = do
    e' <- elab e
    (e1',x) <- withUnshadow mx $ elab e1
    (e2',y) <- withUnshadow my $ elab e2
    z <- freshElabVar
    return $ TmCut z e' (TmPlusCase z x e1' y e2')

{-TODO: ensure that fundefs have unique vars-}

instance ElabM (StateT ElabState (ReaderT (M.Map Var Var) (ExceptT ElabErr Identity))) where

data FunDef = FD String (Ctx Var.Var) Ty Term deriving (Eq,Ord,Show)

data RunCmd = RC String (M.Map Var.Var Surf.UntypedPrefix)

type Program = [Either FunDef RunCmd]

elabCtx g =
    let bindings = ctxBindings g in
    let ks = M.keysSet bindings in 
    S.fold (\x -> M.insert x x) M.empty ks

doElab :: Surf.Program -> IO Program
doElab = mapM $ \case
                    Right (Surf.RC s xs) -> return (Right (RC s (M.fromList xs)))
                    Left (Surf.FD f g s e) -> do
                        let initCtxMap = elabCtx g
                        case runIdentity (runExceptT (runReaderT (runStateT (elab e) (ES 0)) initCtxMap)) of
                            Right (e',_) -> return (Left (FD f g s e'))
                            Left err -> error (pp err)
