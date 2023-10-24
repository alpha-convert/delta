{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
module Frontend.ElabSyntax (doElab, Term(..)) where

import Values ( Lit(..) )
import Var (Var(..))
import Control.Monad.State (MonadState (put), get, StateT (runStateT))
import Control.Monad.Except (MonadError)

import qualified Frontend.SurfaceSyntax as Surf
import Control.Monad.Identity (Identity (runIdentity))
import Util.PrettyPrint (PrettyPrint(..))

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

class (MonadState ElabState m) => ElabM m where

freshElabVar :: (ElabM m) => m Var
freshElabVar = do
    es <- get
    put $ ES (nextVar es + 1)
    return $ Var.Var $ "__x" ++ show (nextVar es)

elabMaybeVar :: (ElabM m) => Maybe Var -> m Var
elabMaybeVar Nothing = freshElabVar
elabMaybeVar (Just x) = return x

elab :: (ElabM m) => Surf.Term -> m Term
elab (Surf.TmLitR l) = return (TmLitR l)
elab Surf.TmEpsR = return TmEpsR
elab (Surf.TmVar x) = return (TmVar x)
elab (Surf.TmCatL mx my e1 e2) = do
    e1' <- elab e1
    e2' <- elab e2
    z <- freshElabVar
    x <- elabMaybeVar mx
    y <- elabMaybeVar my
    return $ TmCut z e1' (TmCatL x y z e2')
elab (Surf.TmCatR e1 e2) = do
    e1' <- elab e1
    e2' <- elab e2
    return (TmCatR e1' e2')
elab (Surf.TmInl e) = TmInl <$> elab e
elab (Surf.TmInr e) = TmInr <$> elab e
elab (Surf.TmPlusCase e mx e1 my e2) = do
    e' <- elab e
    e1' <- elab e1
    e2' <- elab e2
    z <- freshElabVar
    x <- elabMaybeVar mx
    y <- elabMaybeVar my
    return $ TmCut z e' (TmPlusCase z x e1' y e2')

{-TODO: ensure that fundefs have unique vars-}

instance ElabM (StateT ElabState Identity) where

doElab :: Surf.Term -> IO Term
doElab e = return . fst . runIdentity $ runStateT (elab e) (ES 0)