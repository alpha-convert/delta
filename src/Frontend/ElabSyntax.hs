{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
module Frontend.ElabSyntax (doElab, Term(..), Program, Cmd(..), elabTests) where

import Values ( Lit(..) )
import Var (Var(..), TyVar, FunVar)
import Control.Monad.State (MonadState (put), get, StateT (runStateT))
import Control.Monad.Except (MonadError (throwError), ExceptT, runExceptT)
import Types

import qualified Frontend.SurfaceSyntax as Surf
import Control.Monad.Identity (Identity (runIdentity))
import Util.PrettyPrint (PrettyPrint(..))
import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad.RWS.Strict (MonadReader (local, ask))
import Control.Monad.Reader (ReaderT (runReaderT), asks)
import Test.HUnit
import Data.List (intercalate)
import qualified Data.Functor
import Data.Functor ((<&>))
import qualified HistPgm as Hist
import qualified Data.List as Hist

data Term =
      TmLitR Lit
    | TmEpsR
    | TmVar Var
    | TmCatL Var Var Var Term
    | TmCatR Term Term
    | TmParL Var Var Var Term
    | TmParR Term Term
    | TmInl Term
    | TmInr Term
    | TmPlusCase Var Var Term Var Term
    | TmIte Var Term Term
    | TmNil
    | TmCons Term Term
    | TmStarCase Var Term Var Var Term
    | TmCut Var Term Term
    | TmWait Var Term
    | TmHistPgm Hist.Term
    | TmRec (CtxStruct Term)
    | TmFunCall Var.FunVar [TyF Var.TyVar] (CtxStruct Term)
    deriving (Eq, Ord, Show)

instance PrettyPrint Term where
    pp = go False
        where
            go _ (TmLitR l) = pp l
            go _ TmEpsR = "sink"
            go _ (TmVar (Var x)) = x
            go _ TmNil = "nil"
            go _ (TmCatR e1 e2) = concat ["(",go False e1,";",go False e2,")"]
            go _ (TmParR e1 e2) = concat ["(",go False e1,",",go False e2,")"]
            go _ (TmHistPgm eh) = concat ["{",pp eh,"}"]
            go True e = concat ["(", go False e, ")"]
            go False (TmCatL (Var x) (Var y) (Var z) e) = concat ["let (",x,";",y,") = ",z," in ",go False e]
            go False (TmParL (Var x) (Var y) (Var z) e) = concat ["let (",x,",",y,") = ",z," in ",go False e]
            go False (TmIte z e1 e2) = concat ["if ", pp z, " then ", go True e1, " else ", go True e2]
            go False (TmInl e) = "inl " ++ go True e
            go False (TmInr e) = "inr " ++ go True e
            go False (TmPlusCase (Var z) (Var x) e1 (Var y) e2) = concat ["case ",z," of inl ",x," => ",go True e1," | inr",y," => ",go True e2]
            go False (TmCut (Var x) e1 e2) = concat ["let ",x," = ",go True e1," in ",go True e2]
            go False (TmCons e1 e2) = concat [go True e1," :: ", go True e2]
            go False (TmStarCase (Var z) e1 (Var x) (Var xs) e2) = concat ["case ",z," of nil => ",go True e1," | ",x,"::",xs," => ",go True e2]
            go False (TmRec es) = concat ["rec (", pp (go False <$> es), ")"]
            go False (TmFunCall f [] es) = concat [pp f,"(", pp (go False <$> es), ")"]
            go False (TmFunCall f ts es) = concat [pp f,"[",intercalate "," (map pp ts),"]","(", pp (go False <$> es), ")"]
            go False (TmWait x e) = concat ["wait ", pp x," do ", go True e]

data ElabState = ES { nextVar :: Int } deriving (Eq, Ord, Show)

data ElabErr =
      UnboundVar Var
    | EqualBoundVars Var
    | PolymorphicRec Var.FunVar
    deriving (Eq, Ord, Show)

instance PrettyPrint ElabErr where
    pp (UnboundVar (Var x)) = concat ["Variable ",x," not bound. This is a compiler bug."]
    pp (EqualBoundVars x) = concat ["Binding two copies of the same variable ",pp x]
    pp (PolymorphicRec f) = concat ["Polmorphic recursive calls not supported (function ",pp f,")"]

data ElabInput = EI {renaming :: M.Map Var Var, funName :: Var.FunVar}

class (MonadState ElabState m, MonadReader ElabInput m, MonadError ElabErr m) => ElabM m where


freshElabVar :: (ElabM m) => m Var
freshElabVar = do
    es <- get
    put $ ES (nextVar es + 1)
    return $ Var.Var $ "__x" ++ show (nextVar es)

withUnshadow :: (ElabM m) => Maybe Var -> m a -> m (a,Var)
withUnshadow Nothing u = do
    x <- freshElabVar
    a <- local (\(EI sm l) -> EI (M.insert x x sm) l) u
    return (a,x)
withUnshadow (Just x) u = do
    EI sm _ <- ask
    if M.member x sm then do
        y <- freshElabVar
        a <- local (\(EI sm' fn) -> EI (M.insert x y sm') fn) u
        return (a,y)
    else do
        a <- local (\(EI sm' fn) -> EI (M.insert x x sm') fn) u
        return (a,x)

unshadow :: (ElabM m) => Var -> m Var
unshadow x = do
    EI sm _ <- ask
    case M.lookup x sm of
        Just y -> return y
        Nothing -> throwError (UnboundVar x)

sameBinder :: Maybe Var -> Maybe Var -> Maybe Var
sameBinder Nothing _ = Nothing
sameBinder _ Nothing = Nothing
sameBinder (Just x) (Just y) = if x == y then Just x else Nothing

elab :: (ElabM m) => Surf.Term -> m Term
elab (Surf.TmLitR l) = return (TmLitR l)
elab Surf.TmEpsR = return TmEpsR
elab (Surf.TmHistPgm he) = TmHistPgm <$> elabHist he
elab (Surf.TmVar x) = TmVar <$> unshadow x
elab (Surf.TmCatL mx my e1 e2) = do
    case sameBinder mx my of
        Just x -> throwError (EqualBoundVars x)
        _ -> return ()
    e1' <- elab e1
    ((e2',y),x) <- withUnshadow mx $ withUnshadow my $ elab e2
    z <- freshElabVar
    return $ TmCut z e1' (TmCatL x y z e2')
elab (Surf.TmCatR e1 e2) = do
    e1' <- elab e1
    e2' <- elab e2
    return (TmCatR e1' e2')
elab (Surf.TmParL mx my e1 e2) = do
    case sameBinder mx my of
        Just x -> throwError (EqualBoundVars x)
        _ -> return ()
    e1' <- elab e1
    ((e2',y),x) <- withUnshadow mx $ withUnshadow my $ elab e2
    z <- freshElabVar
    return $ TmCut z e1' (TmParL x y z e2')
elab (Surf.TmParR e1 e2) = do
    e1' <- elab e1
    e2' <- elab e2
    return (TmParR e1' e2')
elab (Surf.TmInl e) = TmInl <$> elab e
elab (Surf.TmInr e) = TmInr <$> elab e
elab (Surf.TmIte e e1 e2) = do
    e' <- elab e
    e1' <- elab e1
    e2' <- elab e2
    z <- freshElabVar
    return $ TmCut z e' (TmIte z e1' e2')
elab (Surf.TmPlusCase e mx e1 my e2) = do
    e' <- elab e
    (e1',x) <- withUnshadow mx $ elab e1
    (e2',y) <- withUnshadow my $ elab e2
    z <- freshElabVar
    return $ TmCut z e' (TmPlusCase z x e1' y e2')
elab Surf.TmNil = return TmNil
elab (Surf.TmCons e1 e2) = TmCons <$> elab e1 <*> elab e2
elab (Surf.TmStarCase e e1 mx mxs e2) = do
    e' <- elab e
    e1' <- elab e1
    ((e2',xs),x) <- withUnshadow mx $ withUnshadow mxs $ elab e2
    z <- freshElabVar
    return $ TmCut z e' (TmStarCase z e1' x xs e2')
elab (Surf.TmFunCall f ts es) = do
    curF <- asks funName
    if f == curF then 
        if not (null ts) then throwError (PolymorphicRec f) else TmRec <$> mapM elab es
    else TmFunCall f ts <$> mapM elab es
elab (Surf.TmWait xs e) = do
    ys <- mapM unshadow xs
    go ys <$> elab e
    where
        go [] e' = e'
        go (x:xs') e' = TmWait x (go xs' e')
elab (Surf.TmCut x e1 e2) = do
    e1' <- elab e1
    (e2',x') <- withUnshadow (Just x) $ elab e2
    return (TmCut x' e1' e2')

elabHist :: (ElabM m) => Hist.Term -> m Hist.Term
elabHist (Hist.TmVar x) = Hist.TmVar <$> unshadow x
elabHist e@(Hist.TmValue _) = return e
elabHist e@Hist.TmEps = return e
elabHist (Hist.TmBinOp b e1 e2) = Hist.TmBinOp b <$> elabHist e1 <*> elabHist e2
elabHist (Hist.TmMonOp m e) = Hist.TmMonOp m <$> elabHist e
elabHist (Hist.TmPair e1 e2) = Hist.TmPair <$> elabHist e1 <*> elabHist e2
elabHist (Hist.TmInl e) = Hist.TmInl <$> elabHist e
elabHist (Hist.TmInr e) = Hist.TmInr <$> elabHist e
elabHist e@Hist.TmNil = return e
elabHist (Hist.TmCons e1 e2) = Hist.TmCons <$> elabHist e1 <*> elabHist e2
elabHist (Hist.TmIte e e1 e2) = Hist.TmIte <$> elabHist e <*> elabHist e1 <*> elabHist e2

{-TODO: ensure that fundefs have unique vars-}

instance ElabM (StateT ElabState (ReaderT ElabInput (ExceptT ElabErr Identity))) where

data Cmd =
      FunDef Var.FunVar [Var.TyVar] (Ctx Var.Var (TyF Var.TyVar)) (TyF Var.TyVar) Term
    | RunCommand Var.FunVar [Ty] (Ctx Var Surf.UntypedPrefix)
    | RunStepCommand Var.FunVar (Ctx Var Surf.UntypedPrefix)
    deriving (Eq,Ord,Show)

type Program = [Cmd]

initShadowMap g =
    let bindings = ctxBindings g in
    let ks = M.keysSet bindings in
    S.fold (\x -> M.insert x x) M.empty ks


elabSingle :: Var.FunVar -> Surf.Term -> S.Set Var -> Either ElabErr (Term, ElabState)
elabSingle f e s = runIdentity (runExceptT (runReaderT (runStateT (elab e) (ES 0)) $ initInput))
    where
        initInput = EI (S.fold (\x -> M.insert x x) M.empty s) f

doElab :: Surf.Program -> IO Program
doElab = mapM $ \case
                    (Surf.FunDef f tvs g s e) ->
                        case elabSingle f e (M.keysSet $ ctxBindings g) of
                            Right (e',_) -> do
                                putStrLn $ "Function " ++ pp f ++ " elaborated OK. Elab term: " ++ pp e' ++ "\n"
                                return (FunDef f tvs g s e')
                            Left err -> error (pp err)
                    (Surf.RunCommand s ts xs) ->
                        case mapM closeTy ts of
                            Left x -> error $ "Tried to run term " ++ pp s ++ ", but provided type with type variable " ++ pp x
                            Right ts' -> return (RunCommand s ts' xs)
                    (Surf.RunStepCommand s xs) -> return (RunStepCommand s xs)

-- >>> elabSingle (Surf.TmCatL Nothing Nothing (Surf.TmCatR (Surf.TmLitR (LInt 4)) (Surf.TmLitR (LInt 4))) Surf.TmEpsR) (S.fromList [])
-- Right (TmCut (Var "__x2") (TmCatR (TmLitR (LInt 4)) (TmLitR (LInt 4))) (TmCatL (Var "__x0") (Var "__x1") (Var "__x2") TmEpsR),ES {nextVar = 3})

elabTests :: Test
elabTests = TestList [
        elabTest (Surf.TmVar (Var.Var "x")) (TmVar (Var.Var "x")) ["x"],
        elabTest (Surf.TmCatL Nothing Nothing (Surf.TmCatR (Surf.TmLitR (LInt 4)) (Surf.TmLitR (LInt 4))) Surf.TmEpsR) (TmCut (Var "__x2") (TmCatR (TmLitR (LInt 4)) (TmLitR (LInt 4))) (TmCatL (Var "__x0") (Var "__x1") (Var "__x2") TmEpsR)) [],
        elabFails (Surf.TmCatL (Just (Var.Var "y")) (Just (Var.Var "y")) (Surf.TmVar $ Var.Var "x") Surf.TmEpsR) ["x"],
        elabTest (Surf.TmCatL (Just (Var.Var "y")) (Just (Var.Var "z")) (Surf.TmVar (Var.Var "z")) (Surf.TmVar (Var.Var "z"))) (TmCut (Var "__x1") (TmVar (Var "z")) (TmCatL (Var "y") (Var "__x0") (Var "__x1") (TmVar (Var "__x0")))) ["z"],
        elabFails (Surf.TmCatL (Just (Var.Var "y")) (Just (Var.Var "z")) (Surf.TmVar (Var.Var "z")) (Surf.TmVar (Var.Var "z"))) []
    ]
    where
        elabTest e e'' xs = TestCase $ do
            case elabSingle undefined e (S.fromList $ Var.Var <$> xs) of
                Right (e',_) -> assertEqual "" e' e''
                Left err -> assertFailure (pp err)
        elabFails e xs = TestCase $ do
            case elabSingle undefined e (S.fromList $ Var.Var <$> xs) of
                Right _ -> assertFailure "Expected failure"
                Left _ -> return ()
