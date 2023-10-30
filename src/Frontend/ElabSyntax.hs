{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
module Frontend.ElabSyntax (doElab, Term(..), Program, FunDef(..), RunCmd(..), elabTests) where

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
import Test.HUnit

data Term =
      TmLitR Lit
    | TmEpsR
    | TmVar Var
    | TmCatL Var Var Var Term
    | TmCatR Term Term
    | TmInl Term
    | TmInr Term
    | TmPlusCase Var Var Term Var Term
    | TmNil
    | TmCons Term Term
    | TmStarCase Var Term Var Var Term
    | TmCut Var Term Term
    deriving (Eq, Ord, Show)

instance PrettyPrint Term where
    pp = go False
        where
            go _ (TmLitR l) = pp l
            go _ TmEpsR = "sink"
            go _ (TmVar (Var x)) = x
            go _ TmNil = "nil"
            go _ (TmCatR e1 e2) = concat ["(",go False e1,";",go False e2,")"]
            go True e = concat ["(", go False e, ")"]
            go False (TmCatL (Var x) (Var y) (Var z) e) = concat ["let (",x,";",y,") = ",z," in ",go False e]
            go False (TmInl e) = "inl " ++ go True e
            go False (TmInr e) = "inl " ++ go True e
            go False (TmPlusCase (Var z) (Var x) e1 (Var y) e2) = concat ["case ",z," of inl ",x," => ",go True e1," | inr",y," => ",go True e2]
            go False (TmCut (Var x) e1 e2) = concat ["let ",x," = ",go True e1," in ",go True e2]
            go False (TmCons e1 e2) = concat [go True e1," :: ", go True e2]
            go False (TmStarCase (Var z) e1 (Var x) (Var xs) e2) = concat ["case ",z," of nil => ",go True e1," | ",x,"::",xs," => ",go True e2]

data ElabState = ES { nextVar :: Int } deriving (Eq, Ord, Show)

data ElabErr =
      UnboundVar Var
    | EqualBoundVars Var
    deriving (Eq, Ord, Show)

instance PrettyPrint ElabErr where
    pp (UnboundVar (Var x)) = concat ["Variable ",x," not bound. This is a compiler bug."]
    pp (EqualBoundVars x) = concat ["Binding two copies of the same variable ",pp x]

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

sameBinder :: Maybe Var -> Maybe Var -> Maybe Var
sameBinder Nothing _ = Nothing
sameBinder _ Nothing = Nothing
sameBinder (Just x) (Just y) = if x == y then Just x else Nothing

elab :: (ElabM m) => Surf.Term -> m Term
elab (Surf.TmLitR l) = return (TmLitR l)
elab Surf.TmEpsR = return TmEpsR
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
elab (Surf.TmInl e) = TmInl <$> elab e
elab (Surf.TmInr e) = TmInr <$> elab e
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

{-TODO: ensure that fundefs have unique vars-}

instance ElabM (StateT ElabState (ReaderT (M.Map Var Var) (ExceptT ElabErr Identity))) where

data FunDef = FD String (Ctx Var.Var) Ty Term deriving (Eq,Ord,Show)

data RunCmd = RC String (M.Map Var.Var Surf.UntypedPrefix)

type Program = [Either FunDef RunCmd]

initShadowMap g =
    let bindings = ctxBindings g in
    let ks = M.keysSet bindings in
    S.fold (\x -> M.insert x x) M.empty ks


elabSingle :: Surf.Term -> S.Set Var -> Either ElabErr (Term, ElabState)
elabSingle e s = runIdentity (runExceptT (runReaderT (runStateT (elab e) (ES 0)) $ S.fold (\x -> M.insert x x) M.empty s))

doElab :: Surf.Program -> IO Program
doElab = mapM $ \case
                    Right (Surf.RC s xs) -> return (Right (RC s (M.fromList xs)))
                    Left (Surf.FD f g s e) ->
                        case elabSingle e (M.keysSet $ ctxBindings g) of
                            Right (e',_) -> return (Left (FD f g s e'))
                            Left err -> error (pp err)

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
            case elabSingle e (S.fromList $ Var.Var <$> xs) of
                Right (e',_) -> assertEqual "" e' e''
                Left err -> assertFailure (pp err)
        elabFails e xs = TestCase $ do
            case elabSingle e (S.fromList $ Var.Var <$> xs) of
                Right _ -> assertFailure "Expected failure"
                Left _ -> return ()

-- >>> elabSingle (Surf.TmCatL (Just (Var.Var "y")) (Just (Var.Var "z")) (Surf.TmVar (Var.Var "z")) (Surf.TmVar (Var.Var "y"))) (S.fromList $ Var.Var <$> ["z"])
-- Right (TmCut (Var "__x1") (TmVar (Var "z")) (TmCatL (Var "y") (Var "__x0") (Var "__x1") (TmVar (Var "y"))),ES {nextVar = 2})

-- Found hole: _ :: Term
-- In the first argument of `elab', namely `(_)'
-- In the expression: elab (_)
-- In an equation for `it_aGCJH': it_aGCJH = elab (_)
-- Relevant bindings include
--   it_aGCJH :: m_aGEPa[sk:1] Term
--     (bound at /Users/jwc/Documents/research/Creek/src/Frontend/ElabSyntax.hs:146:2)
-- Constraints include
--   ElabM
--     m_aGEPa[sk:1] (from /Users/jwc/Documents/research/Creek/src/Frontend/ElabSyntax.hs:146:2-9)
-- Valid hole fits include
--   TmEpsR
--   TmNil
-- Valid refinement hole fits include
--   TmInl _
--   TmInr _
--   TmLitR _
--   TmVar _
--   head _
--   minimum _
--   last _
--   maximum _
--   id _
--   ask _
--   (Some refinement hole fits suppressed; use -fmax-refinement-hole-fits=N or -fno-max-refinement-hole-fits)

-- parseTests = TestList $ [
--         testParse "x" (Surf.TmVar (Var.Var "x")),
--         testParse "3" (Surf.TmLitR (LInt 3)),
--         testParse "true" (Surf.TmLitR (LBool True)),
--         testParse "x :: 5" (Surf.TmCons (Surf.TmVar $ Var.Var "x") (Surf.TmLitR $ LInt 5)),
--         testParse "let (x;_) = (5;false) in inl (a :: nil)" (Surf.TmCatL (Just (Var.Var "x")) Nothing (Surf.TmCatR (Surf.TmLitR $ LInt 5) (Surf.TmLitR $ LBool False)) (Surf.TmInl (Surf.TmCons (Surf.TmVar (Var.Var "a")) Surf.TmNil))),
--         testParse "case (x :: (let (u;v) = l in u) :: ys) of nil => 4 | z :: _ => (z;ys)" (Surf.TmStarCase (Surf.TmCons (Surf.TmVar (Var.Var "x")) (Surf.TmCons (Surf.TmCatL (Just (Var.Var "u")) (Just (Var.Var "v")) (Surf.TmVar (Var.Var "l")) (Surf.TmVar (Var.Var "u"))) (Surf.TmVar (Var.Var "ys")))) (Surf.TmLitR (LInt 4)) (Just $ Var.Var "z") Nothing (Surf.TmCatR (Surf.TmVar (Var.Var "z")) (Surf.TmVar (Var.Var "ys"))))
--     ]
--     where
--         testParse s e = TestCase $ e @?= parseSurfaceSyntax (lexer s)
