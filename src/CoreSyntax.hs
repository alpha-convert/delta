{-# LANGUAGE FlexibleContexts, FlexibleInstances, TupleSections #-}
module CoreSyntax (
  Var,
  Term(..),
  Program,
  Cmd(..),
  substVar,
  sinkTm,
  cut,
  maximalPrefixSubst,
  fixSubst,
  cutArgs,
  bufMap
) where

import Types ( Ty , CtxStruct (..), Ctx, ctxFoldM, CtxEntry (..), TyF (..) )
import Values ( Lit(..), Env, lookupEnv, bindEnv, unbindEnv, Prefix (..), MaximalPrefix (..))
import Var (Var (..), TyVar, FunVar)
import qualified Data.Map as M
import Util.PrettyPrint (PrettyPrint(..))
import Control.Monad.Except (MonadError (throwError), ExceptT, withExceptT)
import Data.Bifunctor
import qualified HistPgm as Hist
import Debug.Trace (trace)
import Backend.Template (Template)
import Buffer
import Util.ErrUtil

data Term buf =
      TmLitR Lit
    | TmEpsR
    | TmVar Var
    | TmCatL Ty Var Var Var (Term buf)
    | TmCatR Ty (Term buf) (Term buf) -- Type of the first component
    | TmParL Var Var Var (Term buf)
    | TmParR (Term buf) (Term buf)
    | TmInl (Term buf)
    | TmInr (Term buf)
    | TmPlusCase buf Ty Var Var (Term buf) Var (Term buf)
    | TmIte  buf Ty Var (Term buf) (Term buf)
    | TmNil
    | TmCons Ty (Term buf) (Term buf) -- type of the first component
    | TmStarCase buf Ty Ty Var (Term buf) Var Var (Term buf) {- first return type, then star type -}
    | TmFix (CtxStruct (Term buf)) (Ctx Var Ty) Ty (Term buf)
    | TmRec (CtxStruct (Term buf))
    | TmWait buf Ty Ty Var (Term buf) -- first return type, then waiting type
    | TmCut Var (Term buf) (Term buf)
    | TmArgsCut (Ctx Var Ty) (CtxStruct (Term buf))  (Term buf)
    | TmHistPgm Ty Hist.Term
    deriving (Eq,Ord,Show)

data Cmd buf =
    FunDef Var.FunVar [Var.TyVar] (Template (Ctx Var.Var Ty)) (Template Ty) (Template (Term buf))
  | SpecializeCommand Var.FunVar [Ty]
  | RunCommand Var.FunVar  (Env Var Prefix)
  | RunStepCommand Var.FunVar (Env Var Prefix)
  | QuickCheckCommand Var.FunVar

type Program buf = [Cmd buf]

instance PrettyPrint buf => PrettyPrint (Term buf) where
    pp = go False
        where
            go _ (TmLitR l) = pp l
            go _ TmEpsR = "sink"
            go _ (TmVar x) = pp x
            go _ (TmCatR _ e1 e2) = concat ["(",go False e1,";",go False e2,")"]
            go _ (TmParR e1 e2) = concat ["(",go False e1,",",go False e2,")"]
            go _ TmNil = "nil"
            go _ (TmRec args) = "rec(" ++ pp args ++ ")"
            go _ (TmHistPgm _ he) = concat ["{", pp he, "}"]
            go True e = concat ["(", go False e, ")"]
            go _ (TmFix args _ _ e) = concat ["fix(",go False e,")[",pp args,"]"]
            go _ (TmCatL t x y z e) = concat ["let_{",pp t,"} (",pp x,";",pp y,") = ",pp z," in ",go False e]
            go _ (TmParL x y z e) = concat ["let (",pp x,",",pp y,") = ",pp z," in ",go False e]
            go _ (TmInl e) = "inl " ++ go True e
            go _ (TmInr e) = "inr " ++ go True e
            go _ (TmPlusCase rho _ z x e1 y e2) = concat ["case_",pp rho," ",pp z," of inl ",pp x," => ",go True e1," | inr",pp y," => ",go True e2]
            go _ (TmIte rho _ z e1 e2) = concat ["if_", pp rho," ", pp z," then ", go True e1," else ", go True e2]
            go _ (TmCons _ e1 e2) = concat [go True e1," :: ",go True e2]
            go _ (TmStarCase rho _ _ z e1 x xs e2) = concat ["case_",pp rho," ",pp z," of nil => ",go True e1," | ",pp x,"::",pp xs," => ",go True e2]
            go False (TmWait rho _ _ x e) = concat ["wait_",pp rho," ", pp x," do ", go True e]
            go _ (TmCut x e e') = concat ["let ",pp x," = ", go True e, " in ", go True e']
            go _ (TmArgsCut g e e') = concat ["let ", pp g, " = ", pp e, " in ", pp e']

rebind :: Ord k => M.Map k a -> k -> k -> M.Map k a
rebind m x z = case M.lookup z m of
                 Nothing -> error "Impossible"
                 Just p -> M.insert x p (M.delete z m)

-- substVar e x y = e[x/y]
-- Requires e be fully alpha-distinct (no shadowing.)
substVar :: (Buffer buf) => Term buf -> Var -> Var -> Term buf
substVar (TmLitR l) _ _ = TmLitR l
substVar TmEpsR _ _ = TmEpsR
substVar (TmVar x') x y | y == x' = TmVar x
substVar (TmVar x') _ _ = TmVar x'
substVar (TmCatL t x' y' z e) x y | y == z = TmCatL t x' y' x (substVar e x y)
substVar (TmCatL t x' y' z e) x y = TmCatL t x' y' z (substVar e x y) {- FIXME: ensure this doesn't capture!! -}
substVar (TmCatR s e1 e2) x y = TmCatR s (substVar e1 x y) (substVar e2 x y)
substVar (TmParL x' y' z e) x y = TmParL x' y' z (substVar e x y) {- FIXME: ensure this doesn't capture!! -}
substVar (TmParR e1 e2) x y = TmParR (substVar e1 x y) (substVar e2 x y)
substVar (TmInl e) x y = TmInl (substVar e x y)
substVar (TmInr e) x y = TmInr (substVar e x y)
substVar (TmPlusCase rho r z x' e1 y' e2) x y | y == z = TmPlusCase rho' r x x' (substVar e1 x y) y' (substVar e2 x y)
  where
    rho' = rebindBuf rho x y
substVar (TmPlusCase rho r z x' e1 y' e2) x y = TmPlusCase rho' r z x' (substVar e1 x y) y' (substVar e2 x y)
  where
    rho' = rebindBuf rho x y
substVar (TmIte rho r z e1 e2) x y | y == z = TmIte rho' r x (substVar e1 x y) (substVar e2 x y)
  where
    rho' = rebindBuf rho x y
substVar (TmIte rho r z e1 e2) x y = TmIte rho' r z (substVar e1 x y) (substVar e2 x y)
  where
    rho' = rebindBuf rho x y

substVar TmNil _ _ = TmNil
substVar (TmCons s e1 e2) x y = TmCons s (substVar e1 x y) (substVar e2 x y)
substVar (TmStarCase rho r s z e1 x' xs' e2) x y | y == z = TmStarCase rho' r s z (substVar e1 x y) x' xs' (substVar e2 x y)
  where
    rho' = rebindBuf rho x y
substVar (TmStarCase rho r s z e1 x' xs' e2) x y = TmStarCase rho' r s z (substVar e1 x y) x' xs' (substVar e2 x y)
  where
    rho' = rebindBuf rho x y
-- TODO: are these correct?
substVar (TmRec args) x y = TmRec $ (\e -> substVar e x y) <$> args
substVar (TmFix args g s e) x y = TmFix ((\e' -> substVar e' x y) <$> args) g s e
substVar (TmWait rho t s u e) x y = if x == u then TmWait rho' t s y (substVar e x y) else TmWait rho' t s u (substVar e x y)
  where
    rho' = rebindBuf rho y x

substVar (TmCut x' e1 e2) x y | x' == y = error "UH OH"
substVar (TmCut x' e1 e2) x y = TmCut x' (substVar e1 x y) (substVar e2 x y)
substVar (TmHistPgm t he) x y = TmHistPgm t (Hist.substVar he x y)
substVar (TmArgsCut g args e) x y = TmArgsCut g ((\e' -> substVar e' x y) <$> args) e

cut :: (Buffer buf, MonadError (Var,Term buf,Term buf) m) => Var -> Term buf -> Term buf -> m (Term buf)
cut x (TmVar y) e' = return (substVar e' y x)
cut _ _ e'@(TmLitR _) = return e'
cut _ _ e'@TmEpsR = return e'
cut _ _ e'@TmNil = return e'
cut x e e'@(TmVar y) = if x == y then return e else return e'
cut x e (TmCons s e1 e2) = TmCons s <$> cut x e e1 <*> cut x e e2
cut x e (TmParR e1 e2) = TmParR <$> cut x e e1 <*> cut x e e2
cut x e (TmCatR s e1 e2) = TmCatR s <$> cut x e e1 <*> cut x e e2

-- cut x e (TmFix args g s e') = do
--   args' <- mapM (\(CE u e'') -> (CE u) <$> cut x e e'') args
--   return (TmFix args' g s e')
cut x e (TmRec args) = TmRec <$> mapM (cut x e) args

cut x e e' = return (TmCut x e e')

{-

z:t | G(x:s) |- wait_rho(e') : r
rho : env(G(x:s)(z:t))
---------------------------------
. | G(x : s)(z:t) |- wait_rho(e') : r


. | G(.)(z : t) |- wait_

-}

-- cut x (TmCatL t' x'' y'' z' e'') e' = TmCatL t' x'' y'' z' <$> cut x e'' e'
-- cut x (TmPlusCase m rho r z x'' e1 y'' e2) e' = do
--     e1' <- cut x e1 e'
--     e2' <- cut x e2 e'
--     -- FIXME: Is this "rho" correct here? I think it might not be.
--     return (TmPlusCase m rho r z x'' e1' y'' e2')

-- cut x e                     (TmCatL t x' y' z e') | x /= z = TmCatL t x' y' z <$> cut x e e'
-- cut _ (TmVar z)        (TmCatL t x' y' _ e') = return (TmCatL t  x' y' z e')
-- cut _ (TmCatR e1 e2)   (TmCatL _ x' y' _ e') = cut x' e1 e' >>= cut y' e2
-- -- cut x e                     e'@(TmCatL {}) = throwError (x,e,e')

-- cut x e                 (TmPlusCase m rho t z x' e1 y' e2) | x /= z = do
--     e1' <- cut x e e1
--     e2' <- cut x e e2
--     return (TmPlusCase (M.delete x m) rho t z x' e1' y' e2')
-- cut z (TmVar x)    (TmPlusCase m rho t _ x' e1 y' e2) = return (TmPlusCase (rebind m x z) rho t x x' e1 y' e2)
-- cut _ (TmInl e)    (TmPlusCase _ _ _ _ x' e1 _ _) = cut x' e e1
-- cut _ (TmInr e)    (TmPlusCase _ _ _ _ _ _ y' e2) = cut y' e e2
-- -- cut x e                 e'@(TmPlusCase {}) = throwError (x,e,e')

-- cut x e (TmInl e') = TmInl <$> cut x e e'
-- cut x e (TmInr e') = TmInr <$> cut x e e'


-- cut x e                     (TmStarCase m rho t s z e1 y ys e2) | x /= z = do
--     e1' <- cut x e e1
--     e2' <- cut x e e2
--     return (TmStarCase (M.delete x m) rho t s z e1' y ys e2')

-- cut z (TmVar x)        (TmStarCase m rho t s _ e1 y ys e2) = return (TmStarCase (rebind m x z) rho t s x e1 y ys e2)
-- cut _ TmNil            (TmStarCase _ _ _ _ _ e1 _ _ _) = return e1
-- cut _ (TmCons eh et)   (TmStarCase _ _ _ _ _ _ y ys e2) = cut y eh e2 >>= cut ys et
-- cut x e                     e'@(TmStarCase {}) = throwError (x,e,e')

cutArgs :: MonadError (Ctx Var.Var Ty, CtxStruct (Term buf)) m => Ctx Var.Var Ty -> CtxStruct (Term buf) -> Term buf -> m (Term buf)
cutArgs EmpCtx EmpCtx e = return e
cutArgs (SngCtx (CE x _)) (SngCtx e') e = return (TmCut x e' e)
cutArgs (SemicCtx g1 g2) (SemicCtx g1' g2') e = do
    e' <- cutArgs g1 g1' e
    cutArgs g2 g2' e'
cutArgs (CommaCtx g1 g2) (CommaCtx g1' g2') e = do
    e' <- cutArgs g1 g1' e
    cutArgs g2 g2' e'
cutArgs g g' _ = throwError (g,g')

-- Throws p if p is not maximal. if p : s and p maximal, the sinkTm : d_p s.
-- At the moment (without par), this returns only TmEpsR
sinkTm :: (MonadError Prefix m) => Prefix -> m (Term buf)
sinkTm p@LitPEmp = throwError p
sinkTm (LitPFull _) = return TmEpsR
sinkTm EpsP = return TmEpsR
sinkTm p@(CatPA _) = throwError p
sinkTm (CatPB _ p) = sinkTm p
sinkTm (ParP p1 p2) = do
  e1 <- sinkTm p1
  e2 <- sinkTm p2
  return (TmParR e1 e2)
sinkTm p@SumPEmp = throwError p
sinkTm (SumPA p) = sinkTm p
sinkTm (SumPB p) = sinkTm p
sinkTm p@StpEmp = throwError p
sinkTm StpDone = return TmEpsR
sinkTm p@(StpA _) = throwError p
sinkTm (StpB _ p) = sinkTm p

maximalPrefixToTerm :: (MonadError (Ty,MaximalPrefix) m) => Ty -> MaximalPrefix -> m (Term buf)
maximalPrefixToTerm TyEps EpsMP = return TmEpsR
maximalPrefixToTerm t p@EpsMP = throwError (t,p)
maximalPrefixToTerm TyInt (LitMP l@(LInt _)) = return (TmLitR l)
maximalPrefixToTerm t p@(LitMP (LInt _)) = throwError (t,p)
maximalPrefixToTerm TyBool (LitMP l@(LBool _)) = return (TmLitR l)
maximalPrefixToTerm t p@(LitMP (LBool _)) = throwError (t,p)
{- That s in TmCatR is the only reason this substitution nees to be typed. -}
maximalPrefixToTerm (TyCat s t) (CatMP p1 p2) = TmCatR s <$> maximalPrefixToTerm s p1 <*> maximalPrefixToTerm t p2 
maximalPrefixToTerm t p@(CatMP _ _) = throwError (t,p)
maximalPrefixToTerm (TyPar s t) (ParMP p1 p2) = TmParR <$> maximalPrefixToTerm s p1 <*> maximalPrefixToTerm t p2
maximalPrefixToTerm t p@(ParMP _ _) = throwError (t,p)
maximalPrefixToTerm (TyPlus s _) (SumMPA p) = TmInl <$> maximalPrefixToTerm s p
maximalPrefixToTerm t p@(SumMPA _) = throwError (t,p)
maximalPrefixToTerm (TyPlus _ t) (SumMPB p) = TmInr <$> maximalPrefixToTerm t p
maximalPrefixToTerm t p@(SumMPB _) = throwError (t,p)
maximalPrefixToTerm (TyStar s) (StMP ps) = go s ps
  where
    go s [] = return TmNil
    go s (p:ps') = TmCons s <$> maximalPrefixToTerm s p <*> go s ps'
maximalPrefixToTerm t p@(StMP _) = throwError (t,p)

{- Would be ideal to get rid of this, and instead have histvalsubst. -}
maximalPrefixSubst :: (Buffer buf, Monad m) => Ty -> MaximalPrefix -> Var -> Term buf -> ExceptT (Var,Ty,MaximalPrefix,Term buf) m (Term buf)
maximalPrefixSubst _ _ _ e@(TmLitR _) = return e
maximalPrefixSubst _ _ _ e@TmEpsR = return e
maximalPrefixSubst s p x e@(TmVar y) | x == y = reThrow (\(t,mp) -> (x,t,mp,e)) (maximalPrefixToTerm s p)
maximalPrefixSubst _ _ _ e@(TmVar _) = return e

maximalPrefixSubst s p x (TmCatL t x' y' z e') | x /= z = TmCatL t x' y' z <$> maximalPrefixSubst s p x e'
maximalPrefixSubst (TyCat s t) (CatMP p1 p2) _ (TmCatL _ x' y' _ e') = do
  e'' <- maximalPrefixSubst s p1 x' e'
  maximalPrefixSubst t p2 y' e''
maximalPrefixSubst s p x e@(TmCatL {}) = throwError (x,s,p,e)

maximalPrefixSubst s p x (TmCatR s' e1 e2) = do
  e1' <- maximalPrefixSubst s p x e1
  e2' <- maximalPrefixSubst s p x e2
  return (TmCatR s' e1' e2')

maximalPrefixSubst s p x (TmParL x' y' z e') | x /= z = TmParL x' y' z <$> maximalPrefixSubst s p x e'
maximalPrefixSubst (TyPar s t) (ParMP p1 p2) _ (TmParL x' y' _ e') = do
  e'' <- maximalPrefixSubst s p1 x' e'
  maximalPrefixSubst t p2 y' e''
maximalPrefixSubst s p x e@(TmParL {}) = throwError (x,s,p,e)

maximalPrefixSubst s p x (TmParR e1 e2) = do
  e1' <- maximalPrefixSubst s p x e1
  e2' <- maximalPrefixSubst s p x e2
  return (TmParR e1' e2')


maximalPrefixSubst s p x (TmInl e') = TmInl <$> maximalPrefixSubst s p x e'
maximalPrefixSubst s p x (TmInr e') = TmInr <$> maximalPrefixSubst s p x e'

maximalPrefixSubst s p x (TmPlusCase rho t z x' e1 y' e2) | x /= z = do
  e1' <- maximalPrefixSubst s p x e1
  e2' <- maximalPrefixSubst s p x e2
  return (TmPlusCase (unbindBuf x rho) t z x' e1' y' e2')
maximalPrefixSubst (TyPlus s _) (SumMPA p) _ (TmPlusCase _ _ _ x' e1 _ _) = maximalPrefixSubst s p x' e1
maximalPrefixSubst (TyPlus _ t) (SumMPB p) _ (TmPlusCase _ _ _ _ _ y' e2) = maximalPrefixSubst t p y' e2
maximalPrefixSubst s p x e@(TmPlusCase {}) = throwError (x,s,p,e)

maximalPrefixSubst s p x (TmIte rho t z e1 e2) | x /= z = do
  e1' <- maximalPrefixSubst s p x e1
  e2' <- maximalPrefixSubst s p x e2
  return (TmIte (unbindBuf x rho) t z e1' e2')
maximalPrefixSubst TyBool (LitMP (LBool True)) _ (TmIte _ _ _ e1 _) = return e1
maximalPrefixSubst TyBool (LitMP (LBool False)) _ (TmIte _ _ _ _ e2) = return e2
maximalPrefixSubst s p x e@(TmIte {}) = throwError (x,s,p,e)

maximalPrefixSubst s p x (TmStarCase rho t r z e1 y' ys' e2) | x /= z = do
  e1' <- maximalPrefixSubst s p x e1
  e2' <- maximalPrefixSubst s p x e2
  return (TmStarCase (unbindBuf x rho) t r z e1' y' ys' e2')
maximalPrefixSubst (TyStar _) (StMP []) _ (TmStarCase _ _ _ _ e1 _ _ _) = return e1
maximalPrefixSubst (TyStar s) (StMP (p:ps)) _ (TmStarCase _ _ _ _ _ y' ys' e2) = do
  e2' <- maximalPrefixSubst s p y' e2
  maximalPrefixSubst (TyStar s) (StMP ps) ys' e2'
maximalPrefixSubst s p x e@(TmStarCase {}) = throwError (x,s,p,e)

maximalPrefixSubst s _ _ e@TmNil = return e
maximalPrefixSubst s p x (TmCons s' e1 e2) = do
  e1' <- maximalPrefixSubst s p x e1
  e2' <- maximalPrefixSubst s p x e2
  return (TmCons s' e1' e2')

maximalPrefixSubst s' p x (TmWait rho t s z e') | x /= z = TmWait (unbindBuf x rho) t s z <$> maximalPrefixSubst s' p x e'
maximalPrefixSubst s p _ (TmWait _ _ _ x e') = maximalPrefixSubst s p x e'

maximalPrefixSubst s' p x (TmFix args g s e') = do
  args' <- mapM (maximalPrefixSubst s' p x) args
  return (TmFix args' g s e')

maximalPrefixSubst s p x (TmRec args) = TmRec <$> mapM (maximalPrefixSubst s p x) args

maximalPrefixSubst s p x (TmCut y e1 e2) = do
  e1' <- maximalPrefixSubst s p x e1
  e2' <- maximalPrefixSubst s p x e2
  return (TmCut y e1' e2')

maximalPrefixSubst s p x (TmHistPgm t he) = TmHistPgm t <$> withExceptT liftErr (Hist.maximalPrefixSubst p x he)
  where
    liftErr (x,p,e) = (x,s,p,TmHistPgm t e)

maximalPrefixSubst s p x (TmArgsCut g args e) = do
  args' <- mapM (maximalPrefixSubst s p x) args
  return (TmArgsCut g args' e)

fixSubst :: CtxStruct (CtxEntry Var Ty) -> Ty -> Term buf -> Term buf -> Term buf
fixSubst g s e = go
    where
        go TmEpsR = TmEpsR
        go (TmLitR l) = TmLitR l
        go (TmVar x) = TmVar x
        go (TmCatL t x y z e') = TmCatL t x y z (go e')
        go (TmCatR s e1 e2) = TmCatR s (go e1) (go e2)
        go (TmParL x y z e') = TmParL x y z (go e')
        go (TmParR e1 e2) = TmParR (go e1) (go e2)
        go (TmInl e') = TmInl (go e')
        go (TmInr e') = TmInr (go e')
        go (TmPlusCase rho r z x e1 y e2) = TmPlusCase rho r z x (go e1) y (go e2)
        go (TmIte rho r z e1 e2) = TmIte rho r z (go e1) (go e2)
        go TmNil = TmNil
        go (TmCons s e1 e2) = TmCons s (go e1) (go e2)
        go (TmStarCase rho r t z e1 y ys e2) = TmStarCase rho r t z (go e1) y ys (go e2)
        go (TmFix args g' s' e') = TmFix (fmap go args) g' s' e'
        go (TmRec args) = TmFix args g s e
        go (TmWait rho r s x e') = TmWait rho r s x (go e')
        go (TmCut x e1 e2) = TmCut x (go e1) (go e2)
        go (TmHistPgm t he) = TmHistPgm t he
        go (TmArgsCut g args e) = TmArgsCut g (go <$> args) e

bufMap :: (buf -> buf') -> Term buf -> Term buf'
bufMap _ (TmLitR l) = TmLitR l
bufMap _ TmEpsR = TmEpsR
bufMap _ (TmVar x) = TmVar x
bufMap f (TmCatL t x y z e) = TmCatL t x y z (bufMap f e)
bufMap f (TmCatR t e1 e2) = TmCatR t (bufMap f e1) (bufMap f e2)
bufMap f (TmParL x y z e) = TmParL x y z (bufMap f e)
bufMap f (TmParR e1 e2) = TmParR (bufMap f e1) (bufMap f e2)
bufMap f (TmInl e) = TmInl (bufMap f e)
bufMap f (TmInr e) = TmInr (bufMap f e)
bufMap f (TmPlusCase buf r z x e1 y e2) = TmPlusCase (f buf) r z x (bufMap f e1) y (bufMap f e2)
bufMap f (TmIte buf t z e1 e2) = TmIte (f buf) t z (bufMap f e1) (bufMap f e2)
bufMap _ TmNil = TmNil
bufMap f (TmCons t e1 e2) = TmCons t (bufMap f e1) (bufMap f e2)
        -- go (TmStarCase rho r t z e1 y ys e2) = TmStarCase rho r t z (go e1) y ys (go e2)
bufMap f (TmStarCase buf r t z e1 y ys e2) = TmStarCase (f buf) r t z (bufMap f e1) y ys (bufMap f e2)
bufMap f (TmFix args g t e) = TmFix (bufMap f <$> args) g t (bufMap f e)
bufMap f (TmRec args) = TmRec (bufMap f <$> args)
bufMap f (TmWait buf r t z e) = TmWait (f buf) r t z (bufMap f e)
bufMap f (TmCut x e1 e2) = TmCut x (bufMap f e1) (bufMap f e2)
bufMap _ (TmHistPgm s hp) = TmHistPgm s hp
bufMap f (TmArgsCut g args e) = TmArgsCut g (bufMap f <$> args) (bufMap f e)