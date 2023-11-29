{-# LANGUAGE  FlexibleContexts #-}
module Backend.SemError where
import qualified Var
import Values
import CoreSyntax
import qualified HistPgm as Hist
import Types
import Util.PrettyPrint
import Control.Monad.Except (MonadError, ExceptT, runExceptT, throwError)

data SemError =
      VarLookupFailed Var.Var
    | NotCatPrefix Var.Var Prefix
    | NotParPrefix Var.Var Prefix
    | NotPlusPrefix Var.Var Prefix
    | NotBoolPrefix Var.Var Prefix
    | ConcatError Term Var.Var Prefix Prefix
    | RuntimeCutError Var.Var Term Term
    | SinkError Prefix
    | MaximalPrefixSubstErr Var.Var Values.MaximalPrefix Term
    | MaximalPrefixError Prefix
    | HistSemErr Hist.SemErr Hist.Term
    | NonMatchingArgs (Ctx Var.Var Ty) (CtxStruct Term)
    | UnionEnvError Var.Var Prefix Prefix
    deriving (Eq, Ord, Show)

instance PrettyPrint SemError where
    pp (VarLookupFailed (Var.Var x)) = concat ["Variable ",x," is unbound. This is a compiler bug."]
    pp (NotCatPrefix (Var.Var z) p) = concat ["Expected variable ",z," to be a cat-prefix. Instead got: ",pp p]
    pp (NotParPrefix (Var.Var z) p) = concat ["Expected variable ",z," to be a par-prefix. Instead got: ",pp p]
    pp (NotPlusPrefix (Var.Var z) p) = concat ["Expected variable ",z," to be a plus-prefix. Instead got: ",pp p]
    pp (NotBoolPrefix (Var.Var z) p) = concat ["Expected variable ",z," to be a bool-prefix. Instead got: ",pp p]
    pp (ConcatError e x p p') = concat ["Tried to concatenate prefixes ", pp p," and ",pp p', " for variable ", pp x, " in term ", pp e]
    pp (RuntimeCutError x e e') = concat ["Error occurred when trying to cut ",pp x," = ",pp e, " in ", pp e',". This is a bug."]
    pp (SinkError p) = concat ["Tried to build sink term for prefix ", pp p, ". This is a bug."]
    pp (MaximalPrefixSubstErr x p e) = concat ["Failed to substitute prefix ", pp p," for ", pp x, " in term ", pp e]
    pp (MaximalPrefixError p) = concat ["Expected prefix ", pp p," to be maximal."]
    pp (HistSemErr err he) = concat ["Encountered error while evaluating historical term ", pp he, ": ", pp err]
    pp (NonMatchingArgs g g') = concat ["Arguments ", pp g', " do not match ", pp g]
    pp (UnionEnvError x p p') = concat ["Variable ", pp x, " has two different bindings: ", pp p, " and ", pp p']

handleConcatError :: Term -> (Var.Var,Prefix, Prefix) -> SemError
handleConcatError e (x,p,p') = ConcatError e x p p'

handleRuntimeCutError :: (Var.Var, Term, Term) -> SemError
handleRuntimeCutError (x,e,e') = RuntimeCutError x e e'

handlePrefixSubstError :: (Var.Var,Values.MaximalPrefix, Term) -> SemError
handlePrefixSubstError (x,p,e) = MaximalPrefixSubstErr x p e

handleHistEvalErr :: Hist.Term -> Hist.SemErr -> SemError
handleHistEvalErr e err = HistSemErr err e

reThrow :: (MonadError SemError m) => (e -> SemError) -> ExceptT e m a -> m a
reThrow k x = runExceptT x >>= either (throwError . k) return