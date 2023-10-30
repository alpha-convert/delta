import Test.HUnit
import Frontend.Parser (lexer, parseSurfaceSyntax)

import qualified CoreSyntax as Core
import qualified Frontend.SurfaceSyntax as Surf
import qualified Frontend.ElabSyntax as Elab
import qualified Var
import Values (Lit(..))
import qualified Semantics as Sem

main :: IO ()
main = runTestTT parseTests >> runTestTT Elab.elabTests >> runTestTT Sem.semTests >> return ()


parseTests = TestList $ [
        testParse "x" (Surf.TmVar (Var.Var "x")),
        testParse "3" (Surf.TmLitR (LInt 3)),
        testParse "true" (Surf.TmLitR (LBool True)),
        testParse "x :: 5" (Surf.TmCons (Surf.TmVar $ Var.Var "x") (Surf.TmLitR $ LInt 5)),
        testParse "let (x;_) = (5;false) in inl (a :: nil)" (Surf.TmCatL (Just (Var.Var "x")) Nothing (Surf.TmCatR (Surf.TmLitR $ LInt 5) (Surf.TmLitR $ LBool False)) (Surf.TmInl (Surf.TmCons (Surf.TmVar (Var.Var "a")) Surf.TmNil))),
        testParse "case (x :: (let (u;v) = l in u) :: ys) of nil => 4 | z :: _ => (z;ys)" (Surf.TmStarCase (Surf.TmCons (Surf.TmVar (Var.Var "x")) (Surf.TmCons (Surf.TmCatL (Just (Var.Var "u")) (Just (Var.Var "v")) (Surf.TmVar (Var.Var "l")) (Surf.TmVar (Var.Var "u"))) (Surf.TmVar (Var.Var "ys")))) (Surf.TmLitR (LInt 4)) (Just $ Var.Var "z") Nothing (Surf.TmCatR (Surf.TmVar (Var.Var "z")) (Surf.TmVar (Var.Var "ys"))))
    ]
    where
        testParse s e = TestCase $ e @?= parseSurfaceSyntax (lexer s)

-- >>> Elab.doElab