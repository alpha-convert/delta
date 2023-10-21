{
module Parser(parseSurfaceSyntax, lexer, Term(..)) where
import SurfaceSyntax(SurfaceSyntax(..))
import Values ( Lit(..))
import Var(Var(..))
import Data.Char ( isDigit, isAlpha, isSpace )

}

%name parseSurfaceSyntax Exp
%tokentype { Token }
%error { parseError }

%token
      let             { TokenLet }
      in              { TokenIn }
      sink            { TokenSink }
      case            { TokenCase }
      of              { TokenOf }
      inl             { TokenInl }
      inr             { TokenInr }
      bool            { TokenBool $$ }
      int             { TokenInt $$ }
      var             { TokenVar (Var.Var $$) }
      '='             { TokenEq }
      '('             { TokenOB }
      ')'             { TokenCB }
      ','             { TokenComma }
      ';'             { TokenSemic }
      '_'             { TokenWild }
      '|'             { TokenPipe }
      '=>'            { TokenArr }

%%

Var     : var     { Var.Var $1 }

WildVar : '_'     { Nothing }
        | Var     { Just $1 }



Exp   : let '(' WildVar ';' WildVar ')' '=' Var in Exp            { TmCatL $3 $5 $8 $10 }
      | '(' Exp ';' Exp ')'                                       { TmCatR $2 $4 }
      | inl Exp                                                   { TmInl $2 }
      | inr Exp                                                   { TmInr $2 }
      | case Var of inl WildVar '=>' Exp '|' inr WildVar '=>' Exp { TmPlusCase $2 $5 $7 $10 $12}
      | int                                                       { TmLitR (LInt $1) }
      | bool                                                      { TmLitR (LBool $1) }
      | sink                                                      { TmEpsR }
      | Var                                                       { TmVar $1 }
      | '(' Exp ')'                                               { $2 }


{

parseError :: [Token] -> a
parseError _ = error "Parse error"

data Token
      = TokenLet
      | TokenIn
      | TokenSink
      | TokenCase
      | TokenOf
      | TokenInl
      | TokenInr
      | TokenInt Int
      | TokenBool Bool
      | TokenVar Var.Var
      | TokenEq
      | TokenComma
      | TokenSemic
      | TokenArr
      | TokenWild
      | TokenPipe
      | TokenOB
      | TokenCB
      deriving (Show)

lexer :: String -> [Token]
lexer [] = []
lexer (c:cs)
      | isSpace c = lexer cs
      | isAlpha c = lexVar (c:cs)
      | isDigit c = lexNum (c:cs)
lexer ('=':'>':cs) = TokenArr : lexer cs
lexer ('=':cs) = TokenEq : lexer cs
lexer (',':cs) = TokenComma : lexer cs
lexer (';':cs) = TokenSemic : lexer cs
lexer ('_':cs) = TokenWild : lexer cs
lexer ('(':cs) = TokenOB : lexer cs
lexer (')':cs) = TokenCB : lexer cs
lexer ('|':cs) = TokenPipe : lexer cs

lexNum cs = TokenInt (read num) : lexer rest
      where (num,rest) = span isDigit cs

lexVar cs =
   case span isAlpha cs of
      ("let",rest) -> TokenLet : lexer rest
      ("in",rest)  -> TokenIn : lexer rest
      ("sink",rest)  -> TokenSink : lexer rest
      ("case",rest)  -> TokenCase : lexer rest
      ("of",rest)  -> TokenOf : lexer rest
      ("inl",rest)  -> TokenInl : lexer rest
      ("inr",rest)  -> TokenInr : lexer rest
      ("true",rest)  -> TokenBool True : lexer rest
      ("false",rest)  -> TokenBool False : lexer rest
      (var,rest)   -> TokenVar (Var.Var var) : lexer rest


}
