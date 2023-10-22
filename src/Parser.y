{
module Parser(parseSurfaceSyntax, parseFunDef, lexer) where
import SurfaceSyntax(Term(..), FunDef(..))
import Values ( Lit(..))
import Var(Var(..))
import Types
import Data.Char ( isDigit, isAlpha, isSpace )

}

%name parseSurfaceSyntax Exp
%name parseTy Ty
%name parseFunDef FunDef
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
      fun             { TokenFun }
      bool            { TokenBool $$ }
      int             { TokenInt $$ }
      var             { TokenVar (Var.Var $$) }
      tyInt           { TokenTyInt }
      tyBool          { TokenTyBool }
      tyEps           { TokenTyEps }
      '='             { TokenEq }
      '('             { TokenOB }
      ')'             { TokenCB }
      '['             { TokenOS }
      ']'             { TokenCS }
      ','             { TokenComma }
      ';'             { TokenSemic }
      ':'             { TokenColon }
      '_'             { TokenWild }
      '|'             { TokenPipe }
      '=>'            { TokenArr }
      '.'             { TokenDot }
      '+'             { TokenPlus }

%%

Var     : var     { Var.Var $1 }

WildVar : '_'     { Nothing }
        | Var     { Just $1 }

Exp   : let '(' WildVar ';' WildVar ')' '=' Exp in Exp            { TmCatL $3 $5 $8 $10 }
      | '(' Exp ';' Exp ')'                                       { TmCatR $2 $4 }
      | inl Exp                                                   { TmInl $2 }
      | inr Exp                                                   { TmInr $2 }
      | case Exp of inl WildVar '=>' Exp '|' inr WildVar '=>' Exp { TmPlusCase $2 $5 $7 $10 $12}
      | int                                                       { TmLitR (LInt $1) }
      | bool                                                      { TmLitR (LBool $1) }
      | sink                                                      { TmEpsR }
      | Var                                                       { TmVar $1 }
      | '(' Exp ')'                                               { $2 }

Ty    : Ty1 '+' Ty1                                               { TyPlus $1 $3 }
      | Ty1                                                       { $1 }

Ty1   : Ty2 '.' Ty2                                               { TyCat $1 $3 }
      | Ty2                                                       { $1 }

Ty2   : tyInt                                                     { TyInt }
      | tyBool                                                    { TyBool }
      | tyEps                                                     { TyEps }
      | '(' Ty ')'                                                { $2 }

FunDef      : fun var '(' Args ')' ':' Ty '=' Exp                      { FD $2 $4 $7 $9 }

Args  : {-empty-}                                                 { [] }
      | Var ':' Ty                                                { [($1,$3)] }
      | Var ':' Ty ';' Args                                       { ($1,$3):$5 }

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
      | TokenFun
      | TokenInt Int
      | TokenBool Bool
      | TokenVar Var.Var
      | TokenEq
      | TokenComma
      | TokenSemic
      | TokenColon
      | TokenArr
      | TokenWild
      | TokenPipe
      | TokenOB
      | TokenCB
      | TokenOS
      | TokenCS
      | TokenDot
      | TokenPlus
      | TokenTyInt
      | TokenTyBool
      | TokenTyEps
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
lexer ('.':cs) = TokenDot : lexer cs
lexer ('+':cs) = TokenPlus : lexer cs
lexer (';':cs) = TokenSemic : lexer cs
lexer (':':cs) = TokenColon : lexer cs
lexer ('_':cs) = TokenWild : lexer cs
lexer ('(':cs) = TokenOB : lexer cs
lexer (')':cs) = TokenCB : lexer cs
lexer ('[':cs) = TokenOS : lexer cs
lexer (']':cs) = TokenCS : lexer cs
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
      ("fun",rest)  -> TokenFun : lexer rest
      ("true",rest)  -> TokenBool True : lexer rest
      ("false",rest)  -> TokenBool False : lexer rest
      ("Eps",rest)  -> TokenTyEps : lexer rest
      ("Int",rest)  -> TokenTyInt : lexer rest
      ("Bool",rest)  -> TokenTyBool : lexer rest
      (var,rest)   -> TokenVar (Var.Var var) : lexer rest


}
