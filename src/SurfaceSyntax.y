{
module TestGrammar where

import Values ( Lit(..))

parseError :: [Token] -> a
parseError _ = error "Parse error"


data Var = Var String

data Term =
      TmLitR Lit
    | TmEpsR
    | TmVar Var
    | TmCatL (Maybe Var) (Maybe Var) Var Term
    | TmCatR Term Term
    | TmInl Term
    | TmInr Term
    | TmPlusCase Var (Maybe Var) Term (Maybe Var) Term

data Token
      = TokenLet
      | TokenIn
      | TokenSink
      | TokenCase
      | TokenOf
      | TokenInl
      | TokenInr
      | TokenInt Int
      | TokenVar String
      | TokenEq
      | TokenComma
      | TokenSemic
      | TokenOB
      | TokenCB
 deriving Show      

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
      (var,rest)   -> TokenVar var : lexer rest

}

%name calc
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
      var             { TokenVar $$ }
      '='             { TokenEq }
      '('             { TokenOB }
      ')'             { TokenCB }
      ','             { TokenComma }
      ';'             { TokenSemic }
      '_'             { TokenWild }
      '|'             { TokenPipe }
      '=>'            { TokenArr }

%%

WildVar : '_'     { Nothing }
        | var     { Just $1 }

Exp   : let '(' WildVar ';' WildVar ')' '=' var in Exp            { TmCatL $3 $5 $8 $10 }
      | '(' Exp ';' Exp ')'                                       { TmCatR $2 $4 }
      | inl Exp                                                   { TmInl $2 }
      | inr Exp                                                   { TmInr $2 }
      | case var of inl WildVar '=>' Exp '|' inr WildVar '=>' Exp { TmPlusCase $2 $5 $7 $10 $12}
      | int                                                       { TmLitR (LInt $1) }
      | var                                                       { TmVar $1 }
      | '(' Exp ')'                                               { $2 }


