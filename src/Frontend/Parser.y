{
module Frontend.Parser(parseSurfaceSyntax, parseFunDef, parseProgram, lexer) where
import Frontend.SurfaceSyntax(Term(..), FunDef(..), UntypedPrefix(..), RunCmd(..))
import Values ( Lit(..))
import Var(Var(..))
import Types
import Data.Char ( isDigit, isAlpha, isSpace )

}

%name parseSurfaceSyntax Exp
%name parseTy Ty
%name parseFunDef FunDef
%name parseProgram Pgm
%name parsePrefix Pfx
%tokentype { Token }
%error { parseError }

%token
      let             { TokenLet }
      in              { TokenIn }
      sink            { TokenSink }
      nil             { TokenNil }
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
      emp             { TokenEmp }
      exec            { TokenExec }
      '='             { TokenEq }
      '('             { TokenOB }
      ')'             { TokenCB }
      '['             { TokenOS }
      ']'             { TokenCS }
      ','             { TokenComma }
      ';'             { TokenSemic }
      ':'             { TokenColon }
      '::'            { TokenCons }
      '_'             { TokenWild }
      '|'             { TokenPipe }
      '=>'            { TokenArr }
      '.'             { TokenDot }
      '+'             { TokenPlus }
      '*'             { TokenStar }

%%

Var     : var     { Var.Var $1 }

WildVar : '_'     { Nothing }
        | Var     { Just $1 }

Exp   : let '(' WildVar ';' WildVar ')' '=' Exp in Exp             { TmCatL $3 $5 $8 $10 }
      | '(' Exp ';' Exp ')'                                        { TmCatR $2 $4 }
      | inl Exp1                                                   { TmInl $2 }
      | inr Exp1                                                   { TmInr $2 }
      | case Exp of inl WildVar '=>' Exp '|' inr WildVar '=>' Exp  { TmPlusCase $2 $5 $7 $10 $12}
      | case Exp of nil '=>' Exp '|' WildVar '::' WildVar '=>' Exp { TmStarCase $2 $6 $8 $10 $12}
      | Exp1 '::' Exp                                              { TmCons $1 $3 }
      | Exp1                                                       { $1 }

Exp1  : int                                                       { TmLitR (LInt $1) }
      | bool                                                      { TmLitR (LBool $1) }
      | sink                                                      { TmEpsR }
      | nil                                                       { TmNil }
      | Var                                                       { TmVar $1 }
      | '(' Exp ')'                                               { $2 }

Ty    : Ty1 '+' Ty1                                               { TyPlus $1 $3 }
      | Ty1                                                       { $1 }

Ty1   : Ty2 '.' Ty2                                               { TyCat $1 $3 }
      | Ty2                                                       { $1 }

Ty2   : Ty3 '*'                                                   { TyStar $1 }
      | Ty3                                                       { $1 }

Ty3   : tyInt                                                     { TyInt }
      | tyBool                                                    { TyBool }
      | tyEps                                                     { TyEps }
      | '(' Ty ')'                                                { $2 }

FunDef      : fun var '(' Args ')' ':' Ty '=' Exp                      { FD $2 $4 $7 $9 }

Args  : {-empty-}                                                 { EmpCtx }
      | Var ':' Ty                                                { SngCtx $1 $3 }
      | Var ':' Ty ';' Args                                       { SemicCtx (SngCtx $1 $3) $5 }

Pgm   : {-empty-}                                                 { [] }
      | FunDef Pgm                                                { (Left $1) : $2 }
      | RunCmd Pgm                                                { (Right $1) : $2 }

Pfx   : '(' Pfx ';' ')'                                           { CatPA $2 }
      | '(' Pfx ';' Pfx ')'                                       { CatPB $2 $4 }
      | emp                                                       { EmpP }
      | inl '(' Pfx ')'                                           { SumPA $3 }
      | inr '(' Pfx ')'                                           { SumPB $3 }
      | int                                                       { LitP (LInt $1) }
      | bool                                                      { LitP (LBool $1) }
      | '[' Stp ']'                                               { Stp $2 }

Stp   : {-empty-}                                                 { [] }
      | Pfx                                                       { [$1] }
      | Pfx ';' Stp                                               { $1 : $3 }

Bindings : {- empty -}                                            { [] }
          | Var '=' Pfx                                           { [($1,$3)] }
          | Var '=' Pfx ';' Bindings                              { ($1,$3) : $5 }

RunCmd : exec var '(' Bindings ')'                                { RC $2 $4 }

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
      | TokenNil
      | TokenFun
      | TokenInt Int
      | TokenBool Bool
      | TokenVar Var.Var
      | TokenEq
      | TokenComma
      | TokenSemic
      | TokenColon
      | TokenCons
      | TokenArr
      | TokenWild
      | TokenPipe
      | TokenOB
      | TokenCB
      | TokenOS
      | TokenCS
      | TokenDot
      | TokenStar
      | TokenEmp
      | TokenExec
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
lexer (':':':':cs) = TokenCons : lexer cs
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
lexer ('*':cs) = TokenStar : lexer cs

lexNum cs = TokenInt (read num) : lexer rest
      where (num,rest) = span isDigit cs

lexVar cs =
   case span (\c -> isAlpha c || c == '\'') cs of
      ("let",rest) -> TokenLet : lexer rest
      ("in",rest)  -> TokenIn : lexer rest
      ("sink",rest)  -> TokenSink : lexer rest
      ("case",rest)  -> TokenCase : lexer rest
      ("of",rest)  -> TokenOf : lexer rest
      ("inl",rest)  -> TokenInl : lexer rest
      ("inr",rest)  -> TokenInr : lexer rest
      ("nil",rest)  -> TokenNil : lexer rest
      ("fun",rest)  -> TokenFun : lexer rest
      ("emp",rest)  -> TokenEmp : lexer rest
      ("true",rest)  -> TokenBool True : lexer rest
      ("false",rest)  -> TokenBool False : lexer rest
      ("exec",rest)  -> TokenExec : lexer rest
      ("Eps",rest)  -> TokenTyEps : lexer rest
      ("Int",rest)  -> TokenTyInt : lexer rest
      ("Bool",rest)  -> TokenTyBool : lexer rest
      (var,rest)   -> TokenVar (Var.Var var) : lexer rest


}
