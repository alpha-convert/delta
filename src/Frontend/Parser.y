{
module Frontend.Parser(parseSurfaceSyntax, parseProgram, lexer) where
import Frontend.SurfaceSyntax(Term(..), Cmd(..), UntypedPrefix(..))
import Values ( Lit(..))
import Var
import Types
import Data.Char ( isDigit, isAlpha, isSpace )
import qualified HistPgm as Hist

}

%name parseSurfaceSyntax Exp
%name parseTy Ty
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
      end             { TokenEnd }
      bool            { TokenBool $$ }
      int             { TokenInt $$ }
      var             { TokenVar (Var.Var $$) }
      if              { TokenIf }
      then            { TokenThen }
      else            { TokenElse }
      tyInt           { TokenTyInt }
      tyBool          { TokenTyBool }
      tyEps           { TokenTyEps }
      emp             { TokenEmp }
      exec            { TokenExec }
      step            { TokenStep }
      wait            { TokenWait }
      rec             { TokenRec }
      do              { TokenDo }
      '='             { TokenEq }
      '('             { TokenOP }
      ')'             { TokenCP }
      '['             { TokenOS }
      ']'             { TokenCS }
      '{'             { TokenOC }
      '}'             { TokenCC }
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
      '-'             { TokenDash }
      '/'             { TokenSlash }
      '||'            { TokenPipes }
      '&&'            { TokenAmps }
      '<'             { TokenLt }
      '>'             { TokenGt }
      '<='            { TokenLeq }
      '>='            { TokenGeq }

%%

Var     : var     { Var.Var $1 }
TyVar     : var     { Var.TyVar $1 }

WildVar : '_'     { Nothing }
        | Var     { Just $1 }

Exp   : let '(' WildVar ';' WildVar ')' '=' Exp in Exp             { TmCatL $3 $5 $8 $10 }
      | let '(' WildVar ',' WildVar ')' '=' Exp in Exp             { TmParL $3 $5 $8 $10 }
      | inl Exp1                                                   { TmInl $2 }
      | inr Exp1                                                   { TmInr $2 }
      | case Exp of inl WildVar '=>' Exp '|' inr WildVar '=>' Exp  { TmPlusCase $2 $5 $7 $10 $12}
      | case Exp of nil '=>' Exp '|' WildVar '::' WildVar '=>' Exp { TmStarCase $2 $6 $8 $10 $12}
      | wait VarList do Exp end                                    { TmWait $2 $4 }
      | if Exp1 then Exp else Exp                                  { TmIte $2 $4 $6 }
      | Exp1 '::' Exp                                              { TmCons $1 $3 }
      | Exp1                                                       { $1 }

Exp1  : int                                                       { TmLitR (LInt $1) }
      | bool                                                      { TmLitR (LBool $1) }
      | sink                                                      { TmEpsR }
      | nil                                                       { TmNil }
      | Var                                                       { TmVar $1 }
      | rec '(' Args ')'                                          { TmRec $3 }
      | '(' Exp ';' Exp ')'                                       { TmCatR $2 $4 }
      | '(' Exp ',' Exp ')'                                       { TmParR $2 $4 }
      | '(' Exp ')'                                               { $2 }
      | '{' HistPgm '}'                                           { TmHistPgm $2 }

HistPgm     : HP1 '<' HP1                                         { Hist.TmBinOp Hist.Lt $1 $3 }
            | HP1 '>' HP1                                         { Hist.TmBinOp Hist.Gt $1 $3 }
            | HP1 '>=' HP1                                        { Hist.TmBinOp Hist.Geq $1 $3 }
            | HP1 '<=' HP1                                        { Hist.TmBinOp Hist.Leq $1 $3 }
            | HP1 '::' HP1                                        { Hist.TmCons $1 $3 }
            | inl HP1                                             { Hist.TmInl $2 }
            | inr HP1                                             { Hist.TmInr $2 }
            | HP1                                                 { $1 }

HP1         : HP2 '+' HP2                                         { Hist.TmBinOp Hist.Add $1 $3 }
            | HP2 '-' HP2                                         { Hist.TmBinOp Hist.Sub $1 $3 }
            | HP2 '||' HP2                                        { Hist.TmBinOp Hist.Or $1 $3 }
            | HP2                                                 { $1 }

HP2         : HP3 '*' HP3                                         { Hist.TmBinOp Hist.Mul $1 $3 }
            | HP3 '/' HP3                                         { Hist.TmBinOp Hist.Div $1 $3 }
            | HP3                                                 { $1 }

HP3         : int                                                 { Hist.TmValue (Hist.VInt $1) }
            | bool                                                { Hist.TmValue (Hist.VBool $1) }
            | nil                                                 { Hist.TmNil }
            | '('')'                                              { Hist.TmEps }
            | Var                                                 { Hist.TmVar $1 }
            | '(' HistPgm ')'                                     { $2 }
            | '(' HistPgm ',' HistPgm ')'                         { Hist.TmPair $2 $4 }

Args  : {- empty -}                                               { EmpCtx }
      | Args1 ',' Args                                           { CommaCtx $1 $3 }
      | Args1 ';' Args                                           { SemicCtx $1 $3 }
      | Args1                                                     { $1 }

Args1 : Exp                                                       { SngCtx $1 }
      | '(' Args ')'                                              { $2 }

Ty    : Ty1 '+' Ty1                                               { TyPlus $1 $3 }
      | Ty1                                                       { $1 }

Ty1   : Ty2 '||' Ty2                                              { TyPar $1 $3 }
      | Ty2                                                       { $1 }

Ty2   : Ty3 '.' Ty3                                               { TyCat $1 $3 }
      | Ty3                                                       { $1 }

Ty3   : Ty3 '*'                                                   { TyStar $1 }
      | Ty4                                                       { $1 }

Ty4   : tyInt                                                     { TyInt }
      | tyBool                                                    { TyBool }
      | tyEps                                                     { TyEps }
      | TyVar                                                     { Types.TyVar $1 }
      | '(' Ty ')'                                                { $2 }

VarList : {-empty-}                                               { [] }
        | Var                                                     { [$1] }
        | Var ',' VarList                                         { $1 : $3 }

TyVarList : {-empty-}                                               { [] }
        | TyVar                                                     { [$1] }
        | TyVar ',' TyVarList                                         { $1 : $3 }

TyList : {-empty-}                                               { [] }
        | Ty                                                     { [$1] }
        | Ty ',' TyList                                         { $1 : $3 }




FunParams  : FunParams1 ',' FunParams                            { CommaCtx $1 $3 } 
           | FunParams1 ';' FunParams                            { SemicCtx $1 $3 }
           | FunParams1                                          { $1 } 

FunParams1 : Var ':' Ty                                           { SngCtx (CE $1 $3) }
           | '(' FunParams ')'                                    { $2 }
          

Pfx   : '(' Pfx ';' ')'                                           { CatPA $2 }
      | '(' Pfx ';' Pfx ')'                                       { CatPB $2 $4 }
      | '(' Pfx ',' Pfx ')'                                       { ParP $2 $4 }
      | emp                                                       { EmpP }
      | inl '(' Pfx ')'                                           { SumPA $3 }
      | inr '(' Pfx ')'                                           { SumPB $3 }
      | int                                                       { LitP (LInt $1) }
      | bool                                                      { LitP (LBool $1) }
      | '[' Stp                                                   { $2 }

Stp   : ']'                                                       { StpDone }
      | Pfx ')'                                                   { StpA $1 }
      | Pfx ']'                                                   { StpB $1 StpDone }
      | Pfx ';' Stp                                               { StpB $1 $3 }

PfxArgs     : PfxArgs1 ',' PfxArgs                                 { CommaCtx $1 $3 } 
            | PfxArgs1 ';' PfxArgs                                 { SemicCtx $1 $3 }
            | PfxArgs1                                             { $1 } 

PfxArgs1    : Var '=' Pfx                                          { SngCtx (CE $1 $3) }
            | '(' PfxArgs ')'                                      { $2 }

Cmd   : fun var '[' TyVarList ']' '(' FunParams ')' ':' Ty '=' Exp      { FunDef $2 $4 $7 $10 $12 }
      | fun var '(' FunParams ')' ':' Ty '=' Exp                        { FunDef $2 [] $4 $7 $9 }
      | exec var '(' PfxArgs ')'                                        { RunCommand $2 [] $4 }
      | exec var '[' TyList ']' '(' PfxArgs ')'                         { RunCommand $2 $4 $7 }
      | exec step var '(' PfxArgs ')'                                   { RunStepCommand $3 $5 }

Pgm   : {-empty-}                                                  { [] }
      | Cmd Pgm                                                    { $1 : $2 }


{

parseError :: [Token] -> a
parseError _ = error "Parse error"

data Token
      = TokenLet
      | TokenIn
      | TokenSink
      | TokenCase
      | TokenIf
      | TokenThen
      | TokenElse
      | TokenOf
      | TokenInl
      | TokenInr
      | TokenNil
      | TokenFun
      | TokenRec
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
      | TokenOP
      | TokenCP
      | TokenOS
      | TokenCS
      | TokenOC
      | TokenCC
      | TokenLt
      | TokenGt
      | TokenLeq
      | TokenGeq
      | TokenDot
      | TokenStar
      | TokenDash
      | TokenSlash
      | TokenEmp
      | TokenAmps
      | TokenPipes
      | TokenExec
      | TokenStep
      | TokenDo
      | TokenWait
      | TokenPlus
      | TokenEnd
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
lexer ('|':'|':cs) = TokenPipes : lexer cs
lexer ('&':'&':cs) = TokenAmps : lexer cs
lexer ('=':'>':cs) = TokenArr : lexer cs
lexer (':':':':cs) = TokenCons : lexer cs
lexer ('<':'=':cs) = TokenLeq : lexer cs
lexer ('>':'=':cs) = TokenGeq : lexer cs
lexer ('<':cs) = TokenLt : lexer cs
lexer ('>':cs) = TokenGt : lexer cs
lexer ('=':cs) = TokenEq : lexer cs
lexer (',':cs) = TokenComma : lexer cs
lexer ('.':cs) = TokenDot : lexer cs
lexer ('+':cs) = TokenPlus : lexer cs
lexer ('-':cs) = TokenDash : lexer cs
lexer ('/':cs) = TokenSlash : lexer cs
lexer (';':cs) = TokenSemic : lexer cs
lexer (':':cs) = TokenColon : lexer cs
lexer ('_':cs) = TokenWild : lexer cs
lexer ('(':cs) = TokenOP : lexer cs
lexer (')':cs) = TokenCP : lexer cs
lexer ('[':cs) = TokenOS : lexer cs
lexer (']':cs) = TokenCS : lexer cs
lexer ('{':cs) = TokenOC : lexer cs
lexer ('}':cs) = TokenCC : lexer cs
lexer ('|':cs) = TokenPipe : lexer cs
lexer ('*':cs) = TokenStar : lexer cs

lexNum cs = TokenInt (read num) : lexer rest
      where (num,rest) = span isDigit cs

lexVar cs =
   case span (\c -> isAlpha c || c == '\'') cs of
      ("let",rest) -> TokenLet : lexer rest
      ("in",rest)  -> TokenIn : lexer rest
      ("if",rest)  -> TokenIf : lexer rest
      ("then",rest)  -> TokenThen : lexer rest
      ("else",rest)  -> TokenElse : lexer rest
      ("sink",rest)  -> TokenSink : lexer rest
      ("case",rest)  -> TokenCase : lexer rest
      ("of",rest)  -> TokenOf : lexer rest
      ("inl",rest)  -> TokenInl : lexer rest
      ("inr",rest)  -> TokenInr : lexer rest
      ("nil",rest)  -> TokenNil : lexer rest
      ("fun",rest)  -> TokenFun : lexer rest
      ("emp",rest)  -> TokenEmp : lexer rest
      ("end",rest)  -> TokenEnd : lexer rest
      ("rec",rest)  -> TokenRec : lexer rest
      ("wait",rest)  -> TokenWait : lexer rest
      ("do",rest)  -> TokenDo : lexer rest
      ("true",rest)  -> TokenBool True : lexer rest
      ("false",rest)  -> TokenBool False : lexer rest
      ("exec",rest)  -> TokenExec : lexer rest
      ("step",rest)  -> TokenStep : lexer rest
      ("Eps",rest)  -> TokenTyEps : lexer rest
      ("Int",rest)  -> TokenTyInt : lexer rest
      ("Bool",rest)  -> TokenTyBool : lexer rest
      (var,rest)   -> TokenVar (Var.Var var) : lexer rest


}
