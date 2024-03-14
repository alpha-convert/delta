{
module Frontend.Parser(parseSurfaceSyntax, parseProgram, lexer) where
import Frontend.SurfaceSyntax(Term(..), Cmd(..), UntypedPrefix(..), MacroParam(..))
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
      mac             { TokenMac }
      end             { TokenEnd }
      bool            { TokenBool $$ }
      int             { TokenInt $$ }
      var             { TokenVar (Var.Var $$) }
      if              { TokenIf }
      as              { TokenAs }
      then            { TokenThen }
      else            { TokenElse }
      tyInt           { TokenTyInt }
      tyBool          { TokenTyBool }
      tyEps           { TokenTyEps }
      emp             { TokenEmp }
      exec            { TokenExec }
      step            { TokenStep }
      specialize      { TokenSpec }
      quickcheck      { TokenQC }
      wait            { TokenWait }
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
FunVar     : var     { Var.FunVar $1 }

WildVar : '_'     { Nothing }
        | Var     { Just $1 }

Exp   : let '(' WildVar ';' WildVar ')' '=' Exp in Exp             { TmCatL $3 $5 $8 $10 }
      | let '(' WildVar ',' WildVar ')' '=' Exp in Exp             { TmParL $3 $5 $8 $10 }
      | let Var '=' Exp in Exp                                     { TmCut $2 $4 $6 }
      | inl Exp1                                                   { TmInl $2 }
      | inr Exp1                                                   { TmInr $2 }
      | case Exp of inl WildVar '=>' Exp '|' inr WildVar '=>' Exp  { TmPlusCase $2 $5 $7 $10 $12}
      | case Exp of nil '=>' Exp '|' WildVar '::' WildVar '=>' Exp { TmStarCase $2 $6 $8 $10 $12}
      | wait WaitList do Exp end                                    { TmWait $2 $4 }
      | if '{' HistPgm '}' then Exp else Exp                       { TmIte $3 $6 $8 }
      | Exp1 '::' Exp                                              { TmCons $1 $3 }
      | Exp1                                                       { $1 }

Exp1  : int                                                       { TmLitR (LInt $1) }
      | bool                                                      { TmLitR (LBool $1) }
      | sink                                                      { TmEpsR }
      | nil                                                       { TmNil }
      | Var                                                       { TmVar $1 }
      | FunVar '(' Args ')'                                       { TmFunCall $1 [] [] Nothing $3 }
      | FunVar '{' HistArgs '}' '(' Args ')'                      { TmFunCall $1 [] $3 Nothing $6 }
      | FunVar '[' TyList ']' '(' Args ')'                        { TmFunCall $1 $3 [] Nothing $6 }
      | FunVar '[' TyList ']' '{' HistArgs '}' '(' Args ')'       { TmFunCall $1 $3 $6 Nothing $9 }
      | FunVar '<' FunVar '>' '(' Args ')'                        { TmFunCall $1 [] [] (Just $3) $6 }
      | FunVar '{' HistArgs'}' '<' FunVar '>' '(' Args ')'        { TmFunCall $1 [] $3 (Just $6) $9 }
      | FunVar '[' TyList ']' '<' FunVar '>' '(' Args ')'         { TmFunCall $1 $3 [] (Just $6) $9 }
      | FunVar '[' TyList ']' '{' HistArgs '}' '<' FunVar '>' '(' Args ')' { TmFunCall $1 $3 $6 (Just $9) $12 }
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

HistArgs : {-empty-}                                              { [] }
         | HistPgm                                                { [$1] }
         | HistPgm ',' HistArgs1                                   { $1 : $3 }

HistArgs1 : {-empty-}                                             { [] }
          | HistPgm ',' HistArgs1                                 { $1 : $3 }

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

WaitList : {-empty-}                                              { [] }
         | Var                                                    { [ Left $1 ] }
         | Exp as Var                                             { [ Right ($1,$3) ] }
         | Var ',' WaitList                                       { (Left $1) : $3 }
         | Exp as Var ',' WaitList                                { (Right ($1,$3)) : $5 }

VarList : {-empty-}                                               { [] }
        | Var                                                     { [$1] }
        | Var ',' VarList                                         { $1 : $3 }

TyVarListBracketed : {-empty-}                                    { [] }
                   | '[' TyVarList ']'                            { $2 }

TyVarList : {-empty-}                                             { [] }
          | TyVar                                                 { [$1] }
          | TyVar ',' TyVarList                                   { $1 : $3 }

TyList : {-empty-}                                               { [] }
        | Ty                                                     { [$1] }
        | Ty ',' TyList                                         { $1 : $3 }

HistVarCtx : {--}                                                 { [] }
            | '{' HistVarCtx1 '}'                                 { $2 }

HistVarCtx1 : Var ':' Ty                                          { [($1,$3)] }
            | Var ':' Ty ',' HistVarCtx2                          { ($1,$3) : $5 }

HistVarCtx2 : {-empty-}                                           { [] }
            | Var ':' Ty ',' HistVarCtx2                          { ($1,$3) : $5 }

VarCtx      : VarCtx1 ',' VarCtx                                  { CommaCtx $1 $3 } 
            | VarCtx1 ';' VarCtx                                  { SemicCtx $1 $3 }
            | VarCtx1                                             { $1 } 

VarCtx1     : Var ':' Ty                                          { SngCtx (CE $1 $3) }
            | '(' VarCtx ')'                                      { $2 }
          

MacroParam : FunVar ':' '(' MacroParamCtx ')' '-' '>' Ty                     { MP $1 [] $4 $8 }
           | FunVar ':' '{' MacroParamHistCtx '}' '(' MacroParamCtx ')' '-' '>' Ty { MP $1 $4 $7 $11 }

-- MacroParamList  : {-empty-}                                           { [] }
            -- | MacroParam                                              { [$1] }
            -- | MacroParam ',' kunArgList                               { $1 : $3 }

MacroParamCtx   : MacroParamCtx1 ',' MacroParamCtx                               { CommaCtx $1 $3 } 
            | MacroParamCtx1 ';' MacroParamCtx                                  { SemicCtx $1 $3 }
            | MacroParamCtx1                                             { $1 } 

MacroParamCtx1     : Ty                                                 { SngCtx $1 }
            | '(' MacroParamCtx ')'                                      { $2 }
 
MacroParamHistCtx : Ty                                          { [$1] }
                   | Ty ',' MacroParamHistCtx1                   { $1 : $3 }

MacroParamHistCtx1 : {-empty-}                                           { [] }
            | Ty ',' MacroParamHistCtx1                                  { $1 : $3 }

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

PfxLitArgs     : PfxLitArgs1 ',' PfxLitArgs                                 { CommaCtx $1 $3 } 
            | PfxLitArgs1 ';' PfxLitArgs                                 { SemicCtx $1 $3 }
            | PfxLitArgs1                                             { $1 } 

PfxLitArgs1    : Var '=' Pfx                                          { SngCtx (CE $1 $3) }
            | '(' PfxLitArgs ')'                                      { $2 }

HistLitArgs : {-empty-}                                                 { []   }
            | Pfx                                                       { [$1] }
            | Pfx ',' HistLitArgs1                                      { $1 : $3 }

HistLitArgs1 : {-empty-}                                                { [] }
             | Pfx ',' HistLitArgs1                                     { $1 : $3 }


Cmd   : fun FunVar TyVarListBracketed HistVarCtx '(' VarCtx ')' ':' Ty '=' Exp            { FunOrMacDef $2 $3 Nothing $4 $6 $9 $11 }
      | fun FunVar TyVarListBracketed '<' MacroParam '>' '(' VarCtx ')' ':' Ty '=' Exp    { FunOrMacDef $2 $3 (Just $5) [] $8 $11 $13 }
      | specialize FunVar '[' TyList ']'                                                  { SpecializeCommand $2 $4 [] }
      | exec FunVar '(' PfxLitArgs ')'                                                       { RunCommand $2 [] $4 }
      | exec FunVar '{' HistLitArgs '}' '(' PfxLitArgs ')'                                   { RunCommand $2 $4 $7 }
      | exec step FunVar '(' PfxLitArgs ')'                                                  { RunStepCommand $3 [] $5 }
      | exec step FunVar '{' HistLitArgs '}' '(' PfxLitArgs ')'                              { RunStepCommand $3 $5 $8 }
      | quickcheck FunVar                                                                 { QuickCheckCommand $2 }

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
      | TokenAs
      | TokenThen
      | TokenElse
      | TokenOf
      | TokenInl
      | TokenInr
      | TokenNil
      | TokenFun
      | TokenMac
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
      | TokenSpec
      | TokenQC
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
      ("as",rest)  -> TokenAs : lexer rest
      ("then",rest)  -> TokenThen : lexer rest
      ("else",rest)  -> TokenElse : lexer rest
      ("sink",rest)  -> TokenSink : lexer rest
      ("case",rest)  -> TokenCase : lexer rest
      ("of",rest)  -> TokenOf : lexer rest
      ("inl",rest)  -> TokenInl : lexer rest
      ("inr",rest)  -> TokenInr : lexer rest
      ("nil",rest)  -> TokenNil : lexer rest
      ("fun",rest)  -> TokenFun : lexer rest
      ("mac",rest)  -> TokenMac : lexer rest
      ("emp",rest)  -> TokenEmp : lexer rest
      ("end",rest)  -> TokenEnd : lexer rest
      ("wait",rest)  -> TokenWait : lexer rest
      ("do",rest)  -> TokenDo : lexer rest
      ("true",rest)  -> TokenBool True : lexer rest
      ("false",rest)  -> TokenBool False : lexer rest
      ("exec",rest)  -> TokenExec : lexer rest
      ("step",rest)  -> TokenStep : lexer rest
      ("specialize",rest)  -> TokenSpec : lexer rest
      ("quickcheck",rest)  -> TokenQC : lexer rest
      ("Eps",rest)  -> TokenTyEps : lexer rest
      ("Int",rest)  -> TokenTyInt : lexer rest
      ("Bool",rest)  -> TokenTyBool : lexer rest
      (var,rest)   -> TokenVar (Var.Var var) : lexer rest


}
