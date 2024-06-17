{
module Parser
( parseTerm
, parseType
, parseKind
, parseModule
) where

import Data.Char
import Lexer
import Types (Name, name, Term (..), Type (..), Kind (..), Module (..))
import Syntax
}

%name parseTermP term
%name parseTypeP type
%name parseKindP kind
%name parseModuleP module

%tokentype { Token }
%error { parseError }

%token
  let   { TokenLet }
  lam   { TokenTermLambda }
  Lam   { TokenTypeLambda }
  the   { TokenTheta }
  var   { TokenTermVar $$ }
  Var   { TokenTypeVar $$ }
  '='   { TokenEqual }  
  ':'   { TokenColon }
  ';'   { TokenSemicolon }
  '.'   { TokenDot }
  '✲'   { TokenStar }
  '('   { TokenOP }
  ')'   { TokenCP }
  '['   { TokenOB }
  ']'   { TokenCB }

%%

term
  : let var '=' term ';' term   { LetP (name $2) $4 $6 }
  | let Var '=' type ';' term   { TLetP (name $2) $4 $6 }
  | '(' term term ')'           { AppP $2 $3 }
  | '(' term type ')'           { PAppP $2 $3 }
  | lam var '.' term            { LamP (name $2) $4 }
  | lam Var '.' term            { PLamP (name $2) $4 }
  | '[' term ':' type ']'       { AnnP $2 $4}
  | var                         { VarP (name $1) }

type
  : let Var '=' type ';' type   { TFLetP (name $2) $4 $6 }
  | let var '=' term ';' type   { TVLetP (name $2) $4 $6 }
  | '(' type type ')'           { FAppP $2 $3 }
  | '(' type term ')'           { VAppP $2 $3 }
  | Lam var '.' type            { VLamP (name $2) $4 }
  | Lam Var '.' type            { FLamP (name $2) $4 }
  | the var '.' term            { ThetP (name $2) $4 }
  | '[' type ':' kind ']'       { TAnnP $2 $4 }
  | Var                         { TVarP (name $1) }

kind
  : '✲'                         { KStarP }
  | the Var '.' type            { KThetP (name $2) $4 }

termDef
  : let var ':' type '=' term   { TermDefP (name $2) $4 $6 }

typeDef
  : let Var ':' kind '=' type   { TypeDefP (name $2) $4 $6 }

module
  :                             { emptyModuleP }
  | module termDef              { addTermDefP $2 $1 }
  | module typeDef              { addTypeDefP $2 $1 }

{
parseError :: [Token] -> a
parseError _ = error "Parse error"

parseTerm :: String -> Term
parseTerm = toTerm . parseTermP . tokenize

parseType :: String -> Type
parseType = toType . parseTypeP . tokenize

parseKind :: String -> Kind
parseKind = toKind . parseKindP . tokenize

parseModule :: String -> Module
parseModule = toModule . parseModuleP . tokenize
}