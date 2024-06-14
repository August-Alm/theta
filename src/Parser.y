{
module Parser where

import Data.Char
import Lexer
import Types (Name, name, Term (..), Type (..), Kind (..))
}

%name parse
%tokentype { Token }
%error { parseError }

%token
    LET { TokenLet }
    TermLAM { TokenTermLambda }
    TypeLAM { TokenTypeLambda }
    Theta { TokenTheta }
    '='   { TokenEqual }  
    ':' { TokenColon }
    ';' { TokenSemicolon }
    '.' { TokenDot }
    TermVAR { TokenTermVar $$ }
    TypeVAR { TokenTypeVar $$ }
    '(' { TokenOP }
    ')' { TokenCP }
    '[' { TokenOB }
    ']' { TokenCB }

%%

term:
  --  LET TermVAR '=' Expression ';' Expression { App (Body [$2] [$6]) $4 }
  TermLAM TermVAR '.' term { Lam (name $2) $4 }


{
parseError :: [Token] -> a
parseError _ = error "Parse error"

parseTerm :: String -> Term
parseTerm = parse . scanTokens
}