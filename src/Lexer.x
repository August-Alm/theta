{
module Lexer (Token (..), scanTokens) where
import Types (Term (..), Type (..), Kind (..))
}

%wrapper "basic"

$alphanum = [a-zA-Z]
$eol = [\n]

tokens :-
  \,                         ;
  $eol                       ;
  $white+                    ;
  let                        { \s -> TokenLet }
  "λ"                        { \s -> TokenTermLambda }
  "Λ"                        { \s -> TokenTypeLambda }
  "θ"                        { \s -> TokenTheta }
  \=                         { \s -> TokenEqual }
  \:                         { \s -> TokenColon }
  \;                         { \s -> TokenSemicolon }
  \.                         { \s -> TokenDot }
  \(                         { \s -> TokenOP }
  \)                         { \s -> TokenCP }
  \[                         { \s -> TokenOB }
  \]                         { \s -> TokenCB }
  [a-z] [$alphanum \_ \']*   { \s -> TokenTermVar s }
  [A-Z] [$alphanum \_ \']*   { \s -> TokenTypeVar s }

{
data Token
  = TokenLet
  | TokenTermLambda
  | TokenTypeLambda
  | TokenTheta
  | TokenEqual
  | TokenColon
  | TokenSemicolon
  | TokenDot
  | TokenOP
  | TokenCP
  | TokenOB
  | TokenCB
  | TokenTermVar String
  | TokenTypeVar String
  deriving (Eq, Show)

scanTokens = alexScanTokens
}