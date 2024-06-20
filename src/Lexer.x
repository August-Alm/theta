{
module Lexer (Token (..), tokenize) where
import Types (Name, Term (..), Type (..), Kind (..))
}

%wrapper "basic"

$alphanum = [a-zA-Z 0-9]
$eol = [\n]

tokens :-
  \,                         ;
  $eol                       ;
  $white+                    ;
  let                        { \_ -> TokenLet }
  "λ"                        { \_ -> TokenTermLambda }
  "Λ"                        { \_ -> TokenTypeLambda }
  "θ"                        { \_ -> TokenTheta }
  "✲"                        { \_ -> TokenStar }
  \=                         { \_ -> TokenEqual }
  \:                         { \_ -> TokenColon }
  \;                         { \_ -> TokenSemicolon }
  \.                         { \_ -> TokenDot }
  \(                         { \_ -> TokenOP }
  \)                         { \_ -> TokenCP }
  \[                         { \_ -> TokenOB }
  \]                         { \_ -> TokenCB }
  [a-z] [$alphanum \_ \']*   { \s -> TokenTermVar s }
  [A-Z] [$alphanum \_ \']*   { \s -> TokenTypeVar s }

{
data Token
  = TokenLet
  | TokenTermLambda
  | TokenTypeLambda
  | TokenTheta
  | TokenStar
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
  | TokenEOF
  deriving (Eq, Show)

tokenize = alexScanTokens
}