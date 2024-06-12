module Env
( Env
, empty
, bindTerm
, bindType
, lookupTerm
, lookupType
, bindFreshTerm
, bindFreshType
) where

import Types
import Data.Text.Short (pack, append)
import Data.Char (chr)
import Data.List (findIndex)

-- | Evaluation environment.
data Env = Env
  { terms :: [(Name, TermH)]
  , types :: [(Name, TypeH)]
  }

indexToName :: Int -> Int -> Name
indexToName shift idx = go idx []
  where
    go i acc =
      if idx > 0
      then go (i `div` 26) (pack [chr ((i - 1) `mod` 26 + shift)] : acc)
      else foldl append mempty acc

empty :: Env
empty = Env { terms = [], types = [] }

bindTerm :: Name -> TermH -> Env -> Env
bindTerm x t env = env { terms = (x, t) : terms env }

bindType :: Name -> TypeH -> Env -> Env
bindType x t env = env { types = (x, t) : types env }

lookupTerm :: Name -> Env -> Maybe TermH
lookupTerm x = lookup x . terms

lookupType :: Name -> Env -> Maybe TypeH
lookupType x = lookup x . types

freshTermName :: Env -> Name -> Name
freshTermName env x =
  case findIndex ((== x) . fst) (terms env) of
    Nothing -> x
    Just i -> indexToName 97 (i + 1)

freshTypeName :: Env -> Name -> Name
freshTypeName env x =
  case findIndex ((== x) . fst) (terms env) of
    Nothing -> x
    Just i -> indexToName 65 (i + 1)

bindFreshTerm :: Name -> Env -> (Name, TermH, Env)
bindFreshTerm x env = (x', VarH x', bindTerm x' (VarH x') env)
  where x' = freshTermName env x

bindFreshType :: Name -> Env -> (Name, TypeH, Env)
bindFreshType x env = (x', TVarH x', bindType x' (TVarH x') env)
  where x' = freshTypeName env x