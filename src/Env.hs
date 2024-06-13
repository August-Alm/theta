module Env
( Env (depth)
, empty
, bindTerm
, bindType
, getTerm
, getType
, freshTerm
, freshType
) where

import Types
import Data.Text.Short (pack)
import Data.Char (chr)
import Data.List (findIndex)

-- | Evaluation environment.
data Env = Env
  { terms :: [(Name, TermH)]
  , types :: [(Name, TypeH)]
  , depth :: !Int
  }

indexToName :: Int -> Int -> Name
indexToName shift idx = go idx []
  where
    go i acc =
      if i > 0
        then go (i `div` 26) (chr ((i - 1) `mod` 26 + shift) : acc)
        else pack . reverse $ acc

empty :: Env
empty = Env { terms = [], types = [], depth = 0 }

bindTerm :: Name -> TermH -> Env -> Env
bindTerm x t env =
    env { terms = (x, t) : terms env, depth = depth env + 1 }

bindType :: Name -> TypeH -> Env -> Env
bindType x t env =
    env { types = (x, t) : types env, depth = depth env + 1 }

freshTermName :: Name -> Env -> Name
freshTermName x env =
  case findIndex ((== x) . fst) (terms env) of
    Just i -> indexToName 97 (i + 1)
    Nothing -> x

freshTypeName :: Name -> Env -> Name
freshTypeName x env =
  case findIndex ((== x) . fst) (types env) of
    Just i -> indexToName 65 (i + 1)
    Nothing -> x

freshTerm :: Name -> Env -> (Name, TermH, Env)
freshTerm x env = (x', v', env')
  where
    x' = freshTermName x env
    v' = VarH x' (-depth env - 1)
    env' = bindTerm x' v' env

freshType :: Name -> Env -> (Name, TypeH, Env)
freshType x env = (x', v', env')
  where
    x' = freshTypeName x env
    v' = TVarH x' (-depth env - 1)
    env' = bindType x' v' env

maybeAt :: Int -> [a] -> Maybe a
maybeAt i xs
  | i < 0 = Nothing
  | otherwise = go i xs
  where
    go 0 (x : _) = Just x
    go j (_ : ys) = go (j - 1) ys
    go _ [] = Nothing

getTerm :: Int -> Env -> Maybe TermH
getTerm i = maybeAt i . fmap snd . terms 

getType :: Int -> Env -> Maybe TypeH
getType i = maybeAt i .fmap snd . types
