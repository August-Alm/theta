module Syntax
( TermP (..)
, TypeP (..)
, KindP (..)
, toTerm
, toType
, toKind
)
where

import Types (Name, Term (..), Type (..), Kind (..))
import Data.List (elemIndex)

data TermP
  = VarP Name 
  | LamP Name TermP
  | PLamP Name TermP
  | AppP TermP TermP
  | PAppP TermP TypeP
  | AnnP TermP TypeP
  | LetP Name TermP TermP
  | TLetP Name TypeP TermP
  deriving Show

data TypeP
  = TVarP Name
  | ThetP Name TermP
  | FLamP Name TypeP
  | VLamP Name TypeP
  | FAppP TypeP TypeP
  | VAppP TypeP TermP
  | TAnnP TypeP KindP
  | TFLetP Name TypeP TypeP
  | TVLetP Name TermP TypeP
  deriving Show

data KindP
  = KThetP Name TypeP
  | KStarP
  deriving Show

data Names = Names
  { terms :: [Name]
  , types :: [Name]
  }

termIndex :: Names -> Name -> Int
termIndex ns x =
  case elemIndex x (terms ns) of
  Just i -> i
  Nothing -> error $ "unbound term variable: " ++ show x

typeIndex :: Names -> Name -> Int
typeIndex ns x =
  case elemIndex x (types ns) of
  Just i -> i
  Nothing -> error $ "unbound type variable: " ++ show x

termOfP :: Names -> TermP -> Term
termOfP ns trm =
  case trm of
  VarP x -> Var x (termIndex ns x)
  LamP x t -> Lam x (termOfP (ns { terms = x : terms ns }) t)
  PLamP x t -> PLam x (termOfP (ns { types = x : types ns }) t)
  AppP t u -> App (termOfP ns t) (termOfP ns u)
  PAppP t a -> PApp (termOfP ns t) (typeOfP ns a)
  AnnP t a -> Ann (termOfP ns t) (typeOfP ns a)
  LetP x t u -> App (Lam x (termOfP ns' u)) (termOfP ns t)
    where ns' = ns { terms = x : terms ns }
  TLetP x t u -> PApp (PLam x (termOfP ns' u)) (typeOfP ns t)
    where ns' = ns { types = x : types ns }

typeOfP :: Names -> TypeP -> Type
typeOfP ns typ =
  case typ of
  TVarP x -> TVar x (typeIndex ns x)
  ThetP x t -> Thet x (termOfP (ns { terms = x : terms ns }) t)
  FLamP x t -> FLam x (typeOfP (ns { types = x : types ns }) t)
  VLamP x t -> VLam x (typeOfP (ns { terms = x : terms ns }) t)
  FAppP t u -> FApp (typeOfP ns t) (typeOfP ns u)
  VAppP t u -> VApp (typeOfP ns t) (termOfP ns u)
  TAnnP t k -> TAnn (typeOfP ns t) (kindOfP ns k)
  TFLetP x t u -> FApp (FLam x (typeOfP ns' u)) (typeOfP ns t)
    where ns' = ns { types = x : types ns }
  TVLetP x t u -> VApp (VLam x (typeOfP ns' u)) (termOfP ns t)
    where ns' = ns { terms = x : terms ns }

kindOfP :: Names -> KindP -> Kind
kindOfP ns k =
  case k of
  KThetP x t -> KThet x (typeOfP (ns { types = x : types ns }) t)
  KStarP -> KStar

toTerm :: TermP -> Term
toTerm = termOfP (Names [] [])

toType :: TypeP -> Type
toType = typeOfP (Names [] [])

toKind :: KindP -> Kind
toKind = kindOfP (Names [] [])
