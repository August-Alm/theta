module Syntax
( TermP (..)
, TypeP (..)
, KindP (..)
, TermDefP (..)
, TypeDefP (..)
, ModuleP (..)
, emptyModuleP
, addTermDefP
, addTypeDefP
, toTerm
, toType
, toKind
, toModule
)
where

import Types
import Data.Map (Map, empty, insert)
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

data TermDefP = TermDefP Name TypeP TermP

data TypeDefP = TypeDefP Name KindP TypeP

data ModuleP = ModuleP
  { termDefsP :: Map Name TermDefP
  , typeDefsP :: Map Name TypeDefP
  , nameDefsP :: [Name]
  }

emptyModuleP :: ModuleP
emptyModuleP =
  ModuleP { termDefsP = Data.Map.empty, typeDefsP = Data.Map.empty, nameDefsP = [] }

addTermDefP :: TermDefP -> ModuleP -> ModuleP
addTermDefP def@(TermDefP x _ _) m =
  m { termDefsP = Data.Map.insert x def (termDefsP m), nameDefsP = x : nameDefsP m }

addTypeDefP :: TypeDefP -> ModuleP -> ModuleP
addTypeDefP def@(TypeDefP x _ _) m =
  m { typeDefsP = Data.Map.insert x def (typeDefsP m), nameDefsP = x : nameDefsP m }

toModule :: ModuleP -> Module
toModule m = Module
  { termDefs = fmap toTermDef (termDefsP m)
  , typeDefs = fmap toTypeDef (typeDefsP m)
  , nameDefs = nameDefsP m
  }
  where
    toTermDef (TermDefP x t trm) = TermDef x (toType t) (toTerm trm)
    toTypeDef (TypeDefP x k typ) = TypeDef x (toKind k) (toType typ)


termVarOrRef :: Names -> Name -> Term
termVarOrRef ns x =
  case elemIndex x (terms ns) of
  Just i -> Var x i
  Nothing -> Ref x

typeVarOrRef :: Names -> Name -> Type
typeVarOrRef ns x =
  case elemIndex x (types ns) of
  Just i -> TVar x i
  Nothing -> TRef x

termOfP :: Names -> TermP -> Term
termOfP ns trm =
  case trm of
  VarP x -> termVarOrRef ns x
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
  TVarP x -> typeVarOrRef ns x
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
