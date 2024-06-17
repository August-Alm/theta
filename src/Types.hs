module Types
( Name
, name
, string
, Term (..)
, Type (..)
, Kind (..)
, TermH (..)
, TypeH (..)
, KindH (..)
, TermDef (..)
, TypeDef (..)
, Module (..)
, getTermDef
, getTypeDef
, addTermDef
, addTypeDef
, emptyModule
) where

import Data.Map (Map, empty, insert, lookup)
import Data.Text.Short (ShortText, pack, unpack)

type Name = ShortText

name :: String -> Name
name = pack

string :: Name -> String
string = unpack

-- | A term in Theta Calculus.
data Term
  = Ref Name       -- x, a reference to a definition
  | Var Name Int   -- x and de Bruijn index
  | Lam Name Term  -- λx.t
  | PLam Name Term -- λX.t
  | App Term Term  -- t t'
  | PApp Term Type -- t T
  | Ann Term Type  -- t : T

instance Show Term where
  show trm =
    case trm of
    Ref x -> unpack x
    Var x _ -> unpack x
    Lam x t -> "λ" ++ unpack x ++ "." ++ show t
    PLam x t -> "λ" ++ unpack x ++ "." ++ show t
    App t u -> "(" ++ show t ++ " " ++ show u ++ ")"
    PApp t u -> "(" ++ show t ++ " " ++ show u ++ ")"
    Ann t u -> "[" ++ show t ++ " : " ++ show u ++ "]"

-- | A type in Theta Calculus.
data Type
  = TRef Name       -- X, a reference to a definition
  | TVar Name Int   -- X and de Bruijn index
  | Thet Name Term  -- θx.t
  | FLam Name Type  -- ΛX.T
  | VLam Name Type  -- Λx.T
  | FApp Type Type  -- T T'
  | VApp Type Term  -- T t
  | TAnn Type Kind  -- T : κ

instance Show Type where
  show typ =
    case typ of
    TRef x -> unpack x
    TVar x _ -> unpack x
    Thet x t -> "θ" ++ unpack x ++ "." ++ show t
    FLam x t -> "Λ" ++ unpack x ++ "." ++ show t
    VLam x t -> "Λ" ++ unpack x ++ "." ++ show t
    FApp t u -> "(" ++ show t ++ " " ++ show u ++ ")"
    VApp t u -> "(" ++ show t ++ " " ++ show u ++ ")"
    TAnn t k -> "[" ++ show t ++ " : " ++ show k ++ "]"

-- | A kind in Theta Calculus.
data Kind
  = KStar  -- ✲
  | KThet Name Type  -- θX.T

instance Show Kind where
  show k =
    case k of
    KStar -> "✲"
    KThet x t -> "θ" ++ unpack x ++ "." ++ show t

-- | Higher-order representation of terms.
data TermH
  = RefH Name
  | VarH Name !Int -- x and de Bruijn depth
  | LamH Name (TermH -> TermH)
  | PLamH Name (TypeH -> TermH)
  | AppH TermH TermH
  | PAppH TermH TypeH
  | AnnH TermH TypeH

-- | Higher-order representation of types.
data TypeH
  = TRefH Name
  | TVarH Name !Int -- X and de Bruijn depth
  | ThetH Name (TermH -> TermH)
  | FLamH Name (TypeH -> TypeH)
  | VLamH Name (TermH -> TypeH)
  | FAppH TypeH TypeH
  | VAppH TypeH TermH
  | TAnnH TypeH KindH

-- | Higher-order representation of kinds.
data KindH
  = KStarH
  | KThetH Name (TypeH -> TypeH)

-- | A top-level term definition.
data TermDef = TermDef Name Type Term

-- | A top-level type definition.
data TypeDef = TypeDef Name Kind Type

-- | A module is a collection of term and type definitions. Also keeps track
-- of the names of the definitions in the reverse order they were added.
data Module = Module
  { termDefs :: Map Name TermDef
  , typeDefs :: Map Name TypeDef
  , nameDefs :: [Name]
  }

emptyModule :: Module
emptyModule =
  Module { termDefs = Data.Map.empty, typeDefs = Data.Map.empty, nameDefs = [] }

getTermDef :: Name -> Module -> Maybe TermDef
getTermDef x m = Data.Map.lookup x (termDefs m)

getTypeDef :: Name -> Module -> Maybe TypeDef
getTypeDef x m = Data.Map.lookup x (typeDefs m)

addTermDef :: TermDef -> Module -> Module
addTermDef def@(TermDef x _ _) m =
  m { termDefs = Data.Map.insert x def (termDefs m), nameDefs = x : nameDefs m }

addTypeDef :: TypeDef -> Module -> Module
addTypeDef def@(TypeDef x _ _) m =
  m { typeDefs = Data.Map.insert x def (typeDefs m), nameDefs = x : nameDefs m }