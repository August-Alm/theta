module Types
( Name
, name
, Term (..)
, Type (..)
, Kind (..)
, TermH (..)
, TypeH (..)
, KindH (..)
) where

import Data.Text.Short (ShortText, pack, unpack)

type Name = ShortText

name :: String -> Name
name = pack

-- | A term in Theta Calculus.
data Term
  = Var Name Int   -- x and de Bruijn index
  | Lam Name Term  -- λx.t
  | PLam Name Term -- λX.t
  | App Term Term  -- t t'
  | PApp Term Type -- t T
  | Ann Term Type  -- t : T

instance Show Term where
  show trm =
    case trm of
    Var x i -> unpack x ++ show i
    Lam x t -> "λ" ++ unpack x ++ "." ++ show t
    PLam x t -> "λ" ++ unpack x ++ "." ++ show t
    App t u -> "(" ++ show t ++ " " ++ show u ++ ")"
    PApp t u -> "(" ++ show t ++ " " ++ show u ++ ")"
    Ann t u -> "[" ++ show t ++ " : " ++ show u ++ "]"

-- | A type in Theta Calculus.
data Type
  = TVar Name Int   -- X and de Bruijn index
  | Thet Name Term  -- θx.t
  | FLam Name Type  -- ΛX.T
  | VLam Name Type  -- Λx.T
  | FApp Type Type  -- T T'
  | VApp Type Term  -- T t
  | TAnn Type Kind  -- T : κ

instance Show Type where
  show typ =
    case typ of
    TVar x i -> unpack x ++ show i
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
  = VarH Name !Int
  | LamH Name !(TermH -> TermH)
  | PLamH Name !(TypeH -> TermH)
  | AppH !TermH !TermH
  | PAppH !TermH !TypeH
  | AnnH !TermH !TypeH

-- | Higher-order representation of types.
data TypeH
  = TVarH Name !Int
  | ThetH Name !(TermH -> TermH)
  | FLamH Name !(TypeH -> TypeH)
  | VLamH Name !(TermH -> TypeH)
  | FAppH !TypeH !TypeH
  | VAppH !TypeH !TermH
  | TAnnH !TypeH !KindH

-- | Higher-order representation of kinds.
data KindH
  = KStarH
  | KThetH Name !(TypeH -> TypeH)
