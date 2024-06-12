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
  = Var Name  -- x
  | Lam Name Term  -- λx.t
  | PLam Name Term  -- λX.t
  | App Term Term  -- t t'
  | PApp Term Type  -- t T
  | Ann Term Type  -- t : T

instance Show Term where
  show = showTerm

-- | A type in Theta Calculus.
data Type
  = TVar Name  -- X
  | Thet Name Term  -- θx.t
  | FLam Name Type  -- ΛX.T
  | VLam Name Type  -- Λx.T
  | FApp !Type !Type  -- T T'
  | VApp !Type !Term  -- T t
  | TAnn !Type !Kind  -- T : κ

instance Show Type where
  show = showType

-- | A kind in Theta Calculus.
data Kind
  = KStar  -- ✲
  | KThet Name Type  -- θX.T

instance Show Kind where
  show = showKind

-- | Higher-order representation of terms.
data TermH
  = VarH Name
  | LamH Name !(TermH -> TermH)
  | PLamH Name !(TypeH -> TermH)
  | AppH !TermH !TermH
  | PAppH !TermH !TypeH
  | AnnH !TermH !TypeH

-- | Higher-order representation of types.
data TypeH
  = TVarH Name
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


showTerm :: Term -> String
showTerm t =
  case t of
  Var x -> unpack x
  Lam x t -> "λ" ++ unpack x ++ "." ++ showTerm t
  PLam x t -> "λ" ++ unpack x ++ "." ++ showTerm t
  App t u -> "(" ++ showTerm t ++ " " ++ showTerm u ++ ")"
  PApp t u -> "(" ++ showTerm t ++ " " ++ showType u ++ ")"
  Ann t u -> "[" ++ showTerm t ++ " : " ++ showType u ++ "]"

showType :: Type -> String
showType a =
  case a of
  TVar x -> unpack x
  Thet x t -> "θ" ++ unpack x ++ "." ++ showTerm t
  FLam x t -> "Λ" ++ unpack x ++ "." ++ showType t
  VLam x t -> "Λ" ++ unpack x ++ "." ++ showType t
  FApp t u -> "(" ++ showType t ++ " " ++ showType u ++ ")"
  VApp t u -> "(" ++ showType t ++ " " ++ showTerm u ++ ")"
  TAnn t k -> "[" ++ showType t ++ " : " ++ showKind k ++ "]"

showKind :: Kind -> String
showKind k =
  case k of
  KStar -> "✲"
  KThet x t -> "θ" ++ unpack x ++ "." ++ showType t