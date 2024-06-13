module Theta
( Types.Term (..)
, Types.Type (..)
, Types.Kind (..)
, Types.name
, normaliseTerm
, normaliseType
, normaliseKind
, check
) where

import Types
import Env
import Data.Data (eqT)

toTermH :: Env -> Term -> TermH
toTermH env trm =
  case trm of
  Var x i ->
    case getTerm i env of
    Just t -> t
    Nothing -> VarH x (depth env - i)
  Lam x t -> LamH x (\v -> toTermH (bindTerm x v env) t)
  App t u -> AppH (toTermH env t) (toTermH env u)
  PLam x t -> PLamH x (\v -> toTermH (bindType x v env) t)
  PApp t a -> PAppH (toTermH env t) (toTypeH env a)
  Ann t a -> AnnH (toTermH env t) (toTypeH env a)

toTypeH :: Env -> Type -> TypeH
toTypeH env typ =
  case typ of
  TVar x i ->
    case getType i env of
    Just t -> t
    Nothing -> TVarH x (depth env - i)
  Thet x t -> ThetH x (\v -> toTermH (bindTerm x v env) t)
  FLam x t -> FLamH x (\v -> toTypeH (bindType x v env) t)
  VLam x t -> VLamH x (\v -> toTypeH (bindTerm x v env) t)
  FApp t u -> FAppH (toTypeH env t) (toTypeH env u)
  VApp t u -> VAppH (toTypeH env t) (toTermH env u)
  TAnn t k -> TAnnH (toTypeH env t) (toKindH env k)

toKindH :: Env -> Kind -> KindH
toKindH env k =
  case k of
  KStar -> KStarH
  KThet x t -> KThetH x (\v -> toTypeH (bindType x v env) t)

ofTermH :: Env -> TermH -> Term
ofTermH env trm =
  case trm of
  VarH x i -> Var x (if i < 0 then depth env + i else i)
  LamH x f ->
    Lam x' (ofTermH env' (f v'))
      where (x', v', env') = freshTerm x env
  AppH t u -> App (ofTermH env t) (ofTermH env u)
  PLamH x f ->
    PLam x' (ofTermH env' (f v'))
      where (x', v', env') = freshType x env
  PAppH t a -> PApp (ofTermH env t) (ofTypeH env a)
  AnnH t a -> Ann (ofTermH env t) (ofTypeH env a)

ofTypeH :: Env -> TypeH -> Type
ofTypeH env typ =
  case typ of
  TVarH x i -> TVar x (if i < 0 then depth env + i else i)
  ThetH x f ->
    Thet x' (ofTermH env' (f v'))
      where (x', v', env') = freshTerm x env
  FLamH x f ->
    FLam x' (ofTypeH env' (f v'))
      where (x', v', env') = freshType x env
  VLamH x f ->
    VLam x' (ofTypeH env' (f v'))
      where (x', v', env') = freshTerm x env
  FAppH t u -> FApp (ofTypeH env t) (ofTypeH env u)
  VAppH t u -> VApp (ofTypeH env t) (ofTermH env u)
  TAnnH t k -> TAnn (ofTypeH env t) (ofKindH env k)

ofKindH :: Env -> KindH -> Kind
ofKindH env k =
  case k of
  KStarH -> KStar
  KThetH x f ->
    KThet x' (ofTypeH env' (f v'))
      where (x', v', env') = freshType x env

normTerm :: TermH -> TermH
normTerm trm =
  case trm of
  VarH _ _ -> trm
  LamH x f -> LamH x (normTerm . f)
  AppH t u ->
    case (normTerm t, normTerm u) of
    (LamH _ f, v) -> f v
    (f, v) -> AppH f v
  PLamH x f -> PLamH x (normTerm . f)
  PAppH f a ->
    case (normTerm f, normType a) of
    (PLamH _ g, b) -> g b
    (g, b) -> PAppH g b
  AnnH t a ->
    case (normTerm t, normType a) of
    (s, ThetH _ f) -> f s
    (LamH _ f, VLamH x b) -> LamH x (\v -> normTerm $ AnnH (f v) (b v))
    (s, VLamH x b) -> LamH x (normTerm . AnnH s . b)
    (PLamH _ f, FLamH x b) -> PLamH x (\v -> normTerm $ AnnH (f v) (b v))
    (s, FLamH x b) -> PLamH x (normTerm . AnnH s . b)
    (AnnH s b, c) | eqType 0 b c -> s
    (s, b) -> AnnH s b

normType :: TypeH -> TypeH
normType typ =
  case typ of
  TVarH _ _ -> typ
  ThetH x f -> ThetH x (normTerm . f)
  FLamH x f -> FLamH x (normType . f)
  VLamH x f -> VLamH x (normType . f)
  FAppH t u ->
    case (normType t, normType u) of
    (FLamH _ f, a) -> f a
    (f, a) -> FAppH f a
  VAppH t u ->
    case (normType t, normTerm u) of
    (VLamH _ f, v) -> f v
    (ThetH x f, b) -> ThetH x (\s -> normTerm $ AppH (f s) b)
    (f, b) -> VAppH f b
  TAnnH t k ->
    case (normType t, normKind k) of
    (s, KThetH _ f) -> f s
    (s@(ThetH _ _), KStarH) -> s
    (TAnnH s k', k'') | eqKind 0 k' k'' -> s
    (s, k') -> TAnnH s k'

normKind :: KindH -> KindH
normKind k =
  case k of
  KStarH -> k
  KThetH x f -> KThetH x (normType . f)

eqTerm :: Int -> TermH -> TermH -> Bool
eqTerm dep t u =
  case (t, u) of
  (VarH _ i, VarH _ j) -> i == j
  (LamH x f, LamH _ g) ->
    eqTerm (dep + 1) (f (VarH x dep)) (g (VarH x dep))
  (LamH x f, _) ->
    eqTerm (dep + 1) (f (VarH x dep)) (AppH u (VarH x dep))
  (_, LamH y g) ->
    eqTerm (dep + 1) (AppH t (VarH y dep)) (g (VarH y dep))
  (PLamH x f, PLamH _ g) ->
    eqTerm (dep + 1) (f (TVarH x dep)) (g (TVarH x dep))
  (PLamH x f, _) ->
    eqTerm (dep + 1) (f (TVarH x dep)) (PAppH u (TVarH x dep))
  (_, PLamH y g) ->
    eqTerm (dep + 1) (PAppH t (TVarH y dep)) (g (TVarH y dep))
  (AppH f x, AppH g y) ->
    eqTerm dep f g && eqTerm dep x y
  (PAppH f a, PAppH g b) ->
    eqTerm dep f g && eqType dep a b
  (AnnH f a, AnnH g b) ->
    eqTerm dep f g && eqType dep a b
  _ -> False

eqType :: Int -> TypeH -> TypeH -> Bool
eqType dep t u =
  case (t, u) of
  (TVarH _ i, TVarH _ j) -> i == j
  (ThetH x f, ThetH _ g) ->
    eqTerm (dep + 1) (f (VarH x dep)) (g (VarH x dep))
  (ThetH x f, _) ->
    eqTerm (dep + 1) (f (VarH x dep)) (AnnH (VarH x dep) u)
  (_, ThetH y g) ->
    eqTerm (dep + 1) (AnnH (VarH y dep) t) (g (VarH y dep))
  (FLamH x f, FLamH _ g) ->
    eqType (dep + 1) (f (TVarH x dep)) (g (TVarH x dep))
  (FLamH x f, a) ->
    eqType (dep + 1) (f (TVarH x dep)) (FAppH a (TVarH x dep))
  (_, FLamH y g) ->
    eqType (dep + 1) (FAppH t (TVarH y dep)) (g (TVarH y dep))
  (VLamH x f, VLamH _ g) ->
    eqType (dep + 1) (f (VarH x dep)) (g (VarH x dep))
  (VLamH x f, _) ->
    eqType (dep + 1) (f (VarH x dep)) (VAppH u (VarH x dep))
  (_, VLamH y g) ->
    eqType (dep + 1) (VAppH t (VarH y dep)) (g (VarH y dep))
  (FAppH f a, FAppH g b) ->
    eqType dep f g && eqType dep a b
  (VAppH f r, VAppH g s) ->
    eqType dep f g && eqTerm dep r s
  (TAnnH f k, TAnnH g l) ->
    eqType dep f g && eqKind dep k l
  _ -> False

eqKind :: Int -> KindH -> KindH -> Bool
eqKind dep k l =
  case (k, l) of
  (KStarH, KStarH) -> True
  (KThetH x f, KThetH _ g) ->
    eqType (dep + 1) (f (TVarH x dep)) (g (TVarH x dep))
  (KThetH x f, _) ->
    eqType (dep + 1) (f (TVarH x dep)) (TAnnH (TVarH x dep) l)
  (_, KThetH y g) ->
    eqType (dep + 1) (TAnnH (TVarH y dep) k) (g (TVarH y dep))

-- | Beta-eta term normalisation.
normaliseTerm :: Term -> Term
normaliseTerm = ofTermH empty . normTerm . toTermH empty

-- | Beta-eta type normalisation.
normaliseType :: Type -> Type
normaliseType = ofTypeH empty . normType . toTypeH empty

-- | Beta-eta kind normalisation.
normaliseKind :: Kind -> Kind
normaliseKind = ofKindH empty . normKind . toKindH empty

-- | Type checking: Checks if @[t : typ]@ normalizes to just @t@. Returns
-- either the normalized @t@ or the normalized pair @(t, [t : typ])@.
check :: Term -> Type -> Either Term (Term, Term)
check t typ =
  if eqTerm 0 tNf tAnn
  then Left (ofTermH empty tNf)
  else Right (ofTermH empty tNf, ofTermH empty tAnn)
    where
      tNf = normTerm . toTermH empty $ t
      tAnn = normTerm . toTermH empty $ Ann t typ