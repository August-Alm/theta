{-# language BlockArguments, BangPatterns #-}

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
import Debug.Trace (trace)

eqTerm :: Env -> TermH -> TermH -> Bool
eqTerm env t u =
  case (t, u) of
  (VarH x, VarH y) -> x == y
  (LamH x f, LamH _ g) ->
    eqTerm env' (f xv) (g xv)
      where (_, xv, env') = bindFreshTerm x env
  (LamH x f, _) ->
    eqTerm env' (f xv) (AppH u xv)
     where (_, xv, env') = bindFreshTerm x env
  (_, LamH y g) ->
    eqTerm env' (AppH t yv) (g yv)
      where (_, yv, env') = bindFreshTerm y env
  (PLamH x f, PLamH _ g) ->
    eqTerm env' (f xt) (g xt)
      where (_, xt, env') = bindFreshType x env
  (PLamH x f, _) ->
    eqTerm env' (f xt) (PAppH u xt)
      where (_, xt, env') = bindFreshType x env
  (_, PLamH y g) ->
    eqTerm env' (PAppH t yt) (g yt)
      where (_, yt, env') = bindFreshType y env
  (AppH f x, AppH g y) ->
    eqTerm env f g && eqTerm env x y
  (PAppH f a, PAppH g b) ->
    eqTerm env f g && eqType env a b
  (AnnH f a, AnnH g b) ->
    eqTerm env f g && eqType env a b
  _ -> False

eqType :: Env -> TypeH -> TypeH -> Bool
eqType env t u =
  let t = debugPrintType env t in
  case (t, u) of
  (TVarH x, TVarH y) -> x == y
  (ThetH x f, ThetH _ g) ->
    eqTerm env' (f xv) (g xv)
      where (_, xv, env') = bindFreshTerm x env
  (ThetH x f, _) ->
    eqTerm env' (f xv) (AnnH xv u)
      where (_, xv, env') = bindFreshTerm x env
  (_, ThetH y g) ->
    eqTerm env' (AnnH yv t) (g yv)
      where (_, yv, env') = bindFreshTerm y env
  (FLamH x f, FLamH _ g) ->
    eqType env' (f xt) (g xt)
      where (_, xt, env') = bindFreshType x env
  (FLamH x f, u) ->
    eqType env' (f xt) (FAppH u xt)
      where (_, xt, env') = bindFreshType x env
  (t, FLamH y g) ->
    eqType env' (FAppH t yv) (g yv)
    where (_, yv, env') = bindFreshType y env
  (VLamH x f, VLamH _ g) ->
    eqType env' (f xv) (g xv)
      where (_, xv, env') = bindFreshTerm x env
  (VLamH x f, _) ->
    eqType env' (f xv) (VAppH u xv)
      where (_, xv, env') = bindFreshTerm x env
  (_, VLamH y g) ->
    eqType env' (VAppH t yv) (g yv)
      where (_, yv, env') = bindFreshTerm y env
  (FAppH f a, FAppH g b) ->
    eqType env f g && eqType env a b
  (VAppH f t, VAppH g u) ->
    eqType env f g && eqTerm env t u
  (TAnnH f k, TAnnH g l) ->
    eqType env f g && eqKind env k l
  _ -> False

eqKind :: Env -> KindH -> KindH -> Bool
eqKind env k l =
  case (k, l) of
  (KStarH, KStarH) -> True
  (KThetH x f, KThetH _ g) ->
    eqType env' (f xt) (g xt)
      where (_, xt, env') = bindFreshType x env
  (KThetH x f, _) ->
    eqType env' (f xt) (TAnnH xt l)
      where (_, xt, env') = bindFreshType x env
  (_, KThetH y g) ->
    eqType env' (TAnnH yt k) (g yt)
      where (_, yt, env') = bindFreshType y env

evTerm :: Env -> Term -> TermH
evTerm env t =
  case t of
  Var x -> case lookupTerm x env of
    Just t -> t
    Nothing -> error "unbound variable" --VarH x
  Lam x t ->
    LamH x (\v -> evTerm (bindTerm x v env) t)
  App t u ->
    case (evTerm env t, evTerm env u) of
    (LamH _ t, u) -> t u
    (t, u) -> AppH t u
  PLam x t' ->
    PLamH x (\v -> evTerm (bindType x v env) t')
  PApp t a ->
    case (evTerm env t, evType env a) of
    (PLamH _ t, u) -> t u
    (t, u) -> PAppH t u
  Ann t a ->
    case (evTerm env t, evType env a) of
    (AnnH t b, a) | eqType env a b -> t
    (LamH _ f, VLamH x a) ->
      LamH x (\v ->
        case a v of
        ThetH _ u -> u (f v)
        av -> AnnH (f v) av)
    (t, VLamH x a) ->
      LamH x (\v ->
        case a v of
        ThetH _ u -> u t
        av -> AnnH (AppH t v) av)
    (PLamH _ t, FLamH x a) ->
      PLamH x (\v ->
        case a v of
        ThetH _ u -> u (t v)
        av -> AnnH (t v) av)
    (PLamH _ t, a) -> AnnH (t a) a
    (t, a) -> AnnH t a

debugPrintTerm :: Env -> TermH -> TermH
debugPrintTerm env t = trace (show . quTerm env $ t) t

debugPrintType :: Env -> TypeH -> TypeH
debugPrintType env t = trace (show . quType env $ t) t

evType :: Env -> Type -> TypeH
evType env a =
  case a of
  TVar x -> case lookupType x env of
    Just t -> t
    Nothing -> error "unbound variable" --TVarH x
  Thet x t ->
    ThetH x (\v -> evTerm (bindTerm x v env) t)
  FLam x t ->
    FLamH x (\v -> evType (bindType x v env) t)
  VLam x t ->
    VLamH x (\v -> evType (bindTerm x v env) t)
  FApp t u ->
    --let t' = debugPrintType env $ evType env t in
    --let u' = debugPrintType env $ evType env u in
    --case (t', u') of
    case (evType env t, evType env u) of
    (FLamH _ t, u) -> t u
    (t, u) -> FAppH t u
  VApp t u ->
    case (evType env t, evTerm env u) of
    (VLamH _ t, u) -> t u
    (ThetH x t, u) ->
      ThetH x (\v ->
        case t v of
        LamH _ f -> f u
        tv -> AppH tv u)
    (t, u) -> VAppH t u
  TAnn t k ->
    case (evType env t, evKind env k) of
    (TAnnH t l, k) | eqKind env k l -> t
    (t, KThetH _ u) -> u t
    (ThetH x t, KStarH) -> ThetH x t
    (t, k) -> TAnnH t k

evKind :: Env -> Kind -> KindH
evKind env k =
  case k of
  KStar -> KStarH
  KThet x t ->
    KThetH x (\v -> evType (bindType x v env) t)

quTerm :: Env -> TermH -> Term
quTerm env t =
  case t of
  VarH x -> Var x
  LamH x f ->
    Lam x' (quTerm env' (f xv))
      where (x', xv, env') = bindFreshTerm x env
  AppH t u ->
    App (quTerm env t) (quTerm env u)
  PLamH x f ->
    PLam x' (quTerm env' (f xt))
      where (x', xt, env') = bindFreshType x env
  PAppH t a ->
    PApp (quTerm env t) (quType env a)
  AnnH t a ->
    Ann (quTerm env t) (quType env a)

quType :: Env -> TypeH -> Type
quType env a =
  case a of
  TVarH x -> TVar x
  ThetH x f ->
    Thet x' (quTerm env' (f xv))
      where (x', xv, env') = bindFreshTerm x env
  FLamH x f ->
    FLam x' (quType env' (f xt))
      where (x', xt, env') = bindFreshType x env
  VLamH x f ->
    VLam x' (quType env' (f xv))
      where (x', xv, env') = bindFreshTerm x env
  FAppH t u ->
    FApp (quType env t) (quType env u)
  VAppH t u ->
    VApp (quType env t) (quTerm env u)
  TAnnH t k ->
    TAnn (quType env t) (quKind env k)

quKind :: Env -> KindH -> Kind
quKind env k =
  case k of
  KStarH -> KStar
  KThetH x f -> KThet x' (quType env' (f xt))
    where (x', xt, env') = bindFreshType x env

-- | Beta-eta term normalisation.
normaliseTerm :: Term -> Term
normaliseTerm = quTerm empty . evTerm empty

-- | Beta-eta type normalisation.
normaliseType :: Type -> Type
normaliseType = quType empty . evType empty

-- | Beta-eta kind normalisation.
normaliseKind :: Kind -> Kind
normaliseKind = quKind empty . evKind empty

-- | Type checking: Checks if @[t : typ]@ normalizes to just @t@. Returns
-- either the normalized @t@ or the normalized pair @(t, [t : typ])@.
check :: Term -> Type -> Either Term (Term, Term)
check t typ =
  if eqTerm empty tNf tAnn
  then Left (quTerm empty tNf)
  else Right (quTerm empty tNf, quTerm empty tAnn)
    where
      tNf = evTerm empty t
      tAnn = evTerm empty (Ann t typ)