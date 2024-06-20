module Theta
( Types.Term (..)
, Types.Type (..)
, Types.Kind (..)
, Types.Module (..)
, Types.TermDef (..)
, Types.TypeDef (..)
, Types.KindDef (..)
, Types.emptyModule
, Types.name
, Types.string
, normaliseTerm
, normaliseType
, normaliseKind
, checkTerm
, checkType
, checkModule
, CheckResult (..)
, Parser.parseTerm
, Parser.parseType
, Parser.parseKind
, Parser.parseModule
) where

import Types
import Env
import Parser
import Debug.Trace (trace)

toTermH :: Env -> Term -> TermH
toTermH env trm =
  case trm of
  Ref x -> RefH x
  Var x i ->
    case getTerm i env of
    Just t -> t
    Nothing -> VarH x (termsDepth env - i)
  Lam x t -> LamH x (\v -> toTermH (bindTerm x v env) t)
  App t u -> AppH (toTermH env t) (toTermH env u)
  PLam x t -> PLamH x (\v -> toTermH (bindType x v env) t)
  PApp t a -> PAppH (toTermH env t) (toTypeH env a)
  Ann t a -> AnnH (toTermH env t) (toTypeH env a)

toTypeH :: Env -> Type -> TypeH
toTypeH env typ =
  case typ of
  TRef x -> TRefH x
  TVar x i ->
    case getType i env of
    Just t -> t
    Nothing -> TVarH x (typesDepth env - i)
  Thet x t -> ThetH x (\v -> toTermH (bindTerm x v env) t)
  FLam x t -> FLamH x (\v -> toTypeH (bindType x v env) t)
  VLam x t -> VLamH x (\v -> toTypeH (bindTerm x v env) t)
  FApp t u -> FAppH (toTypeH env t) (toTypeH env u)
  VApp t u -> VAppH (toTypeH env t) (toTermH env u)
  TAnn t k -> TAnnH (toTypeH env t) (toKindH env k)

toKindH :: Env -> Kind -> KindH
toKindH env k =
  case k of
  KRef x -> KRefH x
  KThet x t -> KThetH x (\v -> toTypeH (bindType x v env) t)

ofTermH :: Env -> TermH -> Term
ofTermH env trm =
  case trm of
  RefH x -> Ref x
  VarH x i -> Var x (if i < 0 then termsDepth env + i else i)
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
  TRefH x -> TRef x
  TVarH x i -> TVar x (if i < 0 then typesDepth env + i else i)
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
  KRefH x -> KRef x
  KThetH x f ->
    KThet x' (ofTypeH env' (f v'))
      where (x', v', env') = freshType x env

unrefTerm :: Module -> TermH -> TermH
unrefTerm m t =
  case t of
  RefH x ->
    case getTermDef x m of
    Just (TermDef _ _ u) -> toTermH Env.empty u
    Nothing -> t
  _ -> t

unrefType :: Module -> TypeH -> TypeH
unrefType m t =
  case t of
  TRefH x ->
    case getTypeDef x m of
    Just (TypeDef _ _ u) -> toTypeH Env.empty u
    Nothing -> t
  _ -> t

unrefKind :: Module -> KindH -> KindH
unrefKind m k =
  case k of
  KRefH x ->
    case getKindDef x m of
    Just (KindDef _ u) -> toKindH Env.empty u
    Nothing -> k
  _ -> k

normTerm :: Module -> TermH -> TermH
normTerm m trm =
  case trm of
  RefH _ -> trm
  VarH _ _ -> trm
  LamH x f -> LamH x (normTerm m . f)
  AppH t u ->
    case (normTerm m (unrefTerm m t), normTerm m u) of
    (LamH _ f, v) -> normTerm m (f v)
    (f, v) -> AppH f v
  PLamH x f -> PLamH x (normTerm m . f)
  PAppH f a ->
    case (normTerm m (unrefTerm m f), normType m a) of
    (PLamH _ g, b) -> g b
    (g, b) -> PAppH g b
  AnnH t a ->
    case (normTerm m t, normType m (unrefType m a)) of
    (s, ThetH _ f) -> normTerm m (f s)
    (LamH _ f, VLamH x b) -> LamH x (\v -> normTerm m $ AnnH (f v) (b v))
    (s, VLamH x b) -> LamH x (\v -> normTerm m $ AnnH (AppH s v) (b v))
    (PLamH _ f, FLamH x b) -> PLamH x (\v -> normTerm m $ AnnH (f v) (b v))
    (s, FLamH x b) -> PLamH x (\v -> normTerm m $ AnnH (PAppH s v) (b v))
    (AnnH s b, c) | eqType m 0 0 b c -> s
    (s, b) -> AnnH s b

normType :: Module -> TypeH -> TypeH
normType m typ =
  case typ of
  TRefH _ -> typ
  TVarH _ _ -> typ
  ThetH x f -> ThetH x (normTerm m . f)
  FLamH x f -> FLamH x (normType m . f)
  VLamH x f -> VLamH x (normType m . f)
  FAppH t u ->
    case (normType m (unrefType m t), normType m u) of
    (FLamH _ f, a) -> f a
    (f, a) -> FAppH f a
  VAppH t u ->
    case (normType m (unrefType m t), normTerm m u) of
    (VLamH _ f, v) -> f v
    (ThetH x f, b) -> ThetH x (\s -> normTerm m $ AppH (f s) b)
    (f, b) -> VAppH f b
  TAnnH t k ->
    case (normType m t, normKind m (unrefKind m k)) of
    (s, KThetH _ f) -> f s
    (TAnnH s k', k'') | eqKind m 0 0 k' k'' -> s
    (s, k') -> TAnnH s k'

normKind :: Module -> KindH -> KindH
normKind m k =
  case k of
  KRefH _ -> k
  KThetH x f -> KThetH x (normType m . f)

redTerm :: Module -> TermH -> TermH
redTerm m trm =
  case trm of
  AppH (LamH _ f) u -> redTerm m (f u)
  AppH t@(RefH _) u -> redTerm m (AppH (redUnrefTerm t) u)
  PAppH (PLamH _ f) a -> redTerm m (f a)
  PAppH t@(RefH _) a -> redTerm m (PAppH (redUnrefTerm t) a)
  AnnH s (ThetH _ f) -> redTerm m (f s)
  AnnH (LamH _ f) (VLamH x b) -> LamH x (\v -> AnnH (f v) (b v))
  AnnH s (VLamH x b) -> LamH x (AnnH s . b)
  AnnH (PLamH _ f) (FLamH x b) -> PLamH x (\v -> AnnH (f v) (b v))
  AnnH s (FLamH x b) -> PLamH x (AnnH s . b)
  AnnH t@(RefH _) u@(TRefH _) -> redTerm m (AnnH (redUnrefTerm t) (redUnrefType u))
  AnnH t@(RefH _) u -> redTerm m (AnnH (redUnrefTerm t) u)
  AnnH s u@(TRefH _) -> redTerm m (AnnH s (redUnrefType u))
  _ -> trm
  where
    redUnrefTerm t = redTerm m (unrefTerm m t)
    redUnrefType t = redType m (unrefType m t)

redType :: Module -> TypeH -> TypeH
redType m typ =
  case typ of
  FAppH (FLamH _ f) a -> redType m (f a)
  FAppH t@(TRefH _) u -> redType m (FAppH (redUnrefType t) u)
  VAppH (VLamH _ f) u -> redType m (f u)
  VAppH t@(TRefH _) u -> redType m (VAppH (redUnrefType t) u)
  TAnnH t (KThetH _ f) -> redType m (f t)
  TAnnH t@(TRefH _) k -> redType m (TAnnH (redUnrefType t) k)
  _ -> typ
  where
    redUnrefType t = redType m (unrefType m t)

traceTerm :: TermH -> TermH
traceTerm t = trace (show (ofTermH Env.empty t)) t

traceType :: TypeH -> TypeH
traceType t = trace (show (ofTypeH Env.empty t)) t

eqTerm :: Module -> Int -> Int -> TermH -> TermH -> Bool
eqTerm m trmDep typDep t u =
  case (t, u) of
  (RefH x, RefH y) ->
    (x == y) || (case (getTermDef x m, getTermDef y m) of
      (Just (TermDef _ _ tt), Just (TermDef _ _ uu)) ->
        eqTerm m trmDep typDep (toTermH Env.empty tt) (toTermH Env.empty uu)
      _ -> False)
  (RefH x, _) ->
    case getTermDef x m of
    Just (TermDef _ _ tt) -> eqTerm m trmDep typDep (toTermH Env.empty tt) u
    _ -> False
  (_, RefH y) ->
    case getTermDef y m of
    Just (TermDef _ _ uu) -> eqTerm m trmDep typDep t (toTermH Env.empty uu)
    _ -> False
  (VarH _ i, VarH _ j) -> i == j
  (LamH x f, LamH _ g) ->
    eqTerm m (trmDep + 1) typDep (f (VarH x trmDep)) (g (VarH x trmDep))
  (LamH x f, _) ->
    eqTerm m (trmDep + 1) typDep (f (VarH x trmDep)) (AppH u (VarH x trmDep))
  (_, LamH y g) ->
    eqTerm m (trmDep + 1) typDep (AppH t (VarH y trmDep)) (g (VarH y trmDep))
  (PLamH x f, PLamH _ g) ->
    eqTerm m trmDep (typDep + 1) (f (TVarH x typDep)) (g (TVarH x typDep))
  (PLamH x f, _) ->
    eqTerm m trmDep (typDep + 1) (f (TVarH x typDep)) (PAppH u (TVarH x typDep))
  (_, PLamH y g) ->
    eqTerm m trmDep (typDep + 1) (PAppH t (TVarH y typDep)) (g (TVarH y typDep))
  (AppH f x, AppH g y) ->
    eqTerm m trmDep typDep f g && eqTerm m trmDep typDep x y
  (PAppH f a, PAppH g b) ->
    eqTerm m trmDep typDep f g && eqType m trmDep typDep a b
  (AnnH f a, AnnH g b) ->
    eqTerm m trmDep typDep f g && eqType m trmDep typDep a b
  _ -> False

eqType :: Module -> Int -> Int -> TypeH -> TypeH -> Bool
eqType m trmDep typDep t u =
  case (t, u) of
  (TRefH x, TRefH y) ->
    (x == y) || (case (getTypeDef x m, getTypeDef y m) of
      (Just (TypeDef _ _ tt), Just (TypeDef _ _ uu)) ->
        eqType m trmDep typDep (toTypeH Env.empty tt) (toTypeH Env.empty uu)
      _ -> False)
  (TRefH x, _) ->
    case getTypeDef x m of
    Just (TypeDef _ _ tt) -> eqType m trmDep typDep (toTypeH Env.empty tt) u
    _ -> False
  (_, TRefH y) ->
    case getTypeDef y m of
    Just (TypeDef _ _ uu) -> eqType m trmDep typDep t (toTypeH Env.empty uu)
    _ -> False
  (TVarH _ i, TVarH _ j) -> i == j
  (ThetH x f, ThetH _ g) ->
    eqTerm m (trmDep + 1) typDep (f (VarH x trmDep)) (g (VarH x trmDep))
  (ThetH x f, _) ->
    eqTerm m (trmDep + 1) typDep (f (VarH x trmDep)) (AnnH (VarH x trmDep) u)
  (_, ThetH y g) ->
    eqTerm m (trmDep + 1) typDep (AnnH (VarH y trmDep) t) (g (VarH y trmDep))
  (FLamH x f, FLamH _ g) ->
    eqType m trmDep (typDep + 1) (f (TVarH x typDep)) (g (TVarH x typDep))
  (FLamH x f, a) ->
    eqType m trmDep (typDep + 1) (f (TVarH x typDep)) (FAppH a (TVarH x typDep))
  (_, FLamH y g) ->
    eqType m trmDep (typDep + 1) (FAppH t (TVarH y typDep)) (g (TVarH y typDep))
  (VLamH x f, VLamH _ g) ->
    eqType m (trmDep + 1) typDep (f (VarH x trmDep)) (g (VarH x trmDep))
  (VLamH x f, _) ->
    eqType m (trmDep + 1) typDep (f (VarH x trmDep)) (VAppH u (VarH x trmDep))
  (_, VLamH y g) ->
    eqType m (trmDep + 1) typDep (VAppH t (VarH y trmDep)) (g (VarH y trmDep))
  (FAppH f a, FAppH g b) ->
    eqType m trmDep typDep f g && eqType m trmDep typDep a b
  (VAppH f r, VAppH g s) ->
    eqType m trmDep typDep f g && eqTerm m trmDep typDep r s
  (TAnnH f k, TAnnH g l) ->
    eqType m trmDep typDep f g && eqKind m trmDep typDep k l
  _ -> False

eqKind :: Module -> Int -> Int -> KindH -> KindH -> Bool
eqKind m trmDep typDep k l =
  case (k, l) of
  (KRefH x, KRefH y) ->
    (x == y) || (case (getKindDef x m, getKindDef y m) of
      (Just (KindDef _ kk), Just (KindDef _ ll)) ->
        eqKind m trmDep typDep (toKindH Env.empty kk) (toKindH Env.empty ll)
      _ -> False)
  (KRefH x, _) ->
    case getKindDef x m of
    Just (KindDef _ kk) -> eqKind m trmDep typDep (toKindH Env.empty kk) l
    _ -> False
  (_, KRefH y) ->
    case getKindDef y m of
    Just (KindDef _ ll) -> eqKind m trmDep typDep k (toKindH Env.empty ll)
    _ -> False
  (KThetH x f, KThetH _ g) ->
    eqType m trmDep (typDep + 1) (f (TVarH x typDep)) (g (TVarH x typDep))

-- | Beta-eta term normalisation.
normaliseTerm :: Module -> Term -> Term
normaliseTerm m = ofTermH empty . normTerm m . toTermH empty

-- | Beta-eta type normalisation.
normaliseType :: Module -> Type -> Type
normaliseType m = ofTypeH empty . normType m . toTypeH empty

-- | Beta-eta kind normalisation.
normaliseKind :: Module -> Kind -> Kind
normaliseKind m = ofKindH empty . normKind m . toKindH empty

-- | Type checking of term: Checks if @[t : typ]@ normalizes to just @t@.
-- Returns either the normalized @t@ or the normalized pair @(t, [t : typ])@.
checkTerm :: Module -> Term -> Type -> Either Term (Term, Term)
checkTerm m t typ =
  if eqTerm m 0 0 tNf tAnn
  then Left (ofTermH empty tNf)
  else Right (ofTermH empty tNf, ofTermH empty tAnn)
    where
      tNf = normTerm m . toTermH empty $ t
      tAnn = normTerm m . toTermH empty $ Ann t typ

-- | Type checking of type: Checks if @[t : k]@ normalizes to just @t@.
-- Returns either the normalized @t@ or the normalized pair @(t, [t : k])@.
checkType :: Module -> Type -> Kind -> Either Type (Type, Type)
checkType m t k =
  if eqType m 0 0 tNf tAnn
  then Left (ofTypeH empty tNf)
  else Right (ofTypeH empty tNf, ofTypeH empty tAnn)
    where
      tNf = normType m . toTypeH empty $ t
      tAnn = normType m . toTypeH empty $ TAnn t k

data CheckResult
  = TypeCheck (TermDef, Either Term (Term, Term))
  | KindCheck (TypeDef, Either Type (Type, Type))
  | K KindDef

checkModule :: Module -> [CheckResult]
checkModule m = fmap result xs
  where
    xs = reverse (nameDefs m)
    result x =
      case getTermDef x m of
      Just def@(TermDef _ typ t) -> TypeCheck (def, checkTerm m t typ)
      Nothing ->
        case getTypeDef x m of
        Just def@(TypeDef _ k t) -> KindCheck (def, checkType m t k)
        Nothing ->
          case getKindDef x m of
          Just def -> K def
          Nothing -> error "impossible!"
