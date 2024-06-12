module Main where

import Theta

-- | Kind @✲ -> ✲@.
-- @θF.ΛX.[(F [X : ✲]) : ✲]@
starStar :: Kind
starStar =
  KThet f (FLam x
    (TAnn (FApp (TVar f) (TAnn (TVar x) KStar)) KStar))
      where
        f = name "F"
        x = name "X"

-- | "Any" type.
-- @θt.t@
any :: Type
any = Thet t (Var t) where t = name "t"

-- | Simple function type @A -> B@.
-- @ΛA.ΛB.θf.λx.[(f [x : A]) : B]@
hom :: Type
hom =
  FLam a (FLam b (Thet f (Lam x
    (Ann (App (Var f) (Ann (Var x) (TVar a))) (TVar b)))))
    where
      a = name "A"
      b = name "B"
      f = name "f"
      x = name "x"

-- | Dependent function type @(x : A) -> B@, aka @Πx:A.B@.
-- @ΛA.ΛB.θf.λx.[(f [x : A]) : (B [x : A])]@
map :: Type
map =
  FLam a (FLam b (Thet f (Lam x
    (Ann (App (Var f) (Ann (Var x) (TVar a))) bx))))
      where
        a = name "A"
        x = name "x"
        b = name "B"
        f = name "f"
        bx = VApp (TVar b) (Ann (Var x) (TVar a))

-- | Forall type, aka @∀x.A.B@.
-- @ΛA.ΛB.θt.λx.[t : (B [x : A])]@
all :: Type
all = FLam a (FLam b (Thet t (Lam x (Ann (Var t) bxa))))
  where
    a = name "A"
    x = name "x"
    b = name "B"
    t = name "t"
    bxa = VApp (TVar b) (Ann (Var x) (TVar a))

-- Polymorphic forall type, aka @∀X:κ.T@.
-- @ΛT.θt.λX.[t : (T [X : κ])]@
pol :: Kind -> Type
pol k = FLam t (Thet t (PLam x (Ann (Var t) bxk)))
  where
    t = name "T"
    x = name "X"
    bxk = FApp (TVar t) (TAnn (TVar x) k) 

-- | Very dependent (self-typed) function type.
-- @ΛA.ΛB.θf.λx.[(f [x : A]) : ((B f) [x : A])]@
ind :: Type
ind =
  FLam a (FLam b (Thet f (Lam x
    (Ann (App (Var f) (Ann (Var x) (TVar a))) (VApp bf xa)))))
    where
      a = name "A"
      b = name "B"
      f = name "f"
      x = name "x"
      bf = VApp (TVar b) (Var f)
      xa = Ann (Var x) (TVar a)

-- | Dependent pairs, aka @Σx:A.B@.
-- @ΛA.ΛB.θpar.(par λx.λy.λp.((p [x : A]) [y : (B [x : A])]))@
sig :: Type
sig =
  FLam a (FLam b (Thet par
    (App (Var par) (Lam x (Lam y (Lam p (App (App (Var p) xa) yb)))))))
      where
        a = name "A"
        b = name "B"
        par = name "par"
        x = name "x"
        y = name "y"
        p = name "p"
        xa = Ann (Var x) (TVar a)
        yb = Ann (Var y) (VApp (TVar b) xa)

-- Examples.

-- | Functorial endomorphism type.
end :: Type
end = FLam x (FApp (FApp hom (TVar x)) (TVar x))
  where
    x = name "X"

-- | Natural transformations type.
nat :: Type
nat = FLam f (FLam g (FLam a (FApp (FApp hom fa) ga)))
  where
    f = name "F"
    g = name "G"
    a = name "A"
    fa = FApp (TVar f) (TVar a)
    ga = FApp (TVar g) (TVar a)

-- | Church numerals type.
church :: Type
church = FApp (FApp nat end) end

idlam :: Term
idlam = PLam a (Lam x (Var x))
  where
    a = name "A"
    x = name "x"

two :: Term
two = PLam a (Lam s (Lam z (App (Var s) (App (Var s) (Var z)))))
  where
    a = name "A"
    s = name "s"
    z = name "z"

report :: Term -> Type -> IO ()
report trm typ =
  case check trm typ of
    Left t -> do
      putStrLn "ok!"
      putStrLn $ "normalized term = " ++ show t
    Right (t, t') -> do
      putStrLn "bad!"
      putStrLn $ "normalized term = " ++ show t
      putStrLn $ "annotated term = " ++ show t'


main :: IO ()
main = do
  putStrLn $ "Hom = " ++ show (normaliseType hom)
  putStrLn $ "Map = " ++ show (normaliseType Main.map)
  putStrLn $ "All = " ++ show (normaliseType Main.all)
  putStrLn $ "Pol ✲ = " ++ show (normaliseType (pol starStar))
  putStrLn $ "Ind = " ++ show (normaliseType ind)
  putStrLn $ "Sig = " ++ show (normaliseType sig)
  putStrLn $ "End = " ++ show (normaliseType end)
  putStrLn $ "Nat = " ++ show (normaliseType nat)
  putStrLn $ "Church = " ++ show (normaliseType church)
  putStrLn ""
  putStrLn "Checking idlam : ∀X:✲.X -> X"
  report idlam end
  putStrLn ""
  putStrLn "Checking two : ∀A:✲.((A -> A) -> A -> A)"
  report two church
