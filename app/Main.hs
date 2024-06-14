module Main where

import Theta

-- | Kind @✲ -> ✲@.
-- @θF.ΛX.[(F [X : ✲]) : ✲]@
starStar :: Kind
starStar =
  KThet f (FLam x
    (TAnn (FApp (TVar f 1) (TAnn (TVar x 0) KStar)) KStar))
      where
        f = name "F"
        x = name "X"

-- | "Any" type.
-- @θt.t@
any :: Type
any = Thet t (Var t 0) where t = name "t"

-- | Simple function type @A -> B@.
-- @ΛA.ΛB.θf.λx.[(f [x : A]) : B]@
hom :: Type
hom =
  FLam a (FLam b (Thet f (Lam x
    (Ann (App (Var f 1) (Ann (Var x 0) (TVar a 1))) (TVar b 0)))))
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
    (Ann (App (Var f 1) (Ann (Var x 0) (TVar a 0))) bx))))
      where
        a = name "A"
        x = name "x"
        b = name "B"
        f = name "f"
        bx = VApp (TVar b 1) (Ann (Var x 0) (TVar a 1))

-- | Forall type, aka @∀x.A.B@.
-- @ΛA.ΛB.θt.λx.[t : (B [x : A])]@
all :: Type
all = FLam a (FLam b (Thet t (Lam x (Ann (Var t 1) bxa))))
  where
    a = name "A"
    x = name "x"
    b = name "B"
    t = name "t"
    bxa = VApp (TVar b 0) (Ann (Var x 0) (TVar a 1))

-- Polymorphic forall type, aka @∀X:κ.T@.
-- @ΛT.θs.λX.[s : (T [X : κ])]@
pol :: Kind -> Type
pol k = FLam t (Thet s (PLam x (Ann (Var s 1) txk)))
  where
    t = name "T"
    s = name "s"
    x = name "X"
    txk = FApp (TVar t 1) (TAnn (TVar x 0) k) 

-- | Very dependent (self-typed) function type.
-- @ΛA.ΛB.θf.λx.[(f [x : A]) : ((B f) [x : A])]@
ind :: Type
ind =
  FLam a (FLam b (Thet f (Lam x
    (Ann (App (Var f 1) (Ann (Var x 0) (TVar a 1))) (VApp bf xa)))))
    where
      a = name "A"
      b = name "B"
      f = name "f"
      x = name "x"
      bf = VApp (TVar b 1) (Var f 1)
      xa = Ann (Var x 0) (TVar a 3)

-- | Dependent pairs, aka @Σx:A.B@.
-- @ΛA.ΛB.θpar.(par λx.λy.λp.((p [x : A]) [y : (B [x : A])]))@
sig :: Type
sig =
  FLam a (FLam b (Thet par
    (App (Var par 0) (Lam x (Lam y (Lam p (App (App (Var p 0) xa) yb)))))))
      where
        a = name "A"
        b = name "B"
        par = name "par"
        x = name "x"
        y = name "y"
        p = name "p"
        xa = Ann (Var x 2) (TVar a 1)
        yb = Ann (Var y 1) (VApp (TVar b 0) xa)

-- Examples.

-- | Functorial endomorphism type.
end :: Type
end = FLam x (FApp (FApp hom (TVar x 0)) (TVar x 0))
  where
    x = name "X"

-- | Natural transformations type.
nat :: Type
nat = FLam f (FLam g (FLam a (FApp (FApp hom fa) ga)))
  where
    f = name "F"
    g = name "G"
    a = name "A"
    fa = FApp (TVar f 2) (TVar a 0)
    ga = FApp (TVar g 1) (TVar a 0)

-- | Church numerals type.
church :: Type
church = FApp (FApp nat end) end

idlam :: Term
idlam = PLam a (Lam x (Var x 0))
  where
    a = name "A"
    x = name "x"

two :: Term
two = PLam a (Lam s (Lam z (App (Var s 1) (App (Var s 1) (Var z 0)))))
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
