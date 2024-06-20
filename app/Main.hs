module Main where

import Theta


star :: Kind
star = KThet (name "T") (TVar (name "T") 0)

-- | Kind @✲ -> ✲@.
-- @θF.ΛX.[(F [X : ✲]) : ✲]@
starStar :: Kind
starStar =
  KThet f (FLam x
    (TAnn (FApp (TVar f 1) (TAnn (TVar x 0) star)) star))
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

reportCheckResult :: CheckResult -> IO ()
reportCheckResult res =
  case res of
  TypeCheck (TermDef x typ t, Left tNf) -> do
    putStrLn $ "ok! " ++ string x ++ " : " ++ show typ
    putStrLn $ "original term = " ++ show t
    putStrLn $ "normalised term = " ++ show tNf
    putStrLn ""
  TypeCheck (TermDef x typ t, Right (tNf, tAnn)) -> do
    putStrLn $ "bad! " ++ string x ++ " : " ++ show typ
    putStrLn $ "original term = " ++ show t
    putStrLn $ "normalised term = " ++ show tNf
    putStrLn $ "annotated term = " ++ show tAnn
    putStrLn ""
  KindCheck (TypeDef x k t, Left tNf) -> do
    putStrLn $ "ok! " ++ string x ++ " : " ++ show k
    putStrLn $ "original type = " ++ show t
    putStrLn $ "normalised type = " ++ show tNf
    putStrLn ""
  KindCheck (TypeDef x k t, Right (tNf, tAnn)) -> do
    putStrLn $ "bad! " ++ string x ++ " : " ++ show k
    putStrLn $ "original type = " ++ show t
    putStrLn $ "normalised type = " ++ show tNf
    putStrLn $ "annotated type = " ++ show tAnn
    putStrLn ""
  K (KindDef x k) -> do
    putStrLn $ "kind! " ++ string x ++ " = " ++ show k
    putStrLn ""

report :: Module -> IO ()
report = mapM_ reportCheckResult . checkModule

reportTypeCheck :: Module -> Term -> Type -> IO ()
reportTypeCheck m trm typ =
  case checkTerm m trm typ of
  Left t -> do
    putStrLn "ok!"
    putStrLn $ "normalised term = " ++ show t
  Right (t, t') -> do
    putStrLn "bad!"
    putStrLn $ "normalised term = " ++ show t
    putStrLn $ "annotated term = " ++ show t'


main :: IO ()
main = do

  report . parseModule $ "let Hom : θF.ΛX.ΛY.[((F [X : ✲]) [Y : ✲]) : ✲] = ΛA.ΛB.θf.λx.[(f [x : A]) : B]"
  
  report . parseModule $
    "let Bool : ✲ = θb.λP.λt.λf.[(((b P) [t : (P true)]) [f : (P false)]) : (P b)] \
    \let true : Bool = λP.λt.λf.t \
    \let false : Bool = λP.λt.λf.t"

  -- @ΛT.θs.λX.[s : (T [X : κ])]@
  report . parseModule $
    "let Church : ✲ = \
    \  let Hom = ΛA.ΛB.θf.λx.[(f [x : [A : ✲]]) : [B : ✲]]; \
    \  ΛA.((Hom ((Hom A) A)) ((Hom A) A))  \
    \let two : Church = λA.λs.λz.(s (s z))"

  -- This fails because of infinite recursion. TODO!
  --report . parseModule $
  --  "let Nat : ✲ = θnat.λP.λs.λz. \
  --  \  [(((nat P) \
  --  \     [s : θs.λn.[(s [n : Nat]) : (P (succ n))]]) \
  --  \     [z : (P zero)]) \
  --  \   : (P nat)]\
  --  \let succ : Nat = λn.λP.λs.λz.((s n) (((n P) s) z)) \
  --  \let zero : Nat = λP.λs.λz.z"

  report . parseModule $
      "let Hom : θF.ΛX.ΛY.[((F [X : ✲]) [Y : ✲]) : ✲] = ΛA.ΛB.θf.λx.[(f [x : A]) : B] \
      \let Either : θF.ΛX.ΛY.[((F [X : ✲]) [Y : ✲]) : ✲] = ΛA.ΛB.θself.λP.λl.λr. \
      \  [(((self P) \
      \     λa.[(l [a : A]) : (P (((left A) B) a))]) \
      \     λb.[(r [b : B]) : (P (((right A) B) b))]) \
      \   : (P self)] \
      \let left : ΛA.ΛB.((Hom A) ((Either A) B)) = λA.λB.λa.λP.λl.λr.(l a) \
      \let right : ΛA.ΛB.((Hom B) ((Either A) B)) = λA.λB.λb.λP.λl.λr.(r b)"

  src <- readFile "mu.tc"
  report . parseModule $ src

