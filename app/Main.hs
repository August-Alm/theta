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

end :: Type
end = FLam a (FApp (FApp hom (TVar a)) (TVar a))
  where
    a = name "A"

nat :: Type
nat = FLam f (FLam g (FLam a (FApp (FApp hom fa) ga)))
  where
    f = name "F"
    g = name "G"
    a = name "A"
    fa = FApp (TVar f) (TVar a)
    ga = FApp (TVar g) (TVar a)

church :: Type
church = (FApp nat end) 
--church = FApp (FApp nat end) end

idlam :: Term
idlam = PLam a (Lam x (Var x))
  where
    a = name "A"
    x = name "x"

main :: IO ()
main = do
  print "Hello, Haskell!"
  --print (normaliseTerm idlam)
  --print (normaliseType hom)
  --print (normaliseType end)
  --print (normaliseType nat)
  print (normaliseType church)
  --do
  --  case check idlam church of
  --    (Left t) -> do
  --      print "good!"
  --      print t
  --    Right (t, t') -> do
  --      print "bad!"
  --      print t
  --      print t'
