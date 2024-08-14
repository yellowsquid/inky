module Inky.Kind

import Control.Function
import Data.Bool.Decidable
import Decidable.Equality.Core

public export
data Kind : Type where
  KStar : Kind
  KArrow : Kind -> Kind -> Kind

export
Eq Kind where
  KStar == KStar = True
  (t1 `KArrow` u1) == (t2 `KArrow` u2) = t1 == t2 && u1 == u2
  _ == _ = False

export
Uninhabited (KStar = KArrow t u) where
  uninhabited prf impossible

export
Uninhabited (KArrow t u = KStar) where
  uninhabited prf impossible

export
Biinjective KArrow where
  biinjective Refl = (Refl, Refl)

export
DecEq Kind where
  decEq KStar KStar = Yes Refl
  decEq KStar (KArrow _ _) = No absurd
  decEq (KArrow k1 k2) KStar = No absurd
  decEq (KArrow k1 k2) (KArrow j1 j2) =
    case (decEq k1 j1, decEq k2 j2) of
      (Yes eq1, Yes eq2) => Yes (cong2 KArrow eq1 eq2)
      (Yes eq1, No neq2) => No (neq2 . snd . biinjective)
      (No neq1, _) => No (neq1 . fst . biinjective)

export
decEqReflects : (k, j : Kind) -> (k = j) `Reflects` (k == j)
decEqReflects KStar KStar = RTrue Refl
decEqReflects KStar (KArrow _ _) = RFalse absurd
decEqReflects (KArrow k1 k2) KStar = RFalse absurd
decEqReflects (KArrow k1 k2) (KArrow j1 j2) with (decEqReflects k1 j1) | (k1 == j1)
  _ | RTrue eq1 | _ with (decEqReflects k2 j2) | (k2 == j2)
    _ | RTrue eq2 | _ = RTrue (cong2 KArrow eq1 eq2)
    _ | RFalse neq2 | _ = RFalse (neq2 . snd . biinjective)
  _ | RFalse neq1 | _ = RFalse (neq1 . fst . biinjective)
