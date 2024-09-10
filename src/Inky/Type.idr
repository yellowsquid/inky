module Inky.Type

import public Data.List1

import Control.Function
import Data.Bool.Decidable
import Data.Either
import Data.These
import Data.These.Decidable
import Decidable.Equality
import Inky.Thinning

-- Utilities -------------------------------------------------------------------

reflectFinEq : (i, j : Fin n) -> (i = j) `Reflects` (i == j)
reflectFinEq FZ FZ = RTrue Refl
reflectFinEq FZ (FS j) = RFalse absurd
reflectFinEq (FS i) FZ = RFalse absurd
reflectFinEq (FS i) (FS j) =
  viaEquivalence (MkEquivalence (\prf => cong FS prf) injective)
    (reflectFinEq i j)

-- Definition ------------------------------------------------------------------

public export
data Ty : Nat -> Type where
  TVar : Fin n -> Ty n
  TNat : Ty n
  TArrow : Ty n -> Ty n -> Ty n
  TUnion : List1 (Ty n) -> Ty n
  TProd : List (Ty n) -> Ty n
  TSum : List (Ty n) -> Ty n
  TFix : Ty (S n) -> Ty n

%name Ty a, b, c

export
Injective TVar where
  injective Refl = Refl

-- Equality --------------------------------------------------------------------

export
eq : Ty n -> Ty n -> Bool
eqAll : List (Ty n) -> List (Ty n) -> Bool
eqAll1 : List1 (Ty n) -> List1 (Ty n) -> Bool

TVar i `eq` TVar j = i == j
TNat `eq` TNat = True
TArrow a b `eq` TArrow c d = (a `eq` c) && (b `eq` d)
TUnion as `eq` TUnion bs = as `eqAll1` bs
TProd as `eq` TProd bs = as `eqAll` bs
TSum as `eq` TSum bs = as `eqAll` bs
TFix a `eq` TFix b = a `eq` b
_ `eq` _ = False

[] `eqAll` [] = True
(a :: as) `eqAll` (b :: bs) = (a `eq` b) && (as `eqAll` bs)
_ `eqAll` _ = False

(a ::: as) `eqAll1` (b ::: bs) = (a `eq` b) && (as `eqAll` bs)

public export
Eq (Ty n) where
  (==) = eq

export
reflectEq : (a, b : Ty n) -> (a = b) `Reflects` (a `eq` b)
reflectEqAll : (as, bs : List (Ty n)) -> (as = bs) `Reflects` (as `eqAll` bs)
reflectEqAll1 : (as, bs : List1 (Ty n)) -> (as = bs) `Reflects` (as `eqAll1` bs)

reflectEq (TVar i) (TVar j) with (reflectFinEq i j) | (i == j)
  _ | RTrue eq | _ = RTrue (cong TVar eq)
  _ | RFalse neq | _ = RFalse (\eq => neq $ injective eq)
reflectEq (TVar i) TNat = RFalse (\case Refl impossible)
reflectEq (TVar i) (TArrow c d) = RFalse (\case Refl impossible)
reflectEq (TVar i) (TUnion c) = RFalse (\case Refl impossible)
reflectEq (TVar i) (TProd c) = RFalse (\case Refl impossible)
reflectEq (TVar i) (TSum c) = RFalse (\case Refl impossible)
reflectEq (TVar i) (TFix b) = RFalse (\case Refl impossible)
reflectEq TNat (TVar j) = RFalse (\case Refl impossible)
reflectEq TNat TNat = RTrue Refl
reflectEq TNat (TArrow c d) = RFalse (\case Refl impossible)
reflectEq TNat (TUnion c) = RFalse (\case Refl impossible)
reflectEq TNat (TProd c) = RFalse (\case Refl impossible)
reflectEq TNat (TSum c) = RFalse (\case Refl impossible)
reflectEq TNat (TFix b) = RFalse (\case Refl impossible)
reflectEq (TArrow a b) (TVar j) = RFalse (\case Refl impossible)
reflectEq (TArrow a b) TNat = RFalse (\case Refl impossible)
reflectEq (TArrow a b) (TArrow c d) with (reflectEq a c) | (a `eq` c)
  _ | RTrue eq1 | _ with (reflectEq b d) | (b `eq` d)
    _ | RTrue eq2 | _ = RTrue (cong2 TArrow eq1 eq2)
    _ | RFalse neq2 | _ = RFalse (\case Refl => neq2 Refl)
  _ | RFalse neq1 | _ = RFalse (\case Refl => neq1 Refl)
reflectEq (TArrow a b) (TUnion c) = RFalse (\case Refl impossible)
reflectEq (TArrow a b) (TProd c) = RFalse (\case Refl impossible)
reflectEq (TArrow a b) (TSum c) = RFalse (\case Refl impossible)
reflectEq (TArrow a b) (TFix c) = RFalse (\case Refl impossible)
reflectEq (TUnion as) (TVar j) = RFalse (\case Refl impossible)
reflectEq (TUnion as) TNat = RFalse (\case Refl impossible)
reflectEq (TUnion as) (TArrow c d) = RFalse (\case Refl impossible)
reflectEq (TUnion as) (TUnion c) with (reflectEqAll1 as c) | (as `eqAll1` c)
  _ | RTrue eq | _ = RTrue (cong TUnion eq)
  _ | RFalse neq | _ = RFalse (\case Refl => neq Refl)
reflectEq (TUnion as) (TProd c) = RFalse (\case Refl impossible)
reflectEq (TUnion as) (TSum c) = RFalse (\case Refl impossible)
reflectEq (TUnion as) (TFix b) = RFalse (\case Refl impossible)
reflectEq (TProd as) (TVar j) = RFalse (\case Refl impossible)
reflectEq (TProd as) TNat = RFalse (\case Refl impossible)
reflectEq (TProd as) (TArrow c d) = RFalse (\case Refl impossible)
reflectEq (TProd as) (TUnion c) = RFalse (\case Refl impossible)
reflectEq (TProd as) (TProd c) with (reflectEqAll as c) | (as `eqAll` c)
  _ | RTrue eq | _ = RTrue (cong TProd eq)
  _ | RFalse neq | _ = RFalse (\case Refl => neq Refl)
reflectEq (TProd as) (TSum c) = RFalse (\case Refl impossible)
reflectEq (TProd as) (TFix b) = RFalse (\case Refl impossible)
reflectEq (TSum as) (TVar j) = RFalse (\case Refl impossible)
reflectEq (TSum as) TNat = RFalse (\case Refl impossible)
reflectEq (TSum as) (TArrow c d) = RFalse (\case Refl impossible)
reflectEq (TSum as) (TUnion c) = RFalse (\case Refl impossible)
reflectEq (TSum as) (TProd c) = RFalse (\case Refl impossible)
reflectEq (TSum as) (TSum c) with (reflectEqAll as c) | (as `eqAll` c)
  _ | RTrue eq | _ = RTrue (cong TSum eq)
  _ | RFalse neq | _ = RFalse (\case Refl => neq Refl)
reflectEq (TSum as) (TFix b) = RFalse (\case Refl impossible)
reflectEq (TFix a) (TVar j) = RFalse (\case Refl impossible)
reflectEq (TFix a) TNat = RFalse (\case Refl impossible)
reflectEq (TFix a) (TArrow c d) = RFalse (\case Refl impossible)
reflectEq (TFix a) (TUnion c) = RFalse (\case Refl impossible)
reflectEq (TFix a) (TProd c) = RFalse (\case Refl impossible)
reflectEq (TFix a) (TSum c) = RFalse (\case Refl impossible)
reflectEq (TFix a) (TFix b) with (reflectEq a b) | (a `eq` b)
  _ | RTrue eq | _ = RTrue (cong TFix eq)
  _ | RFalse neq | _ = RFalse (\case Refl => neq Refl)

reflectEqAll [] [] = RTrue Refl
reflectEqAll [] (b :: bs) = RFalse (\case Refl impossible)
reflectEqAll (a :: as) [] = RFalse (\case Refl impossible)
reflectEqAll (a :: as) (b :: bs) with (reflectEq a b) | (a `eq` b)
  _ | RTrue eq1 | _ with (reflectEqAll as bs) | (as `eqAll` bs)
    _ | RTrue eq2 | _ = RTrue (cong2 (::) eq1 eq2)
    _ | RFalse neq2 | _ = RFalse (\case Refl => neq2 Refl)
  _ | RFalse neq1 | _ = RFalse (\case Refl => neq1 Refl)

reflectEqAll1 (a ::: as) (b ::: bs) with (reflectEq a b) | (a `eq` b)
  _ | RTrue eq1 | _ with (reflectEqAll as bs) | (as `eqAll` bs)
    _ | RTrue eq2 | _ = RTrue (cong2 (:::) eq1 eq2)
    _ | RFalse neq2 | _ = RFalse (\case Refl => neq2 Refl)
  _ | RFalse neq1 | _ = RFalse (\case Refl => neq1 Refl)

-- Occurs ----------------------------------------------------------------------

OccursIn : Fin n -> Ty n -> Type
OccursInAny : Fin n -> List (Ty n) -> Type
OccursInAny1 : Fin n -> List1 (Ty n) -> Type

i `OccursIn` TVar j = i = j
i `OccursIn` TNat = Void
i `OccursIn` TArrow a b = These (i `OccursIn` a) (i `OccursIn` b)
i `OccursIn` TUnion as = i `OccursInAny1` as
i `OccursIn` TProd as = i `OccursInAny` as
i `OccursIn` TSum as = i `OccursInAny` as
i `OccursIn` TFix a = FS i `OccursIn` a

i `OccursInAny` [] = Void
i `OccursInAny` a :: as = These (i `OccursIn` a) (i `OccursInAny` as)

i `OccursInAny1` a ::: as = These (i `OccursIn` a) (i `OccursInAny` as)

-- Decidable

occursIn : (i : Fin n) -> (a : Ty n) -> Bool
occursInAny : (i : Fin n) -> (as : List (Ty n)) -> Bool
occursInAny1 : (i : Fin n) -> (as : List1 (Ty n)) -> Bool

reflectOccursIn :
  (i : Fin n) -> (a : Ty n) ->
  (i `OccursIn` a) `Reflects` (i `occursIn` a)
reflectOccursInAny :
  (i : Fin n) -> (as : List (Ty n)) ->
  (i `OccursInAny` as) `Reflects` (i `occursInAny` as)
reflectOccursInAny1 :
  (i : Fin n) -> (as : List1 (Ty n)) ->
  (i `OccursInAny1` as) `Reflects` (i `occursInAny1` as)

i `occursIn` (TVar j) = i == j
i `occursIn` TNat = False
i `occursIn` (TArrow a b) = (i `occursIn` a) || (i `occursIn` b)
i `occursIn` (TUnion as) = i `occursInAny1` as
i `occursIn` (TProd as) = i `occursInAny` as
i `occursIn` (TSum as) = i `occursInAny` as
i `occursIn` (TFix a) = FS i `occursIn` a

i `occursInAny` [] = False
i `occursInAny` (a :: as) = (i `occursIn` a) || (i `occursInAny` as)

i `occursInAny1` (a ::: as) = (i `occursIn` a) || (i `occursInAny` as)

reflectOccursIn i (TVar j) = reflectFinEq i j
reflectOccursIn i TNat = RFalse id
reflectOccursIn i (TArrow a b) = reflectThese (reflectOccursIn i a) (reflectOccursIn i b)
reflectOccursIn i (TUnion as) = reflectOccursInAny1 i as
reflectOccursIn i (TProd as) = reflectOccursInAny i as
reflectOccursIn i (TSum as) = reflectOccursInAny i as
reflectOccursIn i (TFix a) = reflectOccursIn (FS i) a

reflectOccursInAny i [] = RFalse id
reflectOccursInAny i (a :: as) = reflectThese (reflectOccursIn i a) (reflectOccursInAny i as)

reflectOccursInAny1 i (a ::: as) = reflectThese (reflectOccursIn i a) (reflectOccursInAny i as)

-- Not Strictly Positive -----------------------------------------------------------

-- We use negation so we get a cause on failure.

NotPositiveIn : Fin n -> Ty n -> Type
NotPositiveInAny : Fin n -> List (Ty n) -> Type
NotPositiveInAny1 : Fin n -> List1 (Ty n) -> Type

i `NotPositiveIn` TVar j = Void
i `NotPositiveIn` TNat = Void
i `NotPositiveIn` TArrow a b = These (i `OccursIn` a) (i `NotPositiveIn` b)
i `NotPositiveIn` TUnion as = i `NotPositiveInAny1` as
i `NotPositiveIn` TProd as = i `NotPositiveInAny` as
i `NotPositiveIn` TSum as = i `NotPositiveInAny` as
i `NotPositiveIn` TFix a = FS i `OccursIn` a
  -- Prevent mutual recursion;
  -- Can add back in without breaking things

i `NotPositiveInAny` [] = Void
i `NotPositiveInAny` a :: as = These (i `NotPositiveIn` a) (i `NotPositiveInAny` as)

i `NotPositiveInAny1` a ::: as = These (i `NotPositiveIn` a) (i `NotPositiveInAny` as)

-- Not Positive implies Occurs

notPositiveToOccurs : (a : Ty k) -> i `NotPositiveIn` a -> i `OccursIn` a
notPositiveAnyToOccursAny : (as : List (Ty k)) -> i `NotPositiveInAny` as -> i `OccursInAny` as
notPositiveAny1ToOccursAny1 : (as : List1 (Ty k)) -> i `NotPositiveInAny1` as -> i `OccursInAny1` as

notPositiveToOccurs (TVar j) = absurd
notPositiveToOccurs TNat = id
notPositiveToOccurs (TArrow a b) = mapSnd (notPositiveToOccurs b)
notPositiveToOccurs (TUnion as) = notPositiveAny1ToOccursAny1 as
notPositiveToOccurs (TProd as) = notPositiveAnyToOccursAny as
notPositiveToOccurs (TSum as) = notPositiveAnyToOccursAny as
notPositiveToOccurs (TFix a) = id

notPositiveAnyToOccursAny [] = id
notPositiveAnyToOccursAny (a :: as) = bimap (notPositiveToOccurs a) (notPositiveAnyToOccursAny as)

notPositiveAny1ToOccursAny1 (a ::: as) = bimap (notPositiveToOccurs a) (notPositiveAnyToOccursAny as)

-- Decidable

notEnvPositiveIn : (i : Fin n) -> (a : Ty n) -> Bool
notEnvPositiveInAny : (i : Fin n) -> (as : List (Ty n)) -> Bool
notEnvPositiveInAny1 : (i : Fin n) -> (as : List1 (Ty n)) -> Bool

i `notEnvPositiveIn` (TVar j) = False
i `notEnvPositiveIn` TNat = False
i `notEnvPositiveIn` (TArrow a b) = (i `occursIn` a) || (i `notEnvPositiveIn` b)
i `notEnvPositiveIn` (TUnion as) = i `notEnvPositiveInAny1` as
i `notEnvPositiveIn` (TProd as) = i `notEnvPositiveInAny` as
i `notEnvPositiveIn` (TSum as) = i `notEnvPositiveInAny` as
i `notEnvPositiveIn` (TFix a) = FS i `occursIn` a

i `notEnvPositiveInAny` [] = False
i `notEnvPositiveInAny` (a :: as) = (i `notEnvPositiveIn` a) || (i `notEnvPositiveInAny` as)

i `notEnvPositiveInAny1` (a ::: as) = (i `notEnvPositiveIn` a) || (i `notEnvPositiveInAny` as)

reflectNotPositiveIn :
  (i : Fin n) -> (a : Ty n) ->
  (i `NotPositiveIn` a) `Reflects` (i `notEnvPositiveIn` a)
reflectNotPositiveInAny :
  (i : Fin n) -> (as : List (Ty n)) ->
  (i `NotPositiveInAny` as) `Reflects` (i `notEnvPositiveInAny` as)
reflectNotPositiveInAny1 :
  (i : Fin n) -> (as : List1 (Ty n)) ->
  (i `NotPositiveInAny1` as) `Reflects` (i `notEnvPositiveInAny1` as)

reflectNotPositiveIn i (TVar j) = RFalse id
reflectNotPositiveIn i TNat = RFalse id
reflectNotPositiveIn i (TArrow a b) =
  reflectThese (reflectOccursIn i a) (reflectNotPositiveIn i b)
reflectNotPositiveIn i (TUnion as) = reflectNotPositiveInAny1 i as
reflectNotPositiveIn i (TProd as) = reflectNotPositiveInAny i as
reflectNotPositiveIn i (TSum as) = reflectNotPositiveInAny i as
reflectNotPositiveIn i (TFix a) = reflectOccursIn (FS i) a

reflectNotPositiveInAny i [] = RFalse id
reflectNotPositiveInAny i (a :: as) =
  reflectThese (reflectNotPositiveIn i a) (reflectNotPositiveInAny i as)

reflectNotPositiveInAny1 i (a ::: as) =
  reflectThese (reflectNotPositiveIn i a) (reflectNotPositiveInAny i as)

-- Well Formed -----------------------------------------------------------------

-- Negating reflectidable properties is fun.

export
IllFormed : Ty n -> Type
AnyIllFormed : List (Ty n) -> Type
Any1IllFormed : List1 (Ty n) -> Type

IllFormed (TVar v) = Void
IllFormed TNat = Void
IllFormed (TArrow a b) = These (IllFormed a) (IllFormed b)
IllFormed (TUnion as) = Any1IllFormed as
IllFormed (TProd as) = AnyIllFormed as
IllFormed (TSum as) = AnyIllFormed as
IllFormed (TFix a) = These (FZ `NotPositiveIn` a) (IllFormed a)

AnyIllFormed [] = Void
AnyIllFormed (a :: as) = These (IllFormed a) (AnyIllFormed as)

Any1IllFormed (a ::: as) = These (IllFormed a) (AnyIllFormed as)

-- Decidable

export
illFormed : (a : Ty n) -> Bool
anyIllFormed : (as : List (Ty n)) -> Bool
any1IllFormed : (as : List1 (Ty n)) -> Bool


illFormed (TVar j) = False
illFormed TNat = False
illFormed (TArrow a b) = illFormed a || illFormed b
illFormed (TUnion as) = any1IllFormed as
illFormed (TProd as) = anyIllFormed as
illFormed (TSum as) = anyIllFormed as
illFormed (TFix a) = (FZ `notEnvPositiveIn` a) || illFormed a

anyIllFormed [] = False
anyIllFormed (a :: as) = illFormed a || anyIllFormed as

any1IllFormed (a ::: as) = illFormed a || anyIllFormed as

export
reflectIllFormed : (a : Ty n) -> IllFormed a `Reflects` illFormed a
reflectAnyIllFormed : (as : List (Ty n)) -> AnyIllFormed as `Reflects` anyIllFormed as
reflectAny1IllFormed : (as : List1 (Ty n)) -> Any1IllFormed as `Reflects` any1IllFormed as

reflectIllFormed (TVar j) = RFalse id
reflectIllFormed TNat = RFalse id
reflectIllFormed (TArrow a b) =
  reflectThese (reflectIllFormed a) (reflectIllFormed b)
reflectIllFormed (TUnion as) = reflectAny1IllFormed as
reflectIllFormed (TProd as) = reflectAnyIllFormed as
reflectIllFormed (TSum as) = reflectAnyIllFormed as
reflectIllFormed (TFix a) = reflectThese (reflectNotPositiveIn FZ a) (reflectIllFormed a)

reflectAnyIllFormed [] = RFalse id
reflectAnyIllFormed (a :: as) =
  reflectThese (reflectIllFormed a) (reflectAnyIllFormed as)

reflectAny1IllFormed (a ::: as) =
  reflectThese (reflectIllFormed a) (reflectAnyIllFormed as)

--------------------------------------------------------------------------------
-- Thinning --------------------------------------------------------------------
--------------------------------------------------------------------------------

thin : k `Thins` n -> Ty k -> Ty n
thinAll : k `Thins` n -> List (Ty k) -> List (Ty n)
thinAll1 : k `Thins` n -> List1 (Ty k) -> List1 (Ty n)

thin f (TVar i) = TVar (index f i)
thin f TNat = TNat
thin f (TArrow a b) = TArrow (thin f a) (thin f b)
thin f (TUnion as) = TUnion (thinAll1 f as)
thin f (TProd as) = TProd (thinAll f as)
thin f (TSum as) = TSum (thinAll f as)
thin f (TFix a) = TFix (thin (Keep f) a)

thinAll f [] = []
thinAll f (a :: as) = thin f a :: thinAll f as

thinAll1 f (a ::: as) = thin f a ::: thinAll f as

-- Renaming Coalgebra

thinCong : f ~~~ g -> (a : Ty k) -> thin f a = thin g a
thinCongAll : f ~~~ g -> (as : List (Ty k)) -> thinAll f as = thinAll g as
thinCongAll1 : f ~~~ g -> (as : List1 (Ty k)) -> thinAll1 f as = thinAll1 g as

thinCong prf (TVar i) = cong TVar (prf.index i)
thinCong prf TNat = Refl
thinCong prf (TArrow a b) = cong2 TArrow (thinCong prf a) (thinCong prf b)
thinCong prf (TUnion as) = cong TUnion (thinCongAll1 prf as)
thinCong prf (TProd as) = cong TProd (thinCongAll prf as)
thinCong prf (TSum as) = cong TSum (thinCongAll prf as)
thinCong prf (TFix a) = cong TFix (thinCong (KeepKeep prf) a)

thinCongAll prf [] = Refl
thinCongAll prf (a :: as) = cong2 (::) (thinCong prf a) (thinCongAll prf as)

thinCongAll1 prf (a ::: as) = cong2 (:::) (thinCong prf a) (thinCongAll prf as)

thinId : (a : Ty n) -> thin Id a = a
thinIdAll : (as : List (Ty n)) -> thinAll Id as = as
thinIdAll1 : (as : List1 (Ty n)) -> thinAll1 Id as = as

thinId (TVar i) = cong TVar (indexId i)
thinId TNat = Refl
thinId (TArrow a b) = cong2 TArrow (thinId a) (thinId b)
thinId (TUnion as) = cong TUnion (thinIdAll1 as)
thinId (TProd as) = cong TProd (thinIdAll as)
thinId (TSum as) = cong TSum (thinIdAll as)
thinId (TFix a) = cong TFix (trans (thinCong (KeepId IdId) a) (thinId a))

thinIdAll [] = Refl
thinIdAll (a :: as) = cong2 (::) (thinId a) (thinIdAll as)

thinIdAll1 (a ::: as) = cong2 (:::) (thinId a) (thinIdAll as)

export
Rename Ty where
  var = TVar
  rename = thin
  renameCong = thinCong
  renameId = thinId

-- Properties ------------------------------------------------------------------

-- Occurs --

thinOccursIn :
  (0 f : k `Thins` n) -> (0 i : Fin k) -> (a : Ty k) ->
  i `OccursIn` a ->
  index f i `OccursIn` thin f a
thinOccursInAny :
  (0 f : k `Thins` n) -> (0 i : Fin k) -> (as : List (Ty k)) ->
  i `OccursInAny` as ->
  index f i `OccursInAny` thinAll f as
thinOccursInAny1 :
  (0 f : k `Thins` n) -> (0 i : Fin k) -> (as : List1 (Ty k)) ->
  i `OccursInAny1` as ->
  index f i `OccursInAny1` thinAll1 f as

thinOccursIn f i (TVar x) = \Refl => Refl
thinOccursIn f i TNat = id
thinOccursIn f i (TArrow a b) = bimap (thinOccursIn f i a) (thinOccursIn f i b)
thinOccursIn f i (TUnion as) = thinOccursInAny1 f i as
thinOccursIn f i (TProd as) = thinOccursInAny f i as
thinOccursIn f i (TSum as) = thinOccursInAny f i as
thinOccursIn f i (TFix a) =
  rewrite sym $ indexKeepFS f i in
  thinOccursIn (Keep f) (FS i) a

thinOccursInAny f i [] = id
thinOccursInAny f i (a :: as) = bimap (thinOccursIn f i a) (thinOccursInAny f i as)

thinOccursInAny1 f i (a ::: as) = bimap (thinOccursIn f i a) (thinOccursInAny f i as)

-- Inverse

thinOccursInInv' :
  (0 f : k `Thins` n) -> (0 i : Fin n) ->
  (a : Ty k) ->
  i `OccursIn` thin f a ->
  (j ** (index f j = i, j `OccursIn` a))
thinOccursInAnyInv' :
  (0 f : k `Thins` n) -> (0 i : Fin n) ->
  (as : List (Ty k)) ->
  i `OccursInAny` thinAll f as ->
  (j ** (index f j = i, j `OccursInAny` as))
thinOccursInAny1Inv' :
  (0 f : k `Thins` n) -> (0 i : Fin n) ->
  (as : List1 (Ty k)) ->
  i `OccursInAny1` thinAll1 f as ->
  (j ** (index f j = i, j `OccursInAny1` as))

thinOccursInInv' f i (TVar j) = \eq => (j ** (sym eq , Refl))
thinOccursInInv' f i TNat = absurd
thinOccursInInv' f i (TArrow a b) =
  these
    (\occurs =>
      let (j ** (eq, prf)) = thinOccursInInv' f i a occurs in
      (j ** (eq, This prf)))
    (\occurs =>
      let (j ** (eq, prf)) = thinOccursInInv' f i b occurs in
      (j ** (eq, That prf)))
    (\occurs1, occurs2 =>
      let (j1 ** (eq1, prf1)) = thinOccursInInv' f i a occurs1 in
      let (j2 ** (eq2, prf2)) = thinOccursInInv' f i b occurs2 in
      (j1 ** (eq1,
        Both prf1 $
        rewrite indexInjective f {x = j1, y = j2} $ trans eq1 (sym eq2) in
        prf2)))
thinOccursInInv' f i (TUnion as) = thinOccursInAny1Inv' f i as
thinOccursInInv' f i (TProd as) = thinOccursInAnyInv' f i as
thinOccursInInv' f i (TSum as) = thinOccursInAnyInv' f i as
thinOccursInInv' f i (TFix a) =
  \occurs =>
    case thinOccursInInv' (Keep f) (FS i) a occurs of
      (FZ ** prf) => absurd (trans (sym $ indexKeepFZ f) (fst prf))
      (FS j ** (eq, prf)) =>
        (j ** (irrelevantEq (injective $ trans (sym $ indexKeepFS f j) eq), prf))

thinOccursInAnyInv' f i [] = absurd
thinOccursInAnyInv' f i (a :: as) =
  these
    (\occurs =>
      let (j ** (eq, prf)) = thinOccursInInv' f i a occurs in
      (j ** (eq, This prf)))
    (\occurs =>
      let (j ** (eq, prf)) = thinOccursInAnyInv' f i as occurs in
      (j ** (eq, That prf)))
    (\occurs1, occurs2 =>
      let (j1 ** (eq1, prf1)) = thinOccursInInv' f i a occurs1 in
      let (j2 ** (eq2, prf2)) = thinOccursInAnyInv' f i as occurs2 in
      (j1 ** (eq1,
        Both prf1 $
        rewrite indexInjective f {x = j1, y = j2} $ trans eq1 (sym eq2) in
        prf2)))

thinOccursInAny1Inv' f i (a ::: as) =
  these
    (\occurs =>
      let (j ** (eq, prf)) = thinOccursInInv' f i a occurs in
      (j ** (eq, This prf)))
    (\occurs =>
      let (j ** (eq, prf)) = thinOccursInAnyInv' f i as occurs in
      (j ** (eq, That prf)))
    (\occurs1, occurs2 =>
      let (j1 ** (eq1, prf1)) = thinOccursInInv' f i a occurs1 in
      let (j2 ** (eq2, prf2)) = thinOccursInAnyInv' f i as occurs2 in
      (j1 ** (eq1,
        Both prf1 $
        rewrite indexInjective f {x = j1, y = j2} $ trans eq1 (sym eq2) in
        prf2)))

thinOccursInInv :
  (0 f : k `Thins` n) -> (0 i : Fin k) -> (a : Ty k) ->
  index f i `OccursIn` thin f a ->
  i `OccursIn` a
thinOccursInInv f i a occurs =
  let (j ** (eq, prf)) = thinOccursInInv' f (index f i) a occurs in
  rewrite indexInjective f {x = i, y = j} $ sym eq in
  prf

thinOccursInAny1Inv :
  (0 f : k `Thins` n) -> (0 i : Fin k) -> (as : List1 (Ty k)) ->
  index f i `OccursInAny1` thinAll1 f as ->
  i `OccursInAny1` as
thinOccursInAny1Inv f i as occurs =
  let (j ** (eq, prf)) = thinOccursInAny1Inv' f (index f i) as occurs in
  rewrite indexInjective f {x = i, y = j} $ sym eq in
  prf

-- Not Positive --

thinNotPositiveInv :
  (0 f : k `Thins` n) -> (0 i : Fin k) -> (a : Ty k) ->
  index f i `NotPositiveIn` thin f a -> i `NotPositiveIn` a
thinNotPositiveAnyInv :
  (0 f : k `Thins` n) -> (0 i : Fin k) -> (as : List (Ty k)) ->
  index f i `NotPositiveInAny` thinAll f as -> i `NotPositiveInAny` as
thinNotPositiveAny1Inv :
  (0 f : k `Thins` n) -> (0 i : Fin k) -> (as : List1 (Ty k)) ->
  index f i `NotPositiveInAny1` thinAll1 f as -> i `NotPositiveInAny1` as

thinNotPositiveInv f i (TVar j) = id
thinNotPositiveInv f i TNat = id
thinNotPositiveInv f i (TArrow a b) =
  bimap
    (thinOccursInInv f i a)
    (thinNotPositiveInv f i b)
thinNotPositiveInv f i (TUnion as) = thinNotPositiveAny1Inv f i as
thinNotPositiveInv f i (TProd as) = thinNotPositiveAnyInv f i as
thinNotPositiveInv f i (TSum as) = thinNotPositiveAnyInv f i as
thinNotPositiveInv f i (TFix a) =
  \occurs =>
    thinOccursInInv (Keep f) (FS i) a $
    rewrite indexKeepFS f i in
    occurs

thinNotPositiveAnyInv f i [] = id
thinNotPositiveAnyInv f i (a :: as) =
  bimap (thinNotPositiveInv f i a) (thinNotPositiveAnyInv f i as)

thinNotPositiveAny1Inv f i (a ::: as) =
  bimap (thinNotPositiveInv f i a) (thinNotPositiveAnyInv f i as)

-- Ill Formed --

thinIllFormedInv :
  (0 f : k `Thins` n) -> (a : Ty k) ->
  IllFormed (thin f a) -> IllFormed a
thinAnyIllFormedInv :
  (0 f : k `Thins` n) -> (as : List (Ty k)) ->
  AnyIllFormed (thinAll f as) -> AnyIllFormed as
thinAny1IllFormedInv :
  (0 f : k `Thins` n) -> (as : List1 (Ty k)) ->
  Any1IllFormed (thinAll1 f as) -> Any1IllFormed as

thinIllFormedInv f (TVar i) = id
thinIllFormedInv f TNat = id
thinIllFormedInv f (TArrow a b) = bimap (thinIllFormedInv f a) (thinIllFormedInv f b)
thinIllFormedInv f (TUnion as) = thinAny1IllFormedInv f as
thinIllFormedInv f (TProd as) = thinAnyIllFormedInv f as
thinIllFormedInv f (TSum as) = thinAnyIllFormedInv f as
thinIllFormedInv f (TFix a) =
  bimap
    (\npos => thinNotPositiveInv (Keep f) FZ a $ rewrite indexKeepFZ f in npos)
    (thinIllFormedInv (Keep f) a)

thinAnyIllFormedInv f [] = id
thinAnyIllFormedInv f (a :: as) = bimap (thinIllFormedInv f a) (thinAnyIllFormedInv f as)

thinAny1IllFormedInv f (a ::: as) = bimap (thinIllFormedInv f a) (thinAnyIllFormedInv f as)

--------------------------------------------------------------------------------
-- Substitution ----------------------------------------------------------------
--------------------------------------------------------------------------------

public export
fromVar : Either (Fin n) (Ty n) -> Ty n
fromVar = either TVar id

export
sub : Env k n (Ty n) -> Ty k -> Ty n
subAll : Env k n (Ty n) -> List (Ty k) -> List (Ty n)
subAll1 : Env k n (Ty n) -> List1 (Ty k) -> List1 (Ty n)

sub env (TVar i) = fromVar $ lookup env i
sub env TNat = TNat
sub env (TArrow a b) = TArrow (sub env a) (sub env b)
sub env (TUnion as) = TUnion (subAll1 env as)
sub env (TProd as) = TProd (subAll env as)
sub env (TSum as) = TSum (subAll env as)
sub env (TFix a) = TFix (sub (lift (Drop Id) env :< TVar FZ) a)

subAll env [] = []
subAll env (a :: as) = sub env a :: subAll env as

subAll1 env (a ::: as) = sub env a ::: subAll env as

-- Properties ------------------------------------------------------------------

pushEither :
  (0 f : c -> d) -> (0 g : a -> c) -> (0 h : b -> c) -> (x : Either a b) ->
  f (either g h x) = either (f . g) (f . h) x
pushEither f g h (Left x) = Refl
pushEither f g h (Right x) = Refl

-- Occurs --

subOccursIn :
  (env : Env k n (Ty n)) -> (i : Fin k) -> (a : Ty k) ->
  j `OccursIn` fromVar (lookup env i) ->
  i `OccursIn` a ->
  j `OccursIn` sub env a
subOccursInAny :
  (env : Env k n (Ty n)) -> (i : Fin k) -> (as : List (Ty k)) ->
  j `OccursIn` fromVar (lookup env i) ->
  i `OccursInAny` as ->
  j `OccursInAny` subAll env as
subOccursInAny1 :
  (env : Env k n (Ty n)) -> (i : Fin k) -> (as : List1 (Ty k)) ->
  j `OccursIn` fromVar (lookup env i) ->
  i `OccursInAny1` as ->
  j `OccursInAny1` subAll1 env as

subOccursIn env i (TVar x) occurs = \Refl => occurs
subOccursIn env i TNat occurs = id
subOccursIn env i (TArrow a b) occurs =
  bimap
    (subOccursIn env i a occurs)
    (subOccursIn env i b occurs)
subOccursIn env i (TUnion as) occurs = subOccursInAny1 env i as occurs
subOccursIn env i (TProd as) occurs = subOccursInAny env i as occurs
subOccursIn env i (TSum as) occurs = subOccursInAny env i as occurs
subOccursIn env i (TFix a) occurs =
  subOccursIn (lift (Drop Id) env :< TVar FZ) (FS i) a {j = FS j} $
    rewrite lookupFS (lift (Drop Id) env) (TVar FZ) i in
    rewrite lookupLift (Drop Id) env i in
    rewrite eitherBimapFusion TVar id (index (Drop Id)) (thin (Drop Id)) (lookup env i) in
    rewrite sym $ pushEither (thin (Drop Id)) TVar id (lookup env i) in
    rewrite sym $ indexId j in
    rewrite sym $ indexDrop Id j in
    thinOccursIn (Drop Id) j (fromVar $ lookup env i) $
    occurs

subOccursInAny env i [] occurs = id
subOccursInAny env i (a :: as) occurs =
  bimap (subOccursIn env i a occurs) (subOccursInAny env i as occurs)

subOccursInAny1 env i (a ::: as) occurs =
  bimap (subOccursIn env i a occurs) (subOccursInAny env i as occurs)

-- Inverse

0 EnvOccursUniq : Env k n (Ty n) -> (i : Fin n) -> (j : Fin k) -> Type
EnvOccursUniq env i j = (x : Fin k) -> i `OccursIn` fromVar (lookup env x) -> j = x

liftEnvOccursUniq :
  (0 env : Env k n (Ty n)) ->
  EnvOccursUniq env i j ->
  EnvOccursUniq (lift (Drop Id) env :< TVar FZ) (FS i) (FS j)
liftEnvOccursUniq env prf FZ =
  rewrite lookupFZ (lift (Drop Id) env) (TVar FZ) in
  absurd
liftEnvOccursUniq env prf (FS x) =
  rewrite lookupFS (lift (Drop Id) env) (TVar FZ) x in
  rewrite lookupLift (Drop Id) env x in
  rewrite eitherBimapFusion TVar id (index (Drop Id)) (rename (Drop Id)) (lookup env x) in
  \occurs =>
  cong FS $
  prf x $
  thinOccursInInv (Drop Id) i (fromVar $ lookup env x) $
  rewrite pushEither (rename (Drop Id)) TVar id (lookup env x) in
  rewrite indexDrop Id i in
  rewrite indexId i in
  occurs

liftOccursUniqFZ :
  (env : Env k n (Ty n)) ->
  EnvOccursUniq (lift (Drop Id) env :< TVar FZ) FZ FZ
liftOccursUniqFZ env FZ =
  rewrite lookupFZ (lift (Drop Id) env) (TVar FZ) in
  const Refl
liftOccursUniqFZ env (FS x) =
  rewrite lookupFS (lift (Drop Id) env) (TVar FZ) x in
  rewrite lookupLift (Drop Id) env x in
  rewrite eitherBimapFusion TVar id (index (Drop Id)) (rename (Drop Id)) (lookup env x) in
  \occurs =>
  let
    (j ** (eq, occurs')) =
      thinOccursInInv' (Drop Id) FZ (fromVar $ lookup env x) $
      rewrite pushEither (rename (Drop Id)) TVar id (lookup env x) in
      occurs
  in
  absurd $ trans (sym eq) (indexDrop Id j)

subOccursInInv :
  (0 env : Env k n (Ty n)) ->
  (0 prf : EnvOccursUniq env i j) ->
  (a : Ty k) ->
  i `OccursIn` sub env a -> j `OccursIn` a
subOccursInAnyInv :
  (0 env : Env k n (Ty n)) ->
  (0 prf : EnvOccursUniq env i j) ->
  (as : List (Ty k)) ->
  i `OccursInAny` subAll env as -> j `OccursInAny` as
subOccursInAny1Inv :
  (0 env : Env k n (Ty n)) ->
  (0 prf : EnvOccursUniq env i j) ->
  (as : List1 (Ty k)) ->
  i `OccursInAny1` subAll1 env as -> j `OccursInAny1` as

subOccursInInv env prf (TVar x) = \p => irrelevantEq $ prf x p
subOccursInInv env prf TNat = id
subOccursInInv env prf (TArrow a b) =
  bimap
    (subOccursInInv env prf a)
    (subOccursInInv env prf b)
subOccursInInv env prf (TUnion as) = subOccursInAny1Inv env prf as
subOccursInInv env prf (TProd as) = subOccursInAnyInv env prf as
subOccursInInv env prf (TSum as) = subOccursInAnyInv env prf as
subOccursInInv env prf (TFix a) =
  subOccursInInv
    (lift (Drop Id) env :< TVar FZ)
    (liftEnvOccursUniq env prf)
    a

subOccursInAnyInv env prf [] = id
subOccursInAnyInv env prf (a :: as) =
  bimap
    (subOccursInInv env prf a)
    (subOccursInAnyInv env prf as)

subOccursInAny1Inv env prf (a ::: as) =
  bimap
    (subOccursInInv env prf a)
    (subOccursInAnyInv env prf as)


-- Not Positive --

subNotPositiveIn :
  (env : Env k n (Ty n)) -> (i : Fin k) -> (a : Ty k) ->
  j `OccursIn` fromVar (lookup env i) ->
  i `NotPositiveIn` a ->
  j `NotPositiveIn` sub env a
subNotPositiveInAny :
  (env : Env k n (Ty n)) -> (i : Fin k) -> (as : List (Ty k)) ->
  j `OccursIn` fromVar (lookup env i) ->
  i `NotPositiveInAny` as ->
  j `NotPositiveInAny` subAll env as
subNotPositiveInAny1 :
  (env : Env k n (Ty n)) -> (i : Fin k) -> (as : List1 (Ty k)) ->
  j `OccursIn` fromVar (lookup env i) ->
  i `NotPositiveInAny1` as ->
  j `NotPositiveInAny1` subAll1 env as

subNotPositiveIn env i (TVar x) occurs = absurd
subNotPositiveIn env i TNat occurs = id
subNotPositiveIn env i (TArrow a b) occurs =
  bimap
    (subOccursIn env i a occurs)
    (subNotPositiveIn env i b occurs)
subNotPositiveIn env i (TUnion as) occurs = subNotPositiveInAny1 env i as occurs
subNotPositiveIn env i (TProd as) occurs = subNotPositiveInAny env i as occurs
subNotPositiveIn env i (TSum as) occurs = subNotPositiveInAny env i as occurs
subNotPositiveIn env i (TFix a) occurs =
  subOccursIn (lift (Drop Id) env :< TVar FZ) (FS i) a {j = FS j} $
    rewrite lookupFS (lift (Drop Id) env) (TVar FZ) i in
    rewrite lookupLift (Drop Id) env i in
    rewrite eitherBimapFusion TVar id (index (Drop Id)) (thin (Drop Id)) (lookup env i) in
    rewrite sym $ pushEither (thin (Drop Id)) TVar id (lookup env i) in
    rewrite sym $ indexId j in
    rewrite sym $ indexDrop Id j in
    thinOccursIn (Drop Id) j (fromVar $ lookup env i) $
    occurs

subNotPositiveInAny env i [] occurs = id
subNotPositiveInAny env i (a :: as) occurs =
  bimap
    (subNotPositiveIn env i a occurs)
    (subNotPositiveInAny env i as occurs)

subNotPositiveInAny1 env i (a ::: as) occurs =
  bimap
    (subNotPositiveIn env i a occurs)
    (subNotPositiveInAny env i as occurs)

-- Inverse

0 EnvPositiveIn : Env k n (Ty n) -> (i : Fin n) -> Type
EnvPositiveIn env i = (x : Fin k) -> Not (i `NotPositiveIn` fromVar (lookup env x))

liftPositiveInFZ :
  (env : Env k n (Ty n)) ->
  EnvPositiveIn (lift (Drop Id) env :< TVar FZ) FZ
liftPositiveInFZ env FZ =
  rewrite lookupFZ (lift (Drop Id) env) (TVar FZ) in
  id
liftPositiveInFZ env (FS x) =
  rewrite lookupFS (lift (Drop Id) env) (TVar FZ) x in
  rewrite lookupLift (Drop Id) env x in
  rewrite eitherBimapFusion TVar id (index (Drop Id)) (rename (Drop Id)) (lookup env x) in
  \npos =>
  let
    (j ** (eq, occurs)) =
      thinOccursInInv' (Drop Id) FZ (fromVar $ lookup env x) $
      rewrite pushEither (thin (Drop Id)) TVar id (lookup env x) in
      notPositiveToOccurs _ npos
  in
  absurd $ trans (sym (indexDrop Id j)) eq

subNotPositiveInInv :
  (0 env : Env k n (Ty n)) ->
  (0 prf1 : EnvPositiveIn env i) ->
  (0 prf2 : EnvOccursUniq env i j) ->
  (a : Ty k) ->
  i `NotPositiveIn` sub env a -> j `NotPositiveIn` a
subNotPositiveInAnyInv :
  (0 env : Env k n (Ty n)) ->
  (0 prf1 : EnvPositiveIn env i) ->
  (0 prf2 : EnvOccursUniq env i j) ->
  (as : List (Ty k)) ->
  i `NotPositiveInAny` subAll env as -> j `NotPositiveInAny` as
subNotPositiveInAny1Inv :
  (0 env : Env k n (Ty n)) ->
  (0 prf1 : EnvPositiveIn env i) ->
  (0 prf2 : EnvOccursUniq env i j) ->
  (as : List1 (Ty k)) ->
  i `NotPositiveInAny1` subAll1 env as -> j `NotPositiveInAny1` as

subNotPositiveInInv env prf1 prf2 (TVar x) = \npos => void $ prf1 x npos
subNotPositiveInInv env prf1 prf2 TNat = id
subNotPositiveInInv env prf1 prf2 (TArrow a b) =
  bimap
    (subOccursInInv env prf2 a)
    (subNotPositiveInInv env prf1 prf2 b)
subNotPositiveInInv env prf1 prf2 (TUnion as) = subNotPositiveInAny1Inv env prf1 prf2 as
subNotPositiveInInv env prf1 prf2 (TProd as) = subNotPositiveInAnyInv env prf1 prf2 as
subNotPositiveInInv env prf1 prf2 (TSum as) = subNotPositiveInAnyInv env prf1 prf2 as
subNotPositiveInInv env prf1 prf2 (TFix a) =
  subOccursInInv
    (lift (Drop Id) env :< TVar FZ)
    (liftEnvOccursUniq env prf2)
    a

subNotPositiveInAnyInv env prf1 prf2 [] = id
subNotPositiveInAnyInv env prf1 prf2 (a :: as) =
  bimap
    (subNotPositiveInInv env prf1 prf2 a)
    (subNotPositiveInAnyInv env prf1 prf2 as)

subNotPositiveInAny1Inv env prf1 prf2 (a ::: as) =
  bimap
    (subNotPositiveInInv env prf1 prf2 a)
    (subNotPositiveInAnyInv env prf1 prf2 as)

-- Ill Formed --

subIllFormed :
  (env : Env k n (Ty n)) -> (a : Ty k) ->
  IllFormed a -> IllFormed (sub env a)
subAnyIllFormed :
  (env : Env k n (Ty n)) -> (as : List (Ty k)) ->
  AnyIllFormed as -> AnyIllFormed (subAll env as)
subAny1IllFormed :
  (env : Env k n (Ty n)) -> (as : List1 (Ty k)) ->
  Any1IllFormed as -> Any1IllFormed (subAll1 env as)

subIllFormed env (TVar i) = absurd
subIllFormed env TNat = id
subIllFormed env (TArrow a b) = bimap (subIllFormed env a) (subIllFormed env b)
subIllFormed env (TUnion as) = subAny1IllFormed env as
subIllFormed env (TProd as) = subAnyIllFormed env as
subIllFormed env (TSum as) = subAnyIllFormed env as
subIllFormed env (TFix a) =
  bimap
    (subNotPositiveIn (lift (Drop Id) env :< TVar FZ) FZ a $
      rewrite lookupFZ (lift (Drop Id) env) (TVar FZ) in
      Refl)
    (subIllFormed (lift (Drop Id) env :< TVar FZ) a)

subAnyIllFormed env [] = id
subAnyIllFormed env (a :: as) = bimap (subIllFormed env a) (subAnyIllFormed env as)

subAny1IllFormed env (a ::: as) = bimap (subIllFormed env a) (subAnyIllFormed env as)

-- Inverse

export
0 EnvWellFormed : Env k n (Ty n) -> Type
EnvWellFormed env = (x : Fin k) -> Not (IllFormed $ fromVar $ lookup env x)

liftEnvWellFormed :
  (env : Env k n (Ty n)) ->
  EnvWellFormed env ->
  EnvWellFormed (lift (Drop Id) env :< TVar FZ)
liftEnvWellFormed env prf FZ =
  rewrite lookupFZ (lift (Drop Id) env) (TVar FZ) in
  id
liftEnvWellFormed env prf (FS x) =
  rewrite lookupFS (lift (Drop Id) env) (TVar FZ) x in
  rewrite lookupLift (Drop Id) env x in
  rewrite eitherBimapFusion TVar id (index (Drop Id)) (rename (Drop Id)) (lookup env x) in
  \ill =>
  prf x $
  thinIllFormedInv (Drop Id) (either TVar id $ lookup env x) $
  rewrite pushEither (thin (Drop Id)) TVar id (lookup env x) in
  ill

subIllFormedInv :
  (0 env : Env k n (Ty n)) ->
  (0 prf : EnvWellFormed env) ->
  (a : Ty k) ->
  IllFormed (sub env a) -> IllFormed a
subAnyIllFormedInv :
  (0 env : Env k n (Ty n)) ->
  (0 prf : EnvWellFormed env) ->
  (as : List (Ty k)) ->
  AnyIllFormed (subAll env as) -> AnyIllFormed as
subAny1IllFormedInv :
  (0 env : Env k n (Ty n)) ->
  (0 prf : EnvWellFormed env) ->
  (as : List1 (Ty k)) ->
  Any1IllFormed (subAll1 env as) -> Any1IllFormed as

subIllFormedInv env prf (TVar i) = \ill => void $ prf i ill
subIllFormedInv env prf TNat = id
subIllFormedInv env prf (TArrow a b) =
  bimap
    (subIllFormedInv env prf a)
    (subIllFormedInv env prf b)
subIllFormedInv env prf (TUnion as) = subAny1IllFormedInv env prf as
subIllFormedInv env prf (TProd as) = subAnyIllFormedInv env prf as
subIllFormedInv env prf (TSum as) = subAnyIllFormedInv env prf as
subIllFormedInv env prf (TFix a) =
  bimap
    (subNotPositiveInInv
      (lift (Drop Id) env :< TVar FZ)
      (liftPositiveInFZ env)
      (liftOccursUniqFZ env)
      a)
    (subIllFormedInv
      (lift (Drop Id) env :< TVar FZ)
      (liftEnvWellFormed env prf)
      a)

subAnyIllFormedInv env prf [] = id
subAnyIllFormedInv env prf (a :: as) =
  bimap
    (subIllFormedInv env prf a)
    (subAnyIllFormedInv env prf as)

subAny1IllFormedInv env prf (a ::: as) =
  bimap
    (subIllFormedInv env prf a)
    (subAnyIllFormedInv env prf as)

-- Equivalent

export
subIllFormedEquiv :
  (env : Env k n (Ty n)) ->
  (0 prf : EnvWellFormed env) ->
  (a : Ty k) ->
  IllFormed a <=> IllFormed (sub env a)
subIllFormedEquiv env prf a =
  MkEquivalence
    { leftToRight = subIllFormed env a
    , rightToLeft = subIllFormedInv env prf a
    }
