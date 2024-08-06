module Inky.Binding

import Control.Relation
import Control.Order
import Data.DPair
import Data.List
import Data.Nat
import Data.So
import Decidable.Equality

-- Types -----------------------------------------------------------------------

data WorldRepr : Nat -> List Bool -> Type where
  Done : 0 `WorldRepr` []
  True : w `WorldRepr` bs -> 1 + 2 * w `WorldRepr` True :: bs
  False : w `WorldRepr` bs -> 2 * w `WorldRepr` False :: bs

export
World : Type
World = List Bool

export
Binder : Type
Binder = Nat

Member : Binder -> World -> Type
n `Member` [] = Void
Z `Member` b :: bs = So b
S n `Member` b :: bs = n `Member` bs

export
(:<) : World -> Binder -> World
[] :< Z = True :: []
[] :< (S n) = False :: [] :< n
(_ :: bs) :< Z = True :: bs
(b :: bs) :< (S n) = b :: bs :< n

snocSem : (bs : World) -> (k, n : Binder) -> n `Member` bs :< k <=> Either (n = k) (n `Member` bs)
snocSem [] Z Z = MkEquivalence (const $ Left Refl) (const Oh)
snocSem [] Z (S n) = MkEquivalence absurd absurd
snocSem [] (S k) 0 = MkEquivalence absurd absurd
snocSem [] (S k) (S n) =
  let equiv = snocSem [] k n in
  MkEquivalence
    (mapFst (\prf => cong S prf) . equiv.leftToRight)
    (equiv.rightToLeft . mapFst injective)
snocSem (b :: bs) Z Z =
  MkEquivalence (const $ Left Refl) (const Oh)
snocSem (b :: bs) Z (S n) = MkEquivalence Right (\case (Right x) => x)
snocSem (b :: bs) (S k) Z = MkEquivalence Right (\case (Right x) => x)
snocSem (b :: bs) (S k) (S n) =
  let equiv = snocSem bs k n in
  MkEquivalence
    (mapFst (\prf => cong S prf) . equiv.leftToRight)
    (equiv.rightToLeft . mapFst injective)

export
Name : World -> Type
Name w = Subset Binder (`Member` w)

-- Countable binders -----------------------------------------------------------

export
BZ : Binder
BZ = Z

export
BS : Binder -> Binder
BS = S

-- Binders to names ------------------------------------------------------------

export
nameOf : forall w. (b : Binder) -> Name (w :< b)
nameOf b = Element b ((snocSem w b b).rightToLeft (Left Refl))

export
binder : Name w -> Binder
binder = fst

export
binderNameOf : binder {w = w :< b} (nameOf {w} b) = b
binderNameOf = Refl

-- Empty world -----------------------------------------------------------------

export
Empty : World
Empty = []

export
Uninhabited (Name Empty) where
  uninhabited n = void n.snd

-- Names are comparable and stripable ------------------------------------------

export
Eq (Name w) where
  n == k = n == k

soEq : (n : Nat) -> So (n == n)
soEq Z = Oh
soEq (S k) = soEq k

export
strip : {b : Binder} -> Name (w :< b) -> Maybe (Name w)
strip (Element n member) =
  case decSo (b == n) of
    Yes _ => Nothing
    No neq =>
      Just
        (Element n
          (either
            (\eq => void $ neq $ rewrite eq in soEq b)
            id $
            (snocSem w b n).leftToRight member))

public export
stripWith : {b : Binder} -> Lazy a -> Lazy (Name w -> a) -> Name (w :< b) -> a
stripWith x f = maybe x f . strip

-- Freshness -------------------------------------------------------------------

export
FreshIn : Binder -> World -> Type
FreshIn k bs = So (k `gte` length bs)

export
freshInEmpty : b `FreshIn` Empty
freshInEmpty = Oh

snocLength : (w : World) -> (k : Binder) -> So (k `gte` length w) -> So (S k `gte` length (w :< k))
snocLength [] 0 prf = Oh
snocLength [] (S k) prf = snocLength [] k prf
snocLength (b :: bs) (S k) prf = snocLength bs k prf

%inline
soRecomputable : (0 s : So b) -> So b
soRecomputable Oh = Oh

export
sucFresh : b `FreshIn` w -> BS b `FreshIn` w :< b
sucFresh prf = soRecomputable (snocLength w b prf)

-- World inclusion -------------------------------------------------------------

export
(<=) : World -> World -> Type
w <= v = {n : Binder} -> n `Member` w -> n `Member` v

export
coerce : (0 prf : w <= v) -> Name w -> Name v
coerce lte n = Element n.fst (lte n.snd)

export
Reflexive World (<=) where
  reflexive = id

export
Transitive World (<=) where
  transitive f g = g . f

export
Preorder World (<=) where

export
emptyMin : Empty <= w
emptyMin n impossible

export
snocMono : {w,  v : World} -> (b : Binder) -> w <= v -> w :< b <= v :< b
snocMono b lte {n} = (snocSem v b n).rightToLeft . mapSnd lte . (snocSem w b n).leftToRight

export
freshLte : {b : Binder} -> {w : World} -> (0 fresh : b `FreshIn` w) -> w <= w :< b
freshLte _ {n} = (snocSem w b n).rightToLeft . Right

-- DeBruijn Worlds -------------------------------------------------------------

export
WS : World -> World
WS = (False ::)

public export
shift : World -> World
shift w = WS w :< BZ

export
sucMono : w <= v -> WS w <= WS v
sucMono lte {n = (S n)} member = lte member

public export
shiftMono : {w, v : World} -> w <= v -> shift w <= shift v
shiftMono lte = snocMono BZ (sucMono lte)

export
sucLteShift : WS w <= shift w
sucLteShift {n = (S n)} member = member

export
sucInjective : WS w <= WS v -> w <= v
sucInjective lte {n} member = lte {n = (S n)} member

export
shiftInjective : shift w <= shift v -> w <= v
shiftInjective lte {n} member = lte {n = (S n)} member

export
sucLteShiftInjective : WS w <= shift v -> w <= v
sucLteShiftInjective lte {n} member = lte {n = (S n)} member

export
sucEmpty : WS Empty <= Empty
sucEmpty {n = (S n)} member impossible

-- Suc and snoc ----------------------------------------------------------------

export
sucDistributesOverSnocLte : WS (w :< b) <= WS w :< BS b
sucDistributesOverSnocLte {n = (S n)} member = member

export
sucDistributesOverSnocGte : WS w :< BS b <= WS (w :< b)
sucDistributesOverSnocGte {n = (S n)} member = member
