module Inky.Binding

import Control.Relation
import Control.Order
import Data.Bool
import Data.DPair
import Data.List
import Data.Nat
import Data.Nat.Order.Properties
import Data.So
import Decidable.Equality

-- Types -----------------------------------------------------------------------

export
record World where
  constructor MkWorld
  world : List Bool

export
record Binder where
  constructor MkBinder
  binder : Nat

Member : Nat -> List Bool -> Type
k `Member` [] = Void
Z `Member` b :: bs = So b
S n `Member` b :: bs = n `Member` bs

snoc : List Bool -> Nat -> List Bool
snoc [] Z = True :: []
snoc [] (S n) = False :: snoc [] n
snoc (_ :: bs) Z = True :: bs
snoc (b :: bs) (S n) = b :: snoc bs n

export
(:<) : World -> Binder -> World
w :< x = MkWorld (snoc w.world x.binder)

snocSem :
  (bs : List Bool) -> (k : Nat) -> (n : Nat) ->
  n `Member` snoc bs k <=> Either (n = k) (n `Member` bs)
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
Name w = Subset Nat (`Member` w.world)

-- Countable binders -----------------------------------------------------------

export
BZ : Binder
BZ = MkBinder Z

export
BS : Binder -> Binder
BS = MkBinder . S . binder

-- Binders to names ------------------------------------------------------------

export
nameOf : forall w. (b : Binder) -> Name (w :< b)
nameOf b = Element b.binder ((snocSem w.world b.binder b.binder).rightToLeft (Left Refl))

export
binder : Name w -> Binder
binder = MkBinder . fst

export
binderNameOf : (b : Binder) -> binder {w = w :< b} (nameOf {w} b) = b
binderNameOf (MkBinder k) = Refl

-- [<] world -----------------------------------------------------------------

export
Lin : World
Lin = MkWorld []

export
Uninhabited (Name [<]) where
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
  case decSo (b.binder == n) of
    Yes _ => Nothing
    No neq =>
      Just
        (Element n
          (either
            (\eq => void $ neq $ rewrite eq in soEq b.binder)
            id $
            (snocSem w.world b.binder n).leftToRight member))

public export
maybe' :
  (0 p : Maybe a -> Type) ->
  Lazy (p Nothing) ->
  Lazy ((x : a) -> p (Just x)) ->
  (x : Maybe a) -> p x
maybe' p x f Nothing = x
maybe' p x f (Just y) = f y

public export
stripWith' :
  (0 a : Maybe (Name w) -> Type) -> {b : Binder} ->
  Lazy (a Nothing) -> Lazy ((n : Name w) -> a (Just n)) ->
  (n : Name (w :< b)) -> a (strip {w, b} n)
stripWith' a x f n = maybe' a x f (strip n)

public export
stripWith :
  {b : Binder} -> Lazy a -> Lazy (Name w -> a) -> Name (w :< b) -> a
stripWith x f = maybe x f . strip

-- Freshness -------------------------------------------------------------------

export
record FreshIn (b : Binder) (w : World) where
  constructor MkFresh
  fresh : So (b.binder `gte` length w.world)

export
freshInEmpty : b `FreshIn` [<]
freshInEmpty = MkFresh Oh

snocLength :
  (bs : List Bool) -> (k : Nat) ->
  So (k `gte` length bs) -> So (S k `gte` length (snoc bs k))
snocLength [] 0 prf = Oh
snocLength [] (S k) prf = snocLength [] k prf
snocLength (b :: bs) (S k) prf = snocLength bs k prf

%inline
soRecomputable : (0 s : So b) -> So b
soRecomputable Oh = Oh

export
sucFresh : b `FreshIn` w -> BS b `FreshIn` w :< b
sucFresh prf = MkFresh (soRecomputable (snocLength w.world b.binder prf.fresh))

-- World inclusion -------------------------------------------------------------

export
record (<=) (w, v : World) where
  constructor MkLte
  lte : (n : Nat) -> n `Member` w.world -> n `Member` v.world

export
coerce : (0 prf : w <= v) -> Name w -> Name v
coerce lte n = Element n.fst (lte.lte _ n.snd)

export
Reflexive World (<=) where
  reflexive = MkLte (\_, prf => prf)

export
Transitive World (<=) where
  transitive f g = MkLte (\n => g.lte n . f.lte n)

export
Preorder World (<=) where

export
emptyMin : [<] <= w
emptyMin = MkLte (\_ => absurd)

export
snocMono : {w,  v : World} -> (b : Binder) -> w <= v -> w :< b <= v :< b
snocMono b lte = MkLte
  (\n =>
    (snocSem v.world b.binder _).rightToLeft
  . mapSnd (lte.lte n)
  . (snocSem w.world b.binder _).leftToRight
  )

export
freshLte : {b : Binder} -> {w : World} -> (0 fresh : b `FreshIn` w) -> w <= w :< b
freshLte _ = MkLte (\n => (snocSem w.world b.binder n).rightToLeft . Right)

-- DeBruijn Worlds -------------------------------------------------------------

export
WS : World -> World
WS = MkWorld . (False ::) . world

public export
shift : World -> World
shift w = WS w :< BZ

invertSuc : (n : Nat) -> n `Member` (False :: bs) -> (k ** (S k = n, k `Member` bs))
invertSuc (S n) prf = (n ** (Refl, prf))

export
sucMono : w <= v -> WS w <= WS v
sucMono lte = MkLte (\case
  Z => absurd
  (S n) => lte.lte n)

public export
shiftMono : {w, v : World} -> w <= v -> shift w <= shift v
shiftMono lte = snocMono BZ (sucMono lte)

export
sucLteShift : WS w <= shift w
sucLteShift = MkLte (\case
  Z => absurd
  S n => id)

export
sucInjective : WS w <= WS v -> w <= v
sucInjective lte = MkLte (\n => lte.lte (S n))

export
shiftInjective : shift w <= shift v -> w <= v
shiftInjective lte = MkLte (\n => lte.lte (S n))

export
sucLteShiftInjective : WS w <= shift v -> w <= v
sucLteShiftInjective lte = MkLte (\n => lte.lte (S n))

export
sucEmpty : WS [<] <= [<]
sucEmpty =
  MkLte (\case
    Z => absurd
    (S n) => absurd)

-- Suc and snoc ----------------------------------------------------------------

export
sucDistributesOverSnocLte : WS (w :< b) <= WS w :< BS b
sucDistributesOverSnocLte =
  MkLte (\case
    Z => absurd
    (S n) => id)

export
sucDistributesOverSnocGte : WS w :< BS b <= WS (w :< b)
sucDistributesOverSnocGte =
  MkLte (\case
    Z => absurd
    (S n) => id)

-- Strip and coerce ------------------------------------------------------------

memberUniq : (n : Nat) -> (bs : List Bool) -> (p, q : Member n bs) -> p = q
memberUniq n [] p q = absurd p
memberUniq Z (True :: bs) Oh Oh = Refl
memberUniq Z (False :: bs) p q = absurd p
memberUniq (S n) (_ :: bs) p q = memberUniq n bs p q

export
stripCoerceSnoc :
  (b : Binder) -> (0 lte : w <= v) -> (n : Name (w :< b)) ->
  strip {w = v, b} (coerce (snocMono b lte) n) = map (coerce lte) (strip {w, b} n)
stripCoerceSnoc b lte (Element n member) with (decSo $ equalNat b.binder n)
  _ | Yes _ = Refl
  _ | No _ = cong (\prf => Just $ Element n prf) (memberUniq n v.world {})

-- De Bruijn Utilities ---------------------------------------------------------

public export
(+) : World -> Nat -> World
w + Z = w
w + S n = WS (w + n)

public export
lift : World -> Nat -> World
w `lift` Z = w
w `lift` S n = shift (w `lift` n)

public export
plusMono : (k : Nat) -> w <= v -> w + k <= v + k
plusMono Z lte = lte
plusMono (S k) lte = sucMono (plusMono k lte)

public export
plusInjective : (k : Nat) -> w + k <= v + k -> w <= v
plusInjective Z lte = lte
plusInjective (S k) lte = plusInjective k (sucInjective lte)

public export
liftMono : {w, v : World} -> (k : Nat) -> w <= v -> (w `lift` k) <= (v `lift` k)
liftMono Z lte = lte
liftMono (S k) lte = shiftMono (liftMono k lte)

public export
liftInjective : (k : Nat) -> (w `lift` k) <= (v `lift` k) -> w <= v
liftInjective Z lte = lte
liftInjective (S k) lte = liftInjective k (shiftInjective lte)

plusWorld : (0 w : World) -> (k : Nat) -> (w + k).world = replicate k False ++ w.world
plusWorld w Z = Refl
plusWorld w (S k) = cong (False ::) (plusWorld w k)

liftWorld : (0 w : World) -> (k : Nat) -> (w `lift` k).world = replicate k True ++ w.world
liftWorld w Z = Refl
liftWorld w (S k) = cong (True ::) (liftWorld w k)

plusMember : (k : Nat) -> Member n bs -> Member (k + n) (replicate k False ++ bs)
plusMember Z prf = prf
plusMember (S k) prf = plusMember k prf

export
plus : (k : Nat) -> Name w -> Name (w + k)
plus k (Element n prf) = rewrite plusWorld w k in Element (k + n) (plusMember k prf)

minusMember : {n : Nat} -> (k : Nat) -> Member n (replicate k False ++ bs) -> Member (n `minus` k) bs
minusMember Z prf = rewrite minusZeroRight n in prf
minusMember {n = S n} (S k) prf = minusMember k prf

export
minus : (k : Nat) -> Name (w + k) -> Name w
minus k (Element n prf) =
  Element (n `minus` k)
    (minusMember {bs = w.world} k (rewrite sym $ plusWorld w k in prf))

cmpLt : {n : Nat} -> n `LT` k -> Member n (replicate k True ++ bs) -> Member n (replicate k True ++ [])
cmpLt {n = Z} (LTESucc prf) member = member
cmpLt {n = S n} (LTESucc prf) member = cmpLt prf member

cmpGte : n `GTE` k -> Member n (replicate k True ++ bs) -> Member n (replicate k False ++ bs)
cmpGte LTEZero member = member
cmpGte (LTESucc prf) member = cmpGte prf member

export
cmp : (k : Nat) -> Name (w `lift` k) -> Either (Name ([<] `lift` k)) (Name (w + k))
cmp k (Element n member) =
  case decSo $ n `lt` k of
    Yes prf =>
      Left $
      Element n $
      rewrite liftWorld [<] k in
      cmpLt {bs = w.world} (ltIsLT n k $ soToEq prf) $
      rewrite sym $ liftWorld w k in
      member
    No prf =>
      Right $
      Element n $
      rewrite plusWorld w k in
      cmpGte {bs = w.world} (notltIsGTE n k $ notTrueIsFalse $ prf . eqToSo) $
      rewrite sym $ liftWorld w k in
      member
