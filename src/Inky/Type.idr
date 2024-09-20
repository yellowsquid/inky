module Inky.Type

import Data.Bool.Decidable
import Data.DPair
import Data.Maybe.Decidable
import Data.These
import Data.These.Decidable
import Inky.Context
import Inky.Thinning

-- Definition ------------------------------------------------------------------

public export
data Ty : Context () -> () -> Type where
  TVar : Var ctx v -> Ty ctx v
  TNat : Ty ctx ()
  TArrow : Ty ctx () -> Ty ctx () -> Ty ctx ()
  TProd : Row (Ty ctx ()) -> Ty ctx ()
  TSum : Row (Ty ctx ()) -> Ty ctx ()
  TFix : (x : String) -> Ty (ctx :< (x :- ())) () -> Ty ctx ()

%name Ty a, b, c

--------------------------------------------------------------------------------
-- Thinning --------------------------------------------------------------------
--------------------------------------------------------------------------------

thin : ctx1 `Thins` ctx2 -> forall v. Ty ctx1 v -> Ty ctx2 v
thinAll : ctx1 `Thins` ctx2 -> forall v. Row (Ty ctx1 v) -> Row (Ty ctx2 v)
thinAllFresh :
  (f : ctx1 `Thins` ctx2) -> (x : String) ->
  forall v. (row : Row (Ty ctx1 v)) ->
  So (x `freshIn` row) -> So (x `freshIn` thinAll f row)

thin f (TVar i) = TVar (index f i)
thin f TNat = TNat
thin f (TArrow a b) = TArrow (thin f a) (thin f b)
thin f (TProd as) = TProd (thinAll f as)
thin f (TSum as) = TSum (thinAll f as)
thin f (TFix x a) = TFix x (thin (Keep f) a)

thinAll f [<] = [<]
thinAll f ((:<) as (x :- a) {fresh}) =
  (:<) (thinAll f as) (x :- thin f a) {fresh = thinAllFresh f x as fresh}

thinAllFresh f x [<] = id
thinAllFresh f x (as :< (y :- a)) = andSo . mapSnd (thinAllFresh f x as) . soAnd

-- Renaming Coalgebra

thinCong : f ~~~ g -> forall v. (a : Ty ctx1 v) -> thin f a = thin g a
thinCongAll : f ~~~ g -> forall v. (as : Row (Ty ctx1 v)) -> thinAll f as = thinAll g as

thinCong prf (TVar i) = cong TVar (prf.index i)
thinCong prf TNat = Refl
thinCong prf (TArrow a b) = cong2 TArrow (thinCong prf a) (thinCong prf b)
thinCong prf (TProd as) = cong TProd (thinCongAll prf as)
thinCong prf (TSum as) = cong TSum (thinCongAll prf as)
thinCong prf (TFix x a) = cong (TFix x) (thinCong (KeepKeep prf) a)

thinCongAll prf [<] = Refl
thinCongAll prf (as :< (x :- a)) =
  snocCong2 (thinCongAll prf as) (cong (x :-) $ thinCong prf a)

thinId : (a : Ty ctx v) -> thin Id a = a
thinIdAll : (as : Row (Ty ctx v)) -> thinAll Id as = as

thinId (TVar (%% x)) = Refl
thinId TNat = Refl
thinId (TArrow a b) = cong2 TArrow (thinId a) (thinId b)
thinId (TProd as) = cong TProd (thinIdAll as)
thinId (TSum as) = cong TSum (thinIdAll as)
thinId (TFix x a) = cong (TFix x) (trans (thinCong (KeepId IdId) a) (thinId a))

thinIdAll [<] = Refl
thinIdAll (as :< (x :- a)) =
  snocCong2 (thinIdAll as) (cong (x :-) $ thinId a)

export
Rename () Ty where
  var = TVar
  rename = thin
  renameCong = thinCong
  renameId = thinId

-- Equality --------------------------------------------------------------------

Preeq :
  {ctx2 : Context ()} -> {v : ()} ->
  Ty ctx1 v -> Ty ctx2 v -> ctx1 `Thins` ctx2 -> Type
PreeqAll :
  {ctx2 : Context ()} -> {v : ()} ->
  Row (Ty ctx1 v) -> Row (Ty ctx2 v) -> ctx1 `Thins` ctx2 -> Type

Preeq (TVar i) (TVar j) f = index f i = j
Preeq (TNat) (TNat) f = ()
Preeq (TArrow a b) (TArrow c d) f = (Preeq a c f, Preeq b d f)
Preeq (TProd as) (TProd bs) f = PreeqAll as bs f
Preeq (TSum as) (TSum bs) f = PreeqAll as bs f
Preeq (TFix x a) (TFix y b) f = Preeq a b (Keep f)
Preeq _ _ f = Void

PreeqAll [<] bs f = (bs = [<])
PreeqAll (as :< (x :- a)) bs f =
  ( b ** cs **
  ( Remove x bs b cs
  , Preeq a b f
  , PreeqAll as cs f
  ))

preeqAllReorder :
  (as : Row (Ty ctx1 v)) -> bs <~> cs -> (f : ctx1 `Thins` ctx2) ->
  PreeqAll as bs f -> PreeqAll as cs f
preeqAllReorder [<] [] f Refl = Refl
preeqAllReorder [<] (step :: prf) f Refl impossible
preeqAllReorder (as :< (x :- a)) prf f (b ** bs ** (prf', eq1, eq2)) =
  (b ** bs ** (bimap id (trans (sym prf)) prf', eq1, eq2))

preeq : Ty ctx1 v -> Ty ctx2 v -> ctx1 `Thins` ctx2 -> Bool
preeqAll : Row (Ty ctx1 v) -> Row (Ty ctx2 v) -> ctx1 `Thins` ctx2 -> Bool

preeq (TVar i) (TVar j) f = index f i == j
preeq TNat TNat f = True
preeq (TArrow a b) (TArrow c d) f = preeq a c f && preeq b d f
preeq (TProd as) (TProd bs) f = preeqAll as bs f
preeq (TSum as) (TSum bs) f = preeqAll as bs f
preeq (TFix x a) (TFix y b) f = preeq a b (Keep f)
preeq _ _ f = False

preeqAll [<] bs f = null bs
preeqAll (as :< (x :- a)) bs f =
  case remove' x bs of
    Just (b, bs) => preeq a b f && preeqAll as bs f
    Nothing => False

export
reflectAnd : a `Reflects` b1 -> b `Reflects` b2 -> (a, b) `Reflects` (b1 && b2)
reflectAnd (RTrue x) (RTrue y) = RTrue (x, y)
reflectAnd (RTrue x) (RFalse f) = RFalse (f . snd)
reflectAnd (RFalse f) _ = RFalse (f . fst)

0 reflectPreeq :
  (a : Ty ctx1 v) -> (b : Ty ctx2 v) -> (f : ctx1 `Thins` ctx2) ->
  Preeq a b f `Reflects` preeq a b f
0 reflectPreeqAll :
  (as : Row (Ty ctx1 v)) -> (bs : Row (Ty ctx2 v)) -> (f : ctx1 `Thins` ctx2) ->
  PreeqAll as bs f `Reflects` preeqAll as bs f

reflectPreeq (TVar i) (TVar j) f = reflectEq (index f i) j
reflectPreeq (TVar i) TNat f = RFalse id
reflectPreeq (TVar i) (TArrow a b) f = RFalse id
reflectPreeq (TVar i) (TProd as) f = RFalse id
reflectPreeq (TVar i) (TSum as) f = RFalse id
reflectPreeq (TVar i) (TFix x a) f = RFalse id
reflectPreeq TNat (TVar i) f = RFalse id
reflectPreeq TNat TNat f = RTrue ()
reflectPreeq TNat (TArrow a b) f = RFalse id
reflectPreeq TNat (TProd as) f = RFalse id
reflectPreeq TNat (TSum as) f = RFalse id
reflectPreeq TNat (TFix x a) f = RFalse id
reflectPreeq (TArrow a c) (TVar i) f = RFalse id
reflectPreeq (TArrow a c) TNat f = RFalse id
reflectPreeq (TArrow a c) (TArrow b d) f = reflectAnd (reflectPreeq a b f) (reflectPreeq c d f)
reflectPreeq (TArrow a c) (TProd as) f = RFalse id
reflectPreeq (TArrow a c) (TSum as) f = RFalse id
reflectPreeq (TArrow a c) (TFix x b) f = RFalse id
reflectPreeq (TProd as) (TVar i) f = RFalse id
reflectPreeq (TProd as) TNat f = RFalse id
reflectPreeq (TProd as) (TArrow a b) f = RFalse id
reflectPreeq (TProd as) (TProd bs) f = reflectPreeqAll as bs f
reflectPreeq (TProd as) (TSum bs) f = RFalse id
reflectPreeq (TProd as) (TFix x a) f = RFalse id
reflectPreeq (TSum as) (TVar i) f = RFalse id
reflectPreeq (TSum as) TNat f = RFalse id
reflectPreeq (TSum as) (TArrow a b) f = RFalse id
reflectPreeq (TSum as) (TProd bs) f = RFalse id
reflectPreeq (TSum as) (TSum bs) f = reflectPreeqAll as bs f
reflectPreeq (TSum as) (TFix x a) f = RFalse id
reflectPreeq (TFix x a) (TVar i) f = RFalse id
reflectPreeq (TFix x a) TNat f = RFalse id
reflectPreeq (TFix x a) (TArrow b c) f = RFalse id
reflectPreeq (TFix x a) (TProd as) f = RFalse id
reflectPreeq (TFix x a) (TSum as) f = RFalse id
reflectPreeq (TFix x a) (TFix y b) f = reflectPreeq a b (Keep f)

reflectPreeqAll [<] [<] f = RTrue Refl
reflectPreeqAll [<] (_ :< _) f = RFalse (\case Refl impossible)
reflectPreeqAll (as :< (x :- a)) bs f with (reflectRemove x bs) | (remove' x bs)
  _ | RJust (Evidence fresh prf) | Just (b, cs) with (reflectAnd (reflectPreeq a b f) (reflectPreeqAll as cs f)) | (preeq a b f && preeqAll as cs f)
    _ | RTrue prf' | _ = RTrue (b ** cs ** (Evidence fresh prf, prf'))
    _ | RFalse nprf | _ =
      RFalse (\(b' ** cs' ** (prf1, prf2)) =>
        let (eq, reorder) = removeUnique x bs (Evidence fresh prf) prf1 in
        nprf $
        bimap
          (\x => rewrite eq in x)
          (preeqAllReorder as (sym reorder) f)
          prf2)
  _ | RNothing nprf | _ = RFalse (\(b ** cs ** (prf, _)) => nprf (b, cs) prf)

public export
Eq (Ty ctx v) where
  a == b = preeq a b Id

export
Eq : {ctx : Context ()} -> {v : ()} -> Ty ctx v -> Ty ctx v -> Type
Eq a b = Preeq a b Id

export
0 reflectEq : (a, b : Ty ctx v) -> (a `Eq` b) `Reflects` (a == b)
reflectEq a b = reflectPreeq a b Id

-- Occurs ----------------------------------------------------------------------

OccursIn : Var ctx v -> Ty ctx w -> Type
OccursInAny : Var ctx v -> Row (Ty ctx w) -> Type

i `OccursIn` TVar j = i = j
i `OccursIn` TNat = Void
i `OccursIn` TArrow a b = These (i `OccursIn` a) (i `OccursIn` b)
i `OccursIn` TProd as = i `OccursInAny` as
i `OccursIn` TSum as = i `OccursInAny` as
i `OccursIn` TFix x a = ThereVar i `OccursIn` a

i `OccursInAny` [<] = Void
i `OccursInAny` (as :< (x :- a)) = These (i `OccursIn` a) (i `OccursInAny` as)

-- Decidable

occursIn : (i : Var ctx v) -> (a : Ty ctx w) -> Bool
occursInAny : (i : Var ctx v) -> (as : Row (Ty ctx w)) -> Bool

i `occursIn` (TVar j) = i `eq` j
i `occursIn` TNat = False
i `occursIn` (TArrow a b) = (i `occursIn` a) || (i `occursIn` b)
i `occursIn` (TProd as) = i `occursInAny` as
i `occursIn` (TSum as) = i `occursInAny` as
i `occursIn` (TFix x a) = ThereVar i `occursIn` a

i `occursInAny` [<] = False
i `occursInAny` (as :< (x :- a)) = (i `occursIn` a) || (i `occursInAny` as)

reflectOccursIn :
  (i : Var ctx v) -> (a : Ty ctx w) ->
  (i `OccursIn` a) `Reflects` (i `occursIn` a)
reflectOccursInAny :
  (i : Var ctx v) -> (as : Row (Ty ctx w)) ->
  (i `OccursInAny` as) `Reflects` (i `occursInAny` as)

reflectOccursIn i (TVar j) = reflectEq i j
reflectOccursIn i TNat = RFalse id
reflectOccursIn i (TArrow a b) = reflectThese (reflectOccursIn i a) (reflectOccursIn i b)
reflectOccursIn i (TProd as) = reflectOccursInAny i as
reflectOccursIn i (TSum as) = reflectOccursInAny i as
reflectOccursIn i (TFix x a) = reflectOccursIn (ThereVar i) a

reflectOccursInAny i [<] = RFalse id
reflectOccursInAny i (as :< (x :- a)) =
  reflectThese (reflectOccursIn i a) (reflectOccursInAny i as)

-- Not Strictly Positive -----------------------------------------------------------

-- We use negation so we get a cause on failure.

NotPositiveIn : Var ctx v -> Ty ctx w -> Type
NotPositiveInAny : Var ctx v -> Row (Ty ctx w) -> Type

i `NotPositiveIn` TVar j = Void
i `NotPositiveIn` TNat = Void
i `NotPositiveIn` TArrow a b =
  -- NOTE: forbid on right side of arrow to prevent infinite breadth.
  i `OccursIn` TArrow a b
i `NotPositiveIn` TProd as = i `NotPositiveInAny` as
i `NotPositiveIn` TSum as = i `NotPositiveInAny` as
i `NotPositiveIn` TFix x a =
  -- BUG: forbid under fixpoint to prevent unbounded width
  -- this is safe to add back with the complex encoding of fixpoints
  ThereVar i `OccursIn` a

i `NotPositiveInAny` [<] = Void
i `NotPositiveInAny` as :< (x :- a) = These (i `NotPositiveIn` a) (i `NotPositiveInAny` as)

-- Not Positive implies Occurs

notPositiveToOccurs : (a : Ty ctx v) -> i `NotPositiveIn` a -> i `OccursIn` a
notPositiveAnyToOccursAny : (as : Row (Ty ctx v)) -> i `NotPositiveInAny` as -> i `OccursInAny` as

notPositiveToOccurs (TVar j) = absurd
notPositiveToOccurs TNat = id
notPositiveToOccurs (TArrow a b) = id
notPositiveToOccurs (TProd as) = notPositiveAnyToOccursAny as
notPositiveToOccurs (TSum as) = notPositiveAnyToOccursAny as
notPositiveToOccurs (TFix x a) = id

notPositiveAnyToOccursAny [<] = id
notPositiveAnyToOccursAny (as :< (x :- a)) = bimap (notPositiveToOccurs a) (notPositiveAnyToOccursAny as)

-- -- Decidable

notPositiveIn : (i : Var ctx v) -> (a : Ty ctx w) -> Bool
notPositiveInAny : (i : Var ctx v) -> (as : Row (Ty ctx w)) -> Bool

i `notPositiveIn` (TVar j) = False
i `notPositiveIn` TNat = False
i `notPositiveIn` (TArrow a b) = i `occursIn` TArrow a b
i `notPositiveIn` (TProd as) = i `notPositiveInAny` as
i `notPositiveIn` (TSum as) = i `notPositiveInAny` as
i `notPositiveIn` (TFix x a) = ThereVar i `occursIn` a

i `notPositiveInAny` [<] = False
i `notPositiveInAny` (as :< (x :- a)) = (i `notPositiveIn` a) || (i `notPositiveInAny` as)

reflectNotPositiveIn :
  (i : Var ctx v) -> (a : Ty ctx w) ->
  (i `NotPositiveIn` a) `Reflects` (i `notPositiveIn` a)
reflectNotPositiveInAny :
  (i : Var ctx v) -> (as : Row (Ty ctx w)) ->
  (i `NotPositiveInAny` as) `Reflects` (i `notPositiveInAny` as)

reflectNotPositiveIn i (TVar j) = RFalse id
reflectNotPositiveIn i TNat = RFalse id
reflectNotPositiveIn i (TArrow a b) = reflectOccursIn i (TArrow a b)
reflectNotPositiveIn i (TProd as) = reflectNotPositiveInAny i as
reflectNotPositiveIn i (TSum as) = reflectNotPositiveInAny i as
reflectNotPositiveIn i (TFix x a) = reflectOccursIn (ThereVar i) a

reflectNotPositiveInAny i [<] = RFalse id
reflectNotPositiveInAny i (as :< (x :- a)) =
  reflectThese (reflectNotPositiveIn i a) (reflectNotPositiveInAny i as)

-- Well Formed -----------------------------------------------------------------

-- Negating decidable properties is fun.

export
IllFormed : Ty ctx v -> Type
AnyIllFormed : Row (Ty ctx v) -> Type

IllFormed (TVar v) = Void
IllFormed TNat = Void
IllFormed (TArrow a b) = These (IllFormed a) (IllFormed b)
IllFormed (TProd as) = AnyIllFormed as
IllFormed (TSum as) = AnyIllFormed as
IllFormed (TFix x a) = These (%% x `NotPositiveIn` a) (IllFormed a)

AnyIllFormed [<] = Void
AnyIllFormed (as :< (x :- a)) = These (IllFormed a) (AnyIllFormed as)

-- Decidable

export
illFormed : (a : Ty ctx v) -> Bool
anyIllFormed : (as : Row (Ty ctx v)) -> Bool

illFormed (TVar j) = False
illFormed TNat = False
illFormed (TArrow a b) = illFormed a || illFormed b
illFormed (TProd as) = anyIllFormed as
illFormed (TSum as) = anyIllFormed as
illFormed (TFix x a) = (%% x `notPositiveIn` a) || illFormed a

anyIllFormed [<] = False
anyIllFormed (as :< (x :- a)) = illFormed a || anyIllFormed as

export
reflectIllFormed : (a : Ty ctx v) -> IllFormed a `Reflects` illFormed a
reflectAnyIllFormed : (as : Row (Ty ctx v)) -> AnyIllFormed as `Reflects` anyIllFormed as

reflectIllFormed (TVar j) = RFalse id
reflectIllFormed TNat = RFalse id
reflectIllFormed (TArrow a b) = reflectThese (reflectIllFormed a) (reflectIllFormed b)
reflectIllFormed (TProd as) = reflectAnyIllFormed as
reflectIllFormed (TSum as) = reflectAnyIllFormed as
reflectIllFormed (TFix x a) = reflectThese (reflectNotPositiveIn (%% x) a) (reflectIllFormed a)

reflectAnyIllFormed [<] = RFalse id
reflectAnyIllFormed (as :< (x :- a)) =
  reflectThese (reflectIllFormed a) (reflectAnyIllFormed as)

--------------------------------------------------------------------------------
-- Substitution ----------------------------------------------------------------
--------------------------------------------------------------------------------

public export
fromVar : Either (Var ctx v) (Ty ctx v) -> Ty ctx v
fromVar = either TVar id

export
sub : Env ctx1 ctx2 (Ty ctx2) -> Ty ctx1 v -> Ty ctx2 v
subAll : Env ctx1 ctx2 (Ty ctx2) -> Row (Ty ctx1 v) -> Row (Ty ctx2 v)
subAllFresh :
  (env : Env ctx1 ctx2 (Ty ctx2)) -> (x : String) ->
  (row : Row (Ty ctx1 v)) ->
  So (x `freshIn` row) -> So (x `freshIn` subAll env row)

sub env (TVar i) = fromVar $ lookup env i
sub env TNat = TNat
sub env (TArrow a b) = TArrow (sub env a) (sub env b)
sub env (TProd as) = TProd (subAll env as)
sub env (TSum as) = TSum (subAll env as)
sub env (TFix x a) = TFix x (sub (lift (Drop Id) env :< (x :- TVar (%% x))) a)

subAll env [<] = [<]
subAll env ((:<) as (x :- a) {fresh}) =
  (:<) (subAll env as) (x :- sub env a) {fresh = subAllFresh env x as fresh}

subAllFresh env x [<] = id
subAllFresh env x (as :< (y :- a)) = andSo . mapSnd (subAllFresh env x as) . soAnd
