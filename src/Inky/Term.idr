module Inky.Term

import Data.Bool.Decidable
import Data.DPair
import Data.List.Elem
import Data.Maybe.Decidable
import Data.These
import Data.Vect
import Inky.Thinning
import Inky.Type

-- Redefine so I can prove stuff about it
%hide
Prelude.getAt

getAt : Nat -> List a -> Maybe a
getAt k [] = Nothing
getAt 0 (x :: xs) = Just x
getAt (S k) (x :: xs) = getAt k xs

--------------------------------------------------------------------------------
-- Definition ------------------------------------------------------------------
--------------------------------------------------------------------------------

public export
data SynthTerm : Nat -> Nat -> Type
public export
data CheckTerm : Nat -> Nat -> Type

data SynthTerm where
  Var : Fin tm -> SynthTerm ty tm
  Lit : Nat -> SynthTerm ty tm
  Suc : CheckTerm ty tm -> SynthTerm ty tm
  App : SynthTerm ty tm -> List1 (CheckTerm ty tm) -> SynthTerm ty tm
  Prj : SynthTerm ty tm -> Nat -> SynthTerm ty tm
  Expand : SynthTerm ty tm -> SynthTerm ty tm
  Annot : CheckTerm ty tm -> Ty ty -> SynthTerm ty tm

data CheckTerm where
  Let :
    SynthTerm ty tm ->
    CheckTerm ty (S tm) ->
    CheckTerm ty tm
  Abs : (k : Nat) -> CheckTerm ty (S k + tm) -> CheckTerm ty tm
  Inj : Nat -> CheckTerm ty tm -> CheckTerm ty tm
  Tup : List (CheckTerm ty tm) -> CheckTerm ty tm
  Case :
    SynthTerm ty tm ->
    List (CheckTerm ty (S tm)) ->
    CheckTerm ty tm
  Contract : CheckTerm ty tm -> CheckTerm ty tm
  Fold :
    SynthTerm ty tm ->
    CheckTerm ty (S tm) ->
    CheckTerm ty tm
  Embed :
    SynthTerm ty tm ->
    CheckTerm ty tm

%name SynthTerm e
%name CheckTerm t, u, v

--------------------------------------------------------------------------------
-- Well Formed -----------------------------------------------------------------
--------------------------------------------------------------------------------

GetAt : Nat -> List a -> a -> Type
GetAt k xs x = (n : Elem x xs ** elemToNat n = k)

CanProject : Ty ty -> List (Ty ty) -> Type
CanProject (TUnion as) bs = forget as = bs
CanProject (TProd as) bs = as = bs
CanProject _ bs = Void

CanInject : Ty ty -> List (Ty ty) -> Type
CanInject (TUnion as) bs = forget as = bs
CanInject (TSum as) bs = as = bs
CanInject _ bs = Void

IsFixpoint : Ty ty -> Ty (S ty) -> Type
IsFixpoint TNat b = b = TSum [TProd [], TVar FZ]
IsFixpoint (TFix a) b = a = b
IsFixpoint _ b = Void

IsArrow : {ty : Nat} -> (k : Nat) -> Ty ty -> Vect k (Ty ty) -> Ty ty -> Type
IsArrow 0 a as b = (as = [], b = a)
IsArrow (S k) (TArrow dom cod) as b = (bs ** (as = dom :: bs, IsArrow k cod bs b))
IsArrow (S k) _ as b = Void

IsProduct : Ty ty -> List (Ty ty) -> Type
IsProduct (TProd as) bs = as = bs
IsProduct _ bs = Void

IsSum : Ty ty -> List (Ty ty) -> Type
IsSum (TSum as) bs = as = bs
IsSum _ bs = Void

Synths :
  {ty, tm : Nat} -> (ctx : Vect tm (Ty ty)) ->
  SynthTerm ty tm -> Ty ty -> Type
Checks :
  {ty, tm : Nat} -> (ctx : Vect tm (Ty ty)) ->
  Ty ty -> CheckTerm ty tm -> Type
CheckSpine :
  {ty, tm : Nat} -> (ctx : Vect tm (Ty ty)) ->
  (fun : Ty ty) -> List (CheckTerm ty tm) -> (res : Ty ty) -> Type
CheckSpine1 :
  {ty, tm : Nat} -> (ctx : Vect tm (Ty ty)) ->
  (fun : Ty ty) -> List1 (CheckTerm ty tm) -> (res : Ty ty) -> Type
AllCheck : {ty, tm : Nat} -> (ctx : Vect tm (Ty ty)) -> List (Ty ty) -> List (CheckTerm ty tm) -> Type
AllCheckBinding :
  {ty, tm : Nat} -> (ctx : Vect tm (Ty ty)) -> List (Ty ty) -> Ty ty -> List (CheckTerm ty (S tm)) -> Type

Synths ctx (Var i) a = (a = index i ctx)
Synths ctx (Lit k) a = (a = TNat)
Synths ctx (Suc t) a = (Checks ctx TNat t, a = TNat)
Synths ctx (App e ts) a =
  ( fun **
  ( Synths ctx e fun
  , CheckSpine1 ctx fun ts a
  ))
Synths ctx (Prj e k) a =
  ( b **
  ( Synths ctx e b
  , ( as **
    ( CanProject b as
    , GetAt k as a
    ))
  ))
Synths ctx (Expand e) a =
  ( b **
  ( Synths ctx e b
  , ( c **
    ( IsFixpoint b c
    , a = sub (Base Id :< b) c))
  ))
Synths ctx (Annot t a) b =
  ( Not (IllFormed a)
  , Checks ctx a t
  , a = b
  )

Checks ctx a (Let e t) =
  ( b **
  ( Synths ctx e b
  , Checks (b :: ctx) a t
  ))
Checks ctx a (Abs k t) =
  ( as : Vect (S k) _ ** b **
  ( IsArrow (S k) a as b
  , Checks (as ++ ctx) b t
  ))
Checks ctx a (Inj k t) =
  ( as **
  ( CanInject a as
  , ( b **
    ( GetAt k as b
    , Checks ctx b t
    ))
  ))
Checks ctx a (Tup ts) =
  ( as **
  ( IsProduct a as
  , AllCheck ctx as ts
  ))
Checks ctx a (Case e ts) =
  ( b **
  ( Synths ctx e b
  , ( as **
    ( IsSum b as
    , AllCheckBinding ctx as a ts
    ))
  ))
Checks ctx a (Contract t) =
  ( b **
  ( IsFixpoint a b
  , Checks ctx (sub (Base Id :< a) b) t
  ))
Checks ctx a (Fold e t) =
  ( b **
  ( Synths ctx e b
  , ( c **
    ( IsFixpoint b c
    , Checks (sub (Base Id :< a) c :: ctx) a t
    ))
  ))
Checks ctx a (Embed e) = Synths ctx e a

CheckSpine ctx fun [] res = fun = res
CheckSpine ctx fun (t :: ts) res =
  ( a ** b **
  ( IsArrow 1 fun [a] b
  , Checks ctx a t
  , CheckSpine ctx b ts res
  ))

CheckSpine1 ctx fun (t ::: ts) res =
  ( a ** b **
  ( IsArrow 1 fun [a] b
  , Checks ctx a t
  , CheckSpine ctx b ts res
  ))

AllCheck ctx [] [] = ()
AllCheck ctx [] (t :: ts) = Void
AllCheck ctx (a :: as) [] = Void
AllCheck ctx (a :: as) (t :: ts) = (Checks ctx a t, AllCheck ctx as ts)

AllCheckBinding ctx [] b [] = ()
AllCheckBinding ctx [] b (t :: ts) = Void
AllCheckBinding ctx (a :: as) b [] = Void
AllCheckBinding ctx (a :: as) b (t :: ts) = (Checks (a :: ctx) b t, AllCheckBinding ctx as b ts)

-- Uniqueness

getAtUnique :
  (n : Nat) -> (xs : List a) ->
  GetAt n xs x -> GetAt n xs y -> x = y
getAtUnique 0     (x :: xs) (Here ** prf1)     (Here ** prf2)     = Refl
getAtUnique (S k) (x :: xs) (There n1 ** prf1) (There n2 ** prf2) = getAtUnique k xs (n1 ** injective prf1) (n2 ** injective prf2)
getAtUnique _     []        (n1 ** prf1)       (n2 ** prf2)       impossible

canProjectUnique : (a : Ty ty) -> CanProject a as -> CanProject a bs -> as = bs
canProjectUnique (TUnion as) Refl Refl = Refl
canProjectUnique (TProd as)  Refl Refl = Refl

canInjectUnique : (a : Ty ty) -> CanInject a as -> CanInject a bs -> as = bs
canInjectUnique (TUnion as) Refl Refl = Refl
canInjectUnique (TSum as)   Refl Refl = Refl

isFixpointUnique : (a : Ty ty) -> IsFixpoint a b -> IsFixpoint a c -> b = c
isFixpointUnique TNat Refl Refl = Refl
isFixpointUnique (TFix a) Refl Refl = Refl

isArrowUnique :
  (k : Nat) -> (a : Ty ty) ->
  forall bs, b, cs, c. IsArrow k a bs b -> IsArrow k a cs c -> (bs = cs, b = c)
isArrowUnique 0 a (Refl, Refl) (Refl, Refl) = (Refl, Refl)
isArrowUnique (S k) (TArrow dom cod) (as ** (Refl, prf1)) (bs ** (Refl, prf2)) =
  let (eq1, eq2) = isArrowUnique k cod prf1 prf2 in
  (cong (dom ::) eq1, eq2)

isProductUnique : (a : Ty ty) -> IsProduct a as -> IsProduct a bs -> as = bs
isProductUnique (TProd as) Refl Refl = Refl

isSumUnique : (a : Ty ty) -> IsSum a as -> IsSum a bs -> as = bs
isSumUnique (TSum as) Refl Refl = Refl


synthsUnique :
  (0 ctx : Vect tm (Ty ty)) -> (e : SynthTerm ty tm) ->
  Synths ctx e a -> Synths ctx e b -> a = b
checkSpineUnique :
  (0 ctx : Vect tm (Ty ty)) -> (a : Ty ty) -> (ts : List (CheckTerm ty tm)) ->
  CheckSpine ctx a ts b -> CheckSpine ctx a ts c -> b = c
checkSpine1Unique :
  (0 ctx : Vect tm (Ty ty)) -> (a : Ty ty) -> (ts : List1 (CheckTerm ty tm)) ->
  CheckSpine1 ctx a ts b -> CheckSpine1 ctx a ts c -> b = c

synthsUnique ctx (Var i) prf1 prf2 = trans prf1 (sym prf2)
synthsUnique ctx (Lit k) prf1 prf2 = trans prf1 (sym prf2)
synthsUnique ctx (Suc t) (_, prf1) (_, prf2) = trans prf1 (sym prf2)
synthsUnique ctx (App e ts) (fun1 ** (prf11, prf12)) (fun2 ** (prf21, prf22))
  with (synthsUnique ctx e prf11 prf21)
  synthsUnique ctx (App e ts) (fun ** (prf11, prf12)) (fun ** (prf21, prf22)) | Refl =
    checkSpine1Unique ctx fun ts prf12 prf22
synthsUnique ctx (Prj e k) (a ** (prf11, prf12)) (b ** (prf21, prf22))
  with (synthsUnique ctx e prf11 prf21)
  synthsUnique ctx (Prj e k) (a ** (_, (as ** (prf11, prf12)))) (a ** (_, (bs ** (prf21, prf22)))) | Refl
    with (canProjectUnique a prf11 prf21)
    synthsUnique ctx (Prj e k) (a ** (_, (as ** (_, prf1)))) (a ** (_, (as ** (_, prf2)))) | Refl | Refl =
      getAtUnique k as prf1 prf2
synthsUnique ctx (Expand e) (a ** (prf11, prf12)) (b ** (prf21, prf22))
  with (synthsUnique ctx e prf11 prf21)
  synthsUnique ctx (Expand e) (a ** (_, (b ** (prf11, prf12)))) (a ** (_, (c ** (prf21, prf22)))) | Refl
    with (isFixpointUnique a prf11 prf21)
    synthsUnique ctx (Expand e) (a ** (_, (b ** (_, prf1)))) (a ** (_, (b ** (_, prf2)))) | Refl | Refl =
      trans prf1 (sym prf2)
synthsUnique ctx (Annot t c) prf1 prf2 = trans (sym $ snd $ snd prf1) (snd $ snd prf2)

checkSpineUnique ctx a [] prf1 prf2 = trans (sym prf1) prf2
checkSpineUnique ctx a (t :: ts) (b ** c ** (prf11, _ , prf12)) (d ** e ** (prf21, _ , prf22))
  with (isArrowUnique 1 a prf11 prf21)
  checkSpineUnique ctx a (t :: ts) (b ** c ** (_, _ , prf1)) (b ** c ** (_, _ , prf2)) | (Refl, Refl) =
    checkSpineUnique ctx c ts prf1 prf2

checkSpine1Unique ctx a (t ::: ts) (b ** c ** (prf11, _ , prf12)) (d ** e ** (prf21, _ , prf22))
  with (isArrowUnique 1 a prf11 prf21)
  checkSpine1Unique ctx a (t ::: ts) (b ** c ** (_, _ , prf1)) (b ** c ** (_, _ , prf2)) | (Refl, Refl) =
    checkSpineUnique ctx c ts prf1 prf2

-- Decidable -------------------------------------------------------------------

canProject : Ty ty -> Maybe (List (Ty ty))
canProject (TUnion as) = Just (forget as)
canProject (TProd as) = Just as
canProject _ = Nothing

canInject : Ty ty -> Maybe (List (Ty ty))
canInject (TUnion as) = Just (forget as)
canInject (TSum as) = Just as
canInject _ = Nothing

isFixpoint : Ty ty -> Maybe (Ty (S ty))
isFixpoint TNat = Just (TSum [TProd [], TVar FZ])
isFixpoint (TFix a) = Just a
isFixpoint _ = Nothing

isArrow : (k : Nat) -> Ty ty -> Maybe (Vect k (Ty ty), Ty ty)
isArrow 0 a = Just ([], a)
isArrow (S k) (TArrow a b) = do
  (as, c) <- isArrow k b
  Just (a :: as, c)
isArrow (S k) _ = Nothing

isProduct : Ty ty -> Maybe (List (Ty ty))
isProduct (TProd as) = Just as
isProduct _ = Nothing

isSum : Ty ty -> Maybe (List (Ty ty))
isSum (TSum as) = Just as
isSum _ = Nothing

synths :
  (ctx : Vect tm (Ty ty)) ->
  SynthTerm ty tm -> Maybe (Ty ty)
checks :
  (ctx : Vect tm (Ty ty)) ->
  Ty ty -> CheckTerm ty tm -> Bool
checkSpine :
  (ctx : Vect tm (Ty ty)) ->
  Ty ty -> List (CheckTerm ty tm) -> Maybe (Ty ty)
checkSpine1 :
  (ctx : Vect tm (Ty ty)) ->
  Ty ty -> List1 (CheckTerm ty tm) -> Maybe (Ty ty)
allCheck :
  (ctx : Vect tm (Ty ty)) ->
  List (Ty ty) -> List (CheckTerm ty tm) -> Bool
allCheckBinding :
  (ctx : Vect tm (Ty ty)) ->
  List (Ty ty) -> Ty ty -> List (CheckTerm ty (S tm)) -> Bool

synths ctx (Var i) = Just (index i ctx)
synths ctx (Lit k) = Just TNat
synths ctx (Suc t) = do
  guard (checks ctx TNat t)
  Just TNat
synths ctx (App e ts) = do
  a <- synths ctx e
  checkSpine1 ctx a ts
synths ctx (Prj e k) = do
  a <- synths ctx e
  as <- canProject a
  getAt k as
synths ctx (Expand e) = do
  a <- synths ctx e
  b <- isFixpoint a
  Just (sub (Base Id :< a) b)
synths ctx (Annot t a) = do
  guard (not $ illFormed a)
  guard (checks ctx a t)
  Just a

checks ctx a (Let e t) =
  case synths ctx e of
    Just b => checks (b :: ctx) a t
    Nothing => False
checks ctx a (Abs k t) =
  case isArrow (S k) a of
    Just (as, b) => checks (as ++ ctx) b t
    Nothing => False
checks ctx a (Inj k t) =
  case canInject a of
    Just as =>
      case getAt k as of
        Just b => checks ctx b t
        Nothing => False
    Nothing => False
checks ctx a (Tup ts) =
  case isProduct a of
    Just as => allCheck ctx as ts
    Nothing => False
checks ctx a (Case e ts) =
  case synths ctx e of
    Just b =>
      case isSum b of
        Just as => allCheckBinding ctx as a ts
        Nothing => False
    Nothing => False
checks ctx a (Contract t) =
  case isFixpoint a of
    Just b => checks ctx (sub (Base Id :< a) b) t
    Nothing => False
checks ctx a (Fold e t) =
  case synths ctx e of
    Just b =>
      case isFixpoint b of
        Just c => checks (sub (Base Id :< a) c :: ctx) a t
        Nothing => False
    Nothing => False
checks ctx a (Embed e) =
  case synths ctx e of
    Just b => a == b
    Nothing => False

checkSpine ctx a [] = Just a
checkSpine ctx a (t :: ts) = do
  ([dom], cod) <- isArrow 1 a
  guard (checks ctx dom t)
  checkSpine ctx cod ts

checkSpine1 ctx a (t ::: ts) = do
  ([dom], cod) <- isArrow 1 a
  guard (checks ctx dom t)
  checkSpine ctx cod ts

allCheck ctx [] [] = True
allCheck ctx [] (t :: ts) = False
allCheck ctx (a :: as) [] = False
allCheck ctx (a :: as) (t :: ts) = checks ctx a t && allCheck ctx as ts

allCheckBinding ctx [] b [] = True
allCheckBinding ctx [] b (t :: ts) = False
allCheckBinding ctx (a :: as) b [] = False
allCheckBinding ctx (a :: as) b (t :: ts) = checks (a :: ctx) b t && allCheckBinding ctx as b ts

-- Proof

reflectGetAt : (k : Nat) -> (xs : List a) -> GetAt k xs `OnlyWhen` getAt k xs
reflectGetAt k [] = RNothing (\_, (n ** prf) => absurd n)
reflectGetAt 0 (x :: xs) = RJust (Here ** Refl)
reflectGetAt (S k) (x :: xs) with (reflectGetAt k xs) | (getAt k xs)
  _ | RJust (n ** prf) | _ = RJust (There n ** cong S prf)
  _ | RNothing not | _ = RNothing (\x => \case (There n ** prf) => not x (n ** injective prf))

reflectCanProject : (a : Ty ty) -> CanProject a `OnlyWhen` canProject a
reflectCanProject (TVar i) = RNothing (\x, y => y)
reflectCanProject TNat = RNothing (\x, y => y)
reflectCanProject (TArrow a b) = RNothing (\x, y => y)
reflectCanProject (TUnion as) = RJust Refl
reflectCanProject (TProd as) = RJust Refl
reflectCanProject (TSum as) = RNothing (\x, y => y)
reflectCanProject (TFix a) = RNothing (\x, y => y)

reflectCanInject : (a : Ty ty) -> CanInject a `OnlyWhen` canInject a
reflectCanInject (TVar i) = RNothing (\x, y => y)
reflectCanInject TNat = RNothing (\x, y => y)
reflectCanInject (TArrow a b) = RNothing (\x, y => y)
reflectCanInject (TUnion as) = RJust Refl
reflectCanInject (TProd as) = RNothing (\x, y => y)
reflectCanInject (TSum as) = RJust Refl
reflectCanInject (TFix a) = RNothing (\x, y => y)

reflectIsFixpoint : (a : Ty ty) -> IsFixpoint a `OnlyWhen` isFixpoint a
reflectIsFixpoint (TVar i) = RNothing (\x, y => y)
reflectIsFixpoint TNat = RJust Refl
reflectIsFixpoint (TArrow a b) = RNothing (\x, y => y)
reflectIsFixpoint (TUnion as) = RNothing (\x, y => y)
reflectIsFixpoint (TProd as) = RNothing (\x, y => y)
reflectIsFixpoint (TSum as) = RNothing (\x, y => y)
reflectIsFixpoint (TFix a) = RJust Refl

reflectIsArrow : (k : Nat) -> (a : Ty ty) -> uncurry (IsArrow k a) `OnlyWhen` isArrow k a
reflectIsArrow 0 a = RJust (Refl, Refl)
reflectIsArrow (S k) (TVar i) = RNothing (\(_, _), x => x)
reflectIsArrow (S k) TNat = RNothing (\(_, _), x => x)
reflectIsArrow (S k) (TArrow a b) with (reflectIsArrow k b) | (isArrow k b)
  _ | RJust arrow | Just (as, c) = RJust (as ** (Refl, arrow))
  _ | RNothing notArrow | _ = RNothing (\(a :: as, c), (as ** (Refl, prf)) => notArrow (as, c) prf)
reflectIsArrow (S k) (TUnion as) = RNothing (\(_, _), x => x)
reflectIsArrow (S k) (TProd as) = RNothing (\(_, _), x => x)
reflectIsArrow (S k) (TSum as) = RNothing (\(_, _), x => x)
reflectIsArrow (S k) (TFix a) = RNothing (\(_, _), x => x)

reflectIsProduct : (a : Ty ty) -> IsProduct a `OnlyWhen` isProduct a
reflectIsProduct (TVar i) = RNothing (\x, y => y)
reflectIsProduct TNat = RNothing (\x, y => y)
reflectIsProduct (TArrow a b) = RNothing (\x, y => y)
reflectIsProduct (TUnion as) = RNothing (\x, y => y)
reflectIsProduct (TProd as) = RJust Refl
reflectIsProduct (TSum as) = RNothing (\x, y => y)
reflectIsProduct (TFix a) = RNothing (\x, y => y)

reflectIsSum : (a : Ty ty) -> IsSum a `OnlyWhen` isSum a
reflectIsSum (TVar i) = RNothing (\x, y => y)
reflectIsSum TNat = RNothing (\x, y => y)
reflectIsSum (TArrow a b) = RNothing (\x, y => y)
reflectIsSum (TUnion as) = RNothing (\x, y => y)
reflectIsSum (TProd as) = RNothing (\x, y => y)
reflectIsSum (TSum as) = RJust Refl
reflectIsSum (TFix a) = RNothing (\x, y => y)

-- FIXME: these are total; the termination checker is unreasonably slow.

partial
reflectSynths :
  (ctx : Vect tm (Ty ty)) -> (e : SynthTerm ty tm) ->
  Synths ctx e `OnlyWhen` synths ctx e
partial
reflectChecks :
  (ctx : Vect tm (Ty ty)) -> (a : Ty ty) -> (t : CheckTerm ty tm) ->
  Checks ctx a t `Reflects` checks ctx a t
partial
reflectCheckSpine :
  (ctx : Vect tm (Ty ty)) -> (a : Ty ty) -> (ts : List (CheckTerm ty tm)) ->
  CheckSpine ctx a ts `OnlyWhen` checkSpine ctx a ts
partial
reflectCheckSpine1 :
  (ctx : Vect tm (Ty ty)) -> (a : Ty ty) -> (ts : List1 (CheckTerm ty tm)) ->
  CheckSpine1 ctx a ts `OnlyWhen` checkSpine1 ctx a ts
partial
reflectAllCheck :
  (ctx : Vect tm (Ty ty)) -> (as : List (Ty ty)) -> (ts : List (CheckTerm ty tm)) ->
  AllCheck ctx as ts `Reflects` allCheck ctx as ts
partial
reflectAllCheckBinding :
  (ctx : Vect tm (Ty ty)) -> (as : List (Ty ty)) -> (a : Ty ty) -> (ts : List (CheckTerm ty (S tm))) ->
  AllCheckBinding ctx as a ts `Reflects` allCheckBinding ctx as a ts

reflectSynths ctx (Var i) = RJust Refl
reflectSynths ctx (Lit k) = RJust Refl
reflectSynths ctx (Suc t) with (reflectChecks ctx TNat t) | (checks ctx TNat t)
  _ | RTrue tNat | _ = RJust (tNat, Refl)
  _ | RFalse tNotNat | _ = RNothing (\_, (tNat, _) => tNotNat tNat)
reflectSynths ctx (App e ts) with (reflectSynths ctx e) | (synths ctx e)
  _ | RJust eTy | Just a with (reflectCheckSpine1 ctx a ts) | (checkSpine1 ctx a ts)
    _ | RJust tsSpine | Just b = RJust (a ** (eTy, tsSpine))
    _ | RNothing tsBad | _ =
      RNothing
        (\c, (b ** (eTy', tsSpine)) =>
          let tsSpine = rewrite synthsUnique ctx e {a, b} eTy eTy' in tsSpine in
          tsBad c tsSpine)
  _ | RNothing eBad | _ =
    RNothing (\c, (b ** (eTy, _)) => eBad b eTy)
reflectSynths ctx (Prj e k) with (reflectSynths ctx e) | (synths ctx e)
  _ | RJust eTy | Just a with (reflectCanProject a) | (canProject a)
    _ | RJust prf | Just as with (reflectGetAt k as) | (getAt k as)
      _ | RJust got | Just b = RJust (a ** (eTy, (as ** (prf, got))))
      _ | RNothing not | _ =
        RNothing (\x, (a' ** (eTy', (as' ** (prf', got)))) =>
          let prf' = rewrite synthsUnique ctx e {a, b = a'} eTy eTy' in prf' in
          let got = rewrite canProjectUnique a {as, bs = as'} prf prf' in got in
          not x got)
    _ | RNothing nprf | _ =
      RNothing (\x, (a' ** (eTy', (as' ** (prf, _)))) =>
        let prf = rewrite synthsUnique ctx e {a, b = a'} eTy eTy' in prf in
        nprf as' prf)
  _ | RNothing eBad | _ = RNothing (\x, (a' ** (eTy, _)) => eBad a' eTy)
reflectSynths ctx (Expand e) with (reflectSynths ctx e) | (synths ctx e)
  _ | RJust eTy | Just a with (reflectIsFixpoint a) | (isFixpoint a)
    _ | RJust prf | Just b = RJust (a ** (eTy, (b ** (prf, Refl))))
    _ | RNothing nprf | _ =
      RNothing (\x, (a' ** (eTy', (b ** (prf, eq)))) =>
        let prf = rewrite synthsUnique ctx e {a, b = a'} eTy eTy' in prf in
        nprf b prf)
  _ | RNothing eBad | _ = RNothing (\x, (a ** (eTy, _)) => eBad a eTy)
reflectSynths ctx (Annot t a) with (reflectIllFormed a) | (illFormed a)
  _ | RFalse wf | _ with (reflectChecks ctx a t) | (checks ctx a t)
    _ | RTrue tTy | _ = RJust (wf, tTy, Refl)
    _ | RFalse tBad | _ = RNothing (\x, (_, tTy, Refl) => tBad tTy)
  _ | RTrue notWf | _ = RNothing (\x, (wf, _) => wf notWf)

reflectChecks ctx a (Let e t) with (reflectSynths ctx e) | (synths ctx e)
  _ | RJust eTy | Just b with (reflectChecks (b :: ctx) a t) | (checks (b :: ctx) a t)
    _ | RTrue tTy | _ = RTrue (b ** (eTy, tTy))
    _ | RFalse tBad | _ =
      RFalse (\(b' ** (eTy', tTy)) =>
        let tTy = rewrite synthsUnique ctx e {a = b, b = b'} eTy eTy' in tTy in
        tBad tTy)
  _ | RNothing eBad | Nothing = RFalse (\(b ** (eTy, _)) => eBad b eTy)
reflectChecks ctx a (Abs k t) with (reflectIsArrow (S k) a) | (isArrow (S k) a)
  _ | RJust prf | Just (as, b) with (reflectChecks (as ++ ctx) b t) | (checks (as ++ ctx) b t)
    _ | RTrue tTy | _ = RTrue (as ** b ** (prf, tTy))
    _ | RFalse tBad | _ =
      RFalse (\(as' ** b' ** (prf', tTy)) =>
        let
          tTy =
            rewrite fst $ isArrowUnique (S k) a {bs = as, b, cs = as', c = b'} prf prf' in
            rewrite snd $ isArrowUnique (S k) a {bs = as, b, cs = as', c = b'} prf prf' in
            tTy
        in
        tBad tTy)
  _ | RNothing nprf | _ = RFalse (\(as ** b ** (prf, _)) => nprf (as, b) prf)
reflectChecks ctx a (Inj k t) with (reflectCanInject a) | (canInject a)
  _ | RJust prf | Just as with (reflectGetAt k as) | (getAt k as)
    _ | RJust got | Just b with (reflectChecks ctx b t) | (checks ctx b t)
      _ | RTrue tTy | _ = RTrue (as ** (prf, (b ** (got, tTy))))
      _ | RFalse tBad | _ =
        RFalse (\(as' ** (prf', (b' ** (got', tTy)))) =>
          let got' = rewrite canInjectUnique a {as, bs = as'} prf prf' in got' in
          let tTy = rewrite getAtUnique k as {x = b, y = b'} got got' in tTy in
          tBad tTy)
    _ | RNothing not | _ =
      RFalse (\(as' ** (prf', (b ** (got, _)))) =>
        let got = rewrite canInjectUnique a {as, bs = as'} prf prf' in got in
        not b got)
  _ | RNothing nprf | _ = RFalse (\(as ** (prf, _)) => nprf as prf)
reflectChecks ctx a (Tup ts) with (reflectIsProduct a) | (isProduct a)
  _ | RJust prf | Just as with (reflectAllCheck ctx as ts) | (allCheck ctx as ts)
    _ | RTrue tsTy | _ = RTrue (as ** (prf, tsTy))
    _ | RFalse tsBad | _ =
      RFalse (\(as' ** (prf', tsTy)) =>
        let tsTy = rewrite isProductUnique a {as, bs = as'} prf prf' in tsTy in
        tsBad tsTy)
  _ | RNothing nprf | _ = RFalse (\(as ** (prf, _)) => nprf as prf)
reflectChecks ctx a (Case e ts) with (reflectSynths ctx e) | (synths ctx e)
  _ | RJust eTy | Just b with (reflectIsSum b) | (isSum b)
    _ | RJust prf | Just as with (reflectAllCheckBinding ctx as a ts) | (allCheckBinding ctx as a ts)
      _ | RTrue tsTy | _ = RTrue (b ** (eTy, (as ** (prf, tsTy))))
      _ | RFalse tsBad | _ =
        RFalse
          (\(b' ** (eTy', (as' ** (prf', tsTy)))) =>
            let prf' = rewrite synthsUnique ctx e {a = b, b = b'} eTy eTy' in prf' in
            let tsTy = rewrite isSumUnique b {as, bs = as'} prf prf' in tsTy in
            tsBad tsTy)
    _ | RNothing nprf | _ =
      RFalse (\(b' ** (eTy', (as ** (prf, _)))) =>
        let prf = rewrite synthsUnique ctx e {a = b, b = b'} eTy eTy' in prf in
        nprf as prf)
  _ | RNothing eBad | _ = RFalse (\(b ** (eTy, _)) => eBad b eTy)
reflectChecks ctx a (Contract t) with (reflectIsFixpoint a) | (isFixpoint a)
  _ | RJust prf | Just b with (reflectChecks ctx (sub (Base Id :< a) b) t) | (checks ctx (sub (Base Id :< a) b) t)
    _ | RTrue tTy | _ = RTrue (b ** (prf, tTy))
    _ | RFalse tBad | _ =
      RFalse (\(b' ** (prf', tTy)) =>
        let tTy = rewrite isFixpointUnique a {b, c = b'} prf prf' in tTy in
        tBad tTy)
  _ | RNothing nprf | _ = RFalse (\(b ** (prf, _)) => nprf b prf)
reflectChecks ctx a (Fold e t) with (reflectSynths ctx e) | (synths ctx e)
  _ | RJust eTy | Just b with (reflectIsFixpoint b) | (isFixpoint b)
    _ | RJust prf | Just c with (reflectChecks ((sub (Base Id :< a) c) :: ctx) a t) | (checks ((sub (Base Id :< a) c) :: ctx) a t)
      _ | RTrue tTy | _ = RTrue (b ** (eTy, (c ** (prf, tTy))))
      _ | RFalse tBad | _ =
        RFalse (\(b' ** (eTy', (c' ** (prf', tTy)))) =>
          let prf' = rewrite synthsUnique ctx e {a = b, b = b'} eTy eTy' in prf' in
          let tTy = rewrite isFixpointUnique b {b = c, c = c'} prf prf' in tTy in
          tBad tTy)
    _ | RNothing nprf | _ =
      RFalse (\(b' ** (eTy', (c ** (prf, _)))) =>
        let prf = rewrite synthsUnique ctx e {a = b, b = b'} eTy eTy' in prf in
        nprf c prf)
  _ | RNothing eBad | _ = RFalse (\(b ** (eTy, _)) => eBad b eTy)
reflectChecks ctx a (Embed e) with (reflectSynths ctx e) | (synths ctx e)
  _ | RJust eTy | Just b with (reflectEq a b) | (a == b)
    reflectChecks ctx a (Embed e) | RJust eTy | Just .(a) | RTrue Refl | _ = RTrue eTy
    _ | RFalse neq | _ = RFalse (\eTy' => neq $ synthsUnique ctx e eTy' eTy)
  _ | RNothing eBad | _ = RFalse (\eTy => eBad a eTy)

reflectCheckSpine ctx a [] = RJust Refl
reflectCheckSpine ctx a (t :: ts) with (reflectIsArrow 1 a) | (isArrow 1 a)
  _ | RJust prf | Just ([b], c) with (reflectChecks ctx b t) | (checks ctx b t)
    _ | RTrue tTy | _ with (reflectCheckSpine ctx c ts) | (checkSpine ctx c ts)
      _ | RJust tsTy | Just d = RJust (b ** c ** (prf, tTy, tsTy))
      _ | RNothing tsBad | _ =
        RNothing (\d, (_ ** c' ** (prf', _, tsTy)) =>
          let tsTy = rewrite snd $ isArrowUnique 1 a {b = c, c = c'} prf prf' in tsTy in
          tsBad d tsTy)
    _ | RFalse tBad | _ =
      RNothing (\d, (b' ** _ ** (prf', tTy, _)) =>
        let
          tTy =
            rewrite fst $ biinj (::) $ fst $ isArrowUnique 1 a {bs = [b], cs = [b']} prf prf' in
            tTy
        in
        tBad tTy)
  _ | RNothing nprf | _ = RNothing (\d, (b ** c ** (prf, _)) => nprf ([b], c) prf)

reflectCheckSpine1 ctx a (t ::: ts) with (reflectIsArrow 1 a) | (isArrow 1 a)
  _ | RJust prf | Just ([b], c) with (reflectChecks ctx b t) | (checks ctx b t)
    _ | RTrue tTy | _ with (reflectCheckSpine ctx c ts) | (checkSpine ctx c ts)
      _ | RJust tsTy | Just d = RJust (b ** c ** (prf, tTy, tsTy))
      _ | RNothing tsBad | _ =
        RNothing (\d, (_ ** c' ** (prf', _, tsTy)) =>
          let tsTy = rewrite snd $ isArrowUnique 1 a {b = c, c = c'} prf prf' in tsTy in
          tsBad d tsTy)
    _ | RFalse tBad | _ =
      RNothing (\d, (b' ** _ ** (prf', tTy, _)) =>
        let
          tTy =
            rewrite fst $ biinj (::) $ fst $ isArrowUnique 1 a {bs = [b], cs = [b']} prf prf' in
            tTy
        in
        tBad tTy)
  _ | RNothing nprf | _ = RNothing (\d, (b ** c ** (prf, _)) => nprf ([b], c) prf)

reflectAllCheck ctx [] [] = RTrue ()
reflectAllCheck ctx [] (t :: ts) = RFalse (\x => x)
reflectAllCheck ctx (a :: as) [] = RFalse (\x => x)
reflectAllCheck ctx (a :: as) (t :: ts) with (reflectChecks ctx a t) | (checks ctx a t)
  _ | RTrue tTy | _ with (reflectAllCheck ctx as ts) | (allCheck ctx as ts)
    _ | RTrue tsTy | _ = RTrue (tTy, tsTy)
    _ | RFalse tsBad | _ = RFalse (\(_, tsTy) => tsBad tsTy)
  _ | RFalse tBad | _ = RFalse (\(tTy, _) => tBad tTy)

reflectAllCheckBinding ctx [] b [] = RTrue ()
reflectAllCheckBinding ctx [] b (t :: ts) = RFalse (\x => x)
reflectAllCheckBinding ctx (a :: as) b [] = RFalse (\x => x)
reflectAllCheckBinding ctx (a :: as) b (t :: ts) with (reflectChecks (a :: ctx) b t) | (checks (a :: ctx) b t)
  _ | RTrue tTy | _ with (reflectAllCheckBinding ctx as b ts) | (allCheckBinding ctx as b ts)
    _ | RTrue tsTy | _ = RTrue (tTy, tsTy)
    _ | RFalse tsBad | _ = RFalse (\(_, tsTy) => tsBad tsTy)
  _ | RFalse tBad | _ = RFalse (\(tTy, _) => tBad tTy)
