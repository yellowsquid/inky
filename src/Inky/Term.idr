module Inky.Term

import Data.Bool.Decidable
import Data.DPair
import Data.Maybe.Decidable
import Data.List
import Inky.Context
import Inky.Thinning
import Inky.Type

--------------------------------------------------------------------------------
-- Definition ------------------------------------------------------------------
--------------------------------------------------------------------------------

public export
data SynthTerm : (tyCtx, tmCtx : Context ()) -> Type
public export
data CheckTerm : (tyCtx, tmCtx : Context ()) -> Type

data SynthTerm where
  Var : Var tmCtx v -> SynthTerm tyCtx tmCtx
  Lit : Nat -> SynthTerm tyCtx tmCtx
  Suc : CheckTerm tyCtx tmCtx -> SynthTerm tyCtx tmCtx
  App :
    SynthTerm tyCtx tmCtx ->
    (args : List (CheckTerm tyCtx tmCtx)) ->
    {auto 0 _ : NonEmpty args} ->
    SynthTerm tyCtx tmCtx
  Prj : SynthTerm tyCtx tmCtx -> String -> SynthTerm tyCtx tmCtx
  Expand : SynthTerm tyCtx tmCtx -> SynthTerm tyCtx tmCtx
  Annot : CheckTerm tyCtx tmCtx -> Ty tyCtx () -> SynthTerm tyCtx tmCtx

data CheckTerm where
  Let :
    (x : String) -> SynthTerm tyCtx tmCtx ->
    CheckTerm tyCtx (tmCtx :< (x :- ())) ->
    CheckTerm tyCtx tmCtx
  Abs : (bound : Context ()) -> CheckTerm tyCtx (tmCtx ++ bound) -> CheckTerm tyCtx tmCtx
  Inj : String -> CheckTerm tyCtx tmCtx -> CheckTerm tyCtx tmCtx
  Tup : Context (CheckTerm tyCtx tmCtx) -> CheckTerm tyCtx tmCtx
  Case :
    SynthTerm tyCtx tmCtx ->
    Context (x ** CheckTerm tyCtx (tmCtx :< (x :- ()))) ->
    CheckTerm tyCtx tmCtx
  Contract : CheckTerm tyCtx tmCtx -> CheckTerm tyCtx tmCtx
  Fold :
    SynthTerm tyCtx tmCtx ->
    (x : String) -> CheckTerm tyCtx (tmCtx :< (x :- ())) ->
    CheckTerm tyCtx tmCtx
  Embed :
    SynthTerm tyCtx tmCtx ->
    CheckTerm tyCtx tmCtx

%name SynthTerm e
%name CheckTerm t, u, v

--------------------------------------------------------------------------------
-- Well Formed -----------------------------------------------------------------
--------------------------------------------------------------------------------

-- Lookup name in a row --------------------------------------------------------

GetAt : String -> Row a -> a -> Type
GetAt x ys y = VarPos (forget ys) x y

getAtUnique :
  (x : String) -> (ys : Row a) ->
  GetAt x ys y -> GetAt x ys z -> y = z
getAtUnique x (row :< (x :- b)) Here Here = Refl
getAtUnique x ((:<) row (x :- a) {fresh}) Here (There pos2) = void $ varPosNotFresh pos2 fresh
getAtUnique x ((:<) row (x :- b) {fresh}) (There pos1) Here = void $ varPosNotFresh pos1 fresh
getAtUnique x (row :< (y :- v)) (There pos1) (There pos2) = getAtUnique x row pos1 pos2

getAt : String -> Row a -> Maybe a
getAt x as = fst <$> remove' x as

0 reflectGetAt : (x : String) -> (ys : Row a) -> GetAt x ys `OnlyWhen` getAt x ys
reflectGetAt x ys with (reflectRemove x ys) | (remove' x ys)
  _ | RJust (Evidence fresh prf) | Just (y, _) = RJust (equivVarPos (sym prf) Here)
  _ | RNothing nprf | _ =
    RNothing (\y, pos =>
      nprf (y, snd (removePos ys pos)) $
      Evidence (removedIsFresh ys pos) (sym $ reflectRemovePos ys pos))

-- Test if we have an arrow ----------------------------------------------------

IsArrow : Ty tyCtx () -> Ty tyCtx () -> Ty tyCtx () -> Type
IsArrow (TArrow a b) c d = (c = a, d = b)
IsArrow _ c d = Void

isArrowUnique : (a : Ty tyCtx ()) -> IsArrow a b c -> IsArrow a d e -> (b = d, c = e)
isArrowUnique (TArrow a b) (Refl, Refl) (Refl, Refl) = (Refl, Refl)

isArrow : Ty tyCtx () -> Maybe (Ty tyCtx (), Ty tyCtx ())
isArrow (TArrow a b) = Just (a, b)
isArrow _ = Nothing

reflectIsArrow : (a : Ty tyCtx ()) -> uncurry (IsArrow a) `OnlyWhen` isArrow a
reflectIsArrow (TArrow a b) = RJust (Refl, Refl)
reflectIsArrow (TVar i) = RNothing (\(_, _), x => x)
reflectIsArrow TNat = RNothing (\(_, _), x => x)
reflectIsArrow (TProd as) = RNothing (\(_, _), x => x)
reflectIsArrow (TSum as) = RNothing (\(_, _), x => x)
reflectIsArrow (TFix x a) = RNothing (\(_, _), x => x)

-- Test if we have a product ---------------------------------------------------

IsProduct : Ty tyCtx () -> Row (Ty tyCtx ()) -> Type
IsProduct (TProd as) bs = bs = as
IsProduct _ bs = Void

isProductUnique : (a : Ty tyCtx ()) -> IsProduct a as -> IsProduct a bs -> as = bs
isProductUnique (TProd as) Refl Refl = Refl

isProduct : Ty tyCtx () -> Maybe (Row (Ty tyCtx ()))
isProduct (TProd as) = Just as
isProduct _ = Nothing

reflectIsProduct : (a : Ty tyCtx ()) -> IsProduct a `OnlyWhen` isProduct a
reflectIsProduct (TVar i) = RNothing (\_, x => x)
reflectIsProduct TNat = RNothing (\_, x => x)
reflectIsProduct (TArrow a b) = RNothing (\_, x => x)
reflectIsProduct (TProd as) = RJust Refl
reflectIsProduct (TSum as) = RNothing (\_, x => x)
reflectIsProduct (TFix x a) = RNothing (\_, x => x)

-- Test if we have a sum -------------------------------------------------------

IsSum : Ty tyCtx () -> Row (Ty tyCtx ()) -> Type
IsSum (TSum as) bs = bs = as
IsSum _ bs = Void

isSumUnique : (a : Ty tyCtx ()) -> IsSum a as -> IsSum a bs -> as = bs
isSumUnique (TSum as) Refl Refl = Refl

isSum : Ty tyCtx () -> Maybe (Row (Ty tyCtx ()))
isSum (TSum as) = Just as
isSum _ = Nothing

reflectIsSum : (a : Ty tyCtx ()) -> IsSum a `OnlyWhen` isSum a
reflectIsSum (TVar i) = RNothing (\_, x => x)
reflectIsSum TNat = RNothing (\_, x => x)
reflectIsSum (TArrow a b) = RNothing (\_, x => x)
reflectIsSum (TProd as) = RNothing (\_, x => x)
reflectIsSum (TSum as) = RJust Refl
reflectIsSum (TFix x a) = RNothing (\_, x => x)

-- Test if we have a fixpoint --------------------------------------------------

IsFixpoint : Ty tyCtx () -> (x ** Ty (tyCtx :< (x :- ())) ()) -> Type
IsFixpoint TNat yb = (fst yb = "X", snd yb = TSum [<"Z" :- TProd [<], "S" :- TVar (%% fst yb)])
IsFixpoint (TFix x a) yb = (prf : (fst yb = x) ** (snd yb = (rewrite prf in a)))
IsFixpoint _ yb = Void

isFixpointUnique : (a : Ty tyCtx ()) -> IsFixpoint a xb -> IsFixpoint a yc -> xb = yc
isFixpointUnique TNat {xb = (_ ** _), yc = (_ ** _)} (Refl, Refl) (Refl, Refl) = Refl
isFixpointUnique (TFix x a) {xb = (x ** a), yc = (x ** a)} (Refl ** Refl) (Refl ** Refl) = Refl

isFixpoint : Ty tyCtx () -> Maybe (x ** Ty (tyCtx :< (x :- ())) ())
isFixpoint TNat = Just ("X" ** TSum [<("Z" :- TProd [<]), ("S" :- TVar (%% "X"))])
isFixpoint (TFix x a) = Just (x ** a)
isFixpoint _ = Nothing

reflectIsFixpoint : (a : Ty tyCtx ()) -> IsFixpoint a `OnlyWhen` isFixpoint a
reflectIsFixpoint (TVar i) = RNothing (\_, x => x)
reflectIsFixpoint TNat = RJust (Refl, Refl)
reflectIsFixpoint (TArrow a b) = RNothing (\_, x => x)
reflectIsFixpoint (TProd as) = RNothing (\_, x => x)
reflectIsFixpoint (TSum as) = RNothing (\_, x => x)
reflectIsFixpoint (TFix x a) = RJust (Refl ** Refl)

-- Test if we have a function, collecting the bound types ----------------------

IsFunction :
  {tyCtx : Context ()} ->
  (bound : Context ()) -> (fun : Ty tyCtx ()) ->
  (dom : All (const $ Ty tyCtx ()) bound) -> (cod : Ty tyCtx ()) ->
  Type
IsFunction [<] fun dom cod = (dom = [<], cod = fun)
IsFunction (bound :< (x :- ())) fun dom cod =
  ( b ** c **
  ( IsArrow fun b c
  , ( dom' **
    ( dom = dom' :< (x :- b)
    , IsFunction bound c dom' cod
    ))
  ))


isFunctionUnique :
  (bound : Context ()) -> (a : Ty tyCtx ()) ->
  forall dom1, dom2, cod1, cod2.
  IsFunction bound a dom1 cod1 -> IsFunction bound a dom2 cod2 -> (dom1 = dom2, cod1 = cod2)
isFunctionUnique [<] a (Refl, Refl) (Refl, Refl) = (Refl, Refl)
isFunctionUnique (bound :< (x :- ())) a
  (b1 ** c1 ** (isArrow1, (dom1' ** (Refl, isFunc1))))
  (b2 ** c2 ** (isArrow2, (dom2' ** (Refl, isFunc2))))
  with (isArrowUnique a isArrow1 isArrow2)
  isFunctionUnique (bound :< (x :- ())) a
    (b ** c ** (_, (dom1' ** (Refl, isFunc1))))
    (b ** c ** (_, (dom2' ** (Refl, isFunc2))))
    | (Refl, Refl)
    with (isFunctionUnique bound c isFunc1 isFunc2)
    isFunctionUnique (bound :< (x :- ())) a
      (b ** c ** (_, (dom' ** (Refl, _))))
      (b ** c ** (_, (dom' ** (Refl, _))))
      | (Refl, Refl) | (Refl, Refl) = (Refl, Refl)

isFunction :
  (bound : Context ()) -> Ty tyCtx () ->
  Maybe (All (const $ Ty tyCtx ()) bound, Ty tyCtx ())
isFunction [<] a = Just ([<], a)
isFunction (bound :< (x :- ())) a = do
  (b, c) <- isArrow a
  (dom, cod) <- isFunction bound c
  Just (dom :< (x :- b), cod)

reflectIsFunction :
  (bound : Context ()) -> (a : Ty tyCtx ()) ->
  uncurry (IsFunction bound a) `OnlyWhen` isFunction bound a
reflectIsFunction [<] a = RJust (Refl, Refl)
reflectIsFunction (bound :< (x :- ())) a with (reflectIsArrow a) | (isArrow a)
  _ | RJust isArrow | Just (b, c) with (reflectIsFunction bound c) | (isFunction bound c)
    _ | RJust isFunc | Just (dom, cod) = RJust (b ** c ** (isArrow , (dom ** (Refl, isFunc))))
    _ | RNothing notFunc | _ =
      RNothing (\(dom :< (x :- b'), cod), (b' ** c' ** (isArrow', (dom ** (Refl, isFunc)))) =>
        let (eq1, eq2) = isArrowUnique a {b, c, d = b', e = c'} isArrow isArrow' in
        let isFunc = rewrite eq2 in isFunc in
        notFunc (dom, cod) isFunc)
  _ | RNothing notArrow | _ =
    RNothing (\(dom, cod), (b ** c ** (isArrow, _)) => notArrow (b, c) isArrow)

-- Full type checking and synthesis --------------------------------------------

Synths :
  {tyCtx, tmCtx : Context ()} -> (env : All (const (Ty tyCtx ())) tmCtx) ->
  SynthTerm tyCtx tmCtx -> Ty tyCtx () -> Type
Checks :
  {tyCtx, tmCtx : Context ()} -> (env : All (const (Ty tyCtx ())) tmCtx) ->
  Ty tyCtx () -> CheckTerm tyCtx tmCtx -> Type
CheckSpine :
  {tyCtx, tmCtx : Context ()} -> (env : All (const (Ty tyCtx ())) tmCtx) ->
  (fun : Ty tyCtx ()) -> List (CheckTerm tyCtx tmCtx) -> (res : Ty tyCtx ()) -> Type
AllCheck :
  {tyCtx, tmCtx : Context ()} -> (env : All (const (Ty tyCtx ())) tmCtx) ->
  Row (Ty tyCtx ()) -> Context (CheckTerm tyCtx tmCtx) -> Type
AllCheckBinding :
  {tyCtx, tmCtx : Context ()} -> (env : All (const (Ty tyCtx ())) tmCtx) ->
  Row (Ty tyCtx ()) -> Ty tyCtx () ->
  Context (x : String ** CheckTerm tyCtx (tmCtx :< (x :- ()))) ->
  Type

Synths env (Var i) a = (a = indexAll i env)
Synths env (Lit k) a = (a = TNat)
Synths env (Suc t) a = (Checks env TNat t, a = TNat)
Synths env (App e ts) a =
  ( fun **
  ( Synths env e fun
  , CheckSpine env fun ts a
  ))
Synths env (Prj e x) a =
  ( b **
  ( Synths env e b
  , ( as **
    ( IsProduct b as
    , GetAt x as a
    ))
  ))
Synths env (Expand e) a =
  ( b **
  ( Synths env e b
  , ( xc **
    ( IsFixpoint b xc
    , a = sub (Base Id :< (fst xc :- b)) (snd xc)
    ))
  ))
Synths env (Annot t a) b =
  ( Not (IllFormed a)
  , Checks env a t
  , a = b
  )

Checks env a (Let x e t) =
  ( b **
  ( Synths env e b
  , Checks (env :< (x :- b)) a t
  ))
Checks env a (Abs bound t) =
  ( as ** b **
  ( IsFunction bound a as b
  , Checks (env ++ as) b t
  ))
Checks env a (Inj x t) =
  ( as **
  ( IsSum a as
  , ( b **
    ( GetAt x as b
    , Checks env b t
    ))
  ))
Checks env a (Tup ts) =
  ( as **
  ( IsProduct a as
  , AllCheck env as ts
  ))
Checks env a (Case e ts) =
  ( b **
  ( Synths env e b
  , ( as **
    ( IsSum b as
    , AllCheckBinding env as a ts
    ))
  ))
Checks env a (Contract t) =
  ( xb **
  ( IsFixpoint a xb
  , Checks env (sub (Base Id :< (fst xb :- a)) (snd xb)) t
  ))
Checks env a (Fold e x t) =
  ( b **
  ( Synths env e b
  , ( yc **
    ( IsFixpoint b yc
    , Checks (env :< (x :- sub (Base Id :< (fst yc :- a)) (snd yc))) a t
    ))
  ))
Checks env a (Embed e) =
  ( b **
  ( Synths env e b
  , a `Eq` b
  ))

CheckSpine env fun [] res = fun = res
CheckSpine env fun (t :: ts) res =
  ( a ** b **
  ( IsArrow fun a b
  , Checks env a t
  , CheckSpine env b ts res
  ))

AllCheck env as [<] = (as = [<])
AllCheck env as (ts :< (x :- t)) =
  ( a ** bs **
  ( Remove x as a bs
  , Checks env a t
  , AllCheck env bs ts
  ))

AllCheckBinding env as a [<] = (as = [<])
AllCheckBinding env as a (ts :< (x :- (y ** t))) =
  ( b ** bs **
  ( Remove x as b bs
  , Checks (env :< (y :- b)) a t
  , AllCheckBinding env bs a ts
  ))

-- Reordering

allCheckReorder :
  as <~> bs -> (ts : Context (CheckTerm tyCtx tmCtx)) ->
  AllCheck env as ts -> AllCheck env bs ts
allCheckReorder [] [<] Refl = Refl
allCheckReorder (_ :: _) [<] Refl impossible
allCheckReorder prf (ts :< (x :- t)) (a ** bs ** (prf1, prf2, prf3)) =
  (a ** bs ** (Evidence prf1.fst (trans (sym prf) prf1.snd), prf2, prf3))

allCheckBindingReorder :
  as <~> bs -> (ts : Context (x ** CheckTerm tyCtx (tmCtx :< (x :- ())))) ->
  AllCheckBinding env as a ts -> AllCheckBinding env bs a ts
allCheckBindingReorder [] [<] Refl = Refl
allCheckBindingReorder (_ :: _) [<] Refl impossible
allCheckBindingReorder prf (ts :< (x :- (y ** t))) (b ** bs ** (prf1, prf2, prf3)) =
  (b ** bs ** (Evidence prf1.fst (trans (sym prf) prf1.snd), prf2, prf3))

-- Uniqueness

synthsUnique :
  (0 env : All (const $ Ty tyCtx ()) tmCtx) -> (e : SynthTerm tyCtx tmCtx) ->
  Synths env e a -> Synths env e b -> a = b
checkSpineUnique :
  (0 env : All (const $ Ty tyCtx ()) tmCtx) ->
  (fun : Ty tyCtx ()) -> (ts : List (CheckTerm tyCtx tmCtx)) ->
  CheckSpine env fun ts a -> CheckSpine env fun ts b -> a = b

synthsUnique env (Var i) prf1 prf2 = trans prf1 (sym prf2)
synthsUnique env (Lit k) prf1 prf2 = trans prf1 (sym prf2)
synthsUnique env (Suc t) (_, prf1) (_, prf2) = trans prf1 (sym prf2)
synthsUnique env (App e ts) (fun1 ** (prf11, prf12)) (fun2 ** (prf21, prf22))
  with (synthsUnique env e prf11 prf21)
  synthsUnique env (App e ts) (fun ** (prf11, prf12)) (fun ** (prf21, prf22)) | Refl =
    checkSpineUnique env fun ts prf12 prf22
synthsUnique env (Prj e k) (a ** (prf11, prf12)) (b ** (prf21, prf22))
  with (synthsUnique env e prf11 prf21)
  synthsUnique env (Prj e k) (a ** (_, (as ** (prf11, prf12)))) (a ** (_, (bs ** (prf21, prf22)))) | Refl
    with (isProductUnique a prf11 prf21)
    synthsUnique env (Prj e k) (a ** (_, (as ** (_, prf1)))) (a ** (_, (as ** (_, prf2)))) | Refl | Refl =
      getAtUnique k as prf1 prf2
synthsUnique env (Expand e) (a ** (prf11, prf12)) (b ** (prf21, prf22))
  with (synthsUnique env e prf11 prf21)
  synthsUnique env (Expand e) (a ** (_, (b ** (prf11, prf12)))) (a ** (_, (c ** (prf21, prf22)))) | Refl
    with (isFixpointUnique a prf11 prf21)
    synthsUnique env (Expand e) (a ** (_, (b ** (_, prf1)))) (a ** (_, (b ** (_, prf2)))) | Refl | Refl =
      trans prf1 (sym prf2)
synthsUnique env (Annot t c) prf1 prf2 = trans (sym $ snd $ snd prf1) (snd $ snd prf2)

checkSpineUnique env fun [] prf1 prf2 = trans (sym prf1) prf2
checkSpineUnique env fun (t :: ts) (a ** b ** (prf11, _ , prf12)) (c ** d ** (prf21, _ , prf22))
  with (isArrowUnique fun prf11 prf21)
  checkSpineUnique env fun (t :: ts) (a ** b ** (_, _ , prf1)) (a ** b ** (_, _ , prf2)) | (Refl, Refl) =
    checkSpineUnique env b ts prf1 prf2

-- Decision

synths :
  (env : All (const (Ty tyCtx ())) tmCtx) ->
  SynthTerm tyCtx tmCtx -> Maybe (Ty tyCtx ())
checks :
  (env : All (const (Ty tyCtx ())) tmCtx) ->
  Ty tyCtx () -> CheckTerm tyCtx tmCtx -> Bool
checkSpine :
  (env : All (const (Ty tyCtx ())) tmCtx) ->
  (fun : Ty tyCtx ()) -> List (CheckTerm tyCtx tmCtx) -> Maybe (Ty tyCtx ())
allCheck :
  (env : All (const (Ty tyCtx ())) tmCtx) ->
  Row (Ty tyCtx ()) -> Context (CheckTerm tyCtx tmCtx) -> Bool
allCheckBinding :
  (env : All (const (Ty tyCtx ())) tmCtx) ->
  Row (Ty tyCtx ()) -> Ty tyCtx () ->
  Context (x ** CheckTerm tyCtx (tmCtx :< (x :- ()))) ->
  Bool

synths env (Var i) = Just (indexAll i env)
synths env (Lit k) = Just TNat
synths env (Suc t) = do
  guard (checks env TNat t)
  Just TNat
synths env (App e ts) = do
  a <- synths env e
  checkSpine env a ts
synths env (Prj e k) = do
  a <- synths env e
  as <- isProduct a
  getAt k as
synths env (Expand e) = do
  a <- synths env e
  (x ** b) <- isFixpoint a
  Just (sub (Base Id :< (x :- a)) b)
synths env (Annot t a) = do
  guard (not $ illFormed a)
  guard (checks env a t)
  Just a

checks env a (Let x e t) =
  case synths env e of
    Just b => checks (env :< (x :- b)) a t
    Nothing => False
checks env a (Abs bound t) =
  case isFunction bound a of
    Just (dom, cod) => checks (env ++ dom) cod t
    Nothing => False
checks env a (Inj k t) =
  case isSum a of
    Just as =>
      case getAt k as of
        Just b => checks env b t
        Nothing => False
    Nothing => False
checks env a (Tup ts) =
  case isProduct a of
    Just as => allCheck env as ts
    Nothing => False
checks env a (Case e ts) =
  case synths env e of
    Just b =>
      case isSum b of
        Just as => allCheckBinding env as a ts
        Nothing => False
    Nothing => False
checks env a (Contract t) =
  case isFixpoint a of
    Just (x ** b) => checks env (sub (Base Id :< (x :- a)) b) t
    Nothing => False
checks env a (Fold e x t) =
  case synths env e of
    Just b =>
      case isFixpoint b of
        Just (y ** c) => checks (env :< (x :- sub (Base Id :< (y :- a)) c)) a t
        Nothing => False
    Nothing => False
checks env a (Embed e) =
  case synths env e of
    Just b => a == b
    Nothing => False

checkSpine env a [] = Just a
checkSpine env a (t :: ts) = do
  (dom, cod) <- isArrow a
  guard (checks env dom t)
  checkSpine env cod ts

allCheck env as [<] = null as
allCheck env as (ts :< (x :- t)) =
  case remove' x as of
    Just (a, bs) => checks env a t && allCheck env bs ts
    Nothing => False

allCheckBinding env as a [<] = null as
allCheckBinding env as a (ts :< (x :- (y ** t))) =
  case remove' x as of
    Just (b, bs) => checks (env :< (y :- b)) a t && allCheckBinding env bs a ts
    Nothing => False

-- Proof

-- FIXME: these are total; the termination checker is unreasonably slow.

partial
0 reflectSynths :
  (env : All (const $ Ty tyCtx ()) tmCtx) ->
  (e : SynthTerm tyCtx tmCtx) ->
  Synths env e `OnlyWhen` synths env e
partial
0 reflectChecks :
  (env : All (const $ Ty tyCtx ()) tmCtx) ->
  (a : Ty tyCtx ()) -> (t : CheckTerm tyCtx tmCtx) ->
  Checks env a t `Reflects` checks env a t
partial
0 reflectCheckSpine :
  (env : All (const $ Ty tyCtx ()) tmCtx) ->
  (fun : Ty tyCtx ()) -> (ts : List (CheckTerm tyCtx tmCtx)) ->
  CheckSpine env fun ts `OnlyWhen` checkSpine env fun ts
partial
0 reflectAllCheck :
  (env : All (const $ Ty tyCtx ()) tmCtx) ->
  (as : Row (Ty tyCtx ())) -> (ts : Context (CheckTerm tyCtx tmCtx)) ->
  AllCheck env as ts `Reflects` allCheck env as ts
partial
0 reflectAllCheckBinding :
  (env : All (const $ Ty tyCtx ()) tmCtx) ->
  (as : Row (Ty tyCtx ())) -> (a : Ty tyCtx ()) ->
  (ts : Context (x ** CheckTerm tyCtx (tmCtx :< (x :- ())))) ->
  AllCheckBinding env as a ts `Reflects` allCheckBinding env as a ts

reflectSynths env (Var i) = RJust Refl
reflectSynths env (Lit k) = RJust Refl
reflectSynths env (Suc t) with (reflectChecks env TNat t) | (checks env TNat t)
  _ | RTrue tNat | _ = RJust (tNat, Refl)
  _ | RFalse tNotNat | _ = RNothing (\_, (tNat, _) => tNotNat tNat)
reflectSynths env (App e ts) with (reflectSynths env e) | (synths env e)
  _ | RJust eTy | Just a with (reflectCheckSpine env a ts) | (checkSpine env a ts)
    _ | RJust tsSpine | Just b = RJust (a ** (eTy, tsSpine))
    _ | RNothing tsBad | _ =
      RNothing
        (\c, (b ** (eTy', tsSpine)) =>
          let tsSpine = rewrite synthsUnique env e {a, b} eTy eTy' in tsSpine in
          tsBad c tsSpine)
  _ | RNothing eBad | _ =
    RNothing (\c, (b ** (eTy, _)) => eBad b eTy)
reflectSynths env (Prj e x) with (reflectSynths env e) | (synths env e)
  _ | RJust eTy | Just a with (reflectIsProduct a) | (isProduct a)
    _ | RJust prf | Just as with (reflectGetAt x as) | (getAt x as)
      _ | RJust got | Just b = RJust (a ** (eTy, (as ** (prf, got))))
      _ | RNothing not | _ =
        RNothing (\x, (a' ** (eTy', (as' ** (prf', got)))) =>
          let prf' = rewrite synthsUnique env e {a, b = a'} eTy eTy' in prf' in
          let got = rewrite isProductUnique a {as, bs = as'} prf prf' in got in
          not x got)
    _ | RNothing nprf | _ =
      RNothing (\x, (a' ** (eTy', (as' ** (prf, _)))) =>
        let prf = rewrite synthsUnique env e {a, b = a'} eTy eTy' in prf in
        nprf as' prf)
  _ | RNothing eBad | _ = RNothing (\x, (a' ** (eTy, _)) => eBad a' eTy)
reflectSynths env (Expand e) with (reflectSynths env e) | (synths env e)
  _ | RJust eTy | Just a with (reflectIsFixpoint a) | (isFixpoint a)
    _ | RJust prf | Just (x ** b) = RJust (a ** (eTy, ((x ** b) ** (prf, Refl))))
    _ | RNothing nprf | _ =
      RNothing (\x, (a' ** (eTy', (b ** (prf, eq)))) =>
        let prf = rewrite synthsUnique env e {a, b = a'} eTy eTy' in prf in
        nprf b prf)
  _ | RNothing eBad | _ = RNothing (\x, (a ** (eTy, _)) => eBad a eTy)
reflectSynths env (Annot t a) with (reflectIllFormed a) | (illFormed a)
  _ | RFalse wf | _ with (reflectChecks env a t) | (checks env a t)
    _ | RTrue tTy | _ = RJust (wf, tTy, Refl)
    _ | RFalse tBad | _ = RNothing (\x, (_, tTy, Refl) => tBad tTy)
  _ | RTrue notWf | _ = RNothing (\x, (wf, _) => wf notWf)

reflectChecks env a (Let x e t) with (reflectSynths env e) | (synths env e)
  _ | RJust eTy | Just b with (reflectChecks (env :< (x :- b)) a t) | (checks (env :< (x :- b)) a t)
    _ | RTrue tTy | _ = RTrue (b ** (eTy, tTy))
    _ | RFalse tBad | _ =
      RFalse (\(b' ** (eTy', tTy)) =>
        let tTy = rewrite synthsUnique env e {a = b, b = b'} eTy eTy' in tTy in
        tBad tTy)
  _ | RNothing eBad | Nothing = RFalse (\(b ** (eTy, _)) => eBad b eTy)
reflectChecks env a (Abs bound t) with (reflectIsFunction bound a) | (isFunction bound a)
  _ | RJust prf | Just (as, b) with (reflectChecks (env ++ as) b t) | (checks (env ++ as) b t)
    _ | RTrue tTy | _ = RTrue (as ** b ** (prf, tTy))
    _ | RFalse tBad | _ =
      RFalse (\(as' ** b' ** (prf', tTy)) =>
        let
          (eq1, eq2) =
            isFunctionUnique bound a
              {dom1 = as, cod1 = b, dom2 = as', cod2 = b'}
              prf prf'
          tTy = rewrite eq1 in rewrite eq2 in tTy
        in
        tBad tTy)
  _ | RNothing nprf | _ = RFalse (\(as ** b ** (prf, _)) => nprf (as, b) prf)
reflectChecks env a (Inj k t) with (reflectIsSum a) | (isSum a)
  _ | RJust prf | Just as with (reflectGetAt k as) | (getAt k as)
    _ | RJust got | Just b with (reflectChecks env b t) | (checks env b t)
      _ | RTrue tTy | _ = RTrue (as ** (prf, (b ** (got, tTy))))
      _ | RFalse tBad | _ =
        RFalse (\(as' ** (prf', (b' ** (got', tTy)))) =>
          let got' = rewrite isSumUnique a {as, bs = as'} prf prf' in got' in
          let tTy = rewrite getAtUnique k as {y = b, z = b'} got got' in tTy in
          tBad tTy
          )
    _ | RNothing not | _ =
      RFalse (\(as' ** (prf', (b ** (got, _)))) =>
        let got = rewrite isSumUnique a {as, bs = as'} prf prf' in got in
        not b got)
  _ | RNothing nprf | _ = RFalse (\(as ** (prf, _)) => nprf as prf)
reflectChecks env a (Tup ts) with (reflectIsProduct a) | (isProduct a)
  _ | RJust prf | Just as with (reflectAllCheck env as ts) | (allCheck env as ts)
    _ | RTrue tsTy | _ = RTrue (as ** (prf, tsTy))
    _ | RFalse tsBad | _ =
      RFalse (\(as' ** (prf', tsTy)) =>
        let tsTy = rewrite isProductUnique a {as, bs = as'} prf prf' in tsTy in
        tsBad tsTy)
  _ | RNothing nprf | _ = RFalse (\(as ** (prf, _)) => nprf as prf)
reflectChecks env a (Case e ts) with (reflectSynths env e) | (synths env e)
  _ | RJust eTy | Just b with (reflectIsSum b) | (isSum b)
    _ | RJust prf | Just as with (reflectAllCheckBinding env as a ts) | (allCheckBinding env as a ts)
      _ | RTrue tsTy | _ = RTrue (b ** (eTy, (as ** (prf, tsTy))))
      _ | RFalse tsBad | _ =
        RFalse
          (\(b' ** (eTy', (as' ** (prf', tsTy)))) =>
            let prf' = rewrite synthsUnique env e {a = b, b = b'} eTy eTy' in prf' in
            let tsTy = rewrite isSumUnique b {as, bs = as'} prf prf' in tsTy in
            tsBad tsTy)
    _ | RNothing nprf | _ =
      RFalse (\(b' ** (eTy', (as ** (prf, _)))) =>
        let prf = rewrite synthsUnique env e {a = b, b = b'} eTy eTy' in prf in
        nprf as prf)
  _ | RNothing eBad | _ = RFalse (\(b ** (eTy, _)) => eBad b eTy)
reflectChecks env a (Contract t) with (reflectIsFixpoint a) | (isFixpoint a)
  _ | RJust prf | Just (x ** b) with (reflectChecks env (sub (Base Id :< (x :- a)) b) t) | (checks env (sub (Base Id :< (x :- a)) b) t)
    _ | RTrue tTy | _ = RTrue ((x ** b) ** (prf, tTy))
    _ | RFalse tBad | _ =
      RFalse (\(b' ** (prf', tTy)) =>
        let
          eq = isFixpointUnique a {xb = (x ** b), yc = b'} prf prf'
          tTy =
            replace {p = \xb => Checks env (sub (Base Id :< (xb.fst :- a)) xb.snd) t}
              (sym eq) tTy
        in
        tBad tTy)
  _ | RNothing nprf | _ = RFalse (\(b ** (prf, _)) => nprf b prf)
reflectChecks env a (Fold e x t) with (reflectSynths env e) | (synths env e)
  _ | RJust eTy | Just b with (reflectIsFixpoint b) | (isFixpoint b)
    _ | RJust prf | Just (y ** c) with (reflectChecks (env :< (x :- sub (Base Id :< (y :- a)) c)) a t) | (checks (env :< (x :- sub (Base Id :< (y :- a)) c)) a t)
      _ | RTrue tTy | _ = RTrue (b ** (eTy, ((y ** c) ** (prf, tTy))))
      _ | RFalse tBad | _ =
        RFalse (\(b' ** (eTy', (c' ** (prf', tTy)))) =>
          let
            prf' = rewrite synthsUnique env e {a = b, b = b'} eTy eTy' in prf'
            eq = isFixpointUnique b {xb = (y ** c), yc = c'} prf prf'
            tTy =
              replace {p = \yc => Checks (env :< (x :- sub (Base Id :< (yc.fst :- a)) yc.snd)) a t}
                (sym eq) tTy
          in
          tBad tTy)
    _ | RNothing nprf | _ =
      RFalse (\(b' ** (eTy', (c ** (prf, _)))) =>
        let prf = rewrite synthsUnique env e {a = b, b = b'} eTy eTy' in prf in
        nprf c prf)
  _ | RNothing eBad | _ = RFalse (\(b ** (eTy, _)) => eBad b eTy)
reflectChecks env a (Embed e) with (reflectSynths env e) | (synths env e)
  _ | RJust eTy | Just b with (reflectEq a b) | (a == b)
    _ | RTrue eq | _ = RTrue (b ** (eTy, eq))
    _ | RFalse neq | _ =
      RFalse (\(b' ** (eTy', eq)) =>
        let eq = rewrite synthsUnique env e {a = b, b = b'} eTy eTy' in eq in
        neq eq)
  _ | RNothing eBad | _ = RFalse (\(b ** (eTy, _)) => eBad b eTy)

reflectCheckSpine env a [] = RJust Refl
reflectCheckSpine env a (t :: ts) with (reflectIsArrow a) | (isArrow a)
  _ | RJust prf | Just (b, c) with (reflectChecks env b t) | (checks env b t)
    _ | RTrue tTy | _ with (reflectCheckSpine env c ts) | (checkSpine env c ts)
      _ | RJust tsTy | Just d = RJust (b ** c ** (prf, tTy, tsTy))
      _ | RNothing tsBad | _ =
        RNothing (\d, (_ ** c' ** (prf', _, tsTy)) =>
          let (eq1, eq2) = isArrowUnique a {c, e = c'} prf prf' in
          let tsTy = rewrite eq2 in tsTy in
          tsBad d tsTy)
    _ | RFalse tBad | _ =
      RNothing (\d, (b' ** _ ** (prf', tTy, _)) =>
        let (eq1, eq2) = isArrowUnique a {b, d = b'} prf prf' in
        let tTy = rewrite eq1 in tTy in
        tBad tTy)
  _ | RNothing nprf | _ = RNothing (\d, (b ** c ** (prf, _)) => nprf (b, c) prf)

reflectAllCheck env [<] [<] = RTrue Refl
reflectAllCheck env (_ :< _) [<] = RFalse (\case Refl impossible)
reflectAllCheck env as (ts :< (x :- t)) with (reflectRemove x as) | (remove' x as)
  _ | RJust prf | Just (a, bs) with (reflectAnd (reflectChecks env a t) (reflectAllCheck env bs ts)) | (checks env a t && allCheck env bs ts)
    _ | RTrue checks | _ = RTrue (a ** bs ** (prf, checks))
    _ | RFalse notChecks | _ =
      RFalse (\(a' ** bs' ** (prf', checks)) =>
        let (eq, reorder) = removeUnique x as prf prf' in
        notChecks $
        bimap (\x => rewrite eq in x) (allCheckReorder (sym reorder) ts) checks)
  _ | RNothing nprf | _ = RFalse (\(a ** bs ** (prf, _)) => nprf (a, bs) prf)

reflectAllCheckBinding env [<] a [<] = RTrue Refl
reflectAllCheckBinding env (_ :< _) a [<] = RFalse (\case Refl impossible)
reflectAllCheckBinding env as a (ts :< (x :- (y ** t))) with (reflectRemove x as) | (remove' x as)
  _ | RJust prf | Just (b, bs) with (reflectAnd (reflectChecks (env :< (y :- b)) a t) (reflectAllCheckBinding env bs a ts)) | (checks (env :< (y :- b)) a t && allCheckBinding env bs a ts)
    _ | RTrue checks | _ = RTrue (b ** bs ** (prf, checks))
    _ | RFalse notChecks | _ =
      RFalse (\(b' ** bs' ** (prf', checks)) =>
        let (eq, reorder) = removeUnique x as prf prf' in
        notChecks $
        bimap (\x => rewrite eq in x) (allCheckBindingReorder (sym reorder) ts) checks)
  _ | RNothing nprf | _ = RFalse (\(b ** bs ** (prf, _)) => nprf (b, bs) prf)
