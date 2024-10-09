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
  Suc : SynthTerm tyCtx tmCtx
  App :
    SynthTerm tyCtx tmCtx ->
    (args : List (CheckTerm tyCtx tmCtx)) ->
    {auto 0 prf : NonEmpty args} ->
    SynthTerm tyCtx tmCtx
  Prj : SynthTerm tyCtx tmCtx -> String -> SynthTerm tyCtx tmCtx
  Expand : SynthTerm tyCtx tmCtx -> SynthTerm tyCtx tmCtx
  Annot : CheckTerm tyCtx tmCtx -> Ty tyCtx () -> SynthTerm tyCtx tmCtx

data CheckTerm where
  LetTy :
    (x : String) -> Ty tyCtx () ->
    CheckTerm (tyCtx :< (x :- ())) tmCtx ->
    CheckTerm tyCtx tmCtx
  Let :
    (x : String) -> SynthTerm tyCtx tmCtx ->
    CheckTerm tyCtx (tmCtx :< (x :- ())) ->
    CheckTerm tyCtx tmCtx
  Abs : (bound : Context ()) -> CheckTerm tyCtx (tmCtx ++ bound) -> CheckTerm tyCtx tmCtx
  Inj : String -> CheckTerm tyCtx tmCtx -> CheckTerm tyCtx tmCtx
  Tup : Row (CheckTerm tyCtx tmCtx) -> CheckTerm tyCtx tmCtx
  Case :
    SynthTerm tyCtx tmCtx ->
    Row (x ** CheckTerm tyCtx (tmCtx :< (x :- ()))) ->
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
  ( dom' ** cod' **
  ( IsFunction bound fun dom' cod'
  , ( b **
    ( IsArrow cod' b cod
    , dom = dom' :< (x :- b)
    ))
  ))

isFunctionUnique :
  (bound : Context ()) -> (a : Ty tyCtx ()) ->
  forall dom1, dom2, cod1, cod2.
  IsFunction bound a dom1 cod1 -> IsFunction bound a dom2 cod2 -> (dom1 = dom2, cod1 = cod2)
isFunctionUnique [<] a (Refl, Refl) (Refl, Refl) = (Refl, Refl)
isFunctionUnique (bound :< (x :- ())) a
  (dom1 ** cod1 ** (isFunc1, (b1 ** (isArrow1, eq1))))
  (dom2 ** cod2 ** (isFunc2, (b2 ** (isArrow2, eq2))))
  with (isFunctionUnique bound a isFunc1 isFunc2)
  isFunctionUnique (bound :< (x :- ())) a
    (dom ** cod ** (_, (b1 ** (isArrow1, eq1))))
    (dom ** cod ** (_, (b2 ** (isArrow2, eq2))))
    | (Refl, Refl)
    with (isArrowUnique cod isArrow1 isArrow2)
    isFunctionUnique (bound :< (x :- ())) a
      (dom ** cod ** (_, (b ** (isArrow1, Refl))))
      (dom ** cod ** (_, (b ** (isArrow2, Refl))))
      | (Refl, Refl) | (Refl, Refl) = (Refl, Refl)

isFunction :
  (bound : Context ()) -> Ty tyCtx () ->
  Maybe (All (const $ Ty tyCtx ()) bound, Ty tyCtx ())
isFunction [<] a = Just ([<], a)
isFunction (bound :< (x :- ())) a = do
  (dom, cod) <- isFunction bound a
  (b, cod) <- isArrow cod
  Just (dom :< (x :- b), cod)

reflectIsFunction :
  (bound : Context ()) -> (a : Ty tyCtx ()) ->
  uncurry (IsFunction bound a) `OnlyWhen` isFunction bound a
reflectIsFunction [<] a = RJust (Refl, Refl)
reflectIsFunction (bound :< (x :- ())) a with (reflectIsFunction bound a) | (isFunction bound a)
  _ | RJust isFunc | Just (dom', cod') with (reflectIsArrow cod') | (isArrow cod')
    _ | RJust isArrow | Just (b, cod) = RJust (dom' ** cod' ** (isFunc , (b ** (isArrow, Refl))))
    _ | RNothing notArrow | _ =
      RNothing (\(dom :< (x :- b), cod), (dom ** cod'' ** (isFunc', (b ** (isArrow, Refl)))) =>
        let (eq1, eq2) = isFunctionUnique bound a {dom1 = dom', dom2 = dom, cod1 = cod', cod2 = cod''} isFunc isFunc' in
        let isArrow = rewrite eq2 in isArrow in
        notArrow (b, cod) isArrow)
  _ | RNothing notFunc | _ =
    RNothing (\(dom, cod), (dom' ** cod' ** (isFunc, _)) => notFunc (dom', cod') isFunc)

-- Full type checking and synthesis --------------------------------------------

Synths :
  {tmCtx : Context ()} ->
  (tyEnv : DEnv Ty tyCtx) ->
  (env : All (const $ Ty [<] ()) tmCtx) ->
  SynthTerm tyCtx tmCtx -> Ty [<] () -> Type
Checks :
  {tmCtx : Context ()} ->
  (tyEnv : DEnv Ty tyCtx) ->
  (env : All (const $ Ty [<] ()) tmCtx) ->
  Ty [<] () -> CheckTerm tyCtx tmCtx -> Type
CheckSpine :
  {tmCtx : Context ()} ->
  (tyEnv : DEnv Ty tyCtx) ->
  (env : All (const $ Ty [<] ()) tmCtx) ->
  (fun : Ty [<] ()) -> List (CheckTerm tyCtx tmCtx) -> (res : Ty [<] ()) -> Type
AllCheck :
  {tmCtx : Context ()} ->
  (tyEnv : DEnv Ty tyCtx) ->
  (env : All (const $ Ty [<] ()) tmCtx) ->
  Row (Ty [<] ()) -> Row (CheckTerm tyCtx tmCtx) -> Type
AllCheckBinding :
  {tmCtx : Context ()} ->
  (tyEnv : DEnv Ty tyCtx) ->
  (env : All (const $ Ty [<] ()) tmCtx) ->
  Row (Ty [<] ()) -> Ty [<] () ->
  Row (x : String ** CheckTerm tyCtx (tmCtx :< (x :- ()))) ->
  Type

Synths tyEnv env (Var i) a = (a = indexAll i env)
Synths tyEnv env (Lit k) a = (a = TNat)
Synths tyEnv env Suc a = (a = TArrow TNat TNat)
Synths tyEnv env (App e ts) a =
  ( fun **
  ( Synths tyEnv env e fun
  , CheckSpine tyEnv env fun ts a
  ))
Synths tyEnv env (Prj e x) a =
  ( b **
  ( Synths tyEnv env e b
  , ( as **
    ( IsProduct b as
    , GetAt x as a
    ))
  ))
Synths tyEnv env (Expand e) a =
  ( b **
  ( Synths tyEnv env e b
  , ( xc **
    ( IsFixpoint b xc
    , a = sub (Base Id :< (fst xc :- b)) (snd xc)
    ))
  ))
Synths tyEnv env (Annot t a) b =
  ( Not (IllFormed a)
  , Checks tyEnv env (expand tyEnv a) t
  , expand tyEnv a = b
  )

Checks tyEnv env a (LetTy x b t) =
  ( Not (IllFormed b)
  , Checks (tyEnv :< (x :- b)) env a t
  )
Checks tyEnv env a (Let x e t) =
  ( b **
  ( Synths tyEnv env e b
  , Checks tyEnv (env :< (x :- b)) a t
  ))
Checks tyEnv env a (Abs bound t) =
  ( as ** b **
  ( IsFunction bound a as b
  , Checks tyEnv (env ++ as) b t
  ))
Checks tyEnv env a (Inj x t) =
  ( as **
  ( IsSum a as
  , ( b **
    ( GetAt x as b
    , Checks tyEnv env b t
    ))
  ))
Checks tyEnv env a (Tup ts) =
  ( as **
  ( IsProduct a as
  , AllCheck tyEnv env as ts
  ))
Checks tyEnv env a (Case e ts) =
  ( b **
  ( Synths tyEnv env e b
  , ( as **
    ( IsSum b as
    , AllCheckBinding tyEnv env as a ts
    ))
  ))
Checks tyEnv env a (Contract t) =
  ( xb **
  ( IsFixpoint a xb
  , Checks tyEnv env (sub (Base Id :< (fst xb :- a)) (snd xb)) t
  ))
Checks tyEnv env a (Fold e x t) =
  ( b **
  ( Synths tyEnv env e b
  , ( yc **
    ( IsFixpoint b yc
    , Checks tyEnv (env :< (x :- sub (Base Id :< (fst yc :- a)) (snd yc))) a t
    ))
  ))
Checks tyEnv env a (Embed e) =
  ( b **
  ( Synths tyEnv env e b
  , a `Eq` b
  ))

CheckSpine tyEnv env fun [] res = fun = res
CheckSpine tyEnv env fun (t :: ts) res =
  ( a ** b **
  ( IsArrow fun a b
  , Checks tyEnv env a t
  , CheckSpine tyEnv env b ts res
  ))

AllCheck tyEnv env as [<] = (as = [<])
AllCheck tyEnv env as (ts :< (x :- t)) =
  ( a ** bs **
  ( Remove x as a bs
  , Checks tyEnv env a t
  , AllCheck tyEnv env bs ts
  ))

AllCheckBinding tyEnv env as a [<] = (as = [<])
AllCheckBinding tyEnv env as a (ts :< (x :- (y ** t))) =
  ( b ** bs **
  ( Remove x as b bs
  , Checks tyEnv (env :< (y :- b)) a t
  , AllCheckBinding tyEnv env bs a ts
  ))

-- Reordering

allCheckReorder :
  as <~> bs -> (ts : Row (CheckTerm tyCtx tmCtx)) ->
  AllCheck tyEnv env as ts -> AllCheck tyEnv env bs ts
allCheckReorder [] [<] Refl = Refl
allCheckReorder (_ :: _) [<] Refl impossible
allCheckReorder prf (ts :< (x :- t)) (a ** bs ** (prf1, prf2, prf3)) =
  (a ** bs ** (Evidence prf1.fst (trans (sym prf) prf1.snd), prf2, prf3))

allCheckBindingReorder :
  as <~> bs -> (ts : Row (x ** CheckTerm tyCtx (tmCtx :< (x :- ())))) ->
  AllCheckBinding tyEnv env as a ts -> AllCheckBinding tyEnv env bs a ts
allCheckBindingReorder [] [<] Refl = Refl
allCheckBindingReorder (_ :: _) [<] Refl impossible
allCheckBindingReorder prf (ts :< (x :- (y ** t))) (b ** bs ** (prf1, prf2, prf3)) =
  (b ** bs ** (Evidence prf1.fst (trans (sym prf) prf1.snd), prf2, prf3))

-- Uniqueness

synthsUnique :
  (0 tyEnv : DEnv Ty tyCtx) ->
  (0 env : All (const $ Ty [<] ()) tmCtx) ->
  (e : SynthTerm tyCtx tmCtx) ->
  Synths tyEnv env e a -> Synths tyEnv env e b -> a = b
checkSpineUnique :
  (0 tyEnv : DEnv Ty tyCtx) ->
  (0 env : All (const $ Ty [<] ()) tmCtx) ->
  (fun : Ty [<] ()) -> (ts : List (CheckTerm tyCtx tmCtx)) ->
  CheckSpine tyEnv env fun ts a -> CheckSpine tyEnv env fun ts b -> a = b

synthsUnique tyEnv env (Var i) prf1 prf2 = trans prf1 (sym prf2)
synthsUnique tyEnv env (Lit k) prf1 prf2 = trans prf1 (sym prf2)
synthsUnique tyEnv env Suc prf1 prf2 = trans prf1 (sym prf2)
synthsUnique tyEnv env (App e ts) (fun1 ** (prf11, prf12)) (fun2 ** (prf21, prf22))
  with (synthsUnique tyEnv env e prf11 prf21)
  synthsUnique tyEnv env (App e ts) (fun ** (prf11, prf12)) (fun ** (prf21, prf22)) | Refl =
    checkSpineUnique tyEnv env fun ts prf12 prf22
synthsUnique tyEnv env (Prj e k) (a ** (prf11, prf12)) (b ** (prf21, prf22))
  with (synthsUnique tyEnv env e prf11 prf21)
  synthsUnique tyEnv env (Prj e k) (a ** (_, (as ** (prf11, prf12)))) (a ** (_, (bs ** (prf21, prf22)))) | Refl
    with (isProductUnique a prf11 prf21)
    synthsUnique tyEnv env (Prj e k) (a ** (_, (as ** (_, prf1)))) (a ** (_, (as ** (_, prf2)))) | Refl | Refl =
      getAtUnique k as prf1 prf2
synthsUnique tyEnv env (Expand e) (a ** (prf11, prf12)) (b ** (prf21, prf22))
  with (synthsUnique tyEnv env e prf11 prf21)
  synthsUnique tyEnv env (Expand e) (a ** (_, (b ** (prf11, prf12)))) (a ** (_, (c ** (prf21, prf22)))) | Refl
    with (isFixpointUnique a prf11 prf21)
    synthsUnique tyEnv env (Expand e) (a ** (_, (b ** (_, prf1)))) (a ** (_, (b ** (_, prf2)))) | Refl | Refl =
      trans prf1 (sym prf2)
synthsUnique tyEnv env (Annot t c) prf1 prf2 = trans (sym $ snd $ snd prf1) (snd $ snd prf2)

checkSpineUnique tyEnv env fun [] prf1 prf2 = trans (sym prf1) prf2
checkSpineUnique tyEnv env fun (t :: ts) (a ** b ** (prf11, _ , prf12)) (c ** d ** (prf21, _ , prf22))
  with (isArrowUnique fun prf11 prf21)
  checkSpineUnique tyEnv env fun (t :: ts) (a ** b ** (_, _ , prf1)) (a ** b ** (_, _ , prf2)) | (Refl, Refl) =
    checkSpineUnique tyEnv env b ts prf1 prf2

-- Decision

synths :
  (tyEnv : DEnv Ty tyCtx) ->
  (env : All (const $ Ty [<] ()) tmCtx) ->
  SynthTerm tyCtx tmCtx -> Maybe (Ty [<] ())
export
checks :
  (tyEnv : DEnv Ty tyCtx) ->
  (env : All (const $ Ty [<] ()) tmCtx) ->
  Ty [<] () -> CheckTerm tyCtx tmCtx -> Bool
checkSpine :
  (tyEnv : DEnv Ty tyCtx) ->
  (env : All (const $ Ty [<] ()) tmCtx) ->
  (fun : Ty [<] ()) -> List (CheckTerm tyCtx tmCtx) -> Maybe (Ty [<] ())
allCheck :
  (tyEnv : DEnv Ty tyCtx) ->
  (env : All (const $ Ty [<] ()) tmCtx) ->
  Row (Ty [<] ()) -> Row (CheckTerm tyCtx tmCtx) -> Bool
allCheckBinding :
  (tyEnv : DEnv Ty tyCtx) ->
  (env : All (const $ Ty [<] ()) tmCtx) ->
  Row (Ty [<] ()) -> Ty [<] () ->
  Row (x ** CheckTerm tyCtx (tmCtx :< (x :- ()))) ->
  Bool

synths tyEnv env (Var i) = do
  pure (indexAll i env)
synths tyEnv env (Lit k) = do
  pure TNat
synths tyEnv env Suc = do
  pure (TArrow TNat TNat)
synths tyEnv env (App e ts) = do
  a <- synths tyEnv env e
  checkSpine tyEnv env a ts
synths tyEnv env (Prj e k) = do
  a <- synths tyEnv env e
  as <- isProduct a
  getAt k as
synths tyEnv env (Expand e) = do
  a <- synths tyEnv env e
  (x ** b) <- isFixpoint a
  Just (sub (Base Id :< (x :- a)) b)
synths tyEnv env (Annot t a) = do
  guard (not $ illFormed a)
  guard (checks tyEnv env (expand tyEnv a) t)
  Just (expand tyEnv a)

checks tyEnv env a (LetTy x b t) =
  not (illFormed b) &&
  checks (tyEnv :< (x :- b)) env a t
checks tyEnv env a (Let x e t) =
  case synths tyEnv env e of
    Just b => checks tyEnv (env :< (x :- b)) a t
    Nothing => False
checks tyEnv env a (Abs bound t) =
  case isFunction bound a of
    Just (dom, cod) => checks tyEnv (env ++ dom) cod t
    Nothing => False
checks tyEnv env a (Inj k t) =
  case isSum a of
    Just as =>
      case getAt k as of
        Just b => checks tyEnv env b t
        Nothing => False
    Nothing => False
checks tyEnv env a (Tup ts) =
  case isProduct a of
    Just as => allCheck tyEnv env as ts
    Nothing => False
checks tyEnv env a (Case e ts) =
  case synths tyEnv env e of
    Just b =>
      case isSum b of
        Just as => allCheckBinding tyEnv env as a ts
        Nothing => False
    Nothing => False
checks tyEnv env a (Contract t) =
  case isFixpoint a of
    Just (x ** b) => checks tyEnv env (sub (Base Id :< (x :- a)) b) t
    Nothing => False
checks tyEnv env a (Fold e x t) =
  case synths tyEnv env e of
    Just b =>
      case isFixpoint b of
        Just (y ** c) => checks tyEnv (env :< (x :- sub (Base Id :< (y :- a)) c)) a t
        Nothing => False
    Nothing => False
checks tyEnv env a (Embed e) =
  case synths tyEnv env e of
    Just b => a == b
    Nothing => False

checkSpine tyEnv env a [] = do
  pure a
checkSpine tyEnv env a (t :: ts) = do
  (dom, cod) <- isArrow a
  guard (checks tyEnv env dom t)
  checkSpine tyEnv env cod ts

allCheck tyEnv env as [<] = null as
allCheck tyEnv env as (ts :< (x :- t)) =
  case remove' x as of
    Just (a, bs) => checks tyEnv env a t && allCheck tyEnv env bs ts
    Nothing => False

allCheckBinding tyEnv env as a [<] = null as
allCheckBinding tyEnv env as a (ts :< (x :- (y ** t))) =
  case remove' x as of
    Just (b, bs) => checks tyEnv (env :< (y :- b)) a t && allCheckBinding tyEnv env bs a ts
    Nothing => False

-- Proof

-- FIXME: these are total; the termination checker is unreasonably slow.

partial
0 reflectSynths :
  (tyEnv : DEnv Ty tyCtx) ->
  (env : All (const $ Ty [<] ()) tmCtx) ->
  (e : SynthTerm tyCtx tmCtx) ->
  Synths tyEnv env e `OnlyWhen` synths tyEnv env e
partial
0 reflectChecks :
  (tyEnv : DEnv Ty tyCtx) ->
  (env : All (const $ Ty [<] ()) tmCtx) ->
  (a : Ty [<] ()) -> (t : CheckTerm tyCtx tmCtx) ->
  Checks tyEnv env a t `Reflects` checks tyEnv env a t
partial
0 reflectCheckSpine :
  (tyEnv : DEnv Ty tyCtx) ->
  (env : All (const $ Ty [<] ()) tmCtx) ->
  (fun : Ty [<] ()) -> (ts : List (CheckTerm tyCtx tmCtx)) ->
  CheckSpine tyEnv env fun ts `OnlyWhen` checkSpine tyEnv env fun ts
partial
0 reflectAllCheck :
  (tyEnv : DEnv Ty tyCtx) ->
  (env : All (const $ Ty [<] ()) tmCtx) ->
  (as : Row (Ty [<] ())) -> (ts : Row (CheckTerm tyCtx tmCtx)) ->
  AllCheck tyEnv env as ts `Reflects` allCheck tyEnv env as ts
partial
0 reflectAllCheckBinding :
  (tyEnv : DEnv Ty tyCtx) ->
  (env : All (const $ Ty [<] ()) tmCtx) ->
  (as : Row (Ty [<] ())) -> (a : Ty [<] ()) ->
  (ts : Row (x ** CheckTerm tyCtx (tmCtx :< (x :- ())))) ->
  AllCheckBinding tyEnv env as a ts `Reflects` allCheckBinding tyEnv env as a ts

reflectSynths tyEnv env (Var i) = RJust Refl
reflectSynths tyEnv env (Lit k) = RJust Refl
reflectSynths tyEnv env Suc = RJust Refl
reflectSynths tyEnv env (App e ts) with (reflectSynths tyEnv env e) | (synths tyEnv env e)
  _ | RJust eTy | Just a with (reflectCheckSpine tyEnv env a ts) | (checkSpine tyEnv env a ts)
    _ | RJust tsSpine | Just b = RJust (a ** (eTy, tsSpine))
    _ | RNothing tsBad | _ =
      RNothing
        (\c, (b ** (eTy', tsSpine)) =>
          let tsSpine = rewrite synthsUnique tyEnv env e {a, b} eTy eTy' in tsSpine in
          tsBad c tsSpine)
  _ | RNothing eBad | _ =
    RNothing (\c, (b ** (eTy, _)) => eBad b eTy)
reflectSynths tyEnv env (Prj e x) with (reflectSynths tyEnv env e) | (synths tyEnv env e)
  _ | RJust eTy | Just a with (reflectIsProduct a) | (isProduct a)
    _ | RJust prf | Just as with (reflectGetAt x as) | (getAt x as)
      _ | RJust got | Just b = RJust (a ** (eTy, (as ** (prf, got))))
      _ | RNothing not | _ =
        RNothing (\x, (a' ** (eTy', (as' ** (prf', got)))) =>
          let prf' = rewrite synthsUnique tyEnv env e {a, b = a'} eTy eTy' in prf' in
          let got = rewrite isProductUnique a {as, bs = as'} prf prf' in got in
          not x got)
    _ | RNothing nprf | _ =
      RNothing (\x, (a' ** (eTy', (as' ** (prf, _)))) =>
        let prf = rewrite synthsUnique tyEnv env e {a, b = a'} eTy eTy' in prf in
        nprf as' prf)
  _ | RNothing eBad | _ = RNothing (\x, (a' ** (eTy, _)) => eBad a' eTy)
reflectSynths tyEnv env (Expand e) with (reflectSynths tyEnv env e) | (synths tyEnv env e)
  _ | RJust eTy | Just a with (reflectIsFixpoint a) | (isFixpoint a)
    _ | RJust prf | Just (x ** b) = RJust (a ** (eTy, ((x ** b) ** (prf, Refl))))
    _ | RNothing nprf | _ =
      RNothing (\x, (a' ** (eTy', (b ** (prf, eq)))) =>
        let prf = rewrite synthsUnique tyEnv env e {a, b = a'} eTy eTy' in prf in
        nprf b prf)
  _ | RNothing eBad | _ = RNothing (\x, (a ** (eTy, _)) => eBad a eTy)
reflectSynths tyEnv env (Annot t a) with (reflectIllFormed a) | (illFormed a)
  _ | RFalse wf | _ with (reflectChecks tyEnv env (expand tyEnv a) t) | (checks tyEnv env (expand tyEnv a) t)
    _ | RTrue tTy | _ = RJust (wf, tTy, Refl)
    _ | RFalse tBad | _ = RNothing (\x, (_, tTy, Refl) => tBad tTy)
  _ | RTrue notWf | _ = RNothing (\x, (wf, _) => wf notWf)

reflectChecks tyEnv env a (LetTy x b t) with (reflectIllFormed b) | (illFormed b)
  _ | RFalse wf | _ with (reflectChecks (tyEnv :< (x :- b)) env a t) | (checks (tyEnv :< (x :- b)) env a t)
    _ | RTrue tTy | _ = RTrue (wf, tTy)
    _ | RFalse tBad | _ = RFalse (tBad . snd)
  _ | RTrue notWf | _ = RFalse (\(wf, _) => wf notWf)
reflectChecks tyEnv env a (Let x e t) with (reflectSynths tyEnv env e) | (synths tyEnv env e)
  _ | RJust eTy | Just b with (reflectChecks tyEnv (env :< (x :- b)) a t) | (checks tyEnv (env :< (x :- b)) a t)
    _ | RTrue tTy | _ = RTrue (b ** (eTy, tTy))
    _ | RFalse tBad | _ =
      RFalse (\(b' ** (eTy', tTy)) =>
        let tTy = rewrite synthsUnique tyEnv env e {a = b, b = b'} eTy eTy' in tTy in
        tBad tTy)
  _ | RNothing eBad | Nothing = RFalse (\(b ** (eTy, _)) => eBad b eTy)
reflectChecks tyEnv env a (Abs bound t) with (reflectIsFunction bound a) | (isFunction bound a)
  _ | RJust prf | Just (as, b) with (reflectChecks tyEnv (env ++ as) b t) | (checks tyEnv (env ++ as) b t)
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
reflectChecks tyEnv env a (Inj k t) with (reflectIsSum a) | (isSum a)
  _ | RJust prf | Just as with (reflectGetAt k as) | (getAt k as)
    _ | RJust got | Just b with (reflectChecks tyEnv env b t) | (checks tyEnv env b t)
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
reflectChecks tyEnv env a (Tup ts) with (reflectIsProduct a) | (isProduct a)
  _ | RJust prf | Just as with (reflectAllCheck tyEnv env as ts) | (allCheck tyEnv env as ts)
    _ | RTrue tsTy | _ = RTrue (as ** (prf, tsTy))
    _ | RFalse tsBad | _ =
      RFalse (\(as' ** (prf', tsTy)) =>
        let tsTy = rewrite isProductUnique a {as, bs = as'} prf prf' in tsTy in
        tsBad tsTy)
  _ | RNothing nprf | _ = RFalse (\(as ** (prf, _)) => nprf as prf)
reflectChecks tyEnv env a (Case e ts) with (reflectSynths tyEnv env e) | (synths tyEnv env e)
  _ | RJust eTy | Just b with (reflectIsSum b) | (isSum b)
    _ | RJust prf | Just as with (reflectAllCheckBinding tyEnv env as a ts) | (allCheckBinding tyEnv env as a ts)
      _ | RTrue tsTy | _ = RTrue (b ** (eTy, (as ** (prf, tsTy))))
      _ | RFalse tsBad | _ =
        RFalse
          (\(b' ** (eTy', (as' ** (prf', tsTy)))) =>
            let prf' = rewrite synthsUnique tyEnv env e {a = b, b = b'} eTy eTy' in prf' in
            let tsTy = rewrite isSumUnique b {as, bs = as'} prf prf' in tsTy in
            tsBad tsTy)
    _ | RNothing nprf | _ =
      RFalse (\(b' ** (eTy', (as ** (prf, _)))) =>
        let prf = rewrite synthsUnique tyEnv env e {a = b, b = b'} eTy eTy' in prf in
        nprf as prf)
  _ | RNothing eBad | _ = RFalse (\(b ** (eTy, _)) => eBad b eTy)
reflectChecks tyEnv env a (Contract t) with (reflectIsFixpoint a) | (isFixpoint a)
  _ | RJust prf | Just (x ** b) with (reflectChecks tyEnv env (sub (Base Id :< (x :- a)) b) t) | (checks tyEnv env (sub (Base Id :< (x :- a)) b) t)
    _ | RTrue tTy | _ = RTrue ((x ** b) ** (prf, tTy))
    _ | RFalse tBad | _ =
      RFalse (\(b' ** (prf', tTy)) =>
        let
          eq = isFixpointUnique a {xb = (x ** b), yc = b'} prf prf'
          tTy =
            replace {p = \xb => Checks tyEnv env (sub (Base Id :< (xb.fst :- a)) xb.snd) t}
              (sym eq) tTy
        in
        tBad tTy)
  _ | RNothing nprf | _ = RFalse (\(b ** (prf, _)) => nprf b prf)
reflectChecks tyEnv env a (Fold e x t) with (reflectSynths tyEnv env e) | (synths tyEnv env e)
  _ | RJust eTy | Just b with (reflectIsFixpoint b) | (isFixpoint b)
    _ | RJust prf | Just (y ** c) with (reflectChecks tyEnv (env :< (x :- sub (Base Id :< (y :- a)) c)) a t) | (checks tyEnv (env :< (x :- sub (Base Id :< (y :- a)) c)) a t)
      _ | RTrue tTy | _ = RTrue (b ** (eTy, ((y ** c) ** (prf, tTy))))
      _ | RFalse tBad | _ =
        RFalse (\(b' ** (eTy', (c' ** (prf', tTy)))) =>
          let
            prf' = rewrite synthsUnique tyEnv env e {a = b, b = b'} eTy eTy' in prf'
            eq = isFixpointUnique b {xb = (y ** c), yc = c'} prf prf'
            tTy =
              replace {p = \yc => Checks tyEnv (env :< (x :- sub (Base Id :< (yc.fst :- a)) yc.snd)) a t}
                (sym eq) tTy
          in
          tBad tTy)
    _ | RNothing nprf | _ =
      RFalse (\(b' ** (eTy', (c ** (prf, _)))) =>
        let prf = rewrite synthsUnique tyEnv env e {a = b, b = b'} eTy eTy' in prf in
        nprf c prf)
  _ | RNothing eBad | _ = RFalse (\(b ** (eTy, _)) => eBad b eTy)
reflectChecks tyEnv env a (Embed e) with (reflectSynths tyEnv env e) | (synths tyEnv env e)
  _ | RJust eTy | Just b with (reflectEq a b) | (a == b)
    _ | RTrue eq | _ = RTrue (b ** (eTy, eq))
    _ | RFalse neq | _ =
      RFalse (\(b' ** (eTy', eq)) =>
        let eq = rewrite synthsUnique tyEnv env e {a = b, b = b'} eTy eTy' in eq in
        neq eq)
  _ | RNothing eBad | _ = RFalse (\(b ** (eTy, _)) => eBad b eTy)

reflectCheckSpine tyEnv env a [] = RJust Refl
reflectCheckSpine tyEnv env a (t :: ts) with (reflectIsArrow a) | (isArrow a)
  _ | RJust prf | Just (b, c) with (reflectChecks tyEnv env b t) | (checks tyEnv env b t)
    _ | RTrue tTy | _ with (reflectCheckSpine tyEnv env c ts) | (checkSpine tyEnv env c ts)
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

reflectAllCheck tyEnv env [<] [<] = RTrue Refl
reflectAllCheck tyEnv env (_ :< _) [<] = RFalse (\case Refl impossible)
reflectAllCheck tyEnv env as (ts :< (x :- t)) with (reflectRemove x as) | (remove' x as)
  _ | RJust prf | Just (a, bs) with (reflectAnd (reflectChecks tyEnv env a t) (reflectAllCheck tyEnv env bs ts)) | (checks tyEnv env a t && allCheck tyEnv env bs ts)
    _ | RTrue checks | _ = RTrue (a ** bs ** (prf, checks))
    _ | RFalse notChecks | _ =
      RFalse (\(a' ** bs' ** (prf', checks)) =>
        let (eq, reorder) = removeUnique x as prf prf' in
        notChecks $
        bimap (\x => rewrite eq in x) (allCheckReorder (sym reorder) ts) checks)
  _ | RNothing nprf | _ = RFalse (\(a ** bs ** (prf, _)) => nprf (a, bs) prf)

reflectAllCheckBinding tyEnv env [<] a [<] = RTrue Refl
reflectAllCheckBinding tyEnv env (_ :< _) a [<] = RFalse (\case Refl impossible)
reflectAllCheckBinding tyEnv env as a (ts :< (x :- (y ** t))) with (reflectRemove x as) | (remove' x as)
  _ | RJust prf | Just (b, bs) with (reflectAnd (reflectChecks tyEnv (env :< (y :- b)) a t) (reflectAllCheckBinding tyEnv env bs a ts)) | (checks tyEnv (env :< (y :- b)) a t && allCheckBinding tyEnv env bs a ts)
    _ | RTrue checks | _ = RTrue (b ** bs ** (prf, checks))
    _ | RFalse notChecks | _ =
      RFalse (\(b' ** bs' ** (prf', checks)) =>
        let (eq, reorder) = removeUnique x as prf prf' in
        notChecks $
        bimap (\x => rewrite eq in x) (allCheckBindingReorder (sym reorder) ts) checks)
  _ | RNothing nprf | _ = RFalse (\(b ** bs ** (prf, _)) => nprf (b, bs) prf)
