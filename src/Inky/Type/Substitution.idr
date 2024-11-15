module Inky.Type.Substitution

import Data.List.Quantifiers
import Flap.Decidable.Maybe
import Inky.Type

namespace SnocList
  public export
  data DAll : {0 ctx : SnocList String} -> (p : a -> Type) -> All (Assoc0 a) ctx -> Type where
    Lin : DAll p [<]
    (:<) : DAll p env -> Assoc0 p (n :- a) -> DAll p (env :< (n :- a))

  %name DAll penv

  export
  indexDAll :
    {0 p : a -> Type} ->
    (i : Elem x ctx) -> {0 env : All (Assoc0 a) ctx} ->
    DAll p env -> p (indexAll i env).value
  indexDAll Here (penv :< (l :- px)) = px
  indexDAll (There i) (penv :< (l :- px)) = indexDAll i penv

  export
  mapDProperty :
    {0 p : a -> Type} ->
    {0 q : b -> Type} ->
    {0 f : a -> b} ->
    (forall x. p x -> q (f x)) ->
    DAll p env -> DAll q (mapProperty (map f) env)
  mapDProperty g [<] = [<]
  mapDProperty g (penv :< (l :- px)) = mapDProperty g penv :< (l :- g px)

namespace List
  public export
  data DAll : {0 ctx : List String} -> (p : a -> Type) -> All (Assoc0 a) ctx -> Type where
    Nil : DAll p []
    (::) : Assoc0 p (n :- a) -> List.DAll p env -> DAll p ((n :- a) :: env)

  %name List.DAll penv

export
(<><) : DAll p env1 -> List.DAll p env2 -> DAll p (env1 <>< env2)
penv1 <>< [] = penv1
penv1 <>< (px :: penv2) = (penv1 :< px) <>< penv2

indexAllMap :
  {0 p, q : a -> Type} ->
  (0 f : forall x. p x -> q x) ->
  (i : Elem x sx) -> (env : All p sx) ->
  indexAll i (mapProperty f env) = f (indexAll i env)
indexAllMap f Here (env :< px) = Refl
indexAllMap f (There i) (env :< px) = indexAllMap f i env

-- Strengthening ---------------------------------------------------------------

skipsStrengthens :
  {f : ctx1 `Thins` ctx2} ->
  f `Skips` i.pos ->
  (a : Ty ctx1) ->
  (b ** Strengthen i (thin f a) b)
skipsStrengthensAll :
  {f : ctx1 `Thins` ctx2} ->
  f `Skips` i.pos ->
  (as : Context (Ty ctx1)) ->
  (bs ** (StrengthenAll i (thinAll f as) bs, bs.names = as.names))

skipsStrengthens skips (TVar j) =
  let (k ** eq) = strong f skips j.pos in
  (TVar k ** TVar eq)
  where
  strong :
    forall ctx1, ctx2.
    (f : ctx1 `Thins` ctx2) -> {0 i : Elem y ctx2} ->
    f `Skips` i -> (j : Elem x ctx1) -> (k ** toVar (indexPos f j) = index (dropPos i) k)
  strong (Drop {sx, sy} f) Here j = (toVar (indexPos f j) ** Refl)
  strong (Drop f) (Also skips) j =
    let (k ** eq) = strong f skips j in
    (ThereVar k ** cong ThereVar eq)
  strong (Keep f) (There skips) Here = (toVar Here ** Refl)
  strong (Keep f) (There skips) (There j) =
    let (k ** eq) = strong f skips j in
    (ThereVar k ** cong ThereVar eq)
skipsStrengthens skips (TArrow a b) =
  let (a ** prf1) = skipsStrengthens skips a in
  let (b ** prf2) = skipsStrengthens skips b in
  (TArrow a b ** TArrow prf1 prf2)
skipsStrengthens skips (TProd (MkRow as fresh)) =
  let (as ** (prfs, eq)) = skipsStrengthensAll skips as in
  (TProd (MkRow as (rewrite eq in fresh)) ** TProd prfs)
skipsStrengthens skips (TSum (MkRow as fresh)) =
  let (as ** (prfs, eq)) = skipsStrengthensAll skips as in
  (TSum (MkRow as (rewrite eq in fresh)) ** TSum prfs)
skipsStrengthens skips (TFix x a) =
  let (a ** prf) = skipsStrengthens (There skips) a in
  (TFix x a ** TFix prf)

skipsStrengthensAll skips [<] = ([<] ** ([<], Refl))
skipsStrengthensAll skips (as :< (l :- a)) =
  let (bs ** (prfs, eq)) = skipsStrengthensAll skips as in
  let (b ** prf) = skipsStrengthens skips a in
  (bs :< (l :- b) ** (prfs :< prf, cong (:< l) eq))

thinStrengthen :
  (0 f : ctx1 `Thins` ctx2) ->
  Strengthen i a b -> Strengthen (index f i) (thin f a) (thin (punchOut f i.pos) b)
thinAllStrengthen :
  (0 f : ctx1 `Thins` ctx2) ->
  StrengthenAll i as bs -> StrengthenAll (index f i) (thinAll f as) (thinAll (punchOut f i.pos) bs)

thinStrengthen f (TVar {j, k} prf) =
  TVar $
  rewrite sym $ indexPosComp (dropPos (indexPos f i.pos)) (punchOut f i.pos) k.pos in
  rewrite (punchOutHomo f i.pos).indexPos k.pos in
  rewrite indexPosComp f (dropPos i.pos) k.pos in
  cong (index f) prf
thinStrengthen f (TArrow prf1 prf2) = TArrow (thinStrengthen f prf1) (thinStrengthen f prf2)
thinStrengthen f (TProd {as = MkRow _ _, bs = MkRow _ _} prfs) = TProd (thinAllStrengthen f prfs)
thinStrengthen f (TSum {as = MkRow _ _, bs = MkRow _ _} prfs) = TSum (thinAllStrengthen f prfs)
thinStrengthen f (TFix prf) = TFix (thinStrengthen (Keep f) prf)

thinAllStrengthen f [<] = [<]
thinAllStrengthen f (prfs :< prf) = thinAllStrengthen f prfs :< thinStrengthen f prf

sub'Strengthen :
  {a : Ty ctx1} ->
  {env : All (Assoc0 $ Thinned Ty ctx2) ctx1} ->
  ((k : Var ctx1) ->
    Proof (Ty (dropElem ctx2 j.pos))
      (Strengthen j (indexAll k.pos env).value.extract)
      (i = k)) ->
  Strengthen i a b ->
  (c ** Strengthen j (sub' env a) c)
subAllStrengthen :
  {as : Context (Ty ctx1)} ->
  {env : All (Assoc0 $ Thinned Ty ctx2) ctx1} ->
  ((k : Var ctx1) ->
    Proof (Ty (dropElem ctx2 j.pos))
      (Strengthen j (indexAll k.pos env).value.extract)
      (i = k)) ->
  StrengthenAll i as bs ->
  (cs ** (StrengthenAll j (subAll env as) cs, cs.names = as.names))

sub'Strengthen envStr (TVar {j = k1, k = k2} eq) =
  case envStr k1 of
    Just b `Because` prf => (b ** prf)
    Nothing `Because` prf =>
      void $
      skipsSplit (dropPosSkips i.pos) k2.pos $
      replace {p = (\x => i.pos ~=~ x.pos)}
        (trans prf eq)
        Refl
sub'Strengthen envStr (TArrow prf1 prf2) =
  let (a ** prf1) = sub'Strengthen envStr prf1 in
  let (b ** prf2) = sub'Strengthen envStr prf2 in
  (TArrow a b ** TArrow prf1 prf2)
sub'Strengthen envStr (TProd {as = MkRow as fresh} prfs) =
  let (as ** (prfs, eq)) = subAllStrengthen envStr prfs in
  (TProd (MkRow as (rewrite eq in fresh)) ** TProd prfs)
sub'Strengthen envStr (TSum {as = MkRow as fresh} prfs) =
  let (as ** (prfs, eq)) = subAllStrengthen envStr prfs in
  (TSum (MkRow as (rewrite eq in fresh)) ** TSum prfs)
sub'Strengthen envStr (TFix {x} prf) =
  let (a ** prf) = sub'Strengthen envStr' prf in
  (TFix x a ** TFix prf)
  where
  Env0 : All (Assoc0 $ Thinned Ty (ctx2 :< x)) ctx1
  Env0 = mapProperty (map $ rename $ Drop Id) env

  getEnv0 : (i : Elem y ctx1) -> indexAll i Env0 = map (rename $ Drop Id) (indexAll i env)
  getEnv0 i = indexAllMap (map $ rename $ Drop Id) i env

  Env' : All (Assoc0 $ Thinned Ty (ctx2 :< x)) (ctx1 :< x)
  Env' = Env0 :< (x :- (TVar (%% x) `Over` Id))

  getEnv' : Var (ctx1 :< x) -> Ty (ctx2 :< x)
  getEnv' i = (indexAll i.pos Env').value.extract

  envStr' :
    (k : Var (ctx1 :< x)) ->
    Proof (Ty (dropElem ctx2 j.pos :< x))
      (Strengthen (ThereVar j) (getEnv' k))
      (ThereVar i = k)
  envStr' ((%%) _ {pos = Here}) = Just (TVar (%% x)) `Because` TVar Refl
  envStr' ((%%) name {pos = There k}) =
    map (thin $ Drop Id)
      (\b, prf =>
        rewrite getEnv0 k in
        rewrite sym $ extractHomo (Drop {x} Id) (indexAll k env).value in
        thinStrengthen (Drop Id) prf)
      (\eq => cong ThereVar eq) $
    envStr (%% name)

subAllStrengthen envStr [<] = ([<] ** ([<], Refl))
subAllStrengthen envStr ((:<) prfs {l} prf) =
  let (cs ** (prfs, eq)) = subAllStrengthen envStr prfs in
  let (c ** prf) = sub'Strengthen envStr prf in
  (cs :< (l :- c) ** (prfs :< prf, cong (:< l) eq))

-- Strict Positivity -----------------------------------------------------------

thinStrictlyPositive :
  (0 f : ctx1 `Thins` ctx2) ->
  i `StrictlyPositiveIn` a ->
  index f i `StrictlyPositiveIn` thin f a
thinAllStrictlyPositive :
  (0 f : ctx1 `Thins` ctx2) ->
  i `StrictlyPositiveInAll` as ->
  index f i `StrictlyPositiveInAll` thinAll f as

thinStrictlyPositive f TVar = TVar
thinStrictlyPositive f (TArrow prf) = TArrow (thinStrengthen f prf)
thinStrictlyPositive f (TProd {as = MkRow _ _} prfs) = TProd (thinAllStrictlyPositive f prfs)
thinStrictlyPositive f (TSum {as = MkRow _ _} prfs) = TSum (thinAllStrictlyPositive f prfs)
thinStrictlyPositive f (TFix prf) = TFix (thinStrictlyPositive (Keep f) prf)

thinAllStrictlyPositive f [<] = [<]
thinAllStrictlyPositive f (prfs :< prf) =
  thinAllStrictlyPositive f prfs :< thinStrictlyPositive f prf

sub'StrictlyPositive :
  {a : Ty ctx1} ->
  {env : All (Assoc0 $ Thinned Ty ctx2) ctx1} ->
  ((k : Var ctx1) ->
    Proof (Ty (dropElem ctx2 j.pos))
      (Strengthen j (indexAll k.pos env).value.extract)
      (i = k, j `StrictlyPositiveIn` (indexAll k.pos env).value.extract)) ->
  i `StrictlyPositiveIn` a ->
  j `StrictlyPositiveIn` sub' env a
subAllStrictlyPositive :
  {as : Context (Ty ctx1)} ->
  {env : All (Assoc0 $ Thinned Ty ctx2) ctx1} ->
  ((k : Var ctx1) ->
    Proof (Ty (dropElem ctx2 j.pos))
      (Strengthen j (indexAll k.pos env).value.extract)
      (i = k, j `StrictlyPositiveIn` (indexAll k.pos env).value.extract)) ->
  i `StrictlyPositiveInAll` as ->
  j `StrictlyPositiveInAll` subAll env as

sub'StrictlyPositive envSp (TVar {j = k}) =
  case envSp k of
    Just a `Because` prf => strongIsStrictlyPositive prf
    Nothing `Because` (Refl, prf) => prf
sub'StrictlyPositive envSp (TArrow (TArrow prf1 prf2)) =
  let envStr = \k => map id (\_ => id) fst $ envSp k in
  let (_ ** str1) = sub'Strengthen envStr prf1 in
  let (_ ** str2) = sub'Strengthen envStr prf2 in
  TArrow (TArrow str1 str2)
sub'StrictlyPositive envSp (TProd {as = MkRow _ _} prfs) = TProd (subAllStrictlyPositive envSp prfs)
sub'StrictlyPositive envSp (TSum {as = MkRow _ _} prfs) = TSum (subAllStrictlyPositive envSp prfs)
sub'StrictlyPositive envSp (TFix {x} prf) =
  TFix (sub'StrictlyPositive envSp' prf)
  where
  Env0 : All (Assoc0 $ Thinned Ty (ctx2 :< x)) ctx1
  Env0 = mapProperty (map $ rename $ Drop Id) env

  getEnv0 : (i : Elem y ctx1) -> indexAll i Env0 = map (rename $ Drop Id) (indexAll i env)
  getEnv0 i = indexAllMap (map $ rename $ Drop Id) i env

  Env' : All (Assoc0 $ Thinned Ty (ctx2 :< x)) (ctx1 :< x)
  Env' = Env0 :< (x :- (TVar (%% x) `Over` Id))

  getEnv' : Var (ctx1 :< x) -> Ty (ctx2 :< x)
  getEnv' i = (indexAll i.pos Env').value.extract

  envSp' :
    (k : Var (ctx1 :< x)) ->
    Proof (Ty (dropElem ctx2 j.pos :< x))
      (Strengthen (ThereVar j) (getEnv' k))
      (ThereVar i = k, ThereVar j `StrictlyPositiveIn` (getEnv' k))
  envSp' ((%%) _ {pos = Here}) = Just (TVar (%% x)) `Because` TVar Refl
  envSp' ((%%) name {pos = There k}) =
    map (thin $ Drop Id)
      (\b, prf =>
        rewrite getEnv0 k in
        rewrite sym $ extractHomo (Drop {x} Id) (indexAll k env).value in
        thinStrengthen (Drop Id) prf)
      (\(eq, prf) =>
        ( cong ThereVar eq
        , rewrite getEnv0 k in
          rewrite sym $ extractHomo (Drop {x} Id) (indexAll k env).value in
          thinStrictlyPositive (Drop Id) prf
        )) $
    envSp (%% name)

subAllStrictlyPositive envSp [<] = [<]
subAllStrictlyPositive envSp (prfs :< prf) =
  subAllStrictlyPositive envSp prfs :< sub'StrictlyPositive envSp prf

-- Well Formedness -------------------------------------------------------------

thinWf : (0 f : ctx1 `Thins` ctx2) -> WellFormed a -> WellFormed (thin f a)
thinAllWf : (0 f : ctx1 `Thins` ctx2) -> AllWellFormed as -> AllWellFormed (thinAll f as)

thinWf f TVar = TVar
thinWf f (TArrow wf1 wf2) = TArrow (thinWf f wf1) (thinWf f wf2)
thinWf f (TProd {as = MkRow _ _} wfs) = TProd (thinAllWf f wfs)
thinWf f (TSum {as = MkRow _ _} wfs) = TSum (thinAllWf f wfs)
thinWf f (TFix prf wf) = TFix (thinStrictlyPositive (Keep f) prf) (thinWf (Keep f) wf)

thinAllWf f [<] = [<]
thinAllWf f (wfs :< wf) = thinAllWf f wfs :< thinWf f wf

sub'Wf :
  {a : Ty ctx1} ->
  {env : All (Assoc0 $ Thinned Ty ctx2) ctx1} ->
  DAll (\ty => WellFormed ty.value) env ->
  WellFormed a ->
  WellFormed (sub' env a)
subAllWf :
  {as : Context (Ty ctx1)} ->
  {env : All (Assoc0 $ Thinned Ty ctx2) ctx1} ->
  DAll (\ty => WellFormed ty.value) env ->
  AllWellFormed as ->
  AllWellFormed (subAll env as)

sub'Wf envWf (TVar {i}) =
  thinWf (indexAll i.pos env).value.thins (indexDAll i.pos envWf)
sub'Wf envWf (TArrow wf1 wf2) = TArrow (sub'Wf envWf wf1) (sub'Wf envWf wf2)
sub'Wf envWf (TProd {as = MkRow _ _} wfs) = TProd (subAllWf envWf wfs)
sub'Wf envWf (TSum {as = MkRow _ _} wfs) = TSum (subAllWf envWf wfs)
sub'Wf envWf (TFix {x} prf wf) =
  TFix
    (sub'StrictlyPositive envSp prf)
    (sub'Wf (mapDProperty {f = rename (Drop Id)} id envWf :< (x :- TVar)) wf)
  where
  Env0 : All (Assoc0 $ Thinned Ty (ctx2 :< x)) ctx1
  Env0 = mapProperty (map $ rename $ Drop Id) env

  getEnv0 : (i : Elem y ctx1) -> indexAll i Env0 = map (rename $ Drop Id) (indexAll i env)
  getEnv0 i = indexAllMap (map $ rename $ Drop Id) i env

  Env' : All (Assoc0 $ Thinned Ty (ctx2 :< x)) (ctx1 :< x)
  Env' = Env0 :< (x :- (TVar (%% x) `Over` Id))

  getEnv' : Var (ctx1 :< x) -> Ty (ctx2 :< x)
  getEnv' i = (indexAll i.pos Env').value.extract

  envSp :
    (k : Var (ctx1 :< x)) ->
    Proof (Ty ctx2)
      (Strengthen (%% x) (getEnv' k))
      ((%% x) = k, (%% x) `StrictlyPositiveIn` (getEnv' k))
  envSp ((%%) _ {pos = Here}) = Nothing `Because` (Refl, TVar)
  envSp ((%%) name {pos = There i}) =
    let
      (b ** prf) =
        skipsStrengthens
          {f = (indexAll i Env0).value.thins}
          (rewrite getEnv0 i in Here)
          _
    in
    Just b `Because` prf

subAllWf envWf [<] = [<]
subAllWf envWf (wfs :< wf) = subAllWf envWf wfs :< sub'Wf envWf wf

export
subWf :
  {a : Ty ctx1} ->
  {env : All (Assoc0 $ Ty ctx2) ctx1} ->
  DAll (\ty => WellFormed ty) env ->
  WellFormed a ->
  WellFormed (sub env a)
subWf envWf = sub'Wf (mapDProperty id envWf)
