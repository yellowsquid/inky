module Inky.Thinning

import public Inky.Context

import Control.Function
import Control.WellFounded
import Data.DPair
import Data.Nat

--------------------------------------------------------------------------------
-- Thinnings -------------------------------------------------------------------
--------------------------------------------------------------------------------

public export
data Thins : Context a -> Context a -> Type where
  Id : ctx `Thins` ctx
  Drop : ctx1 `Thins` ctx2 -> ctx1 `Thins` ctx2 :< x
  Keep : ctx1 `Thins` ctx2 -> ctx1 :< (x :- v) `Thins` ctx2 :< (y :- v)

%name Thins f, g, h

-- Basics

public export
indexPos : (f : ctx1 `Thins` ctx2) -> (pos : VarPos ctx1 x v) -> Var ctx2 v
indexPos Id pos = toVar pos
indexPos (Drop f) pos = ThereVar (indexPos f pos)
indexPos (Keep f) Here = toVar Here
indexPos (Keep f) (There pos) = ThereVar (indexPos f pos)

public export
index : ctx1 `Thins` ctx2 -> Var ctx1 v -> Var ctx2 v
index f i = indexPos f i.pos

export
(.) : ctx2 `Thins` ctx3 -> ctx1 `Thins` ctx2 -> ctx1 `Thins` ctx3
Id . g = g
Drop f . g = Drop (f . g)
Keep f . Id = Keep f
Keep f . Drop g = Drop (f . g)
Keep f . Keep g = Keep (f . g)

-- Basic properties

indexPosInjective :
  (f : ctx1 `Thins` ctx2) -> {i : VarPos ctx1 x v} -> {j : VarPos ctx1 y v} ->
  (0 _ : toNat (indexPos f i).pos = toNat (indexPos f j).pos) -> i = j
indexPosInjective Id prf = toNatInjective prf
indexPosInjective (Drop f) prf = indexPosInjective f (injective prf)
indexPosInjective (Keep f) {i = Here} {j = Here} prf = Refl
indexPosInjective (Keep f) {i = There i} {j = There j} prf =
  thereCong (indexPosInjective f $ injective prf)

export
indexInjective : (f : ctx1 `Thins` ctx2) -> {i, j : Var ctx1 v} -> index f i = index f j -> i = j
indexInjective f {i = %% x, j = %% y} prf = toVarCong (indexPosInjective f $ toNatCong' prf)

indexPosComp :
  (f : ctx2 `Thins` ctx3) -> (g : ctx1 `Thins` ctx2) -> (pos : VarPos ctx1 x v) ->
  indexPos (f . g) pos = index f (indexPos g pos)
indexPosComp Id g pos with (indexPos g pos)
  _ | (%% _) = Refl
indexPosComp (Drop f) g pos = cong ThereVar (indexPosComp f g pos)
indexPosComp (Keep f) Id pos = Refl
indexPosComp (Keep f) (Drop g) pos = cong ThereVar (indexPosComp f g pos)
indexPosComp (Keep f) (Keep g) Here = Refl
indexPosComp (Keep f) (Keep g) (There pos) = cong ThereVar (indexPosComp f g pos)

export
indexComp :
  (f : ctx2 `Thins` ctx3) -> (g : ctx1 `Thins` ctx2) -> (i : Var ctx1 v) ->
  index (f . g) i = index f (index g i)
indexComp f g i = indexPosComp f g i.pos

-- Congruence ------------------------------------------------------------------

export
infix 6 ~~~

public export
data (~~~) : ctx1 `Thins` ctx2 -> ctx1 `Thins` ctx2 -> Type where
  IdId : Id ~~~ Id
  IdKeep : Id ~~~ f -> Id ~~~ Keep f
  KeepId : f ~~~ Id -> Keep f ~~~ Id
  DropDrop : f ~~~ g -> Drop f ~~~ Drop g
  KeepKeep : f ~~~ g -> Keep f ~~~ Keep g

%name Thinning.(~~~) prf

(.indexPos) : f ~~~ g -> (pos : VarPos ctx1 x v) -> indexPos f pos = indexPos g pos
(IdId).indexPos pos = Refl
(IdKeep prf).indexPos Here = Refl
(IdKeep prf).indexPos (There pos) = cong ThereVar $ prf.indexPos pos
(KeepId prf).indexPos Here = Refl
(KeepId prf).indexPos (There pos) = cong ThereVar $ prf.indexPos pos
(DropDrop prf).indexPos pos = cong ThereVar $ prf.indexPos pos
(KeepKeep prf).indexPos Here = Refl
(KeepKeep prf).indexPos (There pos) = cong ThereVar $ prf.indexPos pos

export
(.index) : f ~~~ g -> (i : Var ctx1 v) -> index f i = index g i
prf.index i = prf.indexPos i.pos

-- Useful for Parsers ----------------------------------------------------------

public export
dropAll : Length ctx2 -> ctx1 `Thins` ctx1 ++ ctx2
dropAll Z = Id
dropAll (S len) = Drop (dropAll len)

public export
keepAll : Length ctx -> ctx1 `Thins` ctx2 -> ctx1 ++ ctx `Thins` ctx2 ++ ctx
keepAll Z f = f
keepAll (S {x = x :- _} len) f = Keep (keepAll len f)

public export
append :
  ctx1 `Thins` ctx3 -> ctx2 `Thins` ctx4 ->
  {auto len : Length ctx4} ->
  ctx1 ++ ctx2 `Thins` ctx3 ++ ctx4
append f Id = keepAll len f
append f (Drop g) {len = S len} = Drop (append f g)
append f (Keep g) {len = S len} = Keep (append f g)

public export
assoc : Length ctx3 -> ctx1 ++ (ctx2 ++ ctx3) `Thins` (ctx1 ++ ctx2) ++ ctx3
assoc Z = Id
assoc (S {x = x :- _} len) = Keep (assoc len)

public export
growLength : ctx1 `Thins` ctx2 -> Length ctx1 -> Length ctx2
growLength Id len = len
growLength (Drop f) len = S (growLength f len)
growLength (Keep f) (S len) = S (growLength f len)

public export
thinLength : ctx1 `Thins` ctx2 -> Length ctx2 -> Length ctx1
thinLength Id len = len
thinLength (Drop f) (S len) = thinLength f len
thinLength (Keep f) (S len) = S (thinLength f len)

public export
thinAll : ctx1 `Thins` ctx2 -> All p ctx2 -> All p ctx1
thinAll Id env = env
thinAll (Drop f) (env :< (x :- px)) = thinAll f env
thinAll (Keep {x, y} f) (env :< (_ :- px)) = thinAll f env :< (x :- px)

public export
splitL :
  {0 ctx1, ctx2, ctx3 : Context a} ->
  Length ctx3 ->
  ctx1 `Thins` ctx2 ++ ctx3 ->
  Exists (\ctxA => Exists (\ctxB => (ctx1 = ctxA ++ ctxB, ctxA `Thins` ctx2, ctxB `Thins` ctx3)))
splitL Z f = Evidence ctx1 (Evidence [<] (Refl, f, Id))
splitL (S len) Id = Evidence ctx2 (Evidence ctx3 (Refl, Id, Id))
splitL (S len) (Drop f) =
  let Evidence ctxA (Evidence ctxB (Refl, g, h)) = splitL len f in
  Evidence ctxA (Evidence ctxB (Refl, g, Drop h))
splitL (S len) (Keep f) =
  let Evidence ctxA (Evidence ctxB (Refl, g, h)) = splitL len f in
  Evidence ctxA (Evidence (ctxB :< _) (Refl, g, Keep h))

public export
splitR :
  {0 ctx1, ctx2, ctx3 : Context a} ->
  Length ctx2 ->
  ctx1 ++ ctx2 `Thins` ctx3 ->
  Exists (\ctxA => Exists (\ctxB => (ctx3 = ctxA ++ ctxB, ctx1 `Thins` ctxA, ctx2 `Thins` ctxB)))
splitR Z f = Evidence ctx3 (Evidence [<] (Refl, f, Id))
splitR (S len) Id = Evidence ctx1 (Evidence ctx2 (Refl, Id, Id))
splitR (S len) (Drop f) =
  let Evidence ctxA (Evidence ctxB (Refl, g, h)) = splitR (S len) f in
  Evidence ctxA (Evidence (ctxB :< _) (Refl, g, Drop h))
splitR (S len) (Keep f) =
  let Evidence ctxA (Evidence ctxB (Refl, g, h)) = splitR len f in
  Evidence ctxA (Evidence (ctxB :< _) (Refl, g, Keep h))

--------------------------------------------------------------------------------
-- Environments ----------------------------------------------------------------
--------------------------------------------------------------------------------

public export
data Env : Context a -> Context a -> (a -> Type) -> Type where
  Base : {0 ctx1, ctx2 : Context a} -> ctx1 `Thins` ctx2 -> Env ctx1 ctx2 p
  (:<) :
    {0 ctx1, ctx2 : Context a} ->
    Env ctx1 ctx2 p -> (x : Assoc0 (p v)) ->
    Env (ctx1 :< (x.name :- v)) ctx2 p

%name Env env

lookupPos : Env ctx1 ctx2 p -> VarPos ctx1 x v -> Either (Var ctx2 v) (p v)
lookupPos (Base f) pos = Left (indexPos f pos)
lookupPos (env :< (x :- pv)) Here = Right pv
lookupPos (env :< (x :- pv)) (There pos) = lookupPos env pos

export
lookup : Env ctx1 ctx2 p -> Var ctx1 v -> Either (Var ctx2 v) (p v)
lookup env i = lookupPos env i.pos

-- Properties

export
lookupHere :
  (0 env : Env ctx1 ctx2 p) -> (0 x : String) -> (0 pv : p v) ->
  lookup (env :< (x :- pv)) (toVar Here) = Right pv
lookupHere env x pv = Refl

export
lookupFS :
  (0 env : Env ctx1 ctx2 p) -> (0 x : String) -> (0 pv : p v) -> (0 i : Var ctx1 w) ->
  lookup (env :< (x :- pv)) (ThereVar i) = lookup env i
lookupFS env x pv i = Refl

--------------------------------------------------------------------------------
-- Renaming Coalgebras ---------------------------------------------------------
--------------------------------------------------------------------------------

public export
interface Rename (0 a : Type) (0 t : Context a -> a -> Type) where
  var : {0 ctx : Context a} -> {0 v : a} -> Var ctx v -> t ctx v
  rename :
    {0 ctx1, ctx2 : Context a} -> ctx1 `Thins` ctx2 ->
    {0 v : a} -> t ctx1 v -> t ctx2 v
  0 renameCong :
    {0 ctx1, ctx2 : Context a} -> {0 f, g : ctx1 `Thins` ctx2} -> f ~~~ g ->
    {0 v : a} -> (x : t ctx1 v) -> rename f x = rename g x
  0 renameId : {0 ctx : Context a} -> {0 v : a} -> (x : t ctx v) -> rename Id x = x

export
lift : Rename a t => ctx2 `Thins` ctx3 -> Env ctx1 ctx2 (t ctx2) -> Env ctx1 ctx3 (t ctx3)
lift Id env = env
lift f (Base g) = Base (f . g)
lift f (env :< (x :- v)) = lift f env :< (x :- rename f v)

lookupPosLift :
  Rename a t =>
  (f : ctx2 `Thins` ctx3) -> (env : Env ctx1 ctx2 (t ctx2)) -> (pos : VarPos ctx1 x v) ->
  lookupPos (lift f env) pos = bimap (index f) (rename f) (lookupPos env pos)
lookupPosLift Id env pos with (lookupPos env pos)
  _ | Left (%% y) = Refl
  _ | Right y = cong Right $ irrelevantEq $ sym $ renameId y
lookupPosLift (Drop f) (Base g) pos = cong Left $ indexPosComp (Drop f) g pos
lookupPosLift (Keep f) (Base g) pos = cong Left $ indexPosComp (Keep f) g pos
lookupPosLift (Drop f) (env :< (x :- v)) Here = Refl
lookupPosLift (Keep f) (env :< (x :- v)) Here = Refl
lookupPosLift (Drop f) (env :< (x :- v)) (There pos) = lookupPosLift (Drop f) env pos
lookupPosLift (Keep f) (env :< (x :- v)) (There pos) = lookupPosLift (Keep f) env pos

export
lookupLift :
  Rename a t =>
  (f : ctx2 `Thins` ctx3) -> (env : Env ctx1 ctx2 (t ctx2)) -> (i : Var ctx1 v) ->
  lookup (lift f env) i = bimap (index f) (rename f) (lookup env i)
lookupLift f env i = lookupPosLift f env i.pos

-- Well Founded ----------------------------------------------------------------

export
Sized (Context a) where
  size [<] = 0
  size (ctx :< x) = S (size ctx)

-- Environments ------------------------------------------------------

namespace DEnv
  public export
  data DEnv : (0 p : Context a -> a -> Type) -> Context a -> Type where
    Lin : DEnv p [<]
    (:<) :
      DEnv p ctx -> (px : Assoc0 (p ctx x.value)) ->
      {auto 0 prf : px.name = x.name} ->
      DEnv p (ctx :< x)

  %name DEnv.DEnv env

  export
  length : DEnv p ctx -> Length ctx
  length [<] = Z
  length (env :< px) = S (length env)

  public export
  record Entry (p : Context a -> a -> Type) (ctx : Context a) (v : a) where
    constructor MkEntry
    {0 support : Context a}
    0 prf : support `Smaller` ctx
    thins : support `Thins` ctx
    value : p support v

  export
  indexDEnvPos : VarPos ctx x v -> DEnv p ctx -> Entry p ctx v
  indexDEnvPos Here (env :< px) = MkEntry reflexive (Drop Id) px.value
  indexDEnvPos (There pos) (env :< px) =
    let MkEntry prf thins value = indexDEnvPos pos env in
    MkEntry (lteSuccRight prf) (Drop thins) value

  export
  indexDEnv' : Var ctx v -> DEnv p ctx -> Entry p ctx v
  indexDEnv' i env = indexDEnvPos i.pos env

  export
  indexDEnv : Rename a p => Var ctx v -> DEnv p ctx -> p ctx v
  indexDEnv i env =
    let MkEntry _ f x = indexDEnv' i env in
    rename f x

  export
  mapProperty : ({0 ctx : Context a} -> {0 v : a} -> p ctx v -> q ctx v) -> DEnv p ctx -> DEnv q ctx
  mapProperty f [<] = [<]
  mapProperty f (env :< (x :- px)) = mapProperty f env :< (x :- f px)
