module Inky.Thinning

import public Inky.Context

import Data.DPair
import Data.Nat
import Control.Function

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

indexPos : (f : ctx1 `Thins` ctx2) -> (pos : VarPos ctx1 x v) -> Var ctx2 v
indexPos Id pos = toVar pos
indexPos (Drop f) pos = ThereVar (indexPos f pos)
indexPos (Keep f) Here = toVar Here
indexPos (Keep f) (There pos) = ThereVar (indexPos f pos)

export
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

export
indexId : (0 i : Var ctx v) -> index Id i = i
indexId (%% x) = Refl

export
indexDrop : (0 f : ctx1 `Thins` ctx2) -> (0 i : Var ctx1 v) -> index (Drop f) i = ThereVar (index f i)
indexDrop f (%% x) = Refl

export
indexKeepHere : (0 f : ctx1 `Thins` ctx2) -> index (Keep {x, y} f) (%% x) = (%% y)
indexKeepHere f = Refl

export
indexKeepThere :
  (0 f : ctx1 `Thins` ctx2) -> (0 i : Var ctx1 v) ->
  index (Keep f) (ThereVar i) = ThereVar (index f i)
indexKeepThere f (%% x) = Refl

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
  lookup (env :< (x :- pv)) (%% x) = Right pv
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
