module Inky.Thinning

import public Data.Fin

import Control.Function

--------------------------------------------------------------------------------
-- Thinnings -------------------------------------------------------------------
--------------------------------------------------------------------------------

public export
data Thins : Nat -> Nat -> Type where
  Id : n `Thins` n
  Drop : k `Thins` n -> k `Thins` S n
  Keep : k `Thins` n -> S k `Thins` S n

%name Thins f, g, h

-- Basics

export
index : k `Thins` n -> Fin k -> Fin n
index Id x = x
index (Drop f) x = FS (index f x)
index (Keep f) FZ = FZ
index (Keep f) (FS x) = FS (index f x)

export
(.) : k `Thins` n -> j `Thins` k -> j `Thins` n
Id . g = g
Drop f . g = Drop (f . g)
Keep f . Id = Keep f
Keep f . Drop g = Drop (f . g)
Keep f . Keep g = Keep (f . g)

-- Basic properties

export
indexInjective : (f : k `Thins` n) -> {x, y : Fin k} -> index f x = index f y -> x = y
indexInjective Id eq = eq
indexInjective (Drop f) eq = indexInjective f $ injective eq
indexInjective (Keep f) {x = FZ} {y = FZ} eq = Refl
indexInjective (Keep f) {x = FS x} {y = FS y} eq = cong FS $ indexInjective f $ injective eq

export
(f : k `Thins` n) => Injective (index f) where
  injective = indexInjective f

export
indexId : (0 x : Fin n) -> index Id x = x
indexId x = Refl

export
indexDrop : (0 f : k `Thins` n) -> (0 x : Fin k) -> index (Drop f) x = FS (index f x)
indexDrop f x = Refl

export
indexKeepFZ : (0 f : k `Thins` n) -> index (Keep f) FZ = FZ
indexKeepFZ f = Refl

export
indexKeepFS : (0 f : k `Thins` n) -> (0 x : Fin k) -> index (Keep f) (FS x) = FS (index f x)
indexKeepFS f x = Refl

export
indexComp :
  (f : k `Thins` n) -> (g : j `Thins` k) -> (x : Fin j) ->
  index (f . g) x = index f (index g x)
indexComp Id g x = Refl
indexComp (Drop f) g x = cong FS (indexComp f g x)
indexComp (Keep f) Id x = Refl
indexComp (Keep f) (Drop g) x = cong FS (indexComp f g x)
indexComp (Keep f) (Keep g) FZ = Refl
indexComp (Keep f) (Keep g) (FS x) = cong FS (indexComp f g x)

-- Congruence ------------------------------------------------------------------

export
infix 6 ~~~

public export
data (~~~) : k `Thins` n -> k `Thins` n -> Type where
  IdId : Id ~~~ Id
  IdKeep : Id ~~~ f -> Id ~~~ Keep f
  KeepId : f ~~~ Id -> Keep f ~~~ Id
  DropDrop : f ~~~ g -> Drop f ~~~ Drop g
  KeepKeep : f ~~~ g -> Keep f ~~~ Keep g

%name Thinning.(~~~) prf

export
(.index) : f ~~~ g -> (x : Fin k) -> index f x = index g x
(IdId).index x = Refl
(IdKeep prf).index FZ = Refl
(IdKeep prf).index (FS x) = cong FS (prf.index x)
(KeepId prf).index FZ = Refl
(KeepId prf).index (FS x) = cong FS (prf.index x)
(DropDrop prf).index x = cong FS (prf.index x)
(KeepKeep prf).index FZ = Refl
(KeepKeep prf).index (FS x) = cong FS (prf.index x)

export
pointwise : {f, g : k `Thins` n} -> (0 _ : (x : Fin k) -> index f x = index g x) -> f ~~~ g
pointwise {f = Id} {g = Id} prf = IdId
pointwise {f = Id} {g = Drop g} prf = void $ absurd $ prf FZ
pointwise {f = Id} {g = Keep g} prf = IdKeep (pointwise $ \x => injective $ prf $ FS x)
pointwise {f = Drop f} {g = Id} prf = void $ absurd $ prf FZ
pointwise {f = Drop f} {g = Drop g} prf = DropDrop (pointwise $ \x => injective $ prf x)
pointwise {f = Drop f} {g = Keep g} prf = void $ absurd $ prf FZ
pointwise {f = Keep f} {g = Id} prf = KeepId (pointwise $ \x => injective $ prf $ FS x)
pointwise {f = Keep f} {g = Drop g} prf = void $ absurd $ prf FZ
pointwise {f = Keep f} {g = Keep g} prf = KeepKeep (pointwise $ \x => injective $ prf $ FS x)

--------------------------------------------------------------------------------
-- Environments ----------------------------------------------------------------
--------------------------------------------------------------------------------

public export
data Env : Nat -> Nat -> Type -> Type where
  Base : k `Thins` n -> Env k n a
  (:<) : Env k n a -> a -> Env (S k) n a

%name Env env

export
lookup : Env k n a -> Fin k -> Either (Fin n) a
lookup (Base f) x = Left (index f x)
lookup (env :< v) FZ = Right v
lookup (env :< v) (FS x) = lookup env x

-- Properties

export
lookupFZ : (0 env : Env k n a) -> (0 v : a) -> lookup (env :< v) FZ = Right v
lookupFZ env v = Refl

export
lookupFS :
  (0 env : Env k n a) -> (0 v : a) -> (0 x : Fin k) ->
  lookup (env :< v) (FS x) = lookup env x
lookupFS env v x = Refl

--------------------------------------------------------------------------------
-- Renaming Coalgebras ---------------------------------------------------------
--------------------------------------------------------------------------------

public export
interface Rename (0 a : Nat -> Type) where
  var : Fin n -> a n
  rename : k `Thins` n -> a k -> a n
  0 renameCong : {0 f, g : k `Thins` n} -> f ~~~ g -> (x : a k) -> rename f x = rename g x
  0 renameId : (x : a n) -> rename Id x = x

export
lift : Rename a => k `Thins` n -> Env j k (a k) -> Env j n (a n)
lift Id env = env
lift f (Base g) = Base (f . g)
lift f (env :< v) = lift f env :< rename f v

export
lookupLift :
  Rename a =>
  (f : k `Thins` n) -> (env : Env j k (a k)) -> (x : Fin j) ->
  lookup (lift f env) x = bimap (index f) (rename f) (lookup env x)
lookupLift Id env x with (lookup env x)
  _ | Left y = Refl
  _ | Right y = cong Right $ irrelevantEq $ sym $ renameId y
lookupLift (Drop f) (Base g) x = cong Left $ indexComp (Drop f) g x
lookupLift (Drop f) (env :< y) FZ = Refl
lookupLift (Drop f) (env :< y) (FS x) = lookupLift (Drop f) env x
lookupLift (Keep f) (Base g) x = cong Left $ indexComp (Keep f) g x
lookupLift (Keep f) (env :< y) FZ = Refl
lookupLift (Keep f) (env :< y) (FS x) = lookupLift (Keep f) env x
