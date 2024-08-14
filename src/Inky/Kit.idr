module Inky.Kit

import public Control.Monad.Identity
import Inky.Binding
import Inky.Erased

public export
record TrKit (env : World -> World -> Type) (res : World -> Type) where
  constructor MkTrKit
  name : forall w, v. env w v -> Name w -> res v
  binder : forall w, v. env w v -> Binder -> Binder
  extend : forall w, v. (b : Binder) -> (e : env w v) -> env (w :< b) (v :< binder e b)

export
map : (forall w. res1 w -> res2 w) -> TrKit env res1 -> TrKit env res2
map f kit = MkTrKit
  { name = f .: kit.name
  , binder = kit.binder
  , extend = kit.extend
  }

export
pure : Applicative m => TrKit env res -> TrKit env (m . res)
pure = map pure

export
Coerce : TrKit (Erased .: (<=)) Name
Coerce = MkTrKit (\e => coerce e.val) (const id) (\b, e => Forget (snocMono b e.val))

public export
record Supply (w : World) where
  constructor MkSupply
  seed : Binder
  fresh : seed `FreshIn` w

public export
record SubstEnv (res : World -> Type) (w, v : World) where
  constructor MkEnv
  name : Name w -> res v
  supply : Supply v

export
substKitE :
  Monad m =>
  (var : forall w. Name w -> m (res w)) ->
  (coerce : forall w, v. (0 _ : w <= v) -> res w -> m (res v)) ->
  TrKit (SubstEnv (m . res)) (m . res)
substKitE var coerce = MkTrKit
  { name = \e, n => e.name n
  , binder = \e, _ => e.supply.seed
  , extend = \b, e => MkEnv
    { name =
      stripWith
        (var (nameOf e.supply.seed))
        (\n => do
          n <- e.name n
          coerce (freshLte e.supply.fresh) n)
    , supply = MkSupply
      { seed = BS e.supply.seed
      , fresh = sucFresh e.supply.fresh
      }
    }
  }

public export
interface Traverse (0 t : World -> Type) where
  var : Name w -> t w

  traverseE : Applicative m => TrKit env (m . t) -> env w v -> t w -> m (t v)

  renameE : Applicative m => TrKit env (m . Name) -> env w v -> t w -> m (t v)
  renameE kit = traverseE (Kit.map (Prelude.map var) kit)

  traverse : TrKit env t -> env w v -> t w -> t v
  traverse kit e t = (traverseE (Kit.pure kit) e t).runIdentity

  rename : TrKit env Name -> env w v -> t w -> t v
  rename kit e t = (renameE (Kit.pure kit) e t).runIdentity
