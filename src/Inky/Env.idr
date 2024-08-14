module Inky.Env

import Control.Relation
import Inky.Binding

infix 2 :~

public export
record Assoc (0 a : Type) where
  constructor (:~)
  binder : Binder
  value : a

public export
data PartialEnv : Type -> World -> World -> Type where
  Lin : PartialEnv a w w
  (:<) : PartialEnv a w v -> (x : Assoc a) -> PartialEnv a (w :< x.binder) v

public export
Env : Type -> World -> Type
Env a w = PartialEnv a w [<]

public export
partialLookup : PartialEnv a w v -> Name w -> Either (Name v) a
partialLookup [<] = Left
partialLookup (env :< (x :~ v)) = stripWith (Right v) (partialLookup env)

public export
lookup : Env a w -> Name w -> a
lookup = either absurd id .: partialLookup
