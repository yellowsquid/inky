module Inky.Data.Assoc

export
infix 2 :-

public export
record Assoc (a : Type) where
  constructor (:-)
  name : String
  value : a

public export
Functor Assoc where
  map f x = x.name :- f x.value

namespace Irrelevant
  public export
  record Assoc0 (0 p : a -> Type) (x : Assoc a) where
    constructor (:-)
    0 name : String
    {auto 0 prf : x.name = name}
    value : p x.value

  public export
  map : (forall x. p x -> q x) -> forall x. Assoc0 p x -> Assoc0 q x
  map f (n :- px) = n :- f px
