module Inky.Data.Irrelevant

public export
record Irrelevant (a : Type) where
  constructor Forget
  0 value : a

public export
Functor Irrelevant where
  map f x = Forget (f x.value)

public export
Applicative Irrelevant where
  pure x = Forget x
  f <*> x = Forget (f.value x.value)

public export
Monad Irrelevant where
  join x = Forget (x.value.value)
