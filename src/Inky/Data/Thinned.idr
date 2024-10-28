module Inky.Data.Thinned

import public Inky.Data.SnocList.Thinning

public export
record Thinned (0 p : SnocList a -> Type) (ctx : SnocList a) where
  constructor Over
  {0 support : SnocList a}
  value : p support
  thins : support `Thins` ctx

public export
rename : (ctx1 `Thins` ctx2) -> Thinned p ctx1 -> Thinned p ctx2
rename f (value `Over` thins) = value `Over` (f . thins)

public export
(.extract) : Rename a p => Thinned p ctx -> p ctx
(value `Over` thins).extract = rename thins value
