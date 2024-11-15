module Inky.Data.Thinned

import public Flap.Data.SnocList.Thinning

public export
record Thinned (0 p : SnocList a -> Type) (ctx : SnocList a) where
  constructor Over
  {0 support : SnocList a}
  value : p support
  thins : support `Thins` ctx

public export
rename : (ctx1 `Thins` ctx2) -> Thinned p ctx1 -> Thinned p ctx2
rename f v = v.value `Over` (f . v.thins)

public export
(.extract) : Rename a p => Thinned p ctx -> p ctx
v.extract = rename v.thins v.value

export
0 extractHomo :
  Rename a p =>
  (f : ctx1 `Thins` ctx2) -> (x : Thinned p ctx1) ->
  rename f x.extract = (rename f x).extract
extractHomo f x = renameHomo f x.thins x.value
