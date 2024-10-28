module Inky.Data.Context

import public Inky.Data.Assoc
import public Inky.Data.SnocList

import Inky.Data.SnocList.Quantifiers

-- Contexts --------------------------------------------------------------------

public export
Context : Type -> Type
Context a = SnocList (Assoc a)

public export
(.names) : Context a -> SnocList String
[<].names = [<]
(ctx :< nx).names = ctx.names :< nx.name

export
mapNames : (0 f : a -> b) -> (ctx : Context a) -> (map (map f) ctx).names = ctx.names
mapNames f [<] = Refl
mapNames f (ctx :< nx) = cong (:< nx.name) $ mapNames f ctx

-- Construction ----------------------------------------------------------------

public export
fromAll : (ctx : Context a) -> All (const b) ctx.names -> Context b
fromAll [<] [<] = [<]
fromAll (ctx :< (n :- _)) (sx :< x) = fromAll ctx sx :< (n :- x)

export
fromAllNames :
  (ctx : Context a) -> (sx : All (const b) ctx.names) ->
  (fromAll ctx sx).names = ctx.names
fromAllNames [<] [<] = Refl
fromAllNames (ctx :< (n :- _)) (sx :< x) = cong (:< n) $ fromAllNames ctx sx
