module Inky.Data.Row

import public Data.So
import public Flap.Data.Context
import public Flap.Data.SnocList.Quantifiers

import Data.Singleton
import Flap.Data.SnocList.Elem
import Flap.Decidable

public export
FreshIn : String -> SnocList String -> Type
FreshIn n = All (\x => So (x /= n))

public export
AllFresh : SnocList String -> Type
AllFresh = Pairwise (So .: (/=))

public export
record Row (a : Type) where
  constructor MkRow
  context : Context a
  0 fresh : AllFresh context.names

%name Row row

public export
(.names) : Row a -> SnocList String
row.names = row.context.names

-- Equality --------------------------------------------------------------------

export
soUnique : (prf1, prf2 : So b) -> prf1 = prf2
soUnique Oh Oh = Refl

export
freshInUnique : (freshIn1, freshIn2 : x `FreshIn` sx) -> freshIn1 = freshIn2
freshInUnique [<] [<] = Refl
freshInUnique (freshIn1 :< prf1) (freshIn2 :< prf2) =
  cong2 (:<) (freshInUnique freshIn1 freshIn2) (soUnique prf1 prf2)

export
freshUnique : (fresh1, fresh2 : AllFresh sx) -> fresh1 = fresh2
freshUnique [<] [<] = Refl
freshUnique (fresh1 :< freshIn1) (fresh2 :< freshIn2) =
  cong2 (:<) (freshUnique fresh1 fresh2) (freshInUnique freshIn1 freshIn2)

export
rowCong :
  {0 ctx1, ctx2 : Context a} ->
  {0 fresh1 : AllFresh ctx1.names} ->
  {0 fresh2 : AllFresh ctx2.names} ->
  ctx1 = ctx2 -> MkRow ctx1 fresh1 = MkRow ctx2 fresh2
rowCong Refl = rewrite freshUnique fresh1 fresh2 in Refl

-- Smart Constructors ----------------------------------------------------------

public export
Lin : Row a
Lin = MkRow [<] [<]

public export
(:<) :
  (row : Row a) -> (x : Assoc a) ->
  (0 fresh : x.name `FreshIn` row.names) =>
  Row a
row :< x = MkRow (row.context :< x) (row.fresh :< fresh)

export
snocCong :
  {0 x, y : Assoc a} ->
  row1 = row2 -> x = y ->
  {0 fresh1 : x.name `FreshIn` row1.names} ->
  {0 fresh2 : y.name `FreshIn` row2.names} ->
  (:<) row1 x @{fresh1} = (:<) row2 y @{fresh2}
snocCong eq1 eq2 = rowCong $ cong2 (\x, y => x.context :< y) eq1 eq2

public export
fromAll : {sx : SnocList String} -> (ctx : All (Assoc0 b) sx) -> (0 fresh : AllFresh sx) -> Row b
fromAll ctx fresh = MkRow (fromAll ctx) (rewrite fromAllNames ctx in fresh)

-- Interfaces ------------------------------------------------------------------

public export
mapRow : (a -> b) -> (ctx : Context a) -> (0 fresh : AllFresh ctx.names) -> Row b
export
mapRowNames :
  (0 f : a -> b) -> (ctx : Context a) -> (0 fresh : AllFresh ctx.names) ->
  (mapRow f ctx fresh).names = ctx.names

mapRow f [<] [<] = [<]
mapRow f (ctx :< (l :- x)) (prfs :< prf) =
  (:<) (mapRow f ctx prfs) (l :- f x) @{rewrite mapRowNames f ctx prfs in prf}

mapRowNames f [<] [<] = Refl
mapRowNames f (ctx :< (l :- x)) (prfs :< prf) = cong (:< l) $ mapRowNames f ctx prfs

public export
Functor Row where
  map f row = mapRow f row.context row.fresh

public export
Foldable Row where
  foldr f x row = foldr (\x, y => f x.value y) x row.context
  foldl f x row = foldl (\x, y => f x y.value) x row.context
  null row = null row.context
  foldlM f x row = foldlM (\x, y => f x y.value) x row.context
  foldMap f row = foldMap (f . value) row.context

-- Operations ------------------------------------------------------------------

export
isFresh :
  (names : SnocList String) ->
  (name : String) ->
  LazyEither (name `FreshIn` names) (Any (\x => So (x == name)) names)
isFresh names name = all (\x => not (so $ x == name)) names

export
extend : Row a -> Assoc a -> Maybe (Row a)
extend row x = case (isFresh row.names x.name) of
  True `Because` prf => Just ((:<) row x @{prf})
  False `Because` _ => Nothing

-- Search ----------------------------------------------------------------------

noLookupFresh :
  (ctx : Context a) ->
  (0 freshIn : n `FreshIn` ctx.names) ->
  Not (Elem (n :- x) ctx)
noLookupFresh (sx :< (n :- x)) (freshIn :< prf) Here with ((decEq n n).reason) | ((decEq n n).does)
  _ | _ | True = void $ absurd prf
  _ | contra | False = void $ contra Refl
noLookupFresh (sx :< (k :- _)) (freshIn :< prf) (There i) = noLookupFresh sx freshIn i

doLookupUnique :
  (ctx : Context a) ->
  (0 fresh : AllFresh ctx.names) ->
  (i : Elem (n :- x) ctx) ->
  (j : Elem (n :- y) ctx) ->
  the (x ** Elem (n :- x) ctx) (x ** i) = (y ** j)
doLookupUnique (ctx :< (n :- x)) (fresh :< freshIn) Here Here = Refl
doLookupUnique (ctx :< (n :- x)) (fresh :< freshIn) Here (There j) = void $ noLookupFresh ctx freshIn j
doLookupUnique (ctx :< (n :- z)) (fresh :< freshIn) (There i) Here = void $ noLookupFresh ctx freshIn i
doLookupUnique (ctx :< (k :- z)) (fresh :< freshIn) (There i) (There j) =
  cong (\(x ** i) => (x ** There i)) $
  doLookupUnique ctx fresh i j

export
lookupUnique :
  (row : Row a) ->
  (i : Elem (n :- x) row.context) ->
  (j : Elem (n :- y) row.context) ->
  the (x ** Elem (n :- x) row.context) (x ** i) = (y ** j)
lookupUnique row i j = doLookupUnique row.context row.fresh i j

notHere :
  {0 ctx : Context a} ->
  (i : Elem (n :- x) (ctx :< (l :- y))) ->
  Not (n = l) -> (j : Elem (n :- x) ctx ** i = There j)
notHere Here neq = void $ neq Refl
notHere (There i) _ = (i ** Refl)

doLookupRecompute :
  (ctx : Context a) -> (0 fresh : AllFresh ctx.names) ->
  {n : String} -> (0 i : Elem (n :- x) ctx) -> Singleton i
doLookupRecompute [<] [<] i = void $ absurd i
doLookupRecompute (ctx :< (l :- x)) (fresh :< freshIn) i with (decEq n l)
  doLookupRecompute (ctx :< (l :- x)) (fresh :< freshIn) i | True `Because` Refl =
    replace {p = \x => Singleton x.snd}
      (doLookupUnique (ctx :< (l :- x)) (fresh :< freshIn) Here i)
      (Val Here)
  _ | False `Because` contra =
    let 0 jeq = notHere i contra in
    rewrite snd jeq in
    [| There $ doLookupRecompute ctx fresh (fst jeq) |]

export
lookupRecompute :
  (row : Row a) -> {n : String} ->
  (0 i : Elem (n :- x) row.context) -> Singleton i
lookupRecompute row i = doLookupRecompute row.context row.fresh i

-- Removal ---------------------------------------------------------------------

dropElemFreshIn :
  (ctx : Context a) -> n `FreshIn` ctx.names -> (i : Elem nx ctx) ->
  n `FreshIn` (dropElem ctx i).names
dropElemFreshIn (ctx :< (n :- x)) (freshIn :< prf) Here = freshIn
dropElemFreshIn (ctx :< (n :- x)) (freshIn :< prf) (There i) = dropElemFreshIn ctx freshIn i :< prf

export
dropElemFresh :
  (ctx : Context a) -> AllFresh ctx.names -> (i : Elem nx ctx) ->
  AllFresh (dropElem ctx i).names
dropElemFresh (ctx :< (n :- x)) (fresh :< freshIn) Here = fresh
dropElemFresh (ctx :< (n :- x)) (fresh :< freshIn) (There i) =
  dropElemFresh ctx fresh i :< dropElemFreshIn ctx freshIn i
