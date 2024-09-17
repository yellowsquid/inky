module Inky.Context

import public Data.Singleton
import public Data.So

import Data.Bool.Decidable
import Data.Maybe.Decidable
import Data.DPair
import Data.Nat

-- Contexts --------------------------------------------------------------------

export
infix 2 :-

export
prefix 2 %%

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
  record Assoc0 (a : Type) where
    constructor (:-)
    0 name : String
    value : a

  public export
  Functor Assoc0 where
    map f x = x.name :- f x.value

public export
data Context : Type -> Type where
  Lin : Context a
  (:<) : Context a -> Assoc a -> Context a

public export
Functor Context where
  map f [<] = [<]
  map f (ctx :< x) = map f ctx :< map f x

public export
Foldable Context where
  foldr f x [<] = x
  foldr f x (ctx :< (_ :- y)) = foldr f (f y x) ctx

  foldl f x [<] = x
  foldl f x (ctx :< (_ :- y)) = f (foldl f x ctx) y

  null [<] = True
  null (ctx :< x) = False

%name Context ctx

public export
data Length : Context a -> Type where
  Z : Length [<]
  S : Length ctx -> Length (ctx :< x)

%name Length len

public export
(++) : Context a -> Context a -> Context a
ctx ++ [<] = ctx
ctx ++ ctx' :< x = (ctx ++ ctx') :< x

export
lengthAppend : Length ctx1 -> Length ctx2 -> Length (ctx1 ++ ctx2)
lengthAppend len1 Z = len1
lengthAppend len1 (S len2) = S (lengthAppend len1 len2)

length : Context a -> Nat
length [<] = 0
length (ctx :< x) = S (length ctx)

-- Variables -------------------------------------------------------------------

public export
data VarPos : Context a -> (0 x : String) -> a -> Type where
  [search x]
  Here : VarPos (ctx :< (x :- v)) x v
  There : VarPos ctx x v -> VarPos (ctx :< y) x v

public export
record Var (ctx : Context a) (v : a) where
  constructor (%%)
  0 name : String
  {auto pos : VarPos ctx name v}

%name VarPos pos
%name Var i, j, k

public export
toVar : VarPos ctx x v -> Var ctx v
toVar pos = (%%) x {pos}

public export
toNat : VarPos ctx x v -> Nat
toNat Here = 0
toNat (There pos) = S (toNat pos)

public export
ThereVar : Var ctx v -> Var (ctx :< x) v
ThereVar i = toVar (There i.pos)

-- Basic Properties

export
thereCong :
  {0 i : VarPos ctx x v} -> {0 j : VarPos ctx y v} -> i = j ->
  There {y = z} i = There {y = z} j
thereCong Refl = Refl

export
toVarCong : {0 i : VarPos ctx x v} -> {0 j : VarPos ctx y w} -> i = j -> toVar i = toVar j
toVarCong Refl = Refl

export
toNatCong : {0 i : VarPos ctx x v} -> {0 j : VarPos ctx y w} -> i = j -> toNat i = toNat j
toNatCong Refl = Refl

export
toNatCong' : {0 i, j : Var ctx v} -> i = j -> toNat i.pos = toNat j.pos
toNatCong' Refl = Refl

export
toNatInjective : {i : VarPos ctx x v} -> {j : VarPos ctx y w} -> (0 _ : toNat i = toNat j) -> i = j
toNatInjective {i = Here} {j = Here} prf = Refl
toNatInjective {i = There i} {j = There j} prf with (toNatInjective {i} {j} $ injective prf)
  toNatInjective {i = There i} {j = There .(i)} prf | Refl = Refl

export
toVarInjective : {i : VarPos ctx x v} -> {j : VarPos ctx y v} -> (0 _ : toVar i = toVar j) -> i = j
toVarInjective prf = toNatInjective $ toNatCong' prf

-- Decidable Equality

export
eq : Var ctx v -> Var ctx w -> Bool
eq i j = toNat i.pos == toNat j.pos

public export
Eq (Var {a} ctx v) where
  (==) = eq

reflectPosEq :
  (i : VarPos ctx x v) ->
  (j : VarPos ctx y w) ->
  (i = j) `Reflects` (toNat i == toNat j)
reflectPosEq Here Here = RTrue Refl
reflectPosEq Here (There j) = RFalse (\case Refl impossible)
reflectPosEq (There i) Here = RFalse (\case Refl impossible)
reflectPosEq (There i) (There j) with (reflectPosEq i j) | (toNat i == toNat j)
  reflectPosEq (There i) (There .(i)) | RTrue Refl | _ = RTrue Refl
  _ | RFalse neq | _ = RFalse (\case Refl => neq Refl)

export
reflectEq : (i : Var {a} ctx v) -> (j : Var ctx w) -> (i = j) `Reflects` (i `eq` j)
reflectEq ((%%) x {pos = pos1}) ((%%) y {pos = pos2})
  with (reflectPosEq pos1 pos2) | (toNat pos1 == toNat pos2)
  _ | RTrue eq | _ = RTrue (toVarCong eq)
  _ | RFalse neq | _ = RFalse (\case Refl => neq Refl)

-- Weakening

wknLPos : VarPos ctx1 x v -> Length ctx2 -> VarPos (ctx1 ++ ctx2) x v
wknLPos pos Z = pos
wknLPos pos (S len) = There (wknLPos pos len)

wknRPos : VarPos ctx2 x v -> VarPos (ctx1 ++ ctx2) x v
wknRPos Here = Here
wknRPos (There pos) = There (wknRPos pos)

splitPos : Length ctx2 -> VarPos (ctx1 ++ ctx2) x v -> Either (VarPos ctx1 x v) (VarPos ctx2 x v)
splitPos Z pos = Left pos
splitPos (S len) Here = Right Here
splitPos (S len) (There pos) = mapSnd There $ splitPos len pos

export
wknL : {auto len : Length ctx2} -> Var ctx1 v -> Var (ctx1 ++ ctx2) v
wknL i = toVar $ wknLPos i.pos len

export
wknR : Var ctx2 v -> Var (ctx1 ++ ctx2) v
wknR i = toVar $ wknRPos i.pos

export
split : {auto len : Length ctx2} -> Var (ctx1 ++ ctx2) x -> Either (Var ctx1 x) (Var ctx2 x)
split i = bimap toVar toVar $ splitPos len i.pos

export
lift :
  {auto len : Length ctx} ->
  (forall x. Var ctx1 x -> Var ctx2 x) ->
  Var (ctx1 ++ ctx) x -> Var (ctx2 ++ ctx) x
lift f = either (wknL {len} . f) wknR . split {len}

-- Names

nameOfPos : {ctx : Context a} -> VarPos ctx x v -> Singleton x
nameOfPos Here = Val x
nameOfPos (There pos) = nameOfPos pos

export
nameOf : {ctx : Context a} -> (i : Var ctx v) -> Singleton i.name
nameOf i = nameOfPos i.pos

-- Environments ----------------------------------------------------------------

namespace Quantifier
  public export
  data All : (0 p : a -> Type) -> Context a -> Type where
    Lin : All p [<]
    (:<) :
      All p ctx -> (px : Assoc0 (p x.value)) ->
      {auto 0 prf : px.name = x.name}->
      All p (ctx :< x)

  %name Quantifier.All env

  indexAllPos : VarPos ctx x v -> All p ctx -> p v
  indexAllPos Here (env :< px) = px.value
  indexAllPos (There pos) (env :< px) = indexAllPos pos env

  export
  indexAll : Var ctx v -> All p ctx -> p v
  indexAll i env = indexAllPos i.pos env

  export
  mapProperty : ({0 x : a} -> p x -> q x) -> All p ctx -> All q ctx
  mapProperty f [<] = [<]
  mapProperty f (env :< (x :- px)) = mapProperty f env :< (x :- f px)

  export
  (++) : All p ctx1 -> All p ctx2 -> All p (ctx1 ++ ctx2)
  env1 ++ [<] = env1
  env1 ++ env2 :< px = (env1 ++ env2) :< px

-- Rows ------------------------------------------------------------------------

namespace Row
  ||| Contexts where names are unique.
  public export
  data Row : Type -> Type

  public export
  freshIn : String -> Row a -> Bool

  data Row where
    Lin : Row a
    (:<) : (row : Row a) -> (x : Assoc a) -> {auto 0 fresh : So (x.name `freshIn` row)} -> Row a

  x `freshIn` [<] = True
  x `freshIn` (row :< y) = x /= y.name && (x `freshIn` row)

  %name Row row

  public export
  map : (a -> b) -> Row a -> Row b
  export
  0 mapFresh : (f : a -> b) -> (row : Row a) -> So (x `freshIn` row) -> So (x `freshIn` map f row)

  map f [<] = [<]
  map f ((:<) row x {fresh}) = (:<) (map f row) (map f x) {fresh = mapFresh f row fresh}

  mapFresh f [<] = id
  mapFresh f (row :< (y :- _)) = andSo . mapSnd (mapFresh f row) . soAnd

  public export
  Functor Row where
    map = Row.map

  public export
  Foldable Row where
    foldr f x [<] = x
    foldr f x (row :< (_ :- y)) = foldr f (f y x) row

    foldl f x [<] = x
    foldl f x (row :< (_ :- y)) = f (foldl f x row) y

    null [<] = True
    null (row :< x) = False

  ||| Forget the freshness of names.
  public export
  forget : Row a -> Context a
  forget [<] = [<]
  forget (row :< x) = forget row :< x

  -- Equality --

  soUnique : (x, y : So b) -> x = y
  soUnique Oh Oh = Refl

  export
  snocCong2 :
    {0 row1, row2 : Row a} -> row1 = row2 ->
    {0 x, y : Assoc a} -> x = y ->
    {0 fresh1 : So (x.name `freshIn` row1)} ->
    {0 fresh2 : So (y.name `freshIn` row2)} ->
    row1 :< x = row2 :< y
  snocCong2 Refl Refl = rewrite soUnique fresh1 fresh2 in Refl

  -- Variables aren't fresh --

  -- NOTE: cannot implement
  0 strEqReflect : (x, y : String) -> (x = y) `Reflects` (x == y)
  strEqReflect x y = believe_me ()

  0 strEqRefl : (x : String) -> Not (So (x /= x))
  strEqRefl x prf with (strEqReflect x x) | (x == x)
    _ | RTrue _ | _ = absurd prf
    _ | RFalse neq | _ = neq Refl

  export
  0 varPosNotFresh : VarPos (forget row) x v -> Not (So (x `freshIn` row))
  varPosNotFresh {row = row :< (x :- v)} Here fresh = strEqRefl x (fst $ soAnd fresh)
  varPosNotFresh {row = row :< y} (There pos) fresh = varPosNotFresh pos (snd $ soAnd fresh)

  export
  varUniqueIndex : (row : Row a) -> VarPos (forget row) x v -> VarPos (forget row) x w -> v = w
  varUniqueIndex (row :< (x :- _)) Here Here = Refl
  varUniqueIndex ((:<) row (x :- _) {fresh}) Here (There pos2) = void $ varPosNotFresh pos2 fresh
  varUniqueIndex ((:<) row (x :- _) {fresh}) (There pos1) Here = void $ varPosNotFresh pos1 fresh
  varUniqueIndex (row :< (y :- _)) (There pos1) (There pos2) = varUniqueIndex row pos1 pos2

  -- Equivalence --

  export infix 6 <~>

  public export
  data Step : Row a -> Row a -> Type where
    Cong :
      Step row1 row2 -> (0 x : Assoc a) ->
      {0 fresh1 : So (x.name `freshIn` row1)} ->
      {0 fresh2 : So (x.name `freshIn` row2)} ->
      Step (row1 :< x) (row2 :< x)
    Swap :
      (0 x : Assoc a) -> (0 y : Assoc a) ->
      {0 fresh1 : So (x.name `freshIn` row)} ->
      {0 fresh2 : So (y.name `freshIn` row :< x)} ->
      {0 fresh3 : So (y.name `freshIn` row)} ->
      {0 fresh4 : So (x.name `freshIn` row :< y)} ->
      Step (row :< x :< y) (row :< y :< x)

  public export
  data (<~>) : Row a -> Row a -> Type where
    Nil : row <~> row
    (::) : Step row1 row2 -> row2 <~> row3 -> row1 <~> row3

  %name Step step
  %name (<~>) prf

  export
  trans : row1 <~> row2 -> row2 <~> row3 -> row1 <~> row3
  trans [] prf = prf
  trans (step :: prf1) prf2 = step :: trans prf1 prf2

  symStep : Step row1 row2 -> Step row2 row1
  symStep (Cong step x) = Cong (symStep step) x
  symStep (Swap x y) = Swap y x

  export
  sym : row1 <~> row2 -> row2 <~> row1
  sym [] = []
  sym (step :: prf) = trans (sym prf) [symStep step]

  equivLengthStep : Step row1 row2 -> length (forget row1) = length (forget row2)
  equivLengthStep (Cong step x) = cong S (equivLengthStep step)
  equivLengthStep (Swap x y) = Refl

  equivLength : row1 <~> row2 -> length (forget row1) = length (forget row2)
  equivLength [] = Refl
  equivLength (step :: prf) = trans (equivLengthStep step) (equivLength prf)

  export
  Uninhabited ((:<) row x {fresh} <~> [<]) where
    uninhabited prf = absurd (equivLength prf)

  export
  Uninhabited ([<] <~> (:<) row x {fresh}) where
    uninhabited prf = absurd (equivLength prf)

  0 equivFreshInStep : Step row1 row2 -> So (x `freshIn` row1) -> So (x `freshIn` row2)
  equivFreshInStep (Cong step y) = andSo . mapSnd (equivFreshInStep step) . soAnd
  equivFreshInStep (Swap {row} (y :- v) (z :- w)) =
    andSo . mapSnd andSo .
    (\(prf1, prf2, prf3) => (prf2, prf1, prf3)) .
    mapSnd (soAnd {a = x /= y, b = freshIn x row}) . soAnd

  0 equivFreshIn : row1 <~> row2 -> So (x `freshIn` row1) -> So (x `freshIn` row2)
  equivFreshIn [] = id
  equivFreshIn (step :: prf) = equivFreshIn prf . equivFreshInStep step

  cong :
    row1 <~> row2 -> (0 x : Assoc a) ->
    {0 fresh1 : So (x.name `freshIn` row1)} ->
    {0 fresh2 : So (x.name `freshIn` row2)} ->
    row1 :< x <~> row2 :< x
  cong [] x = rewrite soUnique fresh1 fresh2 in []
  cong (step :: prf) x =
    let 0 fresh' = equivFreshInStep step fresh1 in
    Cong step x {fresh2 = fresh'} :: cong prf x

  -- Removal --

  public export
  removePos : (row : Row a) -> VarPos (forget row) x v -> (Singleton v, Row a)
  export
  0 removePosFresh :
    (row : Row a) -> (pos : VarPos (forget row) x v) ->
    So (y `freshIn` row) -> So (y `freshIn` snd (removePos row pos))

  removePos (row :< (_ :- v)) Here = (Val v, row)
  removePos ((:<) row x {fresh}) (There pos) =
    ( fst (removePos row pos)
    , (:<) (snd $ removePos row pos) x {fresh = removePosFresh row pos fresh}
    )

  removePosFresh (row :< _) Here = snd . soAnd
  removePosFresh ((:<) row (z :- v) {fresh}) (There pos) =
    andSo . mapSnd (removePosFresh row pos) . soAnd

  public export
  remove : (row : Row a) -> Var (forget row) v -> (Singleton v, Row a)
  remove row i = removePos row i.pos

  -- Reflection

  -- NOTE: cannot implement
  0 soNotSym : {x, y : String} -> So (x /= y) -> So (y /= x)
  soNotSym = believe_me

  0 freshNotPos : (row : Row a) -> VarPos (forget row) x v -> So (y `freshIn` row) -> So (y /= x)
  freshNotPos (row :< _) Here = fst . soAnd
  freshNotPos (row :< x) (There pos) = freshNotPos row pos . snd . soAnd

  export
  0 removedIsFresh :
    (row : Row a) -> (pos : VarPos (forget row) x v) ->
    So (x `freshIn` snd (removePos row pos))
  removedIsFresh ((:<) row _ {fresh}) Here = fresh
  removedIsFresh ((:<) row (y :- v) {fresh}) (There pos) =
    andSo (soNotSym (freshNotPos row pos fresh), removedIsFresh row pos)

  export
  reflectRemovePos :
    (row : Row a) -> (pos : VarPos (forget row) x v) ->
    (:<) (snd $ removePos row pos) (x :- v) {fresh = removedIsFresh row pos} <~> row
  reflectRemovePos ((:<) row _ {fresh}) Here = []
  reflectRemovePos ((:<) row (y :- w) {fresh}) (There pos) =
    (  Swap (y :- w) (x :- v)
         {fresh4 = andSo (freshNotPos row pos fresh, removePosFresh row pos fresh)}
    :: cong (reflectRemovePos row pos) (y :- w))

  -- Tracing Variables --

  equivVarPosStep : Step row1 row2 -> VarPos (forget row1) x v -> VarPos (forget row2) x v
  equivVarPosStep (Cong step _) Here = Here
  equivVarPosStep (Cong step y) (There pos) = There (equivVarPosStep step pos)
  equivVarPosStep (Swap y _) Here = There Here
  equivVarPosStep (Swap _ z) (There Here) = Here
  equivVarPosStep (Swap y z) (There (There pos)) = There (There pos)

  export
  equivVarPos : row1 <~> row2 -> VarPos (forget row1) x v -> VarPos (forget row2) x v
  equivVarPos [] = id
  equivVarPos (step :: prf) = equivVarPos prf . equivVarPosStep step

  removePosInjectiveStep :
    (prf : Step row1 row2) -> (pos : VarPos (forget row1) x v) ->
    snd (removePos row1 pos) <~> snd (removePos row2 (equivVarPosStep prf pos))
  removePosInjectiveStep (Cong step _) Here = [step]
  removePosInjectiveStep (Cong step (y :- v)) (There pos) =
    cong (removePosInjectiveStep step pos) (y :- v)
  removePosInjectiveStep (Swap (y :- v) _) Here = cong [] (y :- v)
  removePosInjectiveStep (Swap _ (z :- v)) (There Here) = cong [] (z :- v)
  removePosInjectiveStep (Swap (y :- v) (z :- w)) (There (There pos)) = [Swap (y :- v) (z :- w)]

  export
  removePosInjective :
    (prf : row1 <~> row2) -> (pos : VarPos (forget row1) x v) ->
    snd (removePos row1 pos) <~> snd (removePos row2 (equivVarPos prf pos))
  removePosInjective [] pos = []
  removePosInjective (step :: prf) pos =
    trans (removePosInjectiveStep step pos) (removePosInjective prf $ equivVarPosStep step pos)

  export
  equivVarUnique :
    {0 fresh1 : So (x `freshIn` row1)} ->
    {0 fresh2 : So (x `freshIn` row2)} ->
    (prf : row1 :< (x :- v) <~> row2 :< (x :- v)) ->
    equivVarPos prf Here = Here
  equivVarUnique prf with (equivVarPos prf Here)
    _ | Here = Refl
    _ | There pos = void $ varPosNotFresh pos fresh2

  -- Partial Removal --

  FreshOrNothing : String -> Maybe (a, Row a) -> Type
  FreshOrNothing x Nothing = ()
  FreshOrNothing x (Just (a, row)) = So (x `freshIn` row)

  removeHelper :
    (m : Maybe (a, Row a)) -> (x : Assoc a) ->
    (0 fresh : FreshOrNothing x.name m) ->
    Maybe (a, Row a)
  removeHelper Nothing x fresh = Nothing
  removeHelper (Just (v, row)) x fresh = Just (v, row :< x)

  ||| Attempt to remove the value at name `x` from the row.
  export
  remove' : String -> Row a -> Maybe (a, Row a)
  removeFresh :
    (x : String) -> (row : Row a) ->
    {y : String} -> So (y `freshIn` row) -> FreshOrNothing y (remove' x row)

  remove' x [<] = Nothing
  remove' x ((:<) row (y :- v) {fresh}) =
    if y == x
    then Just (v, row)
    else removeHelper (remove' x row) (y :- v) (removeFresh x row fresh)

  removeFresh x [<] prf = ()
  removeFresh x (row :< (y :- v)) {y = z} prf with (y == x)
    _ | True = snd (soAnd prf)
    _ | False with (removeFresh x row $ snd $ soAnd prf) | (remove' x row)
      _ | _ | Nothing = ()
      _ | prf' | Just (v', row') = andSo (fst (soAnd prf), prf')

  -- Reflection

  notSoToSoNot : {b : Bool} -> Not (So b) -> So (not b)
  notSoToSoNot {b = False} nprf = Oh
  notSoToSoNot {b = True} nprf = absurd (nprf Oh)

  0 reflectRemoveHelper : {x, y : String} -> Not (x = y) -> Not (So (x == y))
  reflectRemoveHelper neq eq with (strEqReflect x y) | (x == y)
    reflectRemoveHelper neq Oh | RTrue eq | _ = neq eq

  reflectRemoveHelper' :
    {0 fresh1 : So (y `freshIn` row1)} ->
    (x : String) -> Not (y = x) ->
    (0 fresh2 : So (x `freshIn` row2)) -> (prf : row1 :< (y :- v) <~> row2 :< (x :- v')) ->
    (  pos : VarPos (forget row2) y v
    ** snd (removePos (row2 :< (x :- v')) (equivVarPos prf Here)) <~>
           (:<) (snd (removePos row2 pos)) (x :- v')
             {fresh = removePosFresh row2 pos {y = x} fresh2})
  reflectRemoveHelper' x neq fresh2 prf with (equivVarPos prf Here)
    reflectRemoveHelper' x neq fresh2 prf | Here = absurd (neq Refl)
    reflectRemoveHelper' x neq fresh2 prf | There pos =
      (pos ** [])

  public export
  Remove : String -> Row a -> a -> Row a -> Type
  Remove x row v row' =
    Exists {type = So (x `freshIn` row')} (\fresh => row <~> row' :< (x :- v))

  export
  removeUnique :
    (x : String) -> (row1 : Row a) ->
    Remove x row1 v row2 -> Remove x row1 w row3 -> (v = w, row2 <~> row3)
  removeUnique x row1 (Evidence fresh1 prf1) (Evidence fresh2 prf2) =
    let eq = varUniqueIndex row1 (equivVarPos (sym prf1) Here) (equivVarPos (sym prf2) Here) in
    let
      prf : row2 :< (x :- v) <~> row3 :< (x :- v)
      prf = trans (sym prf1) (rewrite eq in prf2)
    in
    ( eq
    , replace
        {p = \pos => row2 <~> snd (removePos (row3 :< (x :- v)) pos)}
        (equivVarUnique prf)
        (removePosInjective prf Here))

  export
  0 reflectRemove :
    (x : String) -> (row : Row a) ->
    uncurry (Remove x row) `OnlyWhen` remove' x row
  reflectRemove x [<] = RNothing (\(v, row), (Evidence _ prf) => absurd prf)
  reflectRemove x ((:<) row (y :- v) {fresh}) with (strEqReflect y x) | (y == x)
    _ | RTrue eq | _ = rewrite sym eq in RJust (Evidence fresh [])
    _ | RFalse neq | _ with (reflectRemove x row, removeFresh x row {y}) | (remove' x row)
      _ | (RJust (Evidence fresh' prf), mkFresh) | Just (v', row') =
        RJust (Evidence
          (andSo (notSoToSoNot (reflectRemoveHelper (\eq => neq $ sym eq)), fresh'))
          (trans
            (cong prf (y :- v)
              {fresh2 = andSo (notSoToSoNot (reflectRemoveHelper neq), mkFresh fresh)})
            [Swap (x :- v') (y :- v)]))
      _ | (RNothing nprf, mkFresh) | _ =
        RNothing (\(v', row'), (Evidence fresh' prf) =>
          let (pos ** prf') = reflectRemoveHelper' x neq fresh' prf in
          void $
          nprf (v', snd (remove row' ((%%) y {pos}))) $
          Evidence
            (removePosFresh row' pos fresh')
            (trans (removePosInjective prf Here) prf'))
