module Inky.Type

import public Inky.Data.Context.Var
import public Inky.Data.Row
import public Inky.Data.SnocList.Var

import Control.Function
import Data.DPair
import Data.These

import Inky.Data.SnocList.Thinning
import Inky.Data.Thinned
import Inky.Decidable
import Inky.Decidable.Maybe

%hide Prelude.Ops.infixl.(>=>)

-- Definition ------------------------------------------------------------------

public export
data Ty : SnocList String -> Type where
  TVar : Var ctx -> Ty ctx
  TArrow : Ty ctx -> Ty ctx -> Ty ctx
  TProd : (as : Row (Ty ctx)) -> Ty ctx
  TSum : (as : Row (Ty ctx)) -> Ty ctx
  TFix : (x : String) -> Ty (ctx :< x) -> Ty ctx

%name Ty a, b, c

export
Injective TProd where
 injective Refl = Refl

export
Injective TSum where
 injective Refl = Refl

export
fixInjective : TFix x t = TFix y u -> the (x ** Ty (ctx :< x)) (x ** t) = (y ** u)
fixInjective Refl = Refl

-- Decisions -------------------------------------------------------------------

export
Uninhabited (TVar i = TArrow a b) where
  uninhabited Refl impossible

export
Uninhabited (TVar i = TProd as) where
  uninhabited Refl impossible

export
Uninhabited (TVar i = TSum as) where
  uninhabited Refl impossible

export
Uninhabited (TVar i = TFix x a) where
  uninhabited Refl impossible

export
Uninhabited (TArrow a b = TProd as) where
  uninhabited Refl impossible

export
Uninhabited (TArrow a b = TSum as) where
  uninhabited Refl impossible

export
Uninhabited (TArrow a b = TFix x c) where
  uninhabited Refl impossible

export
Uninhabited (TProd as = TArrow a b) where
  uninhabited Refl impossible

export
Uninhabited (TProd as = TSum bs) where
  uninhabited Refl impossible

export
Uninhabited (TProd as = TFix x a) where
  uninhabited Refl impossible

export
Uninhabited (TSum as = TArrow a b) where
  uninhabited Refl impossible

export
Uninhabited (TSum as = TProd bs) where
  uninhabited Refl impossible

export
Uninhabited (TSum as = TFix x a) where
  uninhabited Refl impossible

export
Uninhabited (TFix x a = TArrow b c) where
  uninhabited Refl impossible

export
Uninhabited (TFix x a = TProd as) where
  uninhabited Refl impossible

export
Uninhabited (TFix x a = TSum as) where
  uninhabited Refl impossible

public export
isArrow :
  (a : Ty ctx) ->
  Proof (Ty ctx, Ty ctx) (\bc => a = TArrow (fst bc) (snd bc))
    ((b, c : Ty ctx) -> Not (a = TArrow b c))
isArrow (TVar i) = Nothing `Because` (\_, _ => absurd)
isArrow (TArrow a b) = Just (a, b) `Because` Refl
isArrow (TProd as) = Nothing `Because` (\_, _ => absurd)
isArrow (TSum as) = Nothing `Because` (\_, _ => absurd)
isArrow (TFix x a) = Nothing `Because` (\_, _ => absurd)

public export
isProd : (a : Ty ctx) -> DecWhen (Row (Ty ctx)) (\as => a = TProd as)
isProd (TVar i) = Nothing `Because` (\_ => absurd)
isProd (TArrow a b) = Nothing `Because` (\_ => absurd)
isProd (TProd as) = Just as `Because` Refl
isProd (TSum as) = Nothing `Because` (\_ => absurd)
isProd (TFix x a) = Nothing `Because` (\_ => absurd)

public export
isSum : (a : Ty ctx) -> DecWhen (Row (Ty ctx)) (\as => a = TSum as)
isSum (TVar i) = Nothing `Because` (\_ => absurd)
isSum (TArrow a b) = Nothing `Because` (\_ => absurd)
isSum (TProd as) = Nothing `Because` (\_ => absurd)
isSum (TSum as) = Just as `Because` Refl
isSum (TFix x a) = Nothing `Because` (\_ => absurd)

public export
isFix :
  (a : Ty ctx) ->
  Proof (x ** Ty (ctx :< x)) (\xb => a = TFix (fst xb) (snd xb))
    ((x : _) -> (b : _) -> Not (a = TFix x b))
isFix (TVar i) = Nothing `Because` (\_, _ => absurd)
isFix (TArrow a b) = Nothing `Because` (\_, _ => absurd)
isFix (TProd as) = Nothing `Because` (\_, _ => absurd)
isFix (TSum as) = Nothing `Because` (\_, _ => absurd)
isFix (TFix x a) = Just (x ** a) `Because` Refl

-- Thinning --------------------------------------------------------------------

thin : ctx1 `Thins` ctx2 -> Ty ctx1 -> Ty ctx2
thinAll : ctx1 `Thins` ctx2 -> Context (Ty ctx1) -> Context (Ty ctx2)
thinAllNames :
  (f : ctx1 `Thins` ctx2) ->
  (ctx : Context (Ty ctx1)) ->
  (thinAll f ctx).names = ctx.names

thin f (TVar i) = TVar (index f i)
thin f (TArrow a b) = TArrow (thin f a) (thin f b)
thin f (TProd (MkRow as fresh)) = TProd (MkRow (thinAll f as) (rewrite thinAllNames f as in fresh))
thin f (TSum (MkRow as fresh)) = TSum (MkRow (thinAll f as) (rewrite thinAllNames f as in fresh))
thin f (TFix x a) = TFix x (thin (Keep f) a)

thinAll f [<] = [<]
thinAll f (as :< (n :- a)) = thinAll f as :< (n :- thin f a)

thinAllNames f [<] = Refl
thinAllNames f (as :< (n :- a)) = cong (:< n) $ thinAllNames f as

-- Renaming Coalgebra

thinCong : f ~~~ g -> (a : Ty ctx1) -> thin f a = thin g a
thinCongAll : f ~~~ g -> (as : Context (Ty ctx1)) -> thinAll f as = thinAll g as

thinCong prf (TVar i) = cong TVar (prf.index i)
thinCong prf (TArrow a b) = cong2 TArrow (thinCong prf a) (thinCong prf b)
thinCong prf (TProd (MkRow as fresh)) = cong TProd (rowCong $ thinCongAll prf as)
thinCong prf (TSum (MkRow as fresh)) = cong TSum (rowCong $ thinCongAll prf as)
thinCong prf (TFix x a) = cong (TFix x) (thinCong (KeepKeep prf) a)

thinCongAll prf [<] = Refl
thinCongAll prf (as :< (n :- a)) =
  cong2 (:<) (thinCongAll prf as) (cong (n :-) $ thinCong prf a)

thinId : (a : Ty ctx) -> thin Id a = a
thinIdAll : (as : Context (Ty ctx)) -> thinAll Id as = as

thinId (TVar (%% x)) = Refl
thinId (TArrow a b) = cong2 TArrow (thinId a) (thinId b)
thinId (TProd (MkRow as fresh)) = cong TProd (rowCong $ thinIdAll as)
thinId (TSum (MkRow as fresh)) = cong TSum (rowCong $ thinIdAll as)
thinId (TFix x a) = cong (TFix x) (trans (thinCong (KeepId IdId) a) (thinId a))

thinIdAll [<] = Refl
thinIdAll (as :< (n :- a)) = cong2 (:<) (thinIdAll as) (cong (n :-) $ thinId a)

export
Rename String Ty where
  rename = thin
  renameCong = thinCong
  renameId = thinId

-- Alpha Equivalence ------------------------------------------------------------

namespace Shape
  public export
  data SameShape : Ty ctx1 -> Ty ctx2 -> Type where
    TVar : SameShape (TVar i) (TVar j)
    TArrow : SameShape (TArrow a c) (TArrow b d)
    TProd : SameShape (TProd as) (TProd bs)
    TSum : SameShape (TSum as) (TSum bs)
    TFix : SameShape (TFix x a) (TFix y b)

export
Uninhabited (SameShape (TVar i) (TArrow b d))
  where uninhabited TVar impossible

export
Uninhabited (SameShape (TVar i) (TProd bs))
  where uninhabited TVar impossible

export
Uninhabited (SameShape (TVar i) (TSum bs))
  where uninhabited TVar impossible

export
Uninhabited (SameShape (TVar i) (TFix y b))
  where uninhabited TVar impossible

export
Uninhabited (SameShape (TArrow a b) (TVar j))
  where uninhabited TVar impossible

export
Uninhabited (SameShape (TArrow a c) (TProd bs))
  where uninhabited TVar impossible

export
Uninhabited (SameShape (TArrow a c) (TSum bs))
  where uninhabited TVar impossible

export
Uninhabited (SameShape (TArrow a c) (TFix y b))
  where uninhabited TVar impossible

export
Uninhabited (SameShape (TProd as) (TVar j))
  where uninhabited TVar impossible

export
Uninhabited (SameShape (TProd as) (TArrow b d))
  where uninhabited TVar impossible

export
Uninhabited (SameShape (TProd as) (TSum bs))
  where uninhabited TVar impossible

export
Uninhabited (SameShape (TProd as) (TFix y b))
  where uninhabited TVar impossible

export
Uninhabited (SameShape (TSum as) (TVar j))
  where uninhabited TVar impossible

export
Uninhabited (SameShape (TSum as) (TArrow b d))
  where uninhabited TVar impossible

export
Uninhabited (SameShape (TSum as) (TProd bs))
  where uninhabited TVar impossible

export
Uninhabited (SameShape (TSum as) (TFix y b))
  where uninhabited TVar impossible

export
Uninhabited (SameShape (TFix x a) (TVar j))
  where uninhabited TVar impossible

export
Uninhabited (SameShape (TFix x a) (TArrow b d))
  where uninhabited TVar impossible

export
Uninhabited (SameShape (TFix x a) (TProd bs))
  where uninhabited TVar impossible

export
Uninhabited (SameShape (TFix x a) (TSum bs))
  where uninhabited TVar impossible

namespace Equivalence
  public export
  data Alpha : Ty ctx1 -> Ty ctx2 -> Type
  public export
  data AllAlpha : Context (Ty ctx1) -> Context (Ty ctx2) -> Type

  data Alpha where
    TVar : elemToNat i.pos = elemToNat j.pos -> Alpha (TVar i) (TVar j)
    TArrow : Alpha a b -> Alpha c d -> Alpha (TArrow a c) (TArrow b d)
    TProd : AllAlpha as.context bs.context -> Alpha (TProd as) (TProd bs)
    TSum : AllAlpha as.context bs.context -> Alpha (TSum as) (TSum bs)
    TFix : Alpha a b -> Alpha (TFix x a) (TFix y b)

  data AllAlpha where
    Base : AllAlpha [<] [<]
    Step :
      (i : Elem (n :- b) bs) ->
      Alpha a b ->
      AllAlpha as (dropElem bs i) ->
      AllAlpha (as :< (n :- a)) bs

namespace Inequivalence
  public export
  data NotAlpha : Ty ctx1 -> Ty ctx2 -> Type
  public export
  data AnyNotAlpha : Context (Ty ctx1) -> Context (Ty ctx2) -> Type

  data NotAlpha where
    Shape :
      Not (SameShape a b) ->
      NotAlpha a b
    TVar :
      Not (elemToNat i.pos = elemToNat j.pos) ->
      NotAlpha (TVar i) (TVar j)
    TArrow :
      These (NotAlpha a b) (NotAlpha c d) ->
      NotAlpha (TArrow a c) (TArrow b d)
    TProd :
      AnyNotAlpha as.context bs.context ->
      NotAlpha (TProd as) (TProd bs)
    TSum :
      AnyNotAlpha as.context bs.context ->
      NotAlpha (TSum as) (TSum bs)
    TFix :
      NotAlpha a b ->
      NotAlpha (TFix x a) (TFix y b)

  data AnyNotAlpha where
    Base : AnyNotAlpha [<] (bs :< b)
    Step1 :
      ((b : Ty ctx2) -> Not (Elem (n :- b) bs)) ->
      AnyNotAlpha (as :< (n :- a)) bs
    Step2 :
      (i : Elem (n :- b) bs) ->
      These (NotAlpha a b) (AnyNotAlpha as (dropElem bs i)) ->
      AnyNotAlpha (as :< (n :- a)) bs

%name Alpha prf
%name AllAlpha prfs
%name NotAlpha contra
%name AnyNotAlpha contras

export
alphaShape : Alpha a b -> SameShape a b
alphaShape (TVar prf) = TVar
alphaShape (TArrow prf1 prf2) = TArrow
alphaShape (TProd prfs) = TProd
alphaShape (TSum prfs) = TSum
alphaShape (TFix prf) = TFix

export
alphaRefl : (a : Ty ctx1) -> (0 b : Ty ctx2) -> a ~=~ b -> Alpha a b
allAlphaRefl : (as : Context (Ty ctx1)) -> (bs : Context (Ty ctx2)) -> as ~=~ bs -> AllAlpha as bs

alphaRefl (TVar i) .(TVar i) Refl = TVar Refl
alphaRefl (TArrow a b) .(TArrow a b) Refl = TArrow (alphaRefl a a Refl) (alphaRefl b b Refl)
alphaRefl (TProd (MkRow as fresh)) .(TProd (MkRow as fresh)) Refl = TProd (allAlphaRefl as as Refl)
alphaRefl (TSum (MkRow as fresh)) .(TSum (MkRow as fresh)) Refl = TSum (allAlphaRefl as as Refl)
alphaRefl (TFix x a) .(TFix x a) Refl = TFix (alphaRefl a a Refl)

allAlphaRefl [<] .([<]) Refl = Base
allAlphaRefl (as :< (l :- a)) .(as :< (l :- a)) Refl =
  Step Here (alphaRefl a a Refl) (allAlphaRefl as as Refl)

export
alphaSplit :
  {0 a : Ty ctx1} -> {0 b : Ty ctx2} ->
  Alpha a b -> NotAlpha a b -> Void
export
allAlphaSplit :
  {0 as : Context (Ty ctx1)} -> {0 bs : Context (Ty ctx2)} ->
  (0 fresh : AllFresh bs.names) ->
  AllAlpha as bs -> AnyNotAlpha as bs -> Void

alphaSplit prf (Shape contra) = contra (alphaShape prf)
alphaSplit (TVar prf) (TVar contra) = contra prf
alphaSplit (TArrow prf1 prf2) (TArrow contras) =
  these (alphaSplit prf1) (alphaSplit prf2) (const $ alphaSplit prf2) contras
alphaSplit (TProd {bs} prfs) (TProd contras) = allAlphaSplit bs.fresh prfs contras
alphaSplit (TSum {bs} prfs) (TSum contras) = allAlphaSplit bs.fresh prfs contras
alphaSplit (TFix prf) (TFix contra) = alphaSplit prf contra

allAlphaSplit fresh (Step i prf prfs) (Step1 contra) = void $ contra _ i
allAlphaSplit fresh (Step {as, n} i prf prfs) (Step2 j contras) =
  let 0 eq = lookupUnique (MkRow bs fresh) i j in
  these
    (\contra => alphaSplit prf $ rewrite cong fst eq in contra)
    (\contras =>
      allAlphaSplit (dropElemFresh bs fresh i) prfs $
      replace {p = \bi => AnyNotAlpha as (dropElem bs {x = n :- fst bi} $ snd bi)}
        (sym eq)
        contras)
    (\contra, _ => alphaSplit prf $ rewrite cong fst eq in contra)
    contras

export
alpha : (a : Ty ctx1) -> (b : Ty ctx2) -> LazyEither (Alpha a b) (NotAlpha a b)
export
allAlpha :
  (as : Context (Ty ctx1)) -> (bs : Context (Ty ctx2)) ->
  LazyEither (AllAlpha as bs) (AnyNotAlpha as bs)

alpha (TVar i) (TVar j) = map TVar TVar $ decEq (elemToNat i.pos) (elemToNat j.pos)
alpha (TVar i) (TArrow a b) = False `Because` Shape absurd
alpha (TVar i) (TProd as) = False `Because` Shape absurd
alpha (TVar i) (TSum as) = False `Because` Shape absurd
alpha (TVar i) (TFix x a) = False `Because` Shape absurd
alpha (TArrow a c) (TVar i) = False `Because` Shape absurd
alpha (TArrow a c) (TArrow b d) = map (uncurry TArrow) TArrow $ all (alpha a b) (alpha c d)
alpha (TArrow a c) (TProd as) = False `Because` Shape absurd
alpha (TArrow a c) (TSum as) = False `Because` Shape absurd
alpha (TArrow a c) (TFix x b) = False `Because` Shape absurd
alpha (TProd as) (TVar i) = False `Because` Shape absurd
alpha (TProd as) (TArrow a b) = False `Because` Shape absurd
alpha (TProd (MkRow as _)) (TProd bs) = map TProd TProd $ allAlpha as bs.context
alpha (TProd as) (TSum bs) = False `Because` Shape absurd
alpha (TProd as) (TFix x a) = False `Because` Shape absurd
alpha (TSum as) (TVar i) = False `Because` Shape absurd
alpha (TSum as) (TArrow a b) = False `Because` Shape absurd
alpha (TSum as) (TProd bs) = False `Because` Shape absurd
alpha (TSum (MkRow as _)) (TSum bs) = map TSum TSum $ allAlpha as bs.context
alpha (TSum as) (TFix x a) = False `Because` Shape absurd
alpha (TFix x a) (TVar i) = False `Because` Shape absurd
alpha (TFix x a) (TArrow b c) = False `Because` Shape absurd
alpha (TFix x a) (TProd as) = False `Because` Shape absurd
alpha (TFix x a) (TSum as) = False `Because` Shape absurd
alpha (TFix x a) (TFix y b) = map TFix TFix $ alpha a b

allAlpha [<] [<] = True `Because` Base
allAlpha [<] (bs :< nb) = False `Because` Base
allAlpha (as :< (n :- a)) bs =
  map
    (\((b ** i) ** (prf1, prf2)) => Step i prf1 prf2)
    (either Step1 false) $
  (bi := (decLookup n bs).forget) >=>
  all (alpha a $ fst bi) (allAlpha as (dropElem bs $ snd bi))
  where
  p : (b ** Elem (n :- b) bs) -> Type
  p bi = (Alpha a (fst bi), AllAlpha as (dropElem bs $ snd bi))

  q : (b ** Elem (n :- b) bs) -> Type
  q bi = These (NotAlpha a (fst bi)) (AnyNotAlpha as (dropElem bs $ snd bi))

  false : (bi ** q bi) -> AnyNotAlpha (as :< (n :- a)) bs
  false ((b ** i) ** contras) = Step2 i contras

-- Occurs ----------------------------------------------------------------------

namespace Strengthen
  public export
  data Strengthen : (i : Var ctx) -> Ty ctx -> Ty (dropElem ctx i.pos) -> Type
  public export
  data StrengthenAll :
    (i : Var ctx) -> (as : Context (Ty ctx)) ->
    All (const $ Ty $ dropElem ctx i.pos) as.names -> Type

  data Strengthen where
    TVar : (j = index (dropPos i.pos) k) -> Strengthen i (TVar j) (TVar k)
    TArrow : Strengthen i a c -> Strengthen i b d -> Strengthen i (TArrow a b) (TArrow c d)
    TProd : StrengthenAll i as.context bs -> Strengthen i (TProd as) (TProd $ fromAll as bs)
    TSum : StrengthenAll i as.context bs -> Strengthen i (TSum as) (TSum $ fromAll as bs)
    TFix : Strengthen (ThereVar i) a b -> Strengthen i (TFix x a) (TFix x b)

  data StrengthenAll where
    Lin : StrengthenAll i [<] [<]
    (:<) : StrengthenAll i as bs -> Strengthen i a b -> StrengthenAll i (as :< (l :- a)) (bs :< b)

  %name Strengthen prf
  %name StrengthenAll prfs

strengthenEq : Strengthen i a b -> a = thin (dropPos i.pos) b
strengthenAllEq : StrengthenAll i as bs -> as = thinAll (dropPos i.pos) (fromAll as bs)

strengthenEq (TVar prf) = cong TVar prf
strengthenEq (TArrow prf1 prf2) = cong2 TArrow (strengthenEq prf1) (strengthenEq prf2)
strengthenEq (TProd {as = MkRow _ _} prfs) = cong TProd $ rowCong $ strengthenAllEq prfs
strengthenEq (TSum {as = MkRow _ _} prfs) = cong TSum $ rowCong $ strengthenAllEq prfs
strengthenEq (TFix prf) = cong (TFix _) $ strengthenEq prf

strengthenAllEq [<] = Refl
strengthenAllEq ((:<) {l} prfs prf) =
  cong2 (:<) (strengthenAllEq prfs) (cong (l :-) $ strengthenEq prf)

namespace Occurs
  public export
  data OccursIn : Var ctx -> Ty ctx -> Type
  public export
  data OccursInAny : Var ctx -> Context (Ty ctx) -> Type

  data OccursIn where
    TVar : i = j -> i `OccursIn` TVar j
    TArrow : These (i `OccursIn` a) (i `OccursIn` b) -> i `OccursIn` TArrow a b
    TProd : i `OccursInAny` as.context -> i `OccursIn` TProd as
    TSum : i `OccursInAny` as.context -> i `OccursIn` TSum as
    TFix : ThereVar i `OccursIn` a -> i `OccursIn` TFix x a

  data OccursInAny where
    And : These (i `OccursInAny` as) (i `OccursIn` a) -> i `OccursInAny` (as :< (n :- a))

  %name OccursIn contra
  %name OccursInAny contras

export
Uninhabited (i `OccursInAny` [<]) where
  uninhabited (And contras) impossible

export
strengthenSplit : Strengthen i a b -> i `OccursIn` a -> Void
strengthenAllSplit : StrengthenAll i as bs -> i `OccursInAny` as -> Void

strengthenSplit (TVar Refl) (TVar {i = %% n} contra) = void $ lemma _ _ contra
  where
  lemma :
    (i : Elem x sx) -> (j : Elem y (dropElem sx i)) ->
    Not (toVar i = toVar (indexPos (dropPos i) j))
  lemma Here j prf = absurd (toVarInjective prf)
  lemma (There i) Here prf = absurd (toVarInjective prf)
  lemma (There i) (There j) prf = lemma i j $ toVarCong $ thereInjective $ toVarInjective prf
strengthenSplit (TArrow prf1 prf2) (TArrow contras) =
  these (strengthenSplit prf1) (strengthenSplit prf2) (const $ strengthenSplit prf2) contras
strengthenSplit (TProd prfs) (TProd contras) = strengthenAllSplit prfs contras
strengthenSplit (TSum prfs) (TSum contras) = strengthenAllSplit prfs contras
strengthenSplit (TFix prf) (TFix contra) = strengthenSplit prf contra

strengthenAllSplit (prfs :< prf) (And contras) =
  these (strengthenAllSplit prfs) (strengthenSplit prf) (const $ strengthenSplit prf) contras

export
strengthen :
  (i : Var ctx) -> (a : Ty ctx) ->
  Proof (Ty (dropElem ctx i.pos)) (Strengthen i a) (i `OccursIn` a)
export
strengthenAll :
  (i : Var ctx) -> (as : Context (Ty ctx)) ->
  Proof (All (const $ Ty $ dropElem ctx i.pos) as.names) (StrengthenAll i as) (i `OccursInAny` as)

strengthen ((%%) x {pos = i}) (TVar ((%%) y {pos = j})) =
  map (TVar . toVar)
    (\_, prf => TVar $ toVarCong prf)
    (TVar . toVarCong . skipsDropPos i) $
  strengthen (dropPos i) j
strengthen i (TArrow a b) =
  map (uncurry TArrow) (\(c, d) => uncurry TArrow) TArrow $
  all (strengthen i a) (strengthen i b)
strengthen i (TProd (MkRow as fresh)) =
  map (TProd . fromAll (MkRow as fresh)) (\_ => TProd) TProd $
  strengthenAll i as
strengthen i (TSum (MkRow as fresh)) =
  map (TSum . fromAll (MkRow as fresh)) (\_ => TSum) TSum $
  strengthenAll i as
strengthen i (TFix x a) =
  map (TFix x) (\_ => TFix) TFix $
  strengthen (ThereVar i) a

strengthenAll i [<] = Just [<] `Because` [<]
strengthenAll i (as :< (l :- a)) =
  map (uncurry (:<) . swap) (\(_, _) => uncurry (:<) . swap) (And . swap) $
  all (strengthen i a) (strengthenAll i as)

-- Not Strictly Positive -----------------------------------------------------------

namespace StrictlyPositive
  public export
  data StrictlyPositiveIn : Var ctx -> Ty ctx -> Type
  public export
  data StrictlyPositiveInAll : Var ctx -> Context (Ty ctx) -> Type

  data StrictlyPositiveIn where
    TVar : i `StrictlyPositiveIn` TVar j
    TArrow : Strengthen i (TArrow a b) c -> i `StrictlyPositiveIn` TArrow a b
    TProd : i `StrictlyPositiveInAll` as.context -> i `StrictlyPositiveIn` TProd as
    TSum : i `StrictlyPositiveInAll` as.context -> i `StrictlyPositiveIn` TSum as
    TFix : ThereVar i `StrictlyPositiveIn` a -> i `StrictlyPositiveIn` TFix x a
  data StrictlyPositiveInAll where
    Lin : i `StrictlyPositiveInAll` [<]
    (:<) :
      i `StrictlyPositiveInAll` as -> i `StrictlyPositiveIn` a ->
      i `StrictlyPositiveInAll` (as :< (l :- a))

  %name StrictlyPositiveIn prf
  %name StrictlyPositiveInAll prfs

namespace NotPositive
  public export
  data NotPositiveIn : Var ctx -> Ty ctx -> Type
  public export
  data NotPositiveInAny : Var ctx -> Context (Ty ctx) -> Type

  data NotPositiveIn where
    TArrow : i `OccursIn` TArrow a b -> i `NotPositiveIn` TArrow a b
    TProd : i `NotPositiveInAny` as.context -> i `NotPositiveIn` TProd as
    TSum : i `NotPositiveInAny` as.context -> i `NotPositiveIn` TSum as
    TFix : ThereVar i `NotPositiveIn` a -> i `NotPositiveIn` TFix x a

  data NotPositiveInAny where
    And :
      These (i `NotPositiveInAny` as) (i `NotPositiveIn` a) ->
      i `NotPositiveInAny` (as :< (n :- a))

  %name NotPositiveIn contra
  %name NotPositiveInAny contras

export
Uninhabited (i `NotPositiveIn` TVar j) where
  uninhabited (TArrow contra) impossible

export
Uninhabited (i `NotPositiveInAny` [<]) where
  uninhabited (And contras) impossible

export
strictlyPositiveSplit : i `StrictlyPositiveIn` a -> i `NotPositiveIn` a -> Void
strictlyPositiveAllSplit : i `StrictlyPositiveInAll` as -> i `NotPositiveInAny` as -> Void

strictlyPositiveSplit (TArrow prf) (TArrow contra) = strengthenSplit prf contra
strictlyPositiveSplit (TProd prfs) (TProd contras) = strictlyPositiveAllSplit prfs contras
strictlyPositiveSplit (TSum prfs) (TSum contras) = strictlyPositiveAllSplit prfs contras
strictlyPositiveSplit (TFix prf) (TFix contra) = strictlyPositiveSplit prf contra

strictlyPositiveAllSplit (prfs :< prf) (And contras) =
  these
    (strictlyPositiveAllSplit prfs)
    (strictlyPositiveSplit prf)
    (const $ strictlyPositiveSplit prf)
    contras

export
strictlyPositiveIn :
  (i : Var ctx) -> (a : Ty ctx) ->
  LazyEither (i `StrictlyPositiveIn` a) (i `NotPositiveIn` a)
strictlyPositiveInAll :
  (i : Var ctx) -> (as : Context (Ty ctx)) ->
  LazyEither (i `StrictlyPositiveInAll` as) (i `NotPositiveInAny` as)

i `strictlyPositiveIn` TVar j = True `Because` TVar
i `strictlyPositiveIn` TArrow a b =
  map (\(_ ** prf) => TArrow prf) TArrow $
  (strengthen i $ TArrow a b).forget
i `strictlyPositiveIn` TProd (MkRow as _) = map TProd TProd $ i `strictlyPositiveInAll` as
i `strictlyPositiveIn` TSum (MkRow as _) = map TSum TSum $ i `strictlyPositiveInAll` as
i `strictlyPositiveIn` TFix x a = map TFix TFix $ ThereVar i `strictlyPositiveIn` a

i `strictlyPositiveInAll` [<] = True `Because` [<]
i `strictlyPositiveInAll` (as :< (n :- a)) =
  map (uncurry (:<) . swap) (And . swap) $
  all (i `strictlyPositiveIn` a) (i `strictlyPositiveInAll` as)

-- Well Formed -----------------------------------------------------------------

-- Negating decidable properties is fun.

namespace WellFormed
  public export
  data WellFormed : Ty ctx -> Type
  public export
  data AllWellFormed : Context (Ty ctx) -> Type

  data WellFormed where
    TVar : WellFormed (TVar i)
    TArrow : WellFormed a -> WellFormed b -> WellFormed (TArrow a b)
    TProd : AllWellFormed as.context -> WellFormed (TProd as)
    TSum : AllWellFormed as.context -> WellFormed (TSum as)
    TFix : toVar Here `StrictlyPositiveIn` a -> WellFormed a -> WellFormed (TFix x a)

  data AllWellFormed where
    Lin : AllWellFormed [<]
    (:<) : AllWellFormed as -> WellFormed a -> AllWellFormed (as :< (n :- a))

  %name WellFormed wf
  %name AllWellFormed wfs

namespace IllFormed
  public export
  data IllFormed : Ty ctx -> Type
  public export
  data AnyIllFormed : Context (Ty ctx) -> Type

  data IllFormed where
    TArrow : These (IllFormed a) (IllFormed b) -> IllFormed (TArrow a b)
    TProd : AnyIllFormed as.context -> IllFormed (TProd as)
    TSum : AnyIllFormed as.context -> IllFormed (TSum as)
    TFix : These (toVar Here `NotPositiveIn` a) (IllFormed a) -> IllFormed (TFix x a)

  data AnyIllFormed where
    And : These (AnyIllFormed as) (IllFormed a) -> AnyIllFormed (as :< (n :- a))

  %name IllFormed bad
  %name AnyIllFormed bads

export
Uninhabited (IllFormed (TVar i)) where
  uninhabited (TArrow prf) impossible

export
Uninhabited (AnyIllFormed [<]) where
  uninhabited (And prf) impossible

export
wellFormedSplit : WellFormed a -> IllFormed a -> Void
allWellFormedSplit : AllWellFormed as -> AnyIllFormed as -> Void

wellFormedSplit (TArrow wf1 wf2) (TArrow bads) =
  these (wellFormedSplit wf1) (wellFormedSplit wf2) (const $ wellFormedSplit wf2) bads
wellFormedSplit (TProd wfs) (TProd bads) = allWellFormedSplit wfs bads
wellFormedSplit (TSum wfs) (TSum bads) = allWellFormedSplit wfs bads
wellFormedSplit (TFix prf wf) (TFix bads) =
  these (strictlyPositiveSplit prf) (wellFormedSplit wf) (const $ wellFormedSplit wf) bads

allWellFormedSplit (wfs :< wf) (And bads) =
  these (allWellFormedSplit wfs) (wellFormedSplit wf) (const $ wellFormedSplit wf) bads

export
wellFormed : (a : Ty ctx) -> LazyEither (WellFormed a) (IllFormed a)
export
allWellFormed : (as : Context (Ty ctx)) -> LazyEither (AllWellFormed as) (AnyIllFormed as)

wellFormed (TVar j) = True `Because` TVar
wellFormed (TArrow a b) = map (uncurry TArrow) TArrow $ all (wellFormed a) (wellFormed b)
wellFormed (TProd (MkRow as _)) = map TProd TProd $ allWellFormed as
wellFormed (TSum (MkRow as _)) = map TSum TSum $ allWellFormed as
wellFormed (TFix x a) = map (uncurry TFix) TFix $ all (%% x `strictlyPositiveIn` a) (wellFormed a)

allWellFormed [<] = True `Because` [<]
allWellFormed (as :< (n :- a)) =
  map (uncurry (:<) . swap) (And . swap) $
  all (wellFormed a) (allWellFormed as)

--------------------------------------------------------------------------------
-- Substitution ----------------------------------------------------------------
--------------------------------------------------------------------------------

export
sub : All (const $ Thinned Ty ctx2) ctx1 -> Ty ctx1 -> Ty ctx2
subAll : All (const $ Thinned Ty ctx2) ctx1 -> Context (Ty ctx1) -> Context (Ty ctx2)
subAllNames :
  (f : All (const $ Thinned Ty ctx2) ctx1) ->
  (ctx : Context (Ty ctx1)) ->
  (subAll f ctx).names = ctx.names

sub env (TVar i) = (indexAll i.pos env).extract
sub env (TArrow a b) = TArrow (sub env a) (sub env b)
sub env (TProd (MkRow as fresh)) = TProd (MkRow (subAll env as) (rewrite subAllNames env as in fresh))
sub env (TSum (MkRow as fresh)) = TSum (MkRow (subAll env as) (rewrite subAllNames env as in fresh))
sub env (TFix x a) = TFix x (sub (mapProperty (rename (Drop Id)) env :< (TVar (%% x) `Over` Id)) a)

subAll env [<] = [<]
subAll env (as :< (n :- a)) = subAll env as :< (n :- sub env a)

subAllNames env [<] = Refl
subAllNames env (as :< (n :- a)) = cong (:< n) (subAllNames env as)

-- Special Types ---------------------------------------------------------------

public export
TNat : Ty ctx
TNat = TFix "Nat" (TSum [<"Z" :- TProd [<], "S" :- TVar (%% "Nat")])

public export
TList : Ty ctx -> Ty ctx
TList a =
  TFix "List" (TSum
    [<"N" :- TProd [<]
    , "C" :- TProd [<"H" :- thin (Drop Id) a, "T" :- TVar (%% "List")]])

-- Testing if we have a list

-- TODO: prove correct
isList : (a : Ty ctx) -> Maybe (Ty ctx)
isList (TFix x (TSum (MkRow
  [<"N" :- TProd (MkRow [<] _)
  , "C" :- TProd (MkRow [<"H" :- a, "T" :- TVar ((%%) x {pos = Here})] _)] _))) =
  does (strengthen (%% x) a)
isList (TFix x (TSum (MkRow
  [<"N" :- TProd (MkRow [<] _)
  , "C" :- TProd (MkRow [<"T" :- TVar ((%%) x {pos = Here}), "H" :- a] _)] _))) =
  does (strengthen (%% x) a)
isList (TFix x (TSum (MkRow
  [<"C" :- TProd (MkRow [<"H" :- a, "T" :- TVar ((%%) x {pos = Here})] _)
  , "N" :- TProd (MkRow [<] _)] _))) =
  does (strengthen (%% x) a)
isList (TFix x (TSum (MkRow
  [<"C" :- TProd (MkRow [<"T" :- TVar ((%%) x {pos = Here}), "H" :- a] _)
  , "N" :- TProd (MkRow [<] _)] _))) =
  does (strengthen (%% x) a)
isList _ = Nothing
