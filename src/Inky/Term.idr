module Inky.Term

import public Inky.Type

import Data.List.Quantifiers
import Data.Singleton
import Data.These
import Flap.Data.SnocList.Quantifiers
import Flap.Decidable
import Flap.Decidable.Maybe

%hide Prelude.Ops.infixl.(>=>)

--------------------------------------------------------------------------------
-- Definition ------------------------------------------------------------------
--------------------------------------------------------------------------------

public export
data Mode = Sugar | NoSugar

public export
record WithDoc (a : Type) where
  constructor AddDoc
  value : a
  doc : List String

public export
data Term : Mode -> (m : Type) -> (tyCtx, tmCtx : SnocList String) -> Type where
  Annot : (meta : m) -> Term mode m tyCtx tmCtx -> Ty tyCtx -> Term mode m tyCtx tmCtx
  Var : (meta : m) -> Var tmCtx -> Term mode m tyCtx tmCtx
  Let : (meta : WithDoc m) -> Term mode m tyCtx tmCtx -> (x ** Term mode m tyCtx (tmCtx :< x)) -> Term mode m tyCtx tmCtx
  LetTy : (meta : WithDoc m) -> Ty tyCtx -> (x ** Term mode m (tyCtx :< x) tmCtx) -> Term mode m tyCtx tmCtx
  Abs : (meta : m) -> (bound ** Term mode m tyCtx (tmCtx <>< bound)) -> Term mode m tyCtx tmCtx
  App : (meta : m) -> Term mode m tyCtx tmCtx -> List (Term mode m tyCtx tmCtx) -> Term mode m tyCtx tmCtx
  Tup : (meta : m) -> Row (Term mode m tyCtx tmCtx) -> Term mode m tyCtx tmCtx
  Prj : (meta : m) -> Term mode m tyCtx tmCtx -> (l : String) -> Term mode m tyCtx tmCtx
  Inj : (meta : m) -> (l : String) -> Term mode m tyCtx tmCtx -> Term mode m tyCtx tmCtx
  Case : (meta : m) -> Term mode m tyCtx tmCtx -> Row (x ** Term mode m tyCtx (tmCtx :< x)) -> Term mode m tyCtx tmCtx
  Roll : (meta : m) -> Term mode m tyCtx tmCtx -> Term mode m tyCtx tmCtx
  Unroll : (meta : m) -> Term mode m tyCtx tmCtx -> Term mode m tyCtx tmCtx
  Fold : (meta : m) -> Term mode m tyCtx tmCtx -> (x ** Term mode m tyCtx (tmCtx :< x)) -> Term mode m tyCtx tmCtx
  Map : (meta : m) -> (x ** Ty (tyCtx :< x)) -> Ty tyCtx -> Ty tyCtx -> Term Sugar m tyCtx tmCtx

%name Term e, f, t, u

export
(.meta) : Term mode m tyCtx tmCtx -> m
(Annot meta _ _).meta = meta
(Var meta _).meta = meta
(Let meta _ _).meta = meta.value
(LetTy meta _ _).meta = meta.value
(Abs meta _).meta = meta
(App meta _ _).meta = meta
(Tup meta _).meta = meta
(Prj meta _ _).meta = meta
(Inj meta _ _).meta = meta
(Case meta _ _).meta = meta
(Roll meta _).meta = meta
(Unroll meta _).meta = meta
(Fold meta _ _).meta = meta
(Map meta _ _ _).meta = meta

--------------------------------------------------------------------------------
-- Well Formed -----------------------------------------------------------------
--------------------------------------------------------------------------------

-- Test if we have a function, collecting the bound types ----------------------

public export
data IsFunction :
  (bound : List String) -> (a : Ty tyCtx) ->
  (dom : All (Assoc0 $ Ty tyCtx) bound) -> (cod : Ty tyCtx) ->
  Type
  where
  Done : IsFunction [] a [] a
  Step :
    IsFunction bound b dom cod ->
    IsFunction (x :: bound) (TArrow a b) ((x :- a) :: dom) cod

public export
data NotFunction : (bound : List String) -> (a : Ty tyCtx) -> Type
  where
  Step1 :
    ((b, c : Ty tyCtx) -> Not (a = TArrow b c)) ->
    NotFunction (x :: bound) a
  Step2 :
    NotFunction bound b ->
    NotFunction (x :: bound) (TArrow a b)

%name IsFunction prf
%name NotFunction contra

export
isFunctionUnique :
  IsFunction bound a dom cod -> IsFunction bound a dom' cod' -> (dom = dom', cod = cod')
isFunctionUnique Done Done = (Refl, Refl)
isFunctionUnique (Step {x, a} prf) (Step prf') =
  mapFst (\prf => cong ((x :- a) ::) prf) $ isFunctionUnique prf prf'

export
isFunctionSplit : IsFunction bound a dom cod -> NotFunction bound a -> Void
isFunctionSplit (Step {a, b} prf) (Step1 contra) = void $ contra a b Refl
isFunctionSplit (Step prf) (Step2 contra) = isFunctionSplit prf contra

export
isFunction :
  (bound : List String) -> (a : Ty tyCtx) ->
  Proof (All (Assoc0 $ Ty tyCtx) bound, Ty tyCtx)
    (uncurry $ IsFunction bound a)
    (NotFunction bound a)
isFunction [] a = Just ([], a) `Because` Done
isFunction (x :: bound) a =
  map
    (\y => ((x :- fst (fst y)) :: fst (snd y), snd (snd y)))
    (\((a, b), (dom, cod)), (eq, prf) => rewrite eq in Step prf)
    (either Step1 false) $
  (ab := isArrow a) >=> isFunction bound (snd ab)
  where
  false :
    forall a.
    (y : (Ty tyCtx, Ty tyCtx) ** (a = TArrow (fst y) (snd y), NotFunction bound (snd y))) ->
    NotFunction (x :: bound) a
  false ((a, b) ** (Refl, contra)) = Step2 contra

-- Define well-formedness and ill-formedness

namespace Modes
  public export
  data SynthsOnly : Term mode m tyCtx tmCtx -> Type where
    Annot : SynthsOnly (Annot meta t a)
    Var : SynthsOnly (Var meta i)
    App : SynthsOnly (App meta f ts)
    Prj : SynthsOnly (Prj meta e l)
    Unroll : SynthsOnly (Unroll meta e)
    Map : SynthsOnly (Map meta (x ** a) b c)

  public export
  data ChecksOnly : Term mode m tyCtx tmCtx -> Type where
    Abs : ChecksOnly (Abs meta (bounds ** t))
    Inj : ChecksOnly (Inj meta l t)
    Case : ChecksOnly (Case meta e ts)
    Roll : ChecksOnly (Roll meta t)
    Fold : ChecksOnly (Fold meta e (x ** t))

  %name SynthsOnly shape
  %name ChecksOnly shape

public export
data Synths :
  All (Assoc0 $ Ty [<]) tyCtx ->
  All (Assoc0 $ Ty [<]) tmCtx ->
  Term mode m tyCtx tmCtx -> Ty [<] -> Type
public export
data Checks :
  All (Assoc0 $ Ty [<]) tyCtx ->
  All (Assoc0 $ Ty [<]) tmCtx ->
  Ty [<] -> Term mode m tyCtx tmCtx -> Type

namespace Spine
  public export
  data CheckSpine :
    All (Assoc0 $ Ty [<]) tyCtx ->
    All (Assoc0 $ Ty [<]) tmCtx ->
    Ty [<] -> List (Term mode m tyCtx tmCtx) -> Ty [<] -> Type
    where
    Nil : CheckSpine tyEnv tmEnv a [] a
    (::) :
      Checks tyEnv tmEnv a t ->
      CheckSpine tyEnv tmEnv b ts c ->
      CheckSpine tyEnv tmEnv (TArrow a b) (t :: ts) c

  %name CheckSpine prfs

namespace Synths
  public export
  data AllSynths :
    All (Assoc0 $ Ty [<]) tyCtx ->
    All (Assoc0 $ Ty [<]) tmCtx ->
    Context (Term mode m tyCtx tmCtx) -> Row (Ty [<]) -> Type
    where
    Lin : AllSynths tyEnv tmEnv [<] [<]
    (:<) :
      AllSynths tyEnv tmEnv ts as ->
      {auto 0 freshIn : l `FreshIn` as.names} ->
      Synths tyEnv tmEnv t a ->
      AllSynths tyEnv tmEnv (ts :< (l :- t)) (as :< (l :- a))

  %name AllSynths prfs

namespace Checks
  public export
  data AllChecks :
    All (Assoc0 $ Ty [<]) tyCtx ->
    All (Assoc0 $ Ty [<]) tmCtx ->
    Context (Ty [<]) -> Context (Term mode m tyCtx tmCtx) -> Type
    where
    Base : AllChecks tyEnv tmEnv [<] [<]
    Step :
      (i : Elem (l :- a) as) ->
      Checks tyEnv tmEnv a t ->
      AllChecks tyEnv tmEnv (dropElem as i) ts ->
      AllChecks tyEnv tmEnv as (ts :< (l :- t))

  %name AllChecks prfs

namespace Branches
  public export
  data AllBranches :
    All (Assoc0 $ Ty [<]) tyCtx ->
    All (Assoc0 $ Ty [<]) tmCtx ->
    Context (Ty [<]) -> Ty [<] -> Context (x ** Term mode m tyCtx (tmCtx :< x)) -> Type
    where
    Base : AllBranches tyEnv tmEnv [<] a [<]
    Step :
      (i : Elem (l :- a) as) ->
      Checks tyEnv (tmEnv :< (x :- a)) b t ->
      AllBranches tyEnv tmEnv (dropElem as i) b ts ->
      AllBranches tyEnv tmEnv as b (ts :< (l :- (x ** t)))

  %name AllBranches prfs

data Synths where
  AnnotS :
    WellFormed a ->
    Checks tyEnv tmEnv (sub tyEnv a) t ->
    Synths tyEnv tmEnv (Annot meta t a) (sub tyEnv a)
  VarS :
    Synths tyEnv tmEnv (Var meta i) (indexAll i.pos tmEnv).value
  LetS :
    Synths tyEnv tmEnv e a ->
    Synths tyEnv (tmEnv :< (x :- a)) f b ->
    Synths tyEnv tmEnv (Let meta e (x ** f)) b
  LetTyS :
    WellFormed a ->
    Synths (tyEnv :< (x :- sub tyEnv a)) tmEnv e b ->
    Synths tyEnv tmEnv (LetTy meta a (x ** e)) b
  AppS :
    Synths tyEnv tmEnv f a ->
    CheckSpine tyEnv tmEnv a ts b ->
    Synths tyEnv tmEnv (App meta f ts) b
  TupS :
    AllSynths tyEnv tmEnv es.context as ->
    Synths tyEnv tmEnv (Tup meta es) (TProd as)
  PrjS :
    Synths tyEnv tmEnv e (TProd as) ->
    Elem (l :- a) as.context ->
    Synths tyEnv tmEnv (Prj meta e l) a
  UnrollS :
    Synths tyEnv tmEnv e (TFix x a) ->
    Synths tyEnv tmEnv (Unroll meta e) (sub [<x :- TFix x a] a)
  MapS :
    WellFormed (TFix x a) ->
    WellFormed b ->
    WellFormed c ->
    Synths tyEnv tmEnv (Map meta (x ** a) b c)
      (TArrow (TArrow (sub tyEnv b) (sub tyEnv c))
      (TArrow (sub (tyEnv :< (x :- sub tyEnv b)) a)
              (sub (tyEnv :< (x :- sub tyEnv c)) a)))

data Checks where
  AnnotC :
    Synths tyEnv tmEnv (Annot meta t a) b ->
    Alpha b c ->
    Checks tyEnv tmEnv c (Annot meta t a)
  VarC :
    Synths tyEnv tmEnv (Var {mode} meta i) a ->
    Alpha a b ->
    Checks tyEnv tmEnv b (Var {mode} meta i)
  LetC :
    Synths tyEnv tmEnv e a ->
    Checks tyEnv (tmEnv :< (x :- a)) b t ->
    Checks tyEnv tmEnv b (Let meta e (x ** t))
  LetTyC :
    WellFormed a ->
    Checks (tyEnv :< (x :- sub tyEnv a)) tmEnv b t ->
    Checks tyEnv tmEnv b (LetTy meta a (x ** t))
  AbsC :
    IsFunction bound a dom cod ->
    Checks tyEnv (tmEnv <>< dom) cod t ->
    Checks tyEnv tmEnv a (Abs meta (bound ** t))
  AppC :
    Synths tyEnv tmEnv (App meta e ts) a ->
    Alpha a b ->
    Checks tyEnv tmEnv b (App meta e ts)
  TupC :
    AllChecks tyEnv tmEnv as.context ts.context ->
    Checks tyEnv tmEnv (TProd as) (Tup meta ts)
  PrjC :
    Synths tyEnv tmEnv (Prj meta e l) a ->
    Alpha a b ->
    Checks tyEnv tmEnv b (Prj meta e l)
  InjC :
    Elem (l :- a) as.context ->
    Checks tyEnv tmEnv a t ->
    Checks tyEnv tmEnv (TSum as) (Inj meta l t)
  CaseC :
    Synths tyEnv tmEnv e (TSum as) ->
    AllBranches tyEnv tmEnv as.context a ts.context ->
    Checks tyEnv tmEnv a (Case meta e ts)
  RollC :
    Checks tyEnv tmEnv (sub [<x :- TFix x a] a) t ->
    Checks tyEnv tmEnv (TFix x a) (Roll meta t)
  UnrollC :
    Synths tyEnv tmEnv (Unroll meta e) a ->
    Alpha a b ->
    Checks tyEnv tmEnv b (Unroll meta e)
  FoldC :
    Synths tyEnv tmEnv e (TFix x a) ->
    Checks tyEnv (tmEnv :< (y :- sub [<x :- b] a)) b t ->
    Checks tyEnv tmEnv b (Fold meta e (y ** t))
  MapC :
    Synths tyEnv tmEnv (Map meta (x ** a) b c) d ->
    Alpha d e ->
    Checks tyEnv tmEnv e (Map meta (x ** a) b c)

public export
%inline
EmbedC :
  SynthsOnly e ->
  Synths tyEnv tmEnv e a ->
  Alpha a b ->
  Checks tyEnv tmEnv b e
EmbedC Annot prf1 prf2 = AnnotC prf1 prf2
EmbedC Var prf1 prf2 = VarC prf1 prf2
EmbedC App prf1 prf2 = AppC prf1 prf2
EmbedC Prj prf1 prf2 = PrjC prf1 prf2
EmbedC Unroll prf1 prf2 = UnrollC prf1 prf2
EmbedC Map prf1 prf2 = MapC prf1 prf2

%name Synths prf
%name Checks prf

public export
data NotSynths :
  All (Assoc0 $ Ty [<]) tyCtx ->
  All (Assoc0 $ Ty [<]) tmCtx ->
  Term mode m tyCtx tmCtx -> Type
public export
data NotChecks :
  All (Assoc0 $ Ty [<]) tyCtx ->
  All (Assoc0 $ Ty [<]) tmCtx ->
  Ty [<] -> Term mode m tyCtx tmCtx -> Type

namespace Spine
  public export
  data NotCheckSpine :
    All (Assoc0 $ Ty [<]) tyCtx ->
    All (Assoc0 $ Ty [<]) tmCtx ->
    Ty [<] -> List (Term mode m tyCtx tmCtx) -> Type
    where
    Step1 :
      ((b, c : Ty [<]) -> Not (a = TArrow b c)) ->
      NotCheckSpine tyEnv tmEnv a (t :: ts)
    Step2 :
      These (NotChecks tyEnv tmEnv a t) (NotCheckSpine tyEnv tmEnv b ts) ->
      NotCheckSpine tyEnv tmEnv (TArrow a b) (t :: ts)

  %name NotCheckSpine contras

namespace Synths
  public export
  data AnyNotSynths :
    All (Assoc0 $ Ty [<]) tyCtx ->
    All (Assoc0 $ Ty [<]) tmCtx ->
    (ts : Context (Term mode m tyCtx tmCtx)) -> Type
    where
    Step :
      These (NotSynths tyEnv tmEnv t) (AnyNotSynths tyEnv tmEnv ts) ->
      AnyNotSynths tyEnv tmEnv (ts :< (l :- t))

  %name AnyNotSynths contras

namespace Checks
  public export
  data AnyNotChecks :
    All (Assoc0 $ Ty [<]) tyCtx ->
    All (Assoc0 $ Ty [<]) tmCtx ->
    Context (Ty [<]) -> Context (Term mode m tyCtx tmCtx) -> Type
    where
    Base1 : AnyNotChecks tyEnv tmEnv (as :< la) [<]
    Step1 :
      ((a : Ty [<]) -> Not (Elem (l :- a) as)) ->
      AnyNotChecks tyEnv tmEnv as (ts :< (l :- t))
    Step2 :
      (i : Elem (l :- a) as) ->
      These (NotChecks tyEnv tmEnv a t) (AnyNotChecks tyEnv tmEnv (dropElem as i) ts) ->
      AnyNotChecks tyEnv tmEnv as (ts :< (l :- t))

  %name AnyNotChecks contras

namespace Branches
  public export
  data AnyNotBranches :
    All (Assoc0 $ Ty [<]) tyCtx ->
    All (Assoc0 $ Ty [<]) tmCtx ->
    Context (Ty [<]) -> Ty [<] -> Context (x ** Term mode m tyCtx (tmCtx :< x)) -> Type
    where
    Base1 : AnyNotBranches tyEnv tmEnv (as :< a) b [<]
    Step1 :
      ((a : Ty [<]) -> Not (Elem (l :- a) as)) ->
      AnyNotBranches tyEnv tmEnv as b (ts :< (l :- (x ** t)))
    Step2 :
      (i : Elem (l :- a) as) ->
      These
        (NotChecks tyEnv (tmEnv :< (x :- a)) b t)
        (AnyNotBranches tyEnv tmEnv (dropElem as i) b ts) ->
      AnyNotBranches tyEnv tmEnv as b (ts :< (l :- (x ** t)))

  %name AnyNotBranches contras

data NotSynths where
  ChecksNS :
    ChecksOnly t ->
    NotSynths tyEnv tmEnv t
  AnnotNS :
    These (IllFormed a) (NotChecks tyEnv tmEnv (sub tyEnv a) t) ->
    NotSynths tyEnv tmEnv (Annot meta t a)
  LetNS1 :
    NotSynths tyEnv tmEnv e ->
    NotSynths tyEnv tmEnv (Let meta e (x ** f))
  LetNS2' :
    These
      (NotSynths tyEnv tmEnv (Annot meta' e a))
      (NotSynths tyEnv (tmEnv :< (x :- sub tyEnv a)) f) ->
    NotSynths tyEnv tmEnv (Let meta (Annot meta' e a) (x ** f))
  LetNS2 :
    Synths tyEnv tmEnv e a ->
    NotSynths tyEnv (tmEnv :< (x :- a)) f ->
    NotSynths tyEnv tmEnv (Let meta e (x ** f))
  LetTyNS :
    These (IllFormed a) (NotSynths (tyEnv :< (x :- sub tyEnv a)) tmEnv e) ->
    NotSynths tyEnv tmEnv (LetTy meta a (x ** e))
  AppNS1 :
    NotSynths tyEnv tmEnv f ->
    NotSynths tyEnv tmEnv (App meta f ts)
  AppNS2 :
    Synths tyEnv tmEnv f a ->
    NotCheckSpine tyEnv tmEnv a ts ->
    NotSynths tyEnv tmEnv (App meta f ts)
  TupNS :
    AnyNotSynths tyEnv tmEnv es.context ->
    NotSynths tyEnv tmEnv (Tup meta es)
  PrjNS1 :
    NotSynths tyEnv tmEnv e ->
    NotSynths tyEnv tmEnv (Prj meta e l)
  PrjNS2 :
    Synths tyEnv tmEnv e a ->
    ((as : Row (Ty [<])) -> Not (a = TProd as)) ->
    NotSynths tyEnv tmEnv (Prj meta e l)
  PrjNS3 :
    Synths tyEnv tmEnv e (TProd as) ->
    ((a : Ty [<]) -> Not (Elem (l :- a) as.context)) ->
    NotSynths tyEnv tmEnv (Prj meta e l)
  UnrollNS1 :
    NotSynths tyEnv tmEnv e ->
    NotSynths tyEnv tmEnv (Unroll meta e)
  UnrollNS2 :
    Synths tyEnv tmEnv e a ->
    ((x : String) -> (b : Ty [<x]) -> Not (a = TFix x b)) ->
    NotSynths tyEnv tmEnv (Unroll meta e)
  MapNS :
    These (IllFormed (TFix x a)) (These (IllFormed b) (IllFormed c)) ->
    NotSynths tyEnv tmEnv (Map meta (x ** a) b c)

data NotChecks where
  EmbedNC1 :
    SynthsOnly e ->
    NotSynths tyEnv tmEnv e ->
    NotChecks tyEnv tmEnv b e
  EmbedNC2 :
    SynthsOnly e ->
    Synths tyEnv tmEnv e a ->
    NotAlpha a b ->
    NotChecks tyEnv tmEnv b e
  LetNC1 :
    NotSynths tyEnv tmEnv e ->
    NotChecks tyEnv tmEnv b (Let meta e (x ** t))
  LetNC2' :
    These
      (NotSynths tyEnv tmEnv (Annot meta' e a))
      (NotChecks tyEnv (tmEnv :< (x :- sub tyEnv a)) b t) ->
    NotChecks tyEnv tmEnv b (Let meta (Annot meta' e a) (x ** t))
  LetNC2 :
    Synths tyEnv tmEnv e a ->
    NotChecks tyEnv (tmEnv :< (x :- a)) b t ->
    NotChecks tyEnv tmEnv b (Let meta e (x ** t))
  LetTyNC :
    These (IllFormed a) (NotChecks (tyEnv :< (x :- sub tyEnv a)) tmEnv b t) ->
    NotChecks tyEnv tmEnv b (LetTy meta a (x ** t))
  AbsNC1 :
    NotFunction bound a ->
    NotChecks tyEnv tmEnv a (Abs meta (bound ** t))
  AbsNC2 :
    IsFunction bound a dom cod ->
    NotChecks tyEnv (tmEnv <>< dom) cod t ->
    NotChecks tyEnv tmEnv a (Abs meta (bound ** t))
  TupNC1 :
    ((as : Row (Ty [<])) -> Not (a = TProd as)) ->
    NotChecks tyEnv tmEnv a (Tup meta ts)
  TupNC2 :
    AnyNotChecks tyEnv tmEnv as.context ts.context ->
    NotChecks tyEnv tmEnv (TProd as) (Tup meta ts)
  InjNC1 :
    ((as : Row (Ty [<])) -> Not (a = TSum as)) ->
    NotChecks tyEnv tmEnv a (Inj meta l t)
  InjNC2 :
    ((a : Ty [<]) -> Not (Elem (l :- a) as.context)) ->
    NotChecks tyEnv tmEnv (TSum as) (Inj meta l t)
  InjNC3 :
    Elem (l :- a) as.context ->
    NotChecks tyEnv tmEnv a t ->
    NotChecks tyEnv tmEnv (TSum as) (Inj meta l t)
  CaseNC1 :
    NotSynths tyEnv tmEnv e ->
    NotChecks tyEnv tmEnv a (Case meta e ts)
  CaseNC2 :
    Synths tyEnv tmEnv e b ->
    ((as : Row (Ty [<])) -> Not (b = TSum as)) ->
    NotChecks tyEnv tmEnv a (Case meta e ts)
  CaseNC3 :
    Synths tyEnv tmEnv e (TSum as) ->
    AnyNotBranches tyEnv tmEnv as.context a ts.context ->
    NotChecks tyEnv tmEnv a (Case meta e ts)
  RollNC1 :
    ((x : String) -> (b : Ty [<x]) -> Not (a = TFix x b)) ->
    NotChecks tyEnv tmEnv a (Roll meta t)
  RollNC2 :
    NotChecks tyEnv tmEnv (sub [<x :- TFix x a] a) t ->
    NotChecks tyEnv tmEnv (TFix x a) (Roll meta t)
  FoldNC1 :
    NotSynths tyEnv tmEnv e ->
    NotChecks tyEnv tmEnv b (Fold meta e (y ** t))
  FoldNC2 :
    Synths tyEnv tmEnv e a ->
    ((x : String) -> (c : Ty [<x]) -> Not (a = TFix x c)) ->
    NotChecks tyEnv tmEnv b (Fold meta e (y ** t))
  FoldNC3 :
    Synths tyEnv tmEnv e (TFix x a) ->
    NotChecks tyEnv (tmEnv :< (y :- sub [<x :- b] a)) b t ->
    NotChecks tyEnv tmEnv b (Fold meta e (y ** t))

%name NotSynths contra
%name NotChecks contra

Uninhabited (NotSynths tyEnv tmEnv (Var meta i)) where
  uninhabited (ChecksNS Abs) impossible
  uninhabited (ChecksNS Inj) impossible
  uninhabited (ChecksNS Case) impossible
  uninhabited (ChecksNS Roll) impossible
  uninhabited (ChecksNS Fold) impossible
