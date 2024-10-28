module Inky.Term

import public Inky.Data.Thinned
import public Inky.Type

import Control.Function
import Data.List.Quantifiers
import Data.These
import Inky.Data.SnocList.Quantifiers
import Inky.Decidable
import Inky.Decidable.Maybe

%hide Prelude.Ops.infixl.(>=>)

--------------------------------------------------------------------------------
-- Definition ------------------------------------------------------------------
--------------------------------------------------------------------------------

public export
data Term : (tyCtx, tmCtx : SnocList String) -> Type where
  Annot : Term tyCtx tmCtx -> Ty tyCtx -> Term tyCtx tmCtx
  Var : Var tmCtx -> Term tyCtx tmCtx
  Let : Term tyCtx tmCtx -> (x ** Term tyCtx (tmCtx :< x)) -> Term tyCtx tmCtx
  LetTy : Ty tyCtx -> (x ** Term (tyCtx :< x) tmCtx) -> Term tyCtx tmCtx
  Abs : (bound ** Term tyCtx (tmCtx <>< bound)) -> Term tyCtx tmCtx
  App : Term tyCtx tmCtx -> List (Term tyCtx tmCtx) -> Term tyCtx tmCtx
  Tup : Row (Term tyCtx tmCtx) -> Term tyCtx tmCtx
  Prj : Term tyCtx tmCtx -> (l : String) -> Term tyCtx tmCtx
  Inj : (l : String) -> Term tyCtx tmCtx -> Term tyCtx tmCtx
  Case : Term tyCtx tmCtx -> Row (x ** Term tyCtx (tmCtx :< x)) -> Term tyCtx tmCtx
  Roll : Term tyCtx tmCtx -> Term tyCtx tmCtx
  Unroll : Term tyCtx tmCtx -> Term tyCtx tmCtx
  Fold : Term tyCtx tmCtx -> (x ** Term tyCtx (tmCtx :< x)) -> Term tyCtx tmCtx
  Map : (x ** Ty (tyCtx :< x)) -> Ty tyCtx -> Ty tyCtx -> Term tyCtx tmCtx
  GetChildren : (x ** Ty (tyCtx :< x)) -> Ty tyCtx -> Term tyCtx tmCtx

%name Term e, f, t, u

--------------------------------------------------------------------------------
-- Well Formed -----------------------------------------------------------------
--------------------------------------------------------------------------------

-- Test if we have a function, collecting the bound types ----------------------

public export
data IsFunction :
  (bound : List String) -> (a : Ty tyCtx) ->
  (dom : All (const $ Ty tyCtx) bound) -> (cod : Ty tyCtx) ->
  Type
  where
  Done : IsFunction [] a [] a
  Step :
    IsFunction bound b dom cod ->
    IsFunction (x :: bound) (TArrow a b) (a :: dom) cod

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
isFunctionUnique (Step {a} prf) (Step prf') =
  mapFst (\prf => cong (a ::) prf) $ isFunctionUnique prf prf'

export
isFunctionSplit : IsFunction bound a dom cod -> NotFunction bound a -> Void
isFunctionSplit (Step {a, b} prf) (Step1 contra) = void $ contra a b Refl
isFunctionSplit (Step prf) (Step2 contra) = isFunctionSplit prf contra

export
isFunction :
  (bound : List String) -> (a : Ty tyCtx) ->
  Proof (All (const $ Ty tyCtx) bound, Ty tyCtx)
    (uncurry $ IsFunction bound a)
    (NotFunction bound a)
isFunction [] a = Just ([], a) `Because` Done
isFunction (x :: bound) a =
  map
    (\x => (fst (fst x) :: fst (snd x), snd (snd x)))
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
  data SynthsOnly : Term tyCtx tmCtx -> Type where
    Annot : SynthsOnly (Annot t a)
    Var : SynthsOnly (Var i)
    App : SynthsOnly (App f ts)
    Prj : SynthsOnly (Prj e l)
    Unroll : SynthsOnly (Unroll e)
    Map : SynthsOnly (Map (x ** a) b c)
    GetChildren : SynthsOnly (GetChildren (x ** a) b)

  public export
  data ChecksOnly : Term tyCtx tmCtx -> Type where
    Abs : ChecksOnly (Abs (bounds ** t))
    Inj : ChecksOnly (Inj l t)
    Case : ChecksOnly (Case e ts)
    Roll : ChecksOnly (Roll t)
    Fold : ChecksOnly (Fold e (x ** t))

public export
data Synths :
  All (const $ Thinned Ty [<]) tyCtx ->
  All (const $ Thinned Ty [<]) tmCtx ->
  Term tyCtx tmCtx -> Ty [<] -> Type
public export
data Checks :
  All (const $ Thinned Ty [<]) tyCtx ->
  All (const $ Thinned Ty [<]) tmCtx ->
  Ty [<] -> Term tyCtx tmCtx -> Type

namespace Spine
  public export
  data CheckSpine :
    All (const $ Thinned Ty [<]) tyCtx ->
    All (const $ Thinned Ty [<]) tmCtx ->
    Ty [<] -> List (Term tyCtx tmCtx) -> Ty [<] -> Type
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
    All (const $ Thinned Ty [<]) tyCtx ->
    All (const $ Thinned Ty [<]) tmCtx ->
    (ts : Context (Term tyCtx tmCtx)) -> All (const $ Ty [<]) ts.names -> Type
    where
    Lin : AllSynths tyEnv tmEnv [<] [<]
    (:<) :
      AllSynths tyEnv tmEnv ts as ->
      Synths tyEnv tmEnv t a ->
      AllSynths tyEnv tmEnv (ts :< (l :- t)) (as :< a)

  %name AllSynths prfs

namespace Checks
  public export
  data AllChecks :
    All (const $ Thinned Ty [<]) tyCtx ->
    All (const $ Thinned Ty [<]) tmCtx ->
    Context (Ty [<]) -> Context (Term tyCtx tmCtx) -> Type
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
    All (const $ Thinned Ty [<]) tyCtx ->
    All (const $ Thinned Ty [<]) tmCtx ->
    Context (Ty [<]) -> Ty [<] -> Context (x ** Term tyCtx (tmCtx :< x)) -> Type
    where
    Base : AllBranches tyEnv tmEnv [<] a [<]
    Step :
      (i : Elem (l :- a) as) ->
      Checks tyEnv (tmEnv :< (a `Over` Id)) b t ->
      AllBranches tyEnv tmEnv (dropElem as i) b ts ->
      AllBranches tyEnv tmEnv as b (ts :< (l :- (x ** t)))

  %name AllBranches prfs

data Synths where
  AnnotS :
    Not (IllFormed a) ->
    Checks tyEnv tmEnv (sub tyEnv a) t ->
    Synths tyEnv tmEnv (Annot t a) (sub tyEnv a)
  VarS :
    Synths tyEnv tmEnv (Var i) (indexAll i.pos tmEnv).extract
  LetS :
    Synths tyEnv tmEnv e a ->
    Synths tyEnv (tmEnv :< (a `Over` Id)) f b ->
    Synths tyEnv tmEnv (Let e (x ** f)) b
  LetTyS :
    Not (IllFormed a) ->
    Synths (tyEnv :< (sub tyEnv a `Over` Id)) tmEnv e b ->
    Synths tyEnv tmEnv (LetTy a (x ** e)) b
  AppS :
    Synths tyEnv tmEnv f a ->
    CheckSpine tyEnv tmEnv a ts b ->
    Synths tyEnv tmEnv (App f ts) b
  TupS :
    AllSynths tyEnv tmEnv es.context as ->
    Synths tyEnv tmEnv (Tup es) (TProd (fromAll es as))
  PrjS :
    Synths tyEnv tmEnv e (TProd as) ->
    Elem (l :- a) as.context ->
    Synths tyEnv tmEnv (Prj e l) a
  UnrollS :
    Synths tyEnv tmEnv e (TFix x a) ->
    Synths tyEnv tmEnv (Unroll e) (sub [<TFix x a `Over` Id] a)
  MapS :
    Not (IllFormed (TFix x a)) ->
    Not (IllFormed b) ->
    Not (IllFormed c) ->
    Synths tyEnv tmEnv (Map (x ** a) b c)
      (TArrow (TArrow (sub tyEnv b) (sub tyEnv c))
      (TArrow (sub (tyEnv :< (sub tyEnv b `Over` Id)) a)
              (sub (tyEnv :< (sub tyEnv c `Over` Id)) a)))
  GetChildrenS :
    Not (IllFormed (TFix x a)) ->
    Not (IllFormed b) ->
    Synths tyEnv tmEnv (GetChildren (x ** a) b)
      (TArrow (sub (tyEnv :< (sub tyEnv b `Over` Id)) a)
        (TProd
          [<"Children" :- sub tyEnv b
          , "Shape" :- sub (tyEnv :< (TNat `Over` Id)) a]))

data Checks where
  EmbedC :
    SynthsOnly e ->
    Synths tyEnv tmEnv e a ->
    Alpha a b ->
    Checks tyEnv tmEnv b e
  LetC :
    Synths tyEnv tmEnv e a ->
    Checks tyEnv (tmEnv :< (a `Over` Id)) b t ->
    Checks tyEnv tmEnv b (Let e (x ** t))
  LetTyC :
    Not (IllFormed a) ->
    Checks (tyEnv :< (sub tyEnv a `Over` Id)) tmEnv b t ->
    Checks tyEnv tmEnv b (LetTy a (x ** t))
  AbsC :
    IsFunction bound a dom cod ->
    Checks tyEnv (tmEnv <>< mapProperty (`Over` Id) dom) cod t ->
    Checks tyEnv tmEnv a (Abs (bound ** t))
  TupC :
    AllChecks tyEnv tmEnv as.context ts.context ->
    Checks tyEnv tmEnv (TProd as) (Tup ts)
  InjC :
    Elem (l :- a) as.context ->
    Checks tyEnv tmEnv a t ->
    Checks tyEnv tmEnv (TSum as) (Inj l t)
  CaseC :
    Synths tyEnv tmEnv e (TSum as) ->
    AllBranches tyEnv tmEnv as.context a ts.context ->
    Checks tyEnv tmEnv a (Case e ts)
  RollC :
    Checks tyEnv tmEnv (sub [<TFix x a `Over` Id] a) t ->
    Checks tyEnv tmEnv (TFix x a) (Roll t)
  FoldC :
    Synths tyEnv tmEnv e (TFix x a) ->
    Checks tyEnv (tmEnv :< (sub [<b `Over` Id] a `Over` Id)) b t ->
    Checks tyEnv tmEnv b (Fold e (y ** t))

%name Synths prf
%name Checks prf

public export
data NotSynths :
  All (const $ Thinned Ty [<]) tyCtx ->
  All (const $ Thinned Ty [<]) tmCtx ->
  Term tyCtx tmCtx -> Type
public export
data NotChecks :
  All (const $ Thinned Ty [<]) tyCtx ->
  All (const $ Thinned Ty [<]) tmCtx ->
  Ty [<] -> Term tyCtx tmCtx -> Type

namespace Spine
  public export
  data NotCheckSpine :
    All (const $ Thinned Ty [<]) tyCtx ->
    All (const $ Thinned Ty [<]) tmCtx ->
    Ty [<] -> List (Term tyCtx tmCtx) -> Type
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
    All (const $ Thinned Ty [<]) tyCtx ->
    All (const $ Thinned Ty [<]) tmCtx ->
    (ts : Context (Term tyCtx tmCtx)) -> Type
    where
    Step :
      These (NotSynths tyEnv tmEnv t) (AnyNotSynths tyEnv tmEnv ts) ->
      AnyNotSynths tyEnv tmEnv (ts :< (l :- t))

  %name AnyNotSynths contras

namespace Checks
  public export
  data AnyNotChecks :
    All (const $ Thinned Ty [<]) tyCtx ->
    All (const $ Thinned Ty [<]) tmCtx ->
    Context (Ty [<]) -> Context (Term tyCtx tmCtx) -> Type
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
    All (const $ Thinned Ty [<]) tyCtx ->
    All (const $ Thinned Ty [<]) tmCtx ->
    Context (Ty [<]) -> Ty [<] -> Context (x ** Term tyCtx (tmCtx :< x)) -> Type
    where
    Base1 : AnyNotBranches tyEnv tmEnv (as :< a) b [<]
    Step1 :
      ((a : Ty [<]) -> Not (Elem (l :- a) as)) ->
      AnyNotBranches tyEnv tmEnv as b (ts :< (l :- (x ** t)))
    Step2 :
      (i : Elem (l :- a) as) ->
      These
        (NotChecks tyEnv (tmEnv :< (a `Over` Id)) b t)
        (AnyNotBranches tyEnv tmEnv (dropElem as i) b ts) ->
      AnyNotBranches tyEnv tmEnv as b (ts :< (l :- (x ** t)))

  %name AnyNotBranches contras

data NotSynths where
  ChecksNS :
    ChecksOnly t ->
    NotSynths tyEnv tmEnv t
  AnnotNS :
    These (IllFormed a) (NotChecks tyEnv tmEnv (sub tyEnv a) t) ->
    NotSynths tyEnv tmEnv (Annot t a)
  LetNS1 :
    NotSynths tyEnv tmEnv e ->
    NotSynths tyEnv tmEnv (Let e (x ** f))
  LetNS2 :
    Synths tyEnv tmEnv e a ->
    NotSynths tyEnv (tmEnv :< (a `Over` Id)) f ->
    NotSynths tyEnv tmEnv (Let e (x ** f))
  LetTyNS :
    These (IllFormed a) (NotSynths (tyEnv :< (sub tyEnv a `Over` Id)) tmEnv e) ->
    NotSynths tyEnv tmEnv (LetTy a (x ** e))
  AppNS1 :
    NotSynths tyEnv tmEnv f ->
    NotSynths tyEnv tmEnv (App f ts)
  AppNS2 :
    Synths tyEnv tmEnv f a ->
    NotCheckSpine tyEnv tmEnv a ts ->
    NotSynths tyEnv tmEnv (App f ts)
  TupNS :
    AnyNotSynths tyEnv tmEnv es.context ->
    NotSynths tyEnv tmEnv (Tup es)
  PrjNS1 :
    NotSynths tyEnv tmEnv e ->
    NotSynths tyEnv tmEnv (Prj e l)
  PrjNS2 :
    Synths tyEnv tmEnv e a ->
    ((as : Row (Ty [<])) -> Not (a = TProd as)) ->
    NotSynths tyEnv tmEnv (Prj e l)
  PrjNS3 :
    Synths tyEnv tmEnv e (TProd as) ->
    ((a : Ty [<]) -> Not (Elem (l :- a) as.context)) ->
    NotSynths tyEnv tmEnv (Prj e l)
  UnrollNS1 :
    NotSynths tyEnv tmEnv e ->
    NotSynths tyEnv tmEnv (Unroll e)
  UnrollNS2 :
    Synths tyEnv tmEnv e a ->
    ((x : String) -> (b : Ty [<x]) -> Not (a = TFix x b)) ->
    NotSynths tyEnv tmEnv (Unroll e)
  MapNS :
    These (IllFormed (TFix x a)) (These (IllFormed b) (IllFormed c)) ->
    NotSynths tyEnv tmEnv (Map (x ** a) b c)
  GetChildrenNS :
    These (IllFormed (TFix x a)) (IllFormed b) ->
    NotSynths tyEnv tmEnv (GetChildren (x ** a) b)

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
    NotChecks tyEnv tmEnv b (Let e (x ** t))
  LetNC2 :
    Synths tyEnv tmEnv e a ->
    NotChecks tyEnv (tmEnv :< (a `Over` Id)) b t ->
    NotChecks tyEnv tmEnv b (Let e (x ** t))
  LetTyNC :
    These (IllFormed a) (NotChecks (tyEnv :< (sub tyEnv a `Over` Id)) tmEnv b t) ->
    NotChecks tyEnv tmEnv b (LetTy a (x ** t))
  AbsNC1 :
    NotFunction bound a ->
    NotChecks tyEnv tmEnv a (Abs (bound ** t))
  AbsNC2 :
    IsFunction bound a dom cod ->
    NotChecks tyEnv (tmEnv <>< mapProperty (`Over` Id) dom) cod t ->
    NotChecks tyEnv tmEnv a (Abs (bound ** t))
  TupNC1 :
    ((as : Row (Ty [<])) -> Not (a = TProd as)) ->
    NotChecks tyEnv tmEnv a (Tup ts)
  TupNC2 :
    AnyNotChecks tyEnv tmEnv as.context ts.context ->
    NotChecks tyEnv tmEnv (TProd as) (Tup ts)
  InjNC1 :
    ((as : Row (Ty [<])) -> Not (a = TSum as)) ->
    NotChecks tyEnv tmEnv a (Inj l t)
  InjNC2 :
    ((a : Ty [<]) -> Not (Elem (l :- a) as.context)) ->
    NotChecks tyEnv tmEnv (TSum as) (Inj l t)
  InjNC3 :
    Elem (l :- a) as.context ->
    NotChecks tyEnv tmEnv a t ->
    NotChecks tyEnv tmEnv (TSum as) (Inj l t)
  CaseNC1 :
    NotSynths tyEnv tmEnv e ->
    NotChecks tyEnv tmEnv a (Case e ts)
  CaseNC2 :
    Synths tyEnv tmEnv e b ->
    ((as : Row (Ty [<])) -> Not (b = TSum as)) ->
    NotChecks tyEnv tmEnv a (Case e ts)
  CaseNC3 :
    Synths tyEnv tmEnv e (TSum as) ->
    AnyNotBranches tyEnv tmEnv as.context a ts.context ->
    NotChecks tyEnv tmEnv a (Case e ts)
  RollNC1 :
    ((x : String) -> (b : Ty [<x]) -> Not (a = TFix x b)) ->
    NotChecks tyEnv tmEnv a (Roll t)
  RollNC2 :
    NotChecks tyEnv tmEnv (sub [<TFix x a `Over` Id] a) t ->
    NotChecks tyEnv tmEnv (TFix x a) (Roll t)
  FoldNC1 :
    NotSynths tyEnv tmEnv e ->
    NotChecks tyEnv tmEnv b (Fold e (y ** t))
  FoldNC2 :
    Synths tyEnv tmEnv e a ->
    ((x : String) -> (c : Ty [<x]) -> Not (a = TFix x c)) ->
    NotChecks tyEnv tmEnv b (Fold e (y ** t))
  FoldNC3 :
    Synths tyEnv tmEnv e (TFix x a) ->
    NotChecks tyEnv (tmEnv :< (sub [<b `Over` Id] a `Over` Id)) b t ->
    NotChecks tyEnv tmEnv b (Fold e (y ** t))

%name NotSynths contra
%name NotChecks contra

Uninhabited (NotSynths tyEnv tmEnv (Var i)) where
  uninhabited (ChecksNS Abs) impossible
  uninhabited (ChecksNS Inj) impossible
  uninhabited (ChecksNS Case) impossible
  uninhabited (ChecksNS Roll) impossible
  uninhabited (ChecksNS Fold) impossible

-- Synthesis gives unique types

synthsUnique : Synths tyEnv tmEnv e a -> Synths tyEnv tmEnv e b -> a = b
checkSpineUnique : CheckSpine tyEnv tmEnv a ts b -> CheckSpine tyEnv tmEnv a ts c -> b = c
allSynthsUnique : AllSynths tyEnv tmEnv es as -> AllSynths tyEnv tmEnv es bs -> as = bs

synthsUnique (AnnotS _ _) (AnnotS _ _) = Refl
synthsUnique VarS VarS = Refl
synthsUnique (LetS prf1 prf2) (LetS prf1' prf2') =
  let prf2' = rewrite synthsUnique prf1 prf1' in prf2' in
  synthsUnique prf2 prf2'
synthsUnique (LetTyS _ prf) (LetTyS _ prf') = synthsUnique prf prf'
synthsUnique (AppS prf prfs) (AppS prf' prfs') =
  let prfs' = rewrite synthsUnique prf prf' in prfs' in
  checkSpineUnique prfs prfs'
synthsUnique (TupS {es} prfs) (TupS prfs') =
  cong (TProd . fromAll es) $ allSynthsUnique prfs prfs'
synthsUnique (PrjS {as} prf i) (PrjS {as = bs} prf' j) =
  let j = rewrite inj TProd $ synthsUnique prf prf' in j in
  cong fst $ lookupUnique as i j
synthsUnique (UnrollS {x, a} prf) (UnrollS {x = y, a = b} prf') =
  cong (\(x ** a) => sub [<TFix x a `Over` Id] a) $
  fixInjective $
  synthsUnique prf prf'
synthsUnique (MapS _ _ _) (MapS _ _ _) = Refl
synthsUnique (GetChildrenS _ _) (GetChildrenS _ _) = Refl

checkSpineUnique [] [] = Refl
checkSpineUnique (prf :: prfs) (prf' :: prfs') = checkSpineUnique prfs prfs'

allSynthsUnique [<] [<] = Refl
allSynthsUnique (prfs :< prf) (prfs' :< prf') =
  cong2 (:<) (allSynthsUnique prfs prfs') (synthsUnique prf prf')

-- We cannot both succeed and fail

synthsSplit : Synths tyEnv tmEnv e a -> NotSynths tyEnv tmEnv e -> Void
checksSplit : Checks tyEnv tmEnv a t -> NotChecks tyEnv tmEnv a t -> Void
checkSpineSplit : CheckSpine tyEnv tmEnv a ts b -> NotCheckSpine tyEnv tmEnv a ts -> Void
allSynthsSplit : AllSynths tyEnv tmEnv es as -> AnyNotSynths tyEnv tmEnv es -> Void
allChecksSplit :
  (0 fresh : AllFresh as.names) ->
  AllChecks tyEnv tmEnv as ts -> AnyNotChecks tyEnv tmEnv as ts -> Void
allBranchesSplit :
  (0 fresh : AllFresh as.names) ->
  AllBranches tyEnv tmEnv as a ts -> AnyNotBranches tyEnv tmEnv as a ts -> Void

synthsSplit (AnnotS wf prf) (AnnotNS contras) =
  these wf (checksSplit prf) (const $ checksSplit prf) contras
synthsSplit VarS contra = absurd contra
synthsSplit (LetS prf1 prf2) (LetNS1 contra) = synthsSplit prf1 contra
synthsSplit (LetS prf1 prf2) (LetNS2 prf1' contra) =
  let contra = rewrite synthsUnique prf1 prf1' in contra in
  synthsSplit prf2 contra
synthsSplit (LetTyS wf prf) (LetTyNS contras) =
  these wf (synthsSplit prf) (const $ synthsSplit prf) contras
synthsSplit (AppS prf prfs) (AppNS1 contra) = synthsSplit prf contra
synthsSplit (AppS prf prfs) (AppNS2 prf' contras) =
  let contras = rewrite synthsUnique prf prf' in contras in
  checkSpineSplit prfs contras
synthsSplit (TupS prfs) (TupNS contras) = allSynthsSplit prfs contras
synthsSplit (PrjS prf i) (PrjNS1 contra) = synthsSplit prf contra
synthsSplit (PrjS {as} prf i) (PrjNS2 prf' contra) =
  void $ contra as $ synthsUnique prf' prf
synthsSplit (PrjS {as, a} prf i) (PrjNS3 {as = bs} prf' contra) =
  let i = rewrite inj TProd $ synthsUnique prf' prf in i in
  void $ contra a i
synthsSplit (UnrollS prf) (UnrollNS1 contra) = synthsSplit prf contra
synthsSplit (UnrollS {x, a} prf) (UnrollNS2 prf' contra) =
  void $ contra x a $ synthsUnique prf' prf
synthsSplit (MapS wf1 wf2 wf3) (MapNS contras) =
  these wf1 (these wf2 wf3 (const wf3)) (const $ these wf2 wf3 (const wf3)) contras
synthsSplit (GetChildrenS wf1 wf2) (GetChildrenNS contras) =
  these wf1 wf2 (const wf2) contras

checksSplit (EmbedC _ prf1 prf2) (EmbedNC1 _ contra) = synthsSplit prf1 contra
checksSplit (EmbedC _ prf1 prf2) (EmbedNC2 _ prf1' contra) =
  let contra = rewrite synthsUnique prf1 prf1' in contra in
  alphaSplit prf2 contra
checksSplit (LetC prf1 prf2) (LetNC1 contra) = synthsSplit prf1 contra
checksSplit (LetC prf1 prf2) (LetNC2 prf1' contra) =
  let contra = rewrite synthsUnique prf1 prf1' in contra in
  checksSplit prf2 contra
checksSplit (LetTyC wf prf) (LetTyNC contras) =
  these wf (checksSplit prf) (const $ checksSplit prf) contras
checksSplit (AbsC prf1 prf2) (AbsNC1 contra) = isFunctionSplit prf1 contra
checksSplit (AbsC prf1 prf2) (AbsNC2 prf1' contra) =
  let (eq1, eq2) = isFunctionUnique prf1 prf1' in
  let contra = rewrite eq1 in rewrite eq2 in contra in
  checksSplit prf2 contra
checksSplit (TupC {as} prfs) (TupNC1 contra) = void $ contra as Refl
checksSplit (TupC {as} prfs) (TupNC2 contras) = allChecksSplit as.fresh prfs contras
checksSplit (InjC {as} i prf) (InjNC1 contra) = void $ contra as Refl
checksSplit (InjC {a} i prf) (InjNC2 contra) = void $ contra a i
checksSplit (InjC {as} i prf) (InjNC3 j contra) =
  let contra = rewrite cong fst $ lookupUnique as i j in contra in
  checksSplit prf contra
checksSplit (CaseC prf prfs) (CaseNC1 contra) = synthsSplit prf contra
checksSplit (CaseC {as} prf prfs) (CaseNC2 prf' contra) =
  void $ contra as $ synthsUnique prf' prf
checksSplit (CaseC {as} prf prfs) (CaseNC3 prf' contras) =
  let contras = rewrite inj TSum $ synthsUnique prf prf' in contras in
  allBranchesSplit as.fresh prfs contras
checksSplit (RollC {x, a} prf) (RollNC1 contra) = void $ contra x a Refl
checksSplit (RollC prf) (RollNC2 contra) = checksSplit prf contra
checksSplit (FoldC prf1 prf2) (FoldNC1 contra) = synthsSplit prf1 contra
checksSplit (FoldC {x, a} prf1 prf2) (FoldNC2 prf1' contra) =
  void $ contra x a $ synthsUnique prf1' prf1
checksSplit (FoldC {t, b} prf1 prf2) (FoldNC3 prf1' contra) =
  let
    contra =
      replace
        {p = \(x ** a) => NotChecks tyEnv (tmEnv :< (sub [<b `Over` Id] a `Over` Id)) b t}
        (fixInjective $ synthsUnique prf1' prf1)
        contra
  in
  checksSplit prf2 contra

checkSpineSplit (prf :: prfs) (Step1 contra) = void $ contra _ _ Refl
checkSpineSplit (prf :: prfs) (Step2 contras) =
  these (checksSplit prf) (checkSpineSplit prfs) (const $ checkSpineSplit prfs) contras

allSynthsSplit (prfs :< prf) (Step contras) =
  these (synthsSplit prf) (allSynthsSplit prfs) (const $ allSynthsSplit prfs) contras

allChecksSplit fresh (Step i prf prfs) (Step1 contra) = void $ contra _ i
allChecksSplit fresh (Step {as, t, ts} i prf prfs) (Step2 j contras) =
  let
    contras =
      replace
        {p = \(a ** i) => These (NotChecks tyEnv tmEnv a t) (AnyNotChecks tyEnv tmEnv (dropElem as i) ts)}
        (lookupUnique (MkRow as fresh) j i)
        contras
    0 fresh = dropElemFresh as fresh i
  in
  these (checksSplit prf) (allChecksSplit fresh prfs) (const $ allChecksSplit fresh prfs) contras

allBranchesSplit fresh (Step i prf prfs) (Step1 contra) = void $ contra _ i
allBranchesSplit fresh (Step {as, b, x, t, ts} i prf prfs) (Step2 j contras) =
  let
    contras =
      replace
        {p = \(a ** i) =>
          These
            (NotChecks tyEnv (tmEnv :< (a `Over` Id)) b t)
            (AnyNotBranches tyEnv tmEnv (dropElem as i) b ts)}
        (lookupUnique (MkRow as fresh) j i)
        contras
    0 fresh = dropElemFresh as fresh i
  in
  these (checksSplit prf) (allBranchesSplit fresh prfs) (const $ allBranchesSplit fresh prfs) contras

-- Synthesis and Checking are decidable

fallbackCheck :
  SynthsOnly e ->
  Proof (Ty [<]) (Synths tyEnv tmEnv e) (NotSynths tyEnv tmEnv e) ->
  (a : Ty [<]) ->
  LazyEither (Checks tyEnv tmEnv a e) (NotChecks tyEnv tmEnv a e)
fallbackCheck prf p a =
  map
    (\xPrf => uncurry (EmbedC prf) $ snd xPrf)
    (either (EmbedNC1 prf) (\xPrf => uncurry (EmbedNC2 prf) $ snd xPrf)) $
  (b := p) >=> alpha b a

synths :
  (tyEnv : All (const $ Thinned Ty [<]) tyCtx) ->
  (tmEnv : All (const $ Thinned Ty [<]) tmCtx) ->
  (e : Term tyCtx tmCtx) ->
  Proof (Ty [<]) (Synths tyEnv tmEnv e) (NotSynths tyEnv tmEnv e)
export
checks :
  (tyEnv : All (const $ Thinned Ty [<]) tyCtx) ->
  (tmEnv : All (const $ Thinned Ty [<]) tmCtx) ->
  (a : Ty [<]) -> (t : Term tyCtx tmCtx) ->
  LazyEither (Checks tyEnv tmEnv a t) (NotChecks tyEnv tmEnv a t)
checkSpine :
  (tyEnv : All (const $ Thinned Ty [<]) tyCtx) ->
  (tmEnv : All (const $ Thinned Ty [<]) tmCtx) ->
  (a : Ty [<]) -> (ts : List (Term tyCtx tmCtx)) ->
  Proof (Ty [<]) (CheckSpine tyEnv tmEnv a ts) (NotCheckSpine tyEnv tmEnv a ts)
allSynths :
  (tyEnv : All (const $ Thinned Ty [<]) tyCtx) ->
  (tmEnv : All (const $ Thinned Ty [<]) tmCtx) ->
  (es : Context (Term tyCtx tmCtx)) ->
  Proof (All (const $ Ty [<]) es.names) (AllSynths tyEnv tmEnv es) (AnyNotSynths tyEnv tmEnv es)
allChecks :
  (tyEnv : All (const $ Thinned Ty [<]) tyCtx) ->
  (tmEnv : All (const $ Thinned Ty [<]) tmCtx) ->
  (as : Context (Ty [<])) -> (ts : Context (Term tyCtx tmCtx)) ->
  LazyEither (AllChecks tyEnv tmEnv as ts) (AnyNotChecks tyEnv tmEnv as ts)
allBranches :
  (tyEnv : All (const $ Thinned Ty [<]) tyCtx) ->
  (tmEnv : All (const $ Thinned Ty [<]) tmCtx) ->
  (as : Context (Ty [<])) -> (a : Ty [<]) -> (ts : Context (x ** Term tyCtx (tmCtx :< x))) ->
  LazyEither (AllBranches tyEnv tmEnv as a ts) (AnyNotBranches tyEnv tmEnv as a ts)

synths tyEnv tmEnv (Annot t a) =
  pure (sub tyEnv a) $
  map (uncurry AnnotS) AnnotNS $
  all (not $ illFormed a) (checks tyEnv tmEnv (sub tyEnv a) t)
synths tyEnv tmEnv (Var i) = Just (indexAll i.pos tmEnv).extract `Because` VarS
synths tyEnv tmEnv (Let e (x ** f)) =
  map snd
    (\(_, _), (prf1, prf2) => LetS prf1 prf2)
    (either LetNS1 (\xPrfs => uncurry LetNS2 (snd xPrfs))) $
  (a := synths tyEnv tmEnv e) >=> synths tyEnv (tmEnv :< (a `Over` Id)) f
synths tyEnv tmEnv (LetTy a (x ** e)) =
  map id (\_, (wf, prf) => LetTyS wf prf) LetTyNS $
  all (not $ illFormed a) (synths (tyEnv :< (sub tyEnv a `Over` Id)) tmEnv e)
synths tyEnv tmEnv (Abs (bound ** t)) = Nothing `Because` ChecksNS Abs
synths tyEnv tmEnv (App e ts) =
  map snd
    (\(_, _), (prf1, prf2) => AppS prf1 prf2)
    (either AppNS1 (\xPrfs => uncurry AppNS2 (snd xPrfs))) $
  (a := synths tyEnv tmEnv e) >=> checkSpine tyEnv tmEnv a ts
synths tyEnv tmEnv (Tup (MkRow es fresh)) =
  map (TProd . fromAll (MkRow es fresh)) (\_ => TupS) TupNS $
  allSynths tyEnv tmEnv es
synths tyEnv tmEnv (Prj e l) =
  map (snd . snd) true false $
  (a := synths tyEnv tmEnv e) >=>
  (as := isProd a) >=>
  decLookup l as.context
  where
  true :
    (x : (Ty [<], Row (Ty [<]), Ty [<])) ->
    (Synths tyEnv tmEnv e (fst x), uncurry (\x, yz => (x = TProd (fst yz), uncurry (\y,z => Elem (l :- z) y.context) yz)) x) ->
    Synths tyEnv tmEnv (Prj e l) (snd $ snd x)
  true (.(TProd as), as, a) (prf, Refl, i) = PrjS prf i

  false :
    Either
      (NotSynths tyEnv tmEnv e)
      (a : Ty [<] ** (Synths tyEnv tmEnv e a,
        Either
          ((as : Row (Ty [<])) -> Not (a = TProd as))
          (as : Row (Ty [<]) ** (a = TProd as, (b : Ty [<]) -> Not (Elem (l :- b) as.context))))) ->
    NotSynths tyEnv tmEnv (Prj e l)
  false (Left contra) = PrjNS1 contra
  false (Right (a ** (prf1, Left contra))) = PrjNS2 prf1 contra
  false (Right (.(TProd as) ** (prf1, Right (as ** (Refl, contra))))) = PrjNS3 prf1 contra
synths tyEnv tmEnv (Inj l t) = Nothing `Because` ChecksNS Inj
synths tyEnv tmEnv (Case e (MkRow ts _)) = Nothing `Because` ChecksNS Case
synths tyEnv tmEnv (Roll t) = Nothing `Because` ChecksNS Roll
synths tyEnv tmEnv (Unroll e) =
  map f true false $
  synths tyEnv tmEnv e `andThen` isFix
  where
  f : (Ty [<], (x ** Ty [<x])) -> Ty [<]
  f (a, (x ** b)) = sub [<TFix x b `Over` Id] b

  true :
    (axb : _) ->
    (Synths tyEnv tmEnv e (fst axb), uncurry (\a,xb => a = TFix xb.fst xb.snd) axb) ->
    Synths tyEnv tmEnv (Unroll e) (f axb)
  true (.(TFix x a), (x ** a)) (prf, Refl) = UnrollS prf

  false :
    Either
      (NotSynths tyEnv tmEnv e)
      (a ** (Synths tyEnv tmEnv e a, (x : _) -> (b : _) -> Not (a = TFix x b))) ->
    NotSynths tyEnv tmEnv (Unroll e)
  false (Left contra) = UnrollNS1 contra
  false (Right (a ** (prf, contra))) = UnrollNS2 prf contra
synths tyEnv tmEnv (Fold e (x ** t)) = Nothing `Because` ChecksNS Fold
synths tyEnv tmEnv (Map (x ** a) b c) =
  pure _ $
  map (\(wf1, wf2, wf3) => MapS wf1 wf2 wf3) MapNS $
  all (not $ illFormed (TFix x a)) (all (not $ illFormed b) (not $ illFormed c))
synths tyEnv tmEnv (GetChildren (x ** a) b) =
  pure _ $
  map (uncurry GetChildrenS) GetChildrenNS $
  all (not $ illFormed (TFix x a)) (not $ illFormed b)

checks tyEnv tmEnv a (Annot t b) = fallbackCheck Annot (synths tyEnv tmEnv $ Annot t b) a
checks tyEnv tmEnv a (Var i) = fallbackCheck Var (synths tyEnv tmEnv $ Var i) a
checks tyEnv tmEnv a (Let e (x ** t)) =
  map
    (\(_ ** (prf1, prf2)) => LetC prf1 prf2)
    (either LetNC1 (\xPrfs => uncurry LetNC2 $ snd xPrfs)) $
  (b := synths tyEnv tmEnv e) >=> checks tyEnv (tmEnv :< (b `Over` Id)) a t
checks tyEnv tmEnv a (LetTy b (x ** t)) =
  map (uncurry LetTyC) LetTyNC $
  all (not $ illFormed b) (checks (tyEnv :< (sub tyEnv b `Over` Id)) tmEnv a t)
checks tyEnv tmEnv a (Abs (bound ** t)) =
  map
    (\((_, _) ** (prf1, prf2)) => AbsC prf1 prf2)
    (either AbsNC1 false) $
  (domCod := isFunction bound a) >=>
  checks tyEnv (tmEnv <>< mapProperty (`Over` Id) (fst domCod)) (snd domCod) t
  where
  false :
    (x ** (uncurry (IsFunction bound a) x, NotChecks tyEnv (tmEnv <>< mapProperty (`Over` Id) (fst x)) (snd x) t)) ->
    NotChecks tyEnv tmEnv a (Abs (bound ** t))
  false ((_,_) ** prf) = uncurry AbsNC2 prf
checks tyEnv tmEnv a (App f ts) = fallbackCheck App (synths tyEnv tmEnv $ App f ts) a
checks tyEnv tmEnv a (Tup (MkRow ts fresh')) =
  map true false $
  (as := isProd a) >=> allChecks tyEnv tmEnv as.context ts
  where
  true :
    forall a.
    (as : Row (Ty [<]) ** (a = TProd as, AllChecks tyEnv tmEnv as.context ts)) ->
    Checks tyEnv tmEnv a (Tup (MkRow ts fresh'))
  true (as ** (Refl, prf)) = TupC prf

  false :
    forall a.
    Either
      ((as : Row (Ty [<])) -> Not (a = TProd as))
      (as : Row (Ty [<]) ** (a = TProd as, AnyNotChecks tyEnv tmEnv as.context ts)) ->
    NotChecks tyEnv tmEnv a (Tup (MkRow ts fresh'))
  false (Left contra) = TupNC1 contra
  false (Right (as ** (Refl, contra))) = TupNC2 contra
checks tyEnv tmEnv a (Prj e l) = fallbackCheck Prj (synths tyEnv tmEnv $ Prj e l) a
checks tyEnv tmEnv a (Inj l t) =
  map true false $
  (as := isSum a) >=>
  (b := decLookup l as.context) >=>
  checks tyEnv tmEnv b t
  where
  true :
    forall a.
    (as ** (a = TSum as, (b ** (Elem (l :- b) as.context, Checks tyEnv tmEnv b t)))) ->
    Checks tyEnv tmEnv a (Inj l t)
  true (as ** (Refl, (b ** (i, prf)))) = InjC i prf

  false :
    forall a.
    Either
      ((as : _) -> Not (a = TSum as))
      (as ** (a = TSum as,
        Either
          ((b : _) -> Not (Elem (l :- b) as.context))
          (b ** (Elem (l :- b) as.context, NotChecks tyEnv tmEnv b t)))) ->
    NotChecks tyEnv tmEnv a (Inj l t)
  false (Left contra) = InjNC1 contra
  false (Right (as ** (Refl, Left contra))) = InjNC2 contra
  false (Right (as ** (Refl, Right (b ** (i, contra))))) = InjNC3 i contra
checks tyEnv tmEnv a (Case e (MkRow ts fresh)) =
  map true false $
  (b := synths tyEnv tmEnv e) >=>
  (as := isSum b) >=>
  allBranches tyEnv tmEnv as.context a ts
  where
  true :
    forall fresh.
    (b ** (Synths tyEnv tmEnv e b, (as ** (b = TSum as, AllBranches tyEnv tmEnv as.context a ts)))) ->
    Checks tyEnv tmEnv a (Case e (MkRow ts fresh))
  true (.(TSum as) ** (prf, (as ** (Refl, prfs)))) = CaseC prf prfs

  false :
    forall fresh.
    Either
      (NotSynths tyEnv tmEnv e)
      (b ** (Synths tyEnv tmEnv e b,
        Either
          ((as : _) -> Not (b = TSum as))
          (as ** (b = TSum as, AnyNotBranches tyEnv tmEnv as.context a ts)))) ->
    NotChecks tyEnv tmEnv a (Case e (MkRow ts fresh))
  false (Left contra) = CaseNC1 contra
  false (Right (b ** (prf, Left contra))) = CaseNC2 prf contra
  false (Right (.(TSum as) ** (prf, Right (as ** (Refl, contras))))) = CaseNC3 prf contras
checks tyEnv tmEnv a (Roll t) =
  map true false $
  (xb := isFix a) >=> checks tyEnv tmEnv (ty xb) t
  where
  ty : (x ** Ty [<x]) -> Ty [<]
  ty (x ** b) = sub [<TFix x b `Over` Id] b

  true :
    forall a.
    (xb : (x ** Ty [<x]) ** (a = TFix (fst xb) (snd xb), Checks tyEnv tmEnv (ty xb) t)) ->
    Checks tyEnv tmEnv a (Roll t)
  true ((x ** b) ** (Refl, prf)) = RollC prf

  false :
    forall a.
    Either
      ((x : _) -> (b : Ty [<x]) -> Not (a = TFix x b))
      (xb : (x ** Ty [<x]) ** (a = TFix (fst xb) (snd xb), NotChecks tyEnv tmEnv (ty xb) t)) ->
    NotChecks tyEnv tmEnv a (Roll t)
  false (Left contra) = RollNC1 contra
  false (Right ((x ** b) ** (Refl, contra))) = RollNC2 contra
checks tyEnv tmEnv a (Unroll e) = fallbackCheck Unroll (synths tyEnv tmEnv $ Unroll e) a
checks tyEnv tmEnv a (Fold e (x ** t)) =
  map true false $
  (b := synths tyEnv tmEnv e) >=>
  (yc := isFix b) >=>
  checks tyEnv (tmEnv' yc) a t
  where
  tmEnv' : (y ** Ty [<y]) -> All (const $ Thinned Ty [<]) (tmCtx :< x)
  tmEnv' (y ** c) = tmEnv :< (sub [<a `Over` Id] c `Over` Id)

  true :
    (b ** (Synths tyEnv tmEnv e b,
      (yc ** (b = TFix (fst yc) (snd yc), Checks tyEnv (tmEnv' yc) a t)))) ->
    Checks tyEnv tmEnv a (Fold e (x ** t))
  true (.(TFix y b) ** (prf1, ((y ** b) ** (Refl, prf2)))) = FoldC prf1 prf2

  false :
    Either
      (NotSynths tyEnv tmEnv e)
      (b ** (Synths tyEnv tmEnv e b,
        Either
          ((y : _) -> (c : Ty [<y]) -> Not (b = TFix y c))
          (yc ** (b = TFix (fst yc) (snd yc), NotChecks tyEnv (tmEnv' yc) a t)))) ->
    NotChecks tyEnv tmEnv a (Fold e (x ** t))
  false (Left contra) = FoldNC1 contra
  false (Right (b ** (prf1, Left contra))) = FoldNC2 prf1 contra
  false (Right (.(TFix y b) ** (prf1, Right ((y ** b) ** (Refl, contra))))) = FoldNC3 prf1 contra
checks tyEnv tmEnv a (Map (x ** b) c d) =
  fallbackCheck Map (synths tyEnv tmEnv $ Map (x ** b) c d) a
checks tyEnv tmEnv a (GetChildren (x ** b) c) =
  fallbackCheck GetChildren (synths tyEnv tmEnv $ GetChildren (x ** b) c) a

checkSpine tyEnv tmEnv a [] = Just a `Because` []
checkSpine tyEnv tmEnv a (t :: ts) =
  map snd true false $
  (bc := isArrow a) >=>
  all (checks tyEnv tmEnv (fst bc) t) (checkSpine tyEnv tmEnv (snd bc) ts)
  where
  true :
    forall a.
    (bcd : ((Ty [<], Ty [<]), Ty [<])) ->
    ( a = TArrow (fst $ fst bcd) (snd $ fst bcd)
    , uncurry (\bc,d => (Checks tyEnv tmEnv (fst bc) t, CheckSpine tyEnv tmEnv (snd bc) ts d)) bcd) ->
    CheckSpine tyEnv tmEnv a (t :: ts) (snd bcd)
  true ((b, c), d) (Refl, (prf1, prf2)) = prf1 :: prf2

  false :
    forall a.
    Either
      ((b, c : Ty [<]) -> Not (a = TArrow b c))
      (bc : (Ty [<], Ty [<]) ** (a = TArrow (fst bc) (snd bc),
        These
          (NotChecks tyEnv tmEnv (fst bc) t)
          (NotCheckSpine tyEnv tmEnv (snd bc) ts))) ->
    NotCheckSpine tyEnv tmEnv a (t :: ts)
  false (Left contra) = Step1 contra
  false (Right ((b, c) ** (Refl, contras))) = Step2 contras

allSynths tyEnv tmEnv [<] = Just [<] `Because` [<]
allSynths tyEnv tmEnv (es :< (l :- e)) =
  map (uncurry (flip (:<))) (\(a, as), (prf, prfs) => prfs :< prf) Step $
  all (synths tyEnv tmEnv e) (allSynths tyEnv tmEnv es)

allChecks tyEnv tmEnv [<] [<] = True `Because` Base
allChecks tyEnv tmEnv (as :< la) [<] = False `Because` Base1
allChecks tyEnv tmEnv as (ts :< (l :- t)) =
  map
    (\((a ** i) ** (prf, prfs)) => Step i prf prfs)
    (either Step1 (\xPrf => Step2 (snd $ fst xPrf) (snd xPrf))) $
  (ai := (decLookup l as).forget) >=>
  all (checks tyEnv tmEnv (fst ai) t) (allChecks tyEnv tmEnv (dropElem as $ snd ai) ts)

allBranches tyEnv tmEnv [<] b [<] = True `Because` Base
allBranches tyEnv tmEnv (as :< la) b [<] = False `Because` Base1
allBranches tyEnv tmEnv as b (ts :< (l :- (x ** t))) =
  map
    (\((a ** i) ** (prf, prfs)) => Step i prf prfs)
    (either Step1 (\xPrf => Step2 (snd $ fst xPrf) (snd xPrf))) $
  (ai := (decLookup l as).forget) >=>
  all
    (checks tyEnv (tmEnv :< (fst ai `Over` Id)) b t)
    (allBranches tyEnv tmEnv (dropElem as $ snd ai) b ts)

-- Sugar -----------------------------------------------------------------------

public export
CheckLit : Nat -> Term tyCtx tmCtx
CheckLit 0 = Roll (Inj "Z" $ Tup [<])
CheckLit (S n) = Roll (Inj "S" $ CheckLit n)

public export
Lit : Nat -> Term tyCtx tmCtx
Lit n = Annot (CheckLit n) TNat

public export
Suc : Term tyCtx tmCtx
Suc = Annot (Abs (["_x"] ** Roll (Inj "S" $ Var (%% "_x")))) (TArrow TNat TNat)

export
isCheckLit : Term tyCtx tmCtx -> Maybe Nat
isCheckLit (Roll (Inj "Z" (Tup (MkRow [<] _)))) = Just 0
isCheckLit (Roll (Inj "S" t)) = S <$> isCheckLit t
isCheckLit _ = Nothing

export
isLit : Term tyCtx tmCtx -> Maybe Nat
isLit (Annot t a) =
  if (alpha {ctx2 = [<]} a TNat).does
  then isCheckLit t
  else Nothing
isLit _ = Nothing

export
isSuc : Term tyCtx tmCtx -> Bool
isSuc (Annot (Abs ([x] ** Roll (Inj "S" $ Var ((%%) x {pos = Here})))) a) =
  does (alpha {ctx2 = [<]} a (TArrow TNat TNat))
isSuc _ = False
