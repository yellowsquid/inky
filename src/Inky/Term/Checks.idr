module Inky.Term.Checks

import Control.Function
import Data.DPair
import Data.List.Quantifiers
import Data.Singleton
import Data.These
import Inky.Data.SnocList.Quantifiers
import Inky.Decidable
import Inky.Decidable.Maybe
import Inky.Term

%hide Prelude.Ops.infixl.(>=>)

-- Can recompute type from synthesis proof

export
synthsRecompute :
  {tyEnv : _} -> {tmEnv : _} -> {e : _} ->
  Synths tyEnv tmEnv e a -> Singleton a
checkSpineRecompute :
  {tyEnv : _} -> {tmEnv : _} -> {a : _} ->
  CheckSpine tyEnv tmEnv a ts b -> Singleton b
allSynthsRecompute :
  {tyEnv : _} -> {tmEnv : _} -> {es : Context _} ->
  {0 as : Row (Ty [<])} ->
  AllSynths tyEnv tmEnv es as -> Singleton as

synthsRecompute (AnnotS wf prf) = Val _
synthsRecompute VarS = Val _
synthsRecompute (LetS prf1 prf2) with (synthsRecompute prf1)
  _ | Val _ = synthsRecompute prf2
synthsRecompute (LetTyS wf prf) = synthsRecompute prf
synthsRecompute (AppS prf prfs) with (synthsRecompute prf)
  _ | Val _ = checkSpineRecompute prfs
synthsRecompute (TupS prfs) with (allSynthsRecompute prfs)
  _ | Val _ = Val _
synthsRecompute (PrjS prf i) with (synthsRecompute prf)
  _ | Val _ = [| (nameOf i).value |]
synthsRecompute (UnrollS prf) with (synthsRecompute prf)
  _ | Val _ = Val _
synthsRecompute (MapS f g h) = Val _

checkSpineRecompute [] = Val _
checkSpineRecompute (prf :: prfs) = checkSpineRecompute prfs

allSynthsRecompute [<] = Val _
allSynthsRecompute (prfs :< prf) with (allSynthsRecompute prfs) | (synthsRecompute prf)
  _ | Val _ | Val _ = Val _

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
  cong TProd $ allSynthsUnique prfs prfs'
synthsUnique (PrjS {as} prf i) (PrjS {as = bs} prf' j) =
  let j = rewrite inj TProd $ synthsUnique prf prf' in j in
  cong fst $ lookupUnique as i j
synthsUnique (UnrollS {x, a} prf) (UnrollS {x = y, a = b} prf') =
  cong (\(x ** a) => sub [<TFix x a `Over` Id] a) $
  fixInjective $
  synthsUnique prf prf'
synthsUnique (MapS _ _ _) (MapS _ _ _) = Refl

checkSpineUnique [] [] = Refl
checkSpineUnique (prf :: prfs) (prf' :: prfs') = checkSpineUnique prfs prfs'

allSynthsUnique [<] [<] = Refl
allSynthsUnique ((:<) prfs {l} prf) (prfs' :< prf') =
  snocCong (allSynthsUnique prfs prfs') (cong (l :-) $ synthsUnique prf prf')

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
  these (wellFormedSplit wf) (checksSplit prf) (const $ checksSplit prf) contras
synthsSplit VarS contra = absurd contra
synthsSplit (LetS prf1 prf2) (LetNS1 contra) = synthsSplit prf1 contra
synthsSplit (LetS prf1 prf2) (LetNS2 prf1' contra) =
  let contra = rewrite synthsUnique prf1 prf1' in contra in
  synthsSplit prf2 contra
synthsSplit (LetTyS wf prf) (LetTyNS contras) =
  these (wellFormedSplit wf) (synthsSplit prf) (const $ synthsSplit prf) contras
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
  these (wellFormedSplit wf1)
    (these (wellFormedSplit wf2) (wellFormedSplit wf3) (const $ wellFormedSplit wf3))
    (const $ these (wellFormedSplit wf2) (wellFormedSplit wf3) (const $ wellFormedSplit wf3))
    contras

checksSplit (AnnotC prf1 prf2) (EmbedNC1 Annot contra) = synthsSplit prf1 contra
checksSplit (VarC prf1 prf2) (EmbedNC1 Var contra) = synthsSplit prf1 contra
checksSplit (AppC prf1 prf2) (EmbedNC1 App contra) = synthsSplit prf1 contra
checksSplit (PrjC prf1 prf2) (EmbedNC1 Prj contra) = synthsSplit prf1 contra
checksSplit (UnrollC prf1 prf2) (EmbedNC1 Unroll contra) = synthsSplit prf1 contra
checksSplit (MapC prf1 prf2) (EmbedNC1 Map contra) = synthsSplit prf1 contra
checksSplit (AnnotC prf1 prf2) (EmbedNC2 Annot prf1' contra) =
  let contra = rewrite synthsUnique prf1 prf1' in contra in
  alphaSplit prf2 contra
checksSplit (VarC prf1 prf2) (EmbedNC2 Var prf1' contra) =
  let contra = rewrite synthsUnique prf1 prf1' in contra in
  alphaSplit prf2 contra
checksSplit (AppC prf1 prf2) (EmbedNC2 App prf1' contra) =
  let contra = rewrite synthsUnique prf1 prf1' in contra in
  alphaSplit prf2 contra
checksSplit (PrjC prf1 prf2) (EmbedNC2 Prj prf1' contra) =
  let contra = rewrite synthsUnique prf1 prf1' in contra in
  alphaSplit prf2 contra
checksSplit (UnrollC prf1 prf2) (EmbedNC2 Unroll prf1' contra) =
  let contra = rewrite synthsUnique prf1 prf1' in contra in
  alphaSplit prf2 contra
checksSplit (MapC prf1 prf2) (EmbedNC2 Map prf1' contra) =
  let contra = rewrite synthsUnique prf1 prf1' in contra in
  alphaSplit prf2 contra
checksSplit (LetC prf1 prf2) (LetNC1 contra) = synthsSplit prf1 contra
checksSplit (LetC prf1 prf2) (LetNC2 prf1' contra) =
  let contra = rewrite synthsUnique prf1 prf1' in contra in
  checksSplit prf2 contra
checksSplit (LetTyC wf prf) (LetTyNC contras) =
  these (wellFormedSplit wf) (checksSplit prf) (const $ checksSplit prf) contras
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
  (e : Term mode m tyCtx tmCtx) ->
  Proof (Ty [<]) (Synths tyEnv tmEnv e) (NotSynths tyEnv tmEnv e)
export
checks :
  (tyEnv : All (const $ Thinned Ty [<]) tyCtx) ->
  (tmEnv : All (const $ Thinned Ty [<]) tmCtx) ->
  (a : Ty [<]) -> (t : Term mode m tyCtx tmCtx) ->
  LazyEither (Checks tyEnv tmEnv a t) (NotChecks tyEnv tmEnv a t)
checkSpine :
  (tyEnv : All (const $ Thinned Ty [<]) tyCtx) ->
  (tmEnv : All (const $ Thinned Ty [<]) tmCtx) ->
  (a : Ty [<]) -> (ts : List (Term mode m tyCtx tmCtx)) ->
  Proof (Ty [<]) (CheckSpine tyEnv tmEnv a ts) (NotCheckSpine tyEnv tmEnv a ts)
allSynths :
  (tyEnv : All (const $ Thinned Ty [<]) tyCtx) ->
  (tmEnv : All (const $ Thinned Ty [<]) tmCtx) ->
  (es : Context (Term mode m tyCtx tmCtx)) ->
  (0 fresh : AllFresh es.names) ->
  Proof (Subset (Row (Ty [<])) (\as => es.names = as.names))
    (AllSynths tyEnv tmEnv es . Subset.fst)
    (AnyNotSynths tyEnv tmEnv es)
allChecks :
  (tyEnv : All (const $ Thinned Ty [<]) tyCtx) ->
  (tmEnv : All (const $ Thinned Ty [<]) tmCtx) ->
  (as : Context (Ty [<])) -> (ts : Context (Term mode m tyCtx tmCtx)) ->
  LazyEither (AllChecks tyEnv tmEnv as ts) (AnyNotChecks tyEnv tmEnv as ts)
allBranches :
  (tyEnv : All (const $ Thinned Ty [<]) tyCtx) ->
  (tmEnv : All (const $ Thinned Ty [<]) tmCtx) ->
  (as : Context (Ty [<])) -> (a : Ty [<]) -> (ts : Context (x ** Term mode m tyCtx (tmCtx :< x))) ->
  LazyEither (AllBranches tyEnv tmEnv as a ts) (AnyNotBranches tyEnv tmEnv as a ts)

synths tyEnv tmEnv (Annot _ t a) =
  pure (sub tyEnv a) $
  map (uncurry AnnotS) AnnotNS $
  all (wellFormed a) (checks tyEnv tmEnv (sub tyEnv a) t)
synths tyEnv tmEnv (Var _ i) = Just (indexAll i.pos tmEnv).extract `Because` VarS
synths tyEnv tmEnv (Let _ e (x ** f)) =
  map snd
    (\(_, _), (prf1, prf2) => LetS prf1 prf2)
    (either LetNS1 (\xPrfs => uncurry LetNS2 (snd xPrfs))) $
  (a := synths tyEnv tmEnv e) >=> synths tyEnv (tmEnv :< (a `Over` Id)) f
synths tyEnv tmEnv (LetTy _ a (x ** e)) =
  map id (\_, (wf, prf) => LetTyS wf prf) LetTyNS $
  all (wellFormed a) (synths (tyEnv :< (sub tyEnv a `Over` Id)) tmEnv e)
synths tyEnv tmEnv (Abs _ (bound ** t)) = Nothing `Because` ChecksNS Abs
synths tyEnv tmEnv (App _ e ts) =
  map snd
    (\(_, _), (prf1, prf2) => AppS prf1 prf2)
    (either AppNS1 (\xPrfs => uncurry AppNS2 (snd xPrfs))) $
  (a := synths tyEnv tmEnv e) >=> checkSpine tyEnv tmEnv a ts
synths tyEnv tmEnv (Tup _ (MkRow es fresh)) =
  map (TProd . fst) (\_ => TupS) TupNS $
  allSynths tyEnv tmEnv es fresh
synths tyEnv tmEnv (Prj meta e l) =
  map (snd . snd) true false $
  (a := synths tyEnv tmEnv e) >=>
  (as := isProd a) >=>
  decLookup l as.context
  where
  true :
    (x : (Ty [<], Row (Ty [<]), Ty [<])) ->
    (Synths tyEnv tmEnv e (fst x), uncurry (\x, yz => (x = TProd (fst yz), uncurry (\y,z => Elem (l :- z) y.context) yz)) x) ->
    Synths tyEnv tmEnv (Prj meta e l) (snd $ snd x)
  true (.(TProd as), as, a) (prf, Refl, i) = PrjS prf i

  false :
    Either
      (NotSynths tyEnv tmEnv e)
      (a : Ty [<] ** (Synths tyEnv tmEnv e a,
        Either
          ((as : Row (Ty [<])) -> Not (a = TProd as))
          (as : Row (Ty [<]) ** (a = TProd as, (b : Ty [<]) -> Not (Elem (l :- b) as.context))))) ->
    NotSynths tyEnv tmEnv (Prj meta e l)
  false (Left contra) = PrjNS1 contra
  false (Right (a ** (prf1, Left contra))) = PrjNS2 prf1 contra
  false (Right (.(TProd as) ** (prf1, Right (as ** (Refl, contra))))) = PrjNS3 prf1 contra
synths tyEnv tmEnv (Inj _ l t) = Nothing `Because` ChecksNS Inj
synths tyEnv tmEnv (Case _ e (MkRow ts _)) = Nothing `Because` ChecksNS Case
synths tyEnv tmEnv (Roll _ t) = Nothing `Because` ChecksNS Roll
synths tyEnv tmEnv (Unroll _ e) =
  map f true false $
  synths tyEnv tmEnv e `andThen` isFix
  where
  f : (Ty [<], (x ** Ty [<x])) -> Ty [<]
  f (a, (x ** b)) = sub [<TFix x b `Over` Id] b

  true :
    (axb : _) ->
    (Synths tyEnv tmEnv e (fst axb), uncurry (\a,xb => a = TFix xb.fst xb.snd) axb) ->
    Synths tyEnv tmEnv (Unroll meta e) (f axb)
  true (.(TFix x a), (x ** a)) (prf, Refl) = UnrollS prf

  false :
    Either
      (NotSynths tyEnv tmEnv e)
      (a ** (Synths tyEnv tmEnv e a, (x : _) -> (b : _) -> Not (a = TFix x b))) ->
    NotSynths tyEnv tmEnv (Unroll meta e)
  false (Left contra) = UnrollNS1 contra
  false (Right (a ** (prf, contra))) = UnrollNS2 prf contra
synths tyEnv tmEnv (Fold _ e (x ** t)) = Nothing `Because` ChecksNS Fold
synths tyEnv tmEnv (Map _ (x ** a) b c) =
  pure _ $
  map (\(wf1, wf2, wf3) => MapS wf1 wf2 wf3) MapNS $
  all (wellFormed (TFix x a)) (all (wellFormed b) (wellFormed c))

checks tyEnv tmEnv a (Annot meta t b) = fallbackCheck Annot (synths tyEnv tmEnv $ Annot meta t b) a
checks tyEnv tmEnv a (Var meta i) = fallbackCheck Var (synths tyEnv tmEnv $ Var meta i) a
checks tyEnv tmEnv a (Let _ e (x ** t)) =
  map
    (\(_ ** (prf1, prf2)) => LetC prf1 prf2)
    (either LetNC1 (\xPrfs => uncurry LetNC2 $ snd xPrfs)) $
  (b := synths tyEnv tmEnv e) >=> checks tyEnv (tmEnv :< (b `Over` Id)) a t
checks tyEnv tmEnv a (LetTy _ b (x ** t)) =
  map (uncurry LetTyC) LetTyNC $
  all (wellFormed b) (checks (tyEnv :< (sub tyEnv b `Over` Id)) tmEnv a t)
checks tyEnv tmEnv a (Abs meta (bound ** t)) =
  map
    (\((_, _) ** (prf1, prf2)) => AbsC prf1 prf2)
    (either AbsNC1 false) $
  (domCod := isFunction bound a) >=>
  checks tyEnv (tmEnv <>< mapProperty (`Over` Id) (fst domCod)) (snd domCod) t
  where
  false :
    (x ** (Prelude.uncurry (IsFunction bound a) x, NotChecks tyEnv (tmEnv <>< mapProperty (`Over` Id) (fst x)) (snd x) t)) ->
    NotChecks tyEnv tmEnv a (Abs meta (bound ** t))
  false ((_,_) ** prf) = uncurry AbsNC2 prf
checks tyEnv tmEnv a (App meta f ts) = fallbackCheck App (synths tyEnv tmEnv $ App meta f ts) a
checks tyEnv tmEnv a (Tup _ (MkRow ts fresh')) =
  map true false $
  (as := isProd a) >=> allChecks tyEnv tmEnv as.context ts
  where
  true :
    forall a.
    (as : Row (Ty [<]) ** (a = TProd as, AllChecks tyEnv tmEnv as.context ts)) ->
    Checks tyEnv tmEnv a (Tup meta (MkRow ts fresh'))
  true (as ** (Refl, prf)) = TupC prf

  false :
    forall a.
    Either
      ((as : Row (Ty [<])) -> Not (a = TProd as))
      (as : Row (Ty [<]) ** (a = TProd as, AnyNotChecks tyEnv tmEnv as.context ts)) ->
    NotChecks tyEnv tmEnv a (Tup meta (MkRow ts fresh'))
  false (Left contra) = TupNC1 contra
  false (Right (as ** (Refl, contra))) = TupNC2 contra
checks tyEnv tmEnv a (Prj meta e l) = fallbackCheck Prj (synths tyEnv tmEnv $ Prj meta e l) a
checks tyEnv tmEnv a (Inj _ l t) =
  map true false $
  (as := isSum a) >=>
  (b := decLookup l as.context) >=>
  checks tyEnv tmEnv b t
  where
  true :
    forall a.
    (as ** (a = TSum as, (b ** (Elem (l :- b) as.context, Checks tyEnv tmEnv b t)))) ->
    Checks tyEnv tmEnv a (Inj meta l t)
  true (as ** (Refl, (b ** (i, prf)))) = InjC i prf

  false :
    forall a.
    Either
      ((as : _) -> Not (a = TSum as))
      (as ** (a = TSum as,
        Either
          ((b : _) -> Not (Elem (l :- b) as.context))
          (b ** (Elem (l :- b) as.context, NotChecks tyEnv tmEnv b t)))) ->
    NotChecks tyEnv tmEnv a (Inj meta l t)
  false (Left contra) = InjNC1 contra
  false (Right (as ** (Refl, Left contra))) = InjNC2 contra
  false (Right (as ** (Refl, Right (b ** (i, contra))))) = InjNC3 i contra
checks tyEnv tmEnv a (Case _ e (MkRow ts fresh)) =
  map true false $
  (b := synths tyEnv tmEnv e) >=>
  (as := isSum b) >=>
  allBranches tyEnv tmEnv as.context a ts
  where
  true :
    forall fresh.
    (b ** (Synths tyEnv tmEnv e b, (as ** (b = TSum as, AllBranches tyEnv tmEnv as.context a ts)))) ->
    Checks tyEnv tmEnv a (Case meta e (MkRow ts fresh))
  true (.(TSum as) ** (prf, (as ** (Refl, prfs)))) = CaseC prf prfs

  false :
    forall fresh.
    Either
      (NotSynths tyEnv tmEnv e)
      (b ** (Synths tyEnv tmEnv e b,
        Either
          ((as : _) -> Not (b = TSum as))
          (as ** (b = TSum as, AnyNotBranches tyEnv tmEnv as.context a ts)))) ->
    NotChecks tyEnv tmEnv a (Case meta e (MkRow ts fresh))
  false (Left contra) = CaseNC1 contra
  false (Right (b ** (prf, Left contra))) = CaseNC2 prf contra
  false (Right (.(TSum as) ** (prf, Right (as ** (Refl, contras))))) = CaseNC3 prf contras
checks tyEnv tmEnv a (Roll _ t) =
  map true false $
  (xb := isFix a) >=> checks tyEnv tmEnv (ty xb) t
  where
  ty : (x ** Ty [<x]) -> Ty [<]
  ty (x ** b) = sub [<TFix x b `Over` Id] b

  true :
    forall a.
    (xb : (x ** Ty [<x]) ** (a = TFix (fst xb) (snd xb), Checks tyEnv tmEnv (ty xb) t)) ->
    Checks tyEnv tmEnv a (Roll meta t)
  true ((x ** b) ** (Refl, prf)) = RollC prf

  false :
    forall a.
    Either
      ((x : _) -> (b : Ty [<x]) -> Not (a = TFix x b))
      (xb : (x ** Ty [<x]) ** (a = TFix (fst xb) (snd xb), NotChecks tyEnv tmEnv (ty xb) t)) ->
    NotChecks tyEnv tmEnv a (Roll meta t)
  false (Left contra) = RollNC1 contra
  false (Right ((x ** b) ** (Refl, contra))) = RollNC2 contra
checks tyEnv tmEnv a (Unroll meta e) = fallbackCheck Unroll (synths tyEnv tmEnv $ Unroll meta e) a
checks tyEnv tmEnv a (Fold _ e (x ** t)) =
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
    Checks tyEnv tmEnv a (Fold meta e (x ** t))
  true (.(TFix y b) ** (prf1, ((y ** b) ** (Refl, prf2)))) = FoldC prf1 prf2

  false :
    Either
      (NotSynths tyEnv tmEnv e)
      (b ** (Synths tyEnv tmEnv e b,
        Either
          ((y : _) -> (c : Ty [<y]) -> Not (b = TFix y c))
          (yc ** (b = TFix (fst yc) (snd yc), NotChecks tyEnv (tmEnv' yc) a t)))) ->
    NotChecks tyEnv tmEnv a (Fold meta e (x ** t))
  false (Left contra) = FoldNC1 contra
  false (Right (b ** (prf1, Left contra))) = FoldNC2 prf1 contra
  false (Right (.(TFix y b) ** (prf1, Right ((y ** b) ** (Refl, contra))))) = FoldNC3 prf1 contra
checks tyEnv tmEnv a (Map meta (x ** b) c d) =
  fallbackCheck Map (synths tyEnv tmEnv $ Map meta (x ** b) c d) a

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

allSynths tyEnv tmEnv [<] [<] = Just (Element [<] Refl) `Because` [<]
allSynths tyEnv tmEnv (es :< (l :- e)) (fresh :< freshIn) =
  map
    (\(a, Element as eq) =>
      Element ((:<) as (l :- a) @{rewrite sym eq in freshIn}) (cong (:< l) eq))
    (\(a, Element as eq), (prf, prfs) => (:<) prfs prf @{rewrite sym eq in freshIn})
    Step $
  all (synths tyEnv tmEnv e) (allSynths tyEnv tmEnv es fresh)

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
