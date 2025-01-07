module Inky.Term.Recompute

import Data.List.Quantifiers
import Data.Singleton
import Inky.Term
import Inky.Type.Substitution

%hide Prelude.Ops.infixl.(>=>)

-- Can recompute arguments and result from function

export
isFunctionRecompute :
  {bound : List String} -> {a : Ty tyCtx} ->
  {0 dom : All (Assoc0 $ Ty tyCtx) bound} ->
  (0 _ : IsFunction bound a dom cod) -> (Singleton dom, Singleton cod)
isFunctionRecompute Done = (Val _, Val _)
isFunctionRecompute (Step {a} prf) =
  mapFst (\case Val _ => Val _) $ isFunctionRecompute prf

-- Can recompute type from synthesis proof

export
synthsRecompute :
  {tyEnv : _} -> {tmEnv : _} -> {e : _} ->
  (0 _ : Synths tyEnv tmEnv e a) -> Singleton a
checkSpineRecompute :
  {tyEnv : _} -> {tmEnv : _} -> {a : _} -> {ts : _} ->
  (0 _ : CheckSpine tyEnv tmEnv a ts b) ->
  Singleton b
allSynthsRecompute :
  {tyEnv : _} -> {tmEnv : _} -> {es : Context _} ->
  {0 as : Row (Ty [<])} ->
  (0 _ : AllSynths tyEnv tmEnv es as) -> Singleton as

synthsRecompute (AnnotS wf prf) = Val _
synthsRecompute VarS = Val _
synthsRecompute (LetS prf1 prf2) =
  case synthsRecompute prf1 of
    Val _ => synthsRecompute prf2
synthsRecompute (LetTyS wf prf) = synthsRecompute prf
synthsRecompute (AppS prf prfs) =
  case synthsRecompute prf of
    Val _ => checkSpineRecompute prfs
synthsRecompute (TupS prfs) =
  case allSynthsRecompute prfs of
    Val _ => Val _
synthsRecompute (PrjS {l, as} prf i) =
  case synthsRecompute prf of
    Val _ => case lookupRecompute as i of
      Val i => [| (nameOf i).value |]
synthsRecompute (UnrollS prf) =
  case synthsRecompute prf of
    Val _ => Val _
synthsRecompute (MapS f g h) = Val _

checkSpineRecompute [] = Val _
checkSpineRecompute (prf :: prfs) = checkSpineRecompute prfs

allSynthsRecompute [<] = Val _
allSynthsRecompute (prfs :< prf) =
  case (allSynthsRecompute prfs, synthsRecompute prf) of
    (Val _, Val _) => Val _

-- Synthesised types are well-formed

export
indexAllWellFormed : AllWellFormed as -> Elem (l :- a) as -> WellFormed a
indexAllWellFormed (wfs :< wf) Here = wf
indexAllWellFormed (wfs :< wf) (There i) = indexAllWellFormed wfs i

export
dropAllWellFormed : AllWellFormed as -> (i : Elem (l :- a) as) -> AllWellFormed (dropElem as i)
dropAllWellFormed (wfs :< wf) Here = wfs
dropAllWellFormed (wfs :< wf) (There i) = dropAllWellFormed wfs i :< wf

export
synthsWf :
  {e : Term NoSugar m tyCtx tmCtx} ->
  {tyEnv : All (Assoc0 $ Ty [<]) tyCtx} ->
  {tmEnv : All (Assoc0 $ Ty [<]) tmCtx} ->
  DAll WellFormed tyEnv -> DAll WellFormed tmEnv ->
  Synths tyEnv tmEnv e a -> WellFormed a
checkSpineWf :
  CheckSpine tyEnv tmEnv a ts b ->
  WellFormed a -> WellFormed b
allSynthsWf :
  {es : Context (Term NoSugar m tyCtx tmCtx)} ->
  {tyEnv : All (Assoc0 $ Ty [<]) tyCtx} ->
  {tmEnv : All (Assoc0 $ Ty [<]) tmCtx} ->
  DAll WellFormed tyEnv -> DAll WellFormed tmEnv ->
  AllSynths tyEnv tmEnv es as -> AllWellFormed as.context

synthsWf tyWf tmWf (AnnotS wf prf) = subWf tyWf wf
synthsWf tyWf tmWf (VarS {i}) = indexDAll i.pos tmWf
synthsWf tyWf tmWf (LetS {x} prf1 prf2) =
  case synthsRecompute prf1 of
    Val _ => synthsWf tyWf (tmWf :< (x :- synthsWf tyWf tmWf prf1)) prf2
synthsWf tyWf tmWf (LetTyS wf {x} prf) =
  synthsWf (tyWf :< (x :- subWf tyWf wf)) tmWf prf
synthsWf tyWf tmWf (AppS prf prfs) = checkSpineWf prfs (synthsWf tyWf tmWf prf)
synthsWf tyWf tmWf (TupS prfs) = TProd (allSynthsWf tyWf tmWf prfs)
synthsWf tyWf tmWf (PrjS prf i) =
  let TProd wfs = synthsWf tyWf tmWf prf in
  indexAllWellFormed wfs i
synthsWf tyWf tmWf (UnrollS {x} prf) =
  let TFix sp wf = synthsWf tyWf tmWf prf in
  case synthsRecompute prf of
    Val _ => subWf [<x :- TFix sp wf] wf
synthsWf tyWf tmWf (MapS (TFix {x} sp wf1) wf2 wf3) =
  let wf2 = subWf tyWf wf2 in
  let wf3 = subWf tyWf wf3 in
  TArrow (TArrow wf2 wf3) (TArrow
    (subWf (tyWf :< (x :- wf2)) wf1)
    (subWf (tyWf :< (x :- wf3)) wf1))

checkSpineWf [] wf = wf
checkSpineWf (prf :: prfs) (TArrow wf1 wf2) = checkSpineWf prfs wf2

allSynthsWf tyWf tmWf [<] = [<]
allSynthsWf tyWf tmWf (prfs :< prf) = allSynthsWf tyWf tmWf prfs :< synthsWf tyWf tmWf prf

export
isFunctionWf :
  IsFunction bound a dom cod -> WellFormed a ->
  (DAll WellFormed dom, WellFormed cod)
isFunctionWf Done wf = ([], wf)
isFunctionWf (Step {x} prf) (TArrow wf1 wf2) = mapFst ((x :- wf1) ::) $ isFunctionWf prf wf2
