module Inky.Term.Desugar

import Data.List.Quantifiers
import Data.Maybe
import Inky.Data.List
import Inky.Decidable
import Inky.Term
import Inky.Term.Substitution

-- Desugar map -----------------------------------------------------------------

desugarMap :
  (meta : m) =>
  (a : Ty tyCtx) -> (i : Var tyCtx) -> (0 prf : i `StrictlyPositiveIn` a) ->
  (f : Term mode m tyCtx' tmCtx) ->
  (t : Term mode m tyCtx' tmCtx) ->
  Term mode m tyCtx' tmCtx
desugarMapTuple :
  (meta : m) =>
  (as : Context (Ty tyCtx)) ->
  (0 fresh : AllFresh as.names) ->
  (i : Var tyCtx) -> (0 prfs : i `StrictlyPositiveInAll` as) ->
  (f : Term mode m tyCtx' tmCtx) ->
  (t : Term mode m tyCtx' tmCtx) ->
  Row (Term mode m tyCtx' tmCtx)
desugarMapTupleNames :
  (0 meta : m) =>
  (as : Context (Ty tyCtx)) ->
  (0 fresh : AllFresh as.names) ->
  (0 i : Var tyCtx) -> (0 prfs : i `StrictlyPositiveInAll` as) ->
  (0 f : Term mode m tyCtx' tmCtx) ->
  (0 t : Term mode m tyCtx' tmCtx) ->
  (desugarMapTuple as fresh i prfs f t).names = as.names
desugarMapCase :
  (meta : m) =>
  (as : Context (Ty tyCtx)) ->
  (0 fresh : AllFresh as.names) ->
  (i : Var tyCtx) -> (0 prfs : i `StrictlyPositiveInAll` as) ->
  (f : Term mode m tyCtx' tmCtx) ->
  Row (x ** Term mode m tyCtx' (tmCtx :< x))
desugarMapCaseNames :
  (meta : m) =>
  (as : Context (Ty tyCtx)) ->
  (0 fresh : AllFresh as.names) ->
  (i : Var tyCtx) -> (0 prfs : i `StrictlyPositiveInAll` as) ->
  (f : Term mode m tyCtx' tmCtx) ->
  (desugarMapCase as fresh i prfs f).names = as.names

desugarMap (TVar j) i TVar f t with (i `decEq` j)
  _ | True `Because` _ = App meta f [t]
  _ | False `Because` _ = t
desugarMap (TArrow a b) i (TArrow prf) f t = t
desugarMap (TProd (MkRow as fresh)) i (TProd prfs) f t =
  Tup meta (desugarMapTuple as fresh i prfs f t)
desugarMap (TSum (MkRow as fresh)) i (TSum prfs) f t =
  Case meta t (desugarMapCase as fresh i prfs f)
desugarMap (TFix x a) i (TFix prf) f t =
  Fold meta t ("_eta" ** Roll meta
    (desugarMap a (ThereVar i) prf (thin (Drop Id) f) (Var meta (%% "_eta"))))

desugarMapTuple [<] [<] i [<] f t = [<]
desugarMapTuple (as :< (l :- a)) (fresh :< freshIn) i (prfs :< prf) f t =
  (:<)
    (desugarMapTuple as fresh i prfs f t)
    (l :- desugarMap a i prf f (Prj meta t l))
    @{rewrite desugarMapTupleNames as fresh i prfs f t in freshIn}

desugarMapTupleNames [<] [<] i [<] f t = Refl
desugarMapTupleNames (as :< (l :- a)) (fresh :< freshIn) i (prfs :< prf) f t =
  cong (:< l) $ desugarMapTupleNames as fresh i prfs f t

desugarMapCase [<] [<] i [<] f = [<]
desugarMapCase (as :< (l :- a)) (fresh :< freshIn) i (prfs :< prf) f =
  (:<)
    (desugarMapCase as fresh i prfs f)
    (l :- ("_eta" ** Inj meta l (desugarMap a i prf (thin (Drop Id) f) (Var meta (%% "_eta")))))
    @{rewrite desugarMapCaseNames as fresh i prfs f in freshIn}

desugarMapCaseNames [<] [<] i [<] f = Refl
desugarMapCaseNames (as :< (l :- a)) (fresh :< freshIn) i (prfs :< prf) f =
  cong (:< l) $ desugarMapCaseNames as fresh i prfs f

-- -- Well Formed

-- desugarMapChecks :
--   (0 meta : m) =>
--   (a : Ty (tyCtx :< arg ++ bound)) -> (len : LengthOf bound) ->
--   (0 prf : index (dropAll len) (toVar {sx = tyCtx :< arg} Here) `StrictlyPositiveIn` a) ->
--   {env1 : All (const $ Thinned Ty [<]) tyCtx} ->
--   {env2 : All (const $ Thinned Ty [<]) bound} ->
--   {b, c : Ty [<]} ->
--   Synths tyEnv tmEnv f (TArrow b c) ->
--   Synths tyEnv tmEnv t (sub (((:<) {x = arg} env1 (b `Over` Id)) ++ env2) a) ->
--   SynthsOnly t ->
--   Checks tyEnv tmEnv
--     (sub (((:<) {x = arg} env1 (c `Over` Id)) ++ env2) a)
--     (desugarMap {m} a (index (dropAll len) (toVar {sx = tyCtx :< arg} Here)) prf f t)
-- desugarMapTupleChecks :
--   (0 meta : m) =>
--   (as : Context (Ty (tyCtx :< arg ++ bound))) -> (len' : LengthOf bs) ->
--   (0 fresh' : AllFresh (as <>< bs).names) ->
--   (0 fresh : AllFresh as.names) ->
--   (len : LengthOf bound) ->
--   (0 prfs : index (dropAll len) (toVar {sx = tyCtx :< arg} Here) `StrictlyPositiveInAll` as) ->
--   {env1 : All (const $ Thinned Ty [<]) tyCtx} ->
--   {env2 : All (const $ Thinned Ty [<]) bound} ->
--   {b, c : Ty [<]} ->
--   Synths tyEnv tmEnv f (TArrow b c) ->
--   Synths tyEnv tmEnv t
--     (sub (((:<) {x = arg} env1 (b `Over` Id)) ++ env2) (TProd (MkRow (as <>< bs) fresh'))) ->
--   SynthsOnly t ->
--   AllChecks tyEnv tmEnv
--     (subAll (((:<) {x = arg} env1 (c `Over` Id)) ++ env2) as)
--     (desugarMapTuple {m} as fresh (index (dropAll len) (toVar {sx = tyCtx :< arg} Here)) prfs f t).context
-- desugarMapCaseBranches :
--   (0 meta : m) =>
--   (as : Context (Ty (tyCtx :< arg ++ bound))) -> (len' : LengthOf bs) ->
--   (0 fresh' : AllFresh (as <>< bs).names) ->
--   (0 fresh : AllFresh as.names) ->
--   (len : LengthOf bound) ->
--   (0 prfs : index (dropAll len) (toVar {sx = tyCtx :< arg} Here) `StrictlyPositiveInAll` as) ->
--   {env1 : All (const $ Thinned Ty [<]) tyCtx} ->
--   {env2 : All (const $ Thinned Ty [<]) bound} ->
--   {b, c : Ty [<]} ->
--   Synths tyEnv tmEnv f (TArrow b c) ->
--   AllBranches tyEnv tmEnv
--     (subAll (((:<) {x = arg} env1 (b `Over` Id)) ++ env2) as)
--     (sub (((:<) {x = arg} env1 (c `Over` Id)) ++ env2) (TSum (MkRow (as <>< bs) fresh')))
--     (desugarMapCase {m} as fresh (index (dropAll len) (toVar {sx = tyCtx :< arg} Here)) prfs f).context

-- desugarMapChecks (TVar j) len TVar fun arg argSynOnly
--   with (index (dropAll len) (toVar Here) `decEq` j)
--   desugarMapChecks (TVar _) len TVar fun arg argSynOnly | True `Because` Refl =
--     EmbedC App (AppS fun [EmbedC argSynOnly arg $ alphaSym $ alphaRefl b _ $ ?b]) ?c
--   _ | False `Because` neq =
--     EmbedC argSynOnly arg $ alphaSym $ alphaRefl _ _ ?a
-- desugarMapChecks (TArrow a b) len (TArrow prf) fun arg argSynOnly =
--   EmbedC argSynOnly arg $ ?dmc_2
-- desugarMapChecks (TProd (MkRow as fresh)) len (TProd prfs) fun arg argSynOnly =
--   TupC (desugarMapTupleChecks as Z fresh fresh len prfs fun arg argSynOnly)
-- desugarMapChecks (TSum (MkRow as fresh)) len (TSum prfs) fun arg argSynOnly =
--   CaseC arg (desugarMapCaseBranches as Z fresh fresh len prfs fun)
-- desugarMapChecks (TFix x a) len (TFix prf) fun arg' argSynOnly =
--   let
--     x =
--   -- FoldC arg' (RollC $
--     desugarMapChecks
--       { m
--       , meta
--       , tyCtx
--       , arg
--       , bound = bound :< x
--       , env1
--       , env2 = env2 :< ?dmc_90
--       , b
--       , c
--       , tyEnv
--       , tmEnv = tmEnv :< (?dmc_92 `Over` Id)
--       , f = thin (Drop Id) f
--       , t = Var meta ((%%) "_eta" {pos = Here})
--       }
--       a (S len) prf ?x ?y ?z
--   -- Need assoc. of subst
--   in FoldC arg' (RollC ?dmc_99)

-- Desugar Terms ---------------------------------------------------------------

desugarSynths :
  (len : LengthOf tyCtx) =>
  {t : Term Sugar m tyCtx tmCtx} ->
  (0 _ : Synths tyEnv tmEnv t a) ->
  Term NoSugar m tyCtx tmCtx
desugarChecks :
  LengthOf tyCtx =>
  {t : Term Sugar m tyCtx tmCtx} ->
  (0 _ : Checks tyEnv tmEnv a t) ->
  Term NoSugar m tyCtx tmCtx
desugarCheckSpine :
  LengthOf tyCtx =>
  {ts : List (Term Sugar m tyCtx tmCtx)} ->
  (0 _ : CheckSpine tyEnv tmEnv a ts b) ->
  List (Term NoSugar m tyCtx tmCtx)
desugarAllSynths :
  LengthOf tyCtx =>
  {ts : Context (Term Sugar m tyCtx tmCtx)} ->
  (0 _ : AllSynths tyEnv tmEnv ts as) ->
  Context (Term NoSugar m tyCtx tmCtx)
desugarAllChecks :
  LengthOf tyCtx =>
  {ts : Context (Term Sugar m tyCtx tmCtx)} ->
  (0 _ : AllChecks tyEnv tmEnv as ts) ->
  Context (Term NoSugar m tyCtx tmCtx)
desugarAllBranches :
  LengthOf tyCtx =>
  {ts : Context (x ** Term Sugar m tyCtx (tmCtx :< x))} ->
  (0 _ : AllBranches tyEnv tmEnv as a ts) ->
  Context (x ** Term NoSugar m tyCtx (tmCtx :< x))
desugarAllSynthsNames :
  (0 len : LengthOf tyCtx) =>
  {ts : Context (Term Sugar m tyCtx tmCtx)} ->
  (0 prfs : AllSynths tyEnv tmEnv ts as) ->
  (desugarAllSynths prfs).names = ts.names
desugarAllChecksNames :
  (0 len : LengthOf tyCtx) =>
  {ts : Context (Term Sugar m tyCtx tmCtx)} ->
  (0 prfs : AllChecks tyEnv tmEnv as ts) ->
  (desugarAllChecks prfs).names = ts.names
desugarAllBranchesNames :
  (0 len : LengthOf tyCtx) =>
  {ts : Context (x ** Term Sugar m tyCtx (tmCtx :< x))} ->
  (0 prfs : AllBranches tyEnv tmEnv as a ts) ->
  (desugarAllBranches prfs).names = ts.names

desugarSynths (AnnotS {meta, a} wf prf) = Annot meta (desugarChecks prf) a
desugarSynths (VarS {meta, i}) = Var meta i
desugarSynths (LetS {meta, x} prf1 prf2) = Let meta (desugarSynths prf1) (x ** desugarSynths prf2)
desugarSynths (LetTyS {meta, a, x} wf prf) = LetTy meta a (x ** desugarSynths prf)
desugarSynths (AppS {meta} prf prfs) = App meta (desugarSynths prf) (desugarCheckSpine prfs)
desugarSynths (TupS {meta, es} prfs) =
  Tup meta (MkRow (desugarAllSynths prfs) (rewrite desugarAllSynthsNames prfs in es.fresh))
desugarSynths (PrjS {meta, l} prf i) = Prj meta (desugarSynths prf) l
desugarSynths (UnrollS {meta} prf) = Unroll meta (desugarSynths prf)
desugarSynths (MapS {meta, x, a, b, c} (TFix prf1 wf1) wf2 wf3) =
  Annot meta
    (Abs meta
      (["_fun", "_arg"] ** desugarMap a (%% x) prf1 (Var meta (%% "_fun")) (Var meta (%% "_arg"))))
    (TArrow (TArrow (TArrow b c)
      (sub (tabulate len ((`Over` Id) . TVar . toVar) :< (b `Over` Id)) a))
      (sub (tabulate len ((`Over` Id) . TVar . toVar) :< (c `Over` Id)) a))

desugarChecks (AnnotC prf1 prf2) = desugarSynths prf1
desugarChecks (VarC prf1 prf2) = desugarSynths prf1
desugarChecks (LetC {meta, x} prf1 prf2) = Let meta (desugarSynths prf1) (x ** desugarChecks prf2)
desugarChecks (LetTyC {meta, a, x} wf prf) = LetTy meta a (x ** desugarChecks prf)
desugarChecks (AbsC {meta, bound} prf1 prf2) = Abs meta (bound ** desugarChecks prf2)
desugarChecks (AppC prf1 prf2) = desugarSynths prf1
desugarChecks (TupC {meta, ts} prfs) =
  Tup meta (MkRow (desugarAllChecks prfs) (rewrite desugarAllChecksNames prfs in ts.fresh))
desugarChecks (PrjC prf1 prf2) = desugarSynths prf1
desugarChecks (InjC {meta, l} i prf) = Inj meta l (desugarChecks prf)
desugarChecks (CaseC {meta, ts} prf prfs) =
  Case meta (desugarSynths prf)
    (MkRow (desugarAllBranches prfs) (rewrite desugarAllBranchesNames prfs in ts.fresh))
desugarChecks (RollC {meta} prf) = Roll meta (desugarChecks prf)
desugarChecks (UnrollC prf1 prf2) = desugarSynths prf1
desugarChecks (FoldC {meta, y} prf1 prf2) = Fold meta (desugarSynths prf1) (y ** desugarChecks prf2)
desugarChecks (MapC prf1 prf2) = desugarSynths prf1

desugarCheckSpine [] = []
desugarCheckSpine (prf :: prfs) = desugarChecks prf :: desugarCheckSpine prfs

desugarAllSynths [<] = [<]
desugarAllSynths ((:<) {l} prfs prf) = desugarAllSynths prfs :< (l :- desugarSynths prf)

desugarAllChecks Base = [<]
desugarAllChecks (Step {l} i prf prfs) = desugarAllChecks prfs :< (l :- desugarChecks prf)

desugarAllBranches Base = [<]
desugarAllBranches (Step {l, x} i prf prfs) = desugarAllBranches prfs :< (l :- (x ** desugarChecks prf))

desugarAllSynthsNames [<] = Refl
desugarAllSynthsNames ((:<) {l} prfs prf) = cong (:< l) $ desugarAllSynthsNames prfs

desugarAllChecksNames Base = Refl
desugarAllChecksNames (Step {l} i prf prfs) = cong (:< l) $ desugarAllChecksNames prfs

desugarAllBranchesNames Base = Refl
desugarAllBranchesNames (Step {l} i prf prfs) = cong (:< l) $ desugarAllBranchesNames prfs

-- Fallibly Desugar Terms ------------------------------------------------------

export
maybeDesugar : (len : LengthOf tyCtx) => Term Sugar m tyCtx tmCtx -> Maybe (Term NoSugar m tyCtx tmCtx)
maybeDesugarList :
  (len : LengthOf tyCtx) =>
  List (Term Sugar m tyCtx tmCtx) -> Maybe (List $ Term NoSugar m tyCtx tmCtx)
maybeDesugarAll :
  (len : LengthOf tyCtx) =>
  (ts : Context (Term Sugar m tyCtx tmCtx)) ->
  Maybe (All (const $ Term NoSugar m tyCtx tmCtx) ts.names)
maybeDesugarBranches :
  (len : LengthOf tyCtx) =>
  (ts : Context (x ** Term Sugar m tyCtx (tmCtx :< x))) ->
  Maybe (All (const $ (x ** Term NoSugar m tyCtx (tmCtx :< x))) ts.names)

maybeDesugar (Annot meta t a) = do
  t <- maybeDesugar t
  pure (Annot meta t a)
maybeDesugar (Var meta i) = pure (Var meta i)
maybeDesugar (Let meta e (x ** t)) = do
  e <- maybeDesugar e
  t <- maybeDesugar t
  pure (Let meta e (x ** t))
maybeDesugar (LetTy meta a (x ** t)) = do
  t <- maybeDesugar t
  pure (LetTy meta a (x ** t))
maybeDesugar (Abs meta (bound ** t)) = do
  t <- maybeDesugar t
  pure (Abs meta (bound ** t))
maybeDesugar (App meta e ts) = do
  e <- maybeDesugar e
  ts <- maybeDesugarList ts
  pure (App meta e ts)
maybeDesugar (Tup meta (MkRow ts fresh)) = do
  ts' <- maybeDesugarAll ts
  pure (Tup meta (fromAll (MkRow ts fresh) ts'))
maybeDesugar (Prj meta e l) = do
  e <- maybeDesugar e
  pure (Prj meta e l)
maybeDesugar (Inj meta l t) = do
  t <- maybeDesugar t
  pure (Inj meta l t)
maybeDesugar (Case meta e (MkRow ts fresh)) = do
  e <- maybeDesugar e
  ts' <- maybeDesugarBranches ts
  pure (Case meta e (fromAll (MkRow ts fresh) ts'))
maybeDesugar (Roll meta t) = do
  t <- maybeDesugar t
  pure (Roll meta t)
maybeDesugar (Unroll meta e) = do
  e <- maybeDesugar e
  pure (Unroll meta e)
maybeDesugar (Fold meta e (x ** t)) = do
  e <- maybeDesugar e
  t <- maybeDesugar t
  pure (Fold meta e (x ** t))
maybeDesugar (Map meta (x ** a) b c) =
  case (%% x `strictlyPositiveIn` a) of
    False `Because` contra => Nothing
    True `Because` prf =>
      pure $
      Annot meta
        (Abs meta
          (["_fun", "_arg"] ** desugarMap a (%% x) prf (Var meta (%% "_fun")) (Var meta (%% "_arg"))))
        (TArrow (TArrow (TArrow b c)
          (sub (tabulate len ((`Over` Id) . TVar . toVar) :< (b `Over` Id)) a))
          (sub (tabulate len ((`Over` Id) . TVar . toVar) :< (c `Over` Id)) a))

maybeDesugarList [] = pure []
maybeDesugarList (t :: ts) = [| maybeDesugar t :: maybeDesugarList ts |]

maybeDesugarAll [<] = pure [<]
maybeDesugarAll (ts :< (l :- t)) = [| maybeDesugarAll ts :< maybeDesugar t |]

maybeDesugarBranches [<] = pure [<]
maybeDesugarBranches (ts :< (l :- (x ** t))) = do
  ts <- maybeDesugarBranches ts
  t <- maybeDesugar t
  pure (ts :< (x ** t))
