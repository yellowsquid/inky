module Inky.Term.Pretty.Error

import Data.List.Quantifiers
import Data.Singleton
import Data.String
import Data.These

import Flap.Decidable.Maybe

import Inky.Term
import Inky.Term.Recompute
import Inky.Type.Pretty

import Text.PrettyPrint.Prettyprinter

-- Typing Errors ---------------------------------------------------------------

Pretty (ChecksOnly t) where
  pretty Abs = "abstraction"
  pretty Inj = "injection"
  pretty Case = "case split"
  pretty Roll = "rolling"
  pretty Fold = "fold"

prettyNotSynths :
  {tyCtx, tmCtx : SnocList String} ->
  {e : Term mode m tyCtx tmCtx} ->
  {tyEnv : _} -> {tmEnv : _} ->
  NotSynths tyEnv tmEnv e ->
  List (m, Doc ann)
export
prettyNotChecks :
  {tyCtx, tmCtx : SnocList String} ->
  {a : Ty [<]} ->
  {t : Term mode m tyCtx tmCtx} ->
  {tyEnv : _} -> {tmEnv : _} ->
  NotChecks tyEnv tmEnv a t ->
  List (m, Doc ann)
prettyNotCheckSpine :
  {tyCtx, tmCtx : SnocList String} ->
  {a : Ty [<]} ->
  {ts : List (Term mode m tyCtx tmCtx)} ->
  {tyEnv : _} -> {tmEnv : _} ->
  NotCheckSpine tyEnv tmEnv a ts ->
  List (m, Doc ann)
prettyAnyNotSynths :
  {tyCtx, tmCtx : SnocList String} ->
  {es : Context (Term mode m tyCtx tmCtx)} ->
  {tyEnv : _} -> {tmEnv : _} ->
  AnyNotSynths tyEnv tmEnv es ->
  List (m, Doc ann)
prettyAnyNotChecks :
  {tyCtx, tmCtx : SnocList String} ->
  {ts : Context (Term mode m tyCtx tmCtx)} ->
  {tyEnv : _} -> {tmEnv : _} -> {as : Context _} ->
  (meta : m) ->
  AnyNotChecks tyEnv tmEnv as ts ->
  List (m, Doc ann)
prettyAnyNotBranches :
  {tyCtx, tmCtx : SnocList String} ->
  {ts : Context (x ** Term mode m tyCtx (tmCtx :< x))} ->
  {tyEnv : _} -> {tmEnv : _} -> {as : Context _} -> {a : _} ->
  (meta : m) ->
  AnyNotBranches tyEnv tmEnv as a ts ->
  List (m, Doc ann)

prettyNotSynths (ChecksNS shape) =
  [(e.meta, pretty "cannot synthesise type of" <++> pretty shape)]
prettyNotSynths (AnnotNS {a} (This contra)) =
  [(e.meta, pretty "ill-formed type" <+> line <+> prettyType a Open)]
prettyNotSynths (AnnotNS (That contra)) = prettyNotChecks contra
prettyNotSynths (AnnotNS {a} (Both contra1 contra2)) =
  (e.meta, pretty "ill-formed type" <+> line <+> prettyType a Open) ::
  prettyNotChecks contra2
prettyNotSynths (LetNS1 contra) = prettyNotSynths contra
prettyNotSynths (LetNS2' (This contra)) = prettyNotSynths contra
prettyNotSynths (LetNS2' (That contra)) = prettyNotSynths contra
prettyNotSynths (LetNS2' (Both contra1 contra2)) =
  prettyNotSynths contra1 ++ prettyNotSynths contra2
prettyNotSynths (LetNS2 prf contra) =
  case synthsRecompute prf of
    Val a => prettyNotSynths contra
prettyNotSynths (LetTyNS {a} (This contra)) =
  [(e.meta, pretty "ill-formed type" <+> line <+> prettyType a Open)]
prettyNotSynths (LetTyNS (That contra)) = prettyNotSynths contra
prettyNotSynths (LetTyNS {a} (Both contra1 contra2)) =
  (e.meta, pretty "ill-formed type" <+> line <+> prettyType a Open)
  :: prettyNotSynths contra2
prettyNotSynths (AppNS1 contra) = prettyNotSynths contra
prettyNotSynths (AppNS2 prf contras) =
  case synthsRecompute prf of
    Val a => prettyNotCheckSpine contras
prettyNotSynths (TupNS contras) = prettyAnyNotSynths contras
prettyNotSynths (PrjNS1 contra) = prettyNotSynths contra
prettyNotSynths (PrjNS2 prf f) =
  case synthsRecompute prf of
    Val a =>
      [(e.meta
      , pretty "cannot project non-product type" <+> line <+>
        prettyType a Open
      )]
prettyNotSynths (PrjNS3 {l, as} prf contra) =
  case synthsRecompute prf of
    Val (TProd as) =>
      [(e.meta
      , pretty "unknown label" <++> enclose "'" "'" (pretty l) <+> line <+>
        pretty "in product type" <+> line <+>
        prettyType (TProd as) Open
      )]
prettyNotSynths (UnrollNS1 contra) = prettyNotSynths contra
prettyNotSynths (UnrollNS2 prf contra) =
  case synthsRecompute prf of
    Val a =>
      [(e.meta
      , pretty "cannot unroll non-inductive type" <+> line <+>
        prettyType a Open
      )]
prettyNotSynths (MapNS {a} {b} {c} contras) =
  bifoldMap
    (const [(e.meta, pretty "ill-formed functor" <+> line <+> prettyType a Open)])
    (bifoldMap
      (const [(e.meta, pretty "ill-formed source" <+> line <+> prettyType b Open)])
      (const [(e.meta, pretty "ill-formed target" <+> line <+> prettyType c Open)]))
    contras

prettyNotChecks (EmbedNC1 _ contra) = prettyNotSynths contra
prettyNotChecks (EmbedNC2 _ prf contra) =
  case synthsRecompute prf of
    Val b =>
      [(t.meta
      , pretty "cannot unify" <+> line <+>
        prettyType a Open <+> line <+>
        pretty "and" <+> line <+>
        prettyType b Open
      )]
prettyNotChecks (LetNC1 contra) = prettyNotSynths contra
prettyNotChecks (LetNC2' (This contra)) = prettyNotSynths contra
prettyNotChecks (LetNC2' (That contra)) = prettyNotChecks contra
prettyNotChecks (LetNC2' (Both contra1 contra2)) =
  prettyNotSynths contra1 ++
  prettyNotChecks contra2
prettyNotChecks (LetNC2 prf contra) =
  case synthsRecompute prf of
    Val _ => prettyNotChecks contra
prettyNotChecks (LetTyNC {a} (This contra)) =
  [(t.meta, pretty "ill-formed type" <+> line <+> prettyType a Open)]
prettyNotChecks (LetTyNC (That contra)) = prettyNotChecks contra
prettyNotChecks (LetTyNC (Both contra1 contra2)) =
  (t.meta, pretty "ill-formed type" <+> line <+> prettyType a Open) ::
  prettyNotChecks contra2
prettyNotChecks (AbsNC1 contra) =
  [(t.meta, pretty "cannot abstract to construct type" <+> line <+> prettyType a Open)]
prettyNotChecks (AbsNC2 prf contra) =
  case isFunctionRecompute prf of
    (Val _, Val _) => prettyNotChecks contra
prettyNotChecks (TupNC1 contra) =
  [(t.meta, pretty "cannot tuple to construct type" <+> line <+> prettyType a Open)]
prettyNotChecks (TupNC2 contras) = prettyAnyNotChecks t.meta contras
prettyNotChecks (InjNC1 contra) =
  [(t.meta, pretty "cannot inject to construct type" <+> line <+> prettyType a Open)]
prettyNotChecks (InjNC2 {l} contra) =
  [(t.meta
  , pretty "unknown label" <++> enclose "'" "'" (pretty l) <+> line <+>
    pretty "in sum type" <+> line <+>
    prettyType a Open
  )]
prettyNotChecks (InjNC3 i contra) =
  case [| (nameOf i).value |] of
    Val _ => prettyNotChecks contra
prettyNotChecks (CaseNC1 contra) = prettyNotSynths contra
prettyNotChecks (CaseNC2 prf contra) =
  case synthsRecompute prf of
    Val a => [(t.meta, pretty "cannot case split on type" <+> line <+> prettyType a Open)]
prettyNotChecks (CaseNC3 prf contras) =
  case synthsRecompute prf of
    Val _ => prettyAnyNotBranches t.meta contras
prettyNotChecks (RollNC1 contra) =
  [(t.meta, pretty "cannot roll to construct type" <+> line <+> prettyType a Open)]
prettyNotChecks (RollNC2 contra) = prettyNotChecks contra
prettyNotChecks (FoldNC1 contra) = prettyNotSynths contra
prettyNotChecks (FoldNC2 prf contra) =
  case synthsRecompute prf of
    Val a => [(t.meta, pretty "cannot fold over type" <+> line <+> prettyType a Open)]
prettyNotChecks (FoldNC3 prf contra) =
  case synthsRecompute prf of
    Val _ => prettyNotChecks contra

prettyNotCheckSpine (Step1 {t} contra) =
  [(t.meta, pretty "cannot apply non-function type" <+> line <+> prettyType a Open)]
prettyNotCheckSpine (Step2 (This contra)) = prettyNotChecks contra
prettyNotCheckSpine (Step2 (That contra)) = prettyNotCheckSpine contra
prettyNotCheckSpine (Step2 (Both contra1 contra2)) =
  prettyNotChecks contra1 ++ prettyNotCheckSpine contra2

prettyAnyNotSynths (Step (This contra)) = prettyNotSynths contra
prettyAnyNotSynths (Step (That contra)) = prettyAnyNotSynths contra
prettyAnyNotSynths (Step (Both contra1 contra2)) =
  prettyNotSynths contra1 ++ prettyAnyNotSynths contra2

prettyAnyNotChecks meta Base1 =
  [(meta
  , pretty "missing components" <+> line <+>
    concatWith (surround $ "," <++> neutral) (map pretty as.names <>> [])
  )]
prettyAnyNotChecks meta (Step1 {t, l} contra) =
  [(t.meta , pretty "unknown label" <++> enclose "'" "'" (pretty l))]
prettyAnyNotChecks meta (Step2 i (This contra)) =
  case [| (nameOf i).value |] of
    Val _ => prettyNotChecks contra
prettyAnyNotChecks meta (Step2 i (That contra)) = prettyAnyNotChecks meta contra
prettyAnyNotChecks meta (Step2 i (Both contra1 contra2)) =
  case [| (nameOf i).value |] of
    Val _ => prettyNotChecks contra1 ++ prettyAnyNotChecks meta contra2

prettyAnyNotBranches meta Base1 =
  [(meta
  , pretty "missing cases" <+> line <+>
    concatWith (surround $ "," <++> neutral) (map pretty as.names <>> [])
  )]
prettyAnyNotBranches meta (Step1 {t, l} contra) =
  [(t.meta , pretty "unknown label" <++> enclose "'" "'" (pretty l))]
prettyAnyNotBranches meta (Step2 i (This contra)) =
  case [| (nameOf i).value |] of
    Val _ => prettyNotChecks contra
prettyAnyNotBranches meta (Step2 i (That contra)) = prettyAnyNotBranches meta contra
prettyAnyNotBranches meta (Step2 i (Both contra1 contra2)) =
  case [| (nameOf i).value |] of
    Val _ => prettyNotChecks contra1 ++ prettyAnyNotBranches meta contra2
