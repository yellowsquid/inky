module Inky.Term.Pretty

import Data.List.Quantifiers
import Data.Singleton
import Data.String
import Data.These

import Inky.Decidable.Maybe
import Inky.Term
import Inky.Type.Pretty

import Text.Bounded
import Text.PrettyPrint.Prettyprinter

public export
data TermPrec = Atom | Prefix | Suffix | App | Annot | Open

%name TermPrec d

Eq TermPrec where
  Atom == Atom = True
  Prefix == Prefix = True
  Suffix == Suffix = True
  App == App = True
  Annot == Annot = True
  Open == Open = True
  _ == _ = False

Ord TermPrec where
  compare Atom Atom = EQ
  compare Atom d2 = LT
  compare Prefix Atom = GT
  compare Prefix Prefix = EQ
  compare Prefix d2 = LT
  compare Suffix Atom = GT
  compare Suffix Prefix = GT
  compare Suffix Suffix = EQ
  compare Suffix d2 = LT
  compare App App = EQ
  compare App Annot = LT
  compare App Open = LT
  compare App d2 = GT
  compare Annot Annot = EQ
  compare Annot Open = LT
  compare Annot d2 = GT
  compare Open Open = EQ
  compare Open d2 = GT

export
prettyTerm : {tyCtx, tmCtx : SnocList String} -> Term m tyCtx tmCtx -> TermPrec -> Doc ann
prettyAllTerm : {tyCtx, tmCtx : SnocList String} -> List (Term m tyCtx tmCtx) -> TermPrec -> List (Doc ann)
prettyTermCtx : {tyCtx, tmCtx : SnocList String} -> Context (Term m tyCtx tmCtx) -> TermPrec -> SnocList (Doc ann)
prettyCases : {tyCtx, tmCtx : SnocList String} -> Context (x ** Term m tyCtx (tmCtx :< x)) -> SnocList (Doc ann)
prettyLet : Doc ann -> Doc ann -> Doc ann
lessPrettyTerm : {tyCtx, tmCtx : SnocList String} -> Term m tyCtx tmCtx -> TermPrec -> Doc ann

prettyTerm t d =
  case isLit t <|> isCheckLit t of
    Just k => pretty k
    Nothing =>
      if isSuc t
      then pretty "suc"
      else lessPrettyTerm t d

prettyAllTerm [] d = []
prettyAllTerm (t :: ts) d = prettyTerm t d :: prettyAllTerm ts d

prettyTermCtx [<] d = [<]
prettyTermCtx (ts :< (l :- t)) d = prettyTermCtx ts d :< (pretty l <+> ":" <++> prettyTerm t d)

prettyCases [<] = [<]
prettyCases (ts :< (l :- (x ** Abs _ (bound ** t)))) =
  prettyCases ts :<
  (group $ align $
    pretty l <++> pretty x <++> "=>" <++>
      "\\" <+> concatWith (surround $ "," <++> neutral) (map pretty bound) <++> "=>" <+> line <+>
    prettyTerm t Open)
prettyCases (ts :< (l :- (x ** t))) =
  prettyCases ts :<
  (group $ align $
    pretty l <++> pretty x <++> "=>" <+> line <+>
    prettyTerm t Open)

prettyLet binding term =
  (group $
    pretty "let" <++>
    (group $ hang (-2) $ binding) <+> line <+>
    "in") <+> line <+>
  term

lessPrettyTerm (Annot _ t a) d =
  group $ align $ hang 2 $ parenthesise (d < Annot) $
    prettyTerm t App <++> ":" <+> line <+> prettyType a Open
lessPrettyTerm (Var _ i) d = pretty (unVal $ nameOf i)
lessPrettyTerm (Let _ e (x ** t)) d =
  -- TODO: pretty print annotated abstraction
  group $ align $ parenthesise (d < Open) $
  prettyLet
    (pretty x <++> "=" <+> line <+> prettyTerm e Open)
    (prettyTerm t Open)
lessPrettyTerm (LetTy _ a (x ** t)) d =
  group $ align $ parenthesise (d < Open) $
  prettyLet
    (pretty x <++> "=" <+> line <+> prettyType a Open)
    (prettyTerm t Open)
lessPrettyTerm (Abs _ (bound ** t)) d =
  group $ hang 2 $ parenthesise (d < Open) $
    "\\" <+> concatWith (surround $ "," <+> line) (map pretty bound) <++> "=>" <+> line <+>
    prettyTerm t Open
lessPrettyTerm (App _ (Map _ (x ** a) b c) ts) d =
  group $ align $ hang 2 $ parenthesise (d < App) $
    concatWith (surround line)
      (  pretty "map"
      :: parens (group $ align $ hang 2 $ "\\" <+> pretty x <++> "=>" <+> line <+> prettyType a Open)
      :: prettyType b Atom
      :: prettyType c Atom
      :: prettyAllTerm ts Suffix)
lessPrettyTerm (App _ (GetChildren _ (x ** a) b) ts) d =
  group $ align $ hang 2 $ parenthesise (d < App) $
    concatWith (surround line)
      (  pretty "getChildren"
      :: parens (group $ align $ hang 2 $ "\\" <+> pretty x <++> "=>" <+> line <+> prettyType a Open)
      :: prettyType b Atom
      :: prettyAllTerm ts Suffix)
lessPrettyTerm (App _ f ts) d =
  group $ align $ hang 2 $ parenthesise (d < App) $
    concatWith (surround line) (prettyTerm f Suffix :: prettyAllTerm ts Suffix)
lessPrettyTerm (Tup _ (MkRow ts _)) d =
  let parts = prettyTermCtx ts Open <>> [] in
  group $ align $ enclose "<" ">" $
    flatAlt
      (neutral <++> concatWith (surround $ line' <+> "," <++> neutral) parts <+> line)
      (concatWith (surround $ "," <++> neutral) parts)
lessPrettyTerm (Prj _ e l) d =
  group $ align $ hang 2 $ parenthesise (d < Suffix) $
    prettyTerm e Suffix <+> line' <+> "." <+> pretty l
lessPrettyTerm (Inj _ l t) d =
  group $ align $ hang 2 $ parenthesise (d < App) $
    pretty l <+> line <+> prettyTerm t Suffix
lessPrettyTerm (Case _ e (MkRow ts _)) d =
  let parts = prettyCases ts <>> [] in
  group $ align $ hang 2 $ parenthesise (d < Open) $
    (group $ hang (-2) $ "case" <++> prettyTerm e Open <+> line <+> "of") <+> line <+>
    (braces $
      flatAlt
        (neutral <++> concatWith (surround $ line' <+> ";" <++> neutral) parts <+> line)
        (concatWith (surround $ ";" <++> neutral) parts))
lessPrettyTerm (Roll _ t) d =
  pretty "~" <+>
  parenthesise (d < Prefix) (group $ align $ hang 2 $ prettyTerm t Prefix)
lessPrettyTerm (Unroll _ e) d =
  pretty "!" <+>
  parenthesise (d > Prefix) (group $ align $ hang 2 $ prettyTerm e Prefix)
lessPrettyTerm (Fold _ e (x ** t)) d =
  -- TODO: foldcase
  group $ align $ hang 2 $ parenthesise (d < Open) $
    "fold" <++> prettyTerm e Open <++> "by" <+> hardline <+>
    (group $ align $ hang 2 $ parens $
      "\\" <+> pretty x <++> "=>" <+> line <+> prettyTerm t Open)
lessPrettyTerm (Map _ (x ** a) b c) d =
  group $ align $ hang 2 $ parenthesise (d < App) $
    concatWith (surround line)
      [ pretty "map"
      , group (align $ hang 2 $ parens $  "\\" <+> pretty x <++> "=>" <+> line <+> prettyType a Open)
      , prettyType b Atom
      , prettyType c Atom
      ]
lessPrettyTerm (GetChildren _ (x ** a) b) d =
  group $ align $ hang 2 $ parenthesise (d < App) $
    concatWith (surround line)
      [ pretty "getChildren"
      , group (align $ hang 2 $ parens $  "\\" <+> pretty x <++> "=>" <+> line <+> prettyType a Open)
      , prettyType b Atom
      ]

-- Typing Errors ---------------------------------------------------------------

Pretty (ChecksOnly t) where
  pretty Abs = "abstraction"
  pretty Inj = "injection"
  pretty Case = "case split"
  pretty Roll = "rolling"
  pretty Fold = "fold"

prettyNotSynths :
  {tyCtx, tmCtx : SnocList String} ->
  {e : Term m tyCtx tmCtx} ->
  {tyEnv : _} -> {tmEnv : _} ->
  NotSynths tyEnv tmEnv e ->
  List (m, Doc ann)
export
prettyNotChecks :
  {tyCtx, tmCtx : SnocList String} ->
  {a : Ty [<]} ->
  {t : Term m tyCtx tmCtx} ->
  {tyEnv : _} -> {tmEnv : _} ->
  NotChecks tyEnv tmEnv a t ->
  List (m, Doc ann)
prettyNotCheckSpine :
  {tyCtx, tmCtx : SnocList String} ->
  {a : Ty [<]} ->
  {ts : List (Term m tyCtx tmCtx)} ->
  {tyEnv : _} -> {tmEnv : _} ->
  NotCheckSpine tyEnv tmEnv a ts ->
  List (m, Doc ann)
prettyAnyNotSynths :
  {tyCtx, tmCtx : SnocList String} ->
  {es : Context (Term m tyCtx tmCtx)} ->
  {tyEnv : _} -> {tmEnv : _} ->
  AnyNotSynths tyEnv tmEnv es ->
  List (m, Doc ann)
prettyAnyNotChecks :
  {tyCtx, tmCtx : SnocList String} ->
  {ts : Context (Term m tyCtx tmCtx)} ->
  {tyEnv : _} -> {tmEnv : _} -> {as : Context _} ->
  (meta : m) ->
  AnyNotChecks tyEnv tmEnv as ts ->
  List (m, Doc ann)
prettyAnyNotBranches :
  {tyCtx, tmCtx : SnocList String} ->
  {ts : Context (x ** Term m tyCtx (tmCtx :< x))} ->
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
prettyNotSynths (GetChildrenNS {a} {b}  contras) =
  bifoldMap
    (const [(e.meta, pretty "ill-formed functor" <+> line <+> prettyType a Open)])
    (const [(e.meta, pretty "ill-formed contents" <+> line <+> prettyType b Open)])
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
