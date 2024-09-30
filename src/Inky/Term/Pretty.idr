module Inky.Term.Pretty

import Inky.Context
import Inky.Term
import Inky.Type.Pretty
import Text.PrettyPrint.Prettyprinter

appPrec, prjPrec, expandPrec, annotPrec,
  letPrec, absPrec, injPrec, tupPrec, casePrec, contractPrec, foldPrec : Prec
appPrec = App
prjPrec = User 9
expandPrec = PrefixMinus
annotPrec = Equal
letPrec = Open
absPrec = Open
injPrec = App
tupPrec = Open
casePrec = Open
contractPrec = PrefixMinus
foldPrec = Open

export
prettySynth :
  {tyCtx, tmCtx : Context ()} ->
  SynthTerm tyCtx tmCtx -> Prec -> Doc ann
prettyCheck :
  {tyCtx, tmCtx : Context ()} ->
  CheckTerm tyCtx tmCtx -> Prec -> Doc ann
prettyAllCheck :
  {tyCtx, tmCtx : Context ()} ->
  List (CheckTerm tyCtx tmCtx) -> Prec -> List (Doc ann)
prettyCheckCtx :
  {tyCtx, tmCtx : Context ()} ->
  Row (CheckTerm tyCtx tmCtx) -> Prec -> List (Doc ann)
prettyCheckCtxBinding :
  {tyCtx, tmCtx : Context ()} ->
  Row (x ** CheckTerm tyCtx (tmCtx :< (x :- ()))) -> Prec -> List (Doc ann)

prettySynth (Var i) d = pretty (unVal $ nameOf i)
prettySynth (Lit k) d = pretty k
prettySynth (Suc t) d =
  parenthesise (d >= appPrec) $ group $ align $ hang 2 $
    "suc" <+> line <+> prettyCheck t appPrec
prettySynth (App e ts) d =
  parenthesise (d >= appPrec) $ group $ align $ hang 2 $
    concatWith (surround line) (prettySynth e appPrec :: prettyAllCheck ts appPrec)
prettySynth (Prj e x) d =
  parenthesise (d > prjPrec) $ group $ align $ hang 2 $
    prettySynth e prjPrec <+> "." <+> pretty x
prettySynth (Expand e) d =
  "!" <+>
  (parenthesise (d > expandPrec) $ group $ align $ hang 2 $
    prettySynth e expandPrec)
prettySynth (Annot t a) d =
  parenthesise (d > annotPrec) $ group $ align $ hang 2 $
    prettyCheck t annotPrec <++> ":" <+> line <+> prettyType a annotPrec

prettyCheck (Let x e t) d =
  parenthesise (d > letPrec) $ group $ align $ hang 2 $
    "let" <++>
    (group $ align $ hang 2 $
      pretty x <++> "=" <+> line <+> prettySynth e letPrec
    ) <++>
    "in" <+> line <+>
    prettyCheck t letPrec
prettyCheck (Abs bound t) d =
  parenthesise (d > absPrec) $ group $ align $ hang 2 $
    "\\" <+> concatWith (surround ",") (bindings bound <>> []) <++> "=>" <+> line <+>
    prettyCheck t absPrec
  where
  bindings : Context () -> SnocList (Doc ann)
  bindings [<] = [<]
  bindings (bound :< (x :- ())) = bindings bound :< pretty x
prettyCheck (Inj k t) d =
  parenthesise (d > injPrec) $ group $ align $ hang 2 $
    "<" <+> line' <+> pretty k <+> line' <+> ">" <+> prettyCheck t injPrec
prettyCheck (Tup ts) d =
  parens $ group $ align $ hang 2 $
    concatWith (surround $ "," <+> line) (prettyCheckCtx ts tupPrec)
prettyCheck (Case e ts) d =
  parenthesise (d > casePrec) $ group $ align $ hang 2 $
    "case" <++> prettySynth e casePrec <++> "of" <+> line <+>
    (braces $ align $ hang 2 $
      concatWith (surround hardline) $
      map parens $
      prettyCheckCtxBinding ts casePrec)
prettyCheck (Contract t) d =
  "~" <+>
  (parenthesise (d > contractPrec) $ group $ align $ hang 2 $
    prettyCheck t contractPrec)
prettyCheck (Fold e x t) d =
  parenthesise (d > foldPrec) $ group $ align $ hang 2 $
    "fold" <++> prettySynth e foldPrec <++> "by" <+> line <+>
    (parens $ group $ align $ hang 2 $
      "\\" <+> pretty x <++> "=>" <+> line <+> prettyCheck t foldPrec)
prettyCheck (Embed e) d = prettySynth e d

prettyAllCheck [] d = []
prettyAllCheck (t :: ts) d = prettyCheck t d :: prettyAllCheck ts d

prettyCheckCtx [<] d = []
prettyCheckCtx (ts :< (x :- t)) d =
  (group $ align $ hang 2 $ pretty x <+> ":" <+> line <+> prettyCheck t d) ::
  prettyCheckCtx ts d

prettyCheckCtxBinding [<] d = []
prettyCheckCtxBinding (ts :< (x :- (y ** t))) d =
  (group $ align $ hang 2 $
    "\\" <+> pretty x <++> pretty y <++> "=>" <+> line <+> prettyCheck t d) ::
  prettyCheckCtxBinding ts d
