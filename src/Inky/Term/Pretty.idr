module Inky.Term.Pretty

import Data.Fin
import Data.Fin.Extra
import Data.List
import Data.String
import Inky.Term
import Inky.Type.Pretty
import Text.PrettyPrint.Prettyprinter

asTmChar : Fin 9 -> Char
asTmChar = index' ['x', 'y', 'z', 'a', 'b', 'c', 'd', 'e', 'f']

export
termName : Nat -> String
termName n with (divMod n 9)
  termName _ | Fraction _ 9 q r Refl =
    strSnoc
      (if q == 0 then "" else assert_total (termName $ pred q))
      (asTmChar r)

appPrec, prjPrec, expandPrec, annotPrec,
  letPrec, absPrec, injPrec, tupPrec, casePrec, contractPrec, foldPrec : Prec
appPrec = App
prjPrec = User 9
expandPrec = PrefixMinus
annotPrec = Equal
letPrec = Open
absPrec = Open
injPrec = User 8
tupPrec = User 2
casePrec = Open
contractPrec = PrefixMinus
foldPrec = Open

export
prettySynth : {ty, tm : Nat} -> SynthTerm ty tm -> Prec -> Doc ann
prettyCheck : {ty, tm : Nat} -> CheckTerm ty tm -> Prec -> Doc ann
prettyAllCheck : {ty, tm : Nat} -> List (CheckTerm ty tm) -> Prec -> List (Doc ann)
prettyAll1Check : {ty, tm : Nat} -> List1 (CheckTerm ty tm) -> Prec -> List (Doc ann)

prettySynth (Var i) d = pretty (termName $ finToNat i)
prettySynth (Lit k) d = pretty k
prettySynth (Suc t) d =
  parenthesise (d >= appPrec) $ group $ align $ hang 2 $
    "suc" <+> line <+> prettyCheck t appPrec
prettySynth (App e ts) d =
  parenthesise (d >= appPrec) $ group $ align $ hang 2 $
    concatWith (\x, y => x <+> line <+> y) (prettySynth e appPrec :: prettyAll1Check ts appPrec)
prettySynth (Prj e k) d =
  parenthesise (d > prjPrec) $ group $ align $ hang 2 $
    prettySynth e prjPrec <+> "[" <+> line' <+> pretty k <+> line' <+> "]"
prettySynth (Expand e) d =
  "!" <+>
  (parenthesise (d > expandPrec) $ group $ align $ hang 2 $
    prettySynth e expandPrec)
prettySynth (Annot t a) d =
  parenthesise (d > annotPrec) $ group $ align $ hang 2 $
    prettyCheck t annotPrec <++> ":" <+> line <+> prettyType a annotPrec

prettyCheck (Let e t) d =
  parenthesise (d > letPrec) $ group $ align $ hang 2 $
    "let" <++>
    (group $ align $ hang 2 $
      pretty (termName tm) <++> "=" <+> line <+> prettySynth e letPrec
    ) <++>
    "in" <+> line <+>
    prettyCheck t letPrec
prettyCheck (Abs k t) d =
  parenthesise (d > absPrec) $ group $ align $ hang 2 $
    "\\" <+> concatWith (\x, y => x <+> "," <++> y) (bindings tm (S k)) <++> "=>" <+> line <+>
    prettyCheck t absPrec
  where
  bindings : Nat -> Nat -> List (Doc ann)
  bindings tm 0 = []
  bindings tm (S k) = pretty (termName tm) :: bindings (S tm) k
prettyCheck (Inj k t) d =
  parenthesise (d > injPrec) $ group $ align $ hang 2 $
    "<" <+> line' <+> pretty k <+> line' <+> ">" <+> prettyCheck t injPrec
prettyCheck (Tup []) d = pretty "()"
prettyCheck (Tup [t]) d =
  parens $ group $ align $ hang 2 $
    prettyCheck t tupPrec <+> line <+> ","
prettyCheck (Tup ts) d =
  parenthesise (d > tupPrec) $ group $ align $ hang 2 $
    concatWith (\x, y => x <+> "," <++> line <+> y) (prettyAllCheck ts tupPrec)
prettyCheck (Case e ts) d =
  parenthesise (d > casePrec) $ group $ align $ hang 2 $
    "case" <++> prettySynth e casePrec <++> "of" <+> line <+>
    (braces $ align $ hang 2 $
      concatWith (\x, y => x <+> hardline <+> y) $
      map (\x =>
        parens $ group $ align $ hang 2 $
          "\\" <+> pretty (termName tm) <++> "=>" <+> line <+> x) $
      prettyAllCheck ts casePrec
    )
prettyCheck (Contract t) d =
  "~" <+>
  (parenthesise (d > contractPrec) $ group $ align $ hang 2 $
    prettyCheck t contractPrec)
prettyCheck (Fold e t) d =
  parenthesise (d > foldPrec) $ group $ align $ hang 2 $
    "fold" <++> prettySynth e foldPrec <++> "by" <+> line <+>
    (parens $ group $ align $ hang 2 $
      "\\" <+> pretty (termName tm) <++> "=>" <+> line <+> prettyCheck t foldPrec)
prettyCheck (Embed e) d = prettySynth e d

prettyAllCheck [] d = []
prettyAllCheck (t :: ts) d = prettyCheck t d :: prettyAllCheck ts d

prettyAll1Check (t ::: ts) d = prettyCheck t d :: prettyAllCheck ts d
