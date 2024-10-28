module Inky.Type.Pretty

import Data.Singleton
import Inky.Decidable
import Inky.Type
import Text.PrettyPrint.Prettyprinter

arrowPrec, prodPrec, sumPrec, fixPrec, listPrec : Prec
arrowPrec = Open
prodPrec = Open
sumPrec = Open
fixPrec = Open
listPrec = App

export
prettyType : {ctx : SnocList String} -> Ty ctx -> Prec -> Doc ann
lessPrettyType : {ctx : SnocList String} -> Ty ctx -> Prec -> Doc ann
lessPrettyTypeRow : {ctx : SnocList String} -> Context (Ty ctx) -> Prec -> List (Doc ann)

prettyType a d =
  if does (alpha {ctx2 = [<]} a TNat)
  then pretty "Nat"
  else case isList a of
    Just b =>
      parenthesise (d >= listPrec) $ group $ align $ hang 2 $
        pretty "List" <+> line <+>
        prettyType (assert_smaller a b) d
    Nothing => lessPrettyType a d

lessPrettyType (TVar i) d = pretty (unVal $ nameOf i)
lessPrettyType (TArrow a b) d =
  parenthesise (d > arrowPrec) $ group $ align $ hang 2 $
    let parts = stripArrow b in
    concatWith (surround $ neutral <++> "->" <+> line) (prettyType a arrowPrec :: parts)
  where
  stripArrow : Ty ctx -> List (Doc ann)
  stripArrow (TArrow a b) = prettyType a arrowPrec :: stripArrow b
  stripArrow a = [prettyType a arrowPrec]
lessPrettyType (TProd (MkRow as _)) d =
  enclose "<" ">" $ group $ align $ hang 2 $
    let parts = lessPrettyTypeRow as prodPrec in
    concatWith (surround $ "," <+> line) parts
lessPrettyType (TSum (MkRow as _)) d =
  enclose "[" "]" $ group $ align $ hang 2 $
    let parts = lessPrettyTypeRow as prodPrec in
    concatWith (surround $ "," <+> line) parts
lessPrettyType (TFix x a) d =
  parens $ group $ align $ hang 2 $
    "\\" <+> pretty x <++> "=>" <+> line <+>
    prettyType a fixPrec

lessPrettyTypeRow [<] d = []
lessPrettyTypeRow (as :< (x :- a)) d =
  (group $ align $ hang 2 $ pretty x <+> ":" <+> line <+> prettyType a d)
  :: lessPrettyTypeRow as d
