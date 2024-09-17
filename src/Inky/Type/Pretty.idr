module Inky.Type.Pretty

import Inky.Context
import Inky.Type
import Text.PrettyPrint.Prettyprinter

arrowPrec, prodPrec, sumPrec, fixPrec : Prec
arrowPrec = Open
prodPrec = Open
sumPrec = Open
fixPrec = Open

export
prettyType : {ctx : Context ()} -> Ty ctx () -> Prec -> Doc ann
prettyTypeRow : {ctx : Context ()} -> Row (Ty ctx ()) -> Prec -> List (Doc ann)

prettyType (TVar i) d = pretty (unVal $ nameOf i)
prettyType TNat d = pretty "Nat"
prettyType (TArrow a b) d =
  parenthesise (d > arrowPrec) $ group $ align $ hang 2 $
    let parts = stripArrow b in
    concatWith (surround $ "->" <+> line) (prettyType a arrowPrec :: parts)
  where
  stripArrow : Ty ctx () -> List (Doc ann)
  stripArrow (TArrow a b) = prettyType a arrowPrec :: stripArrow b
  stripArrow a = [prettyType a arrowPrec]
prettyType (TProd as) d =
  enclose "<" ">" $ group $ align $ hang 2 $
    let parts = prettyTypeRow as prodPrec in
    concatWith (surround $ "," <+> line) parts
prettyType (TSum as) d =
  enclose "[" "]" $ group $ align $ hang 2 $
    let parts = prettyTypeRow as prodPrec in
    concatWith (surround $ "," <+> line) parts
prettyType (TFix x a) d =
  parens $ group $ align $ hang 2 $
    "\\" <+> pretty x <++> "=>" <+> line <+>
    prettyType a fixPrec

prettyTypeRow [<] d = []
prettyTypeRow (as :< (x :- a)) d =
  (group $ align $ hang 2 $ pretty x <+> ":" <+> line <+> prettyType a d)
  :: prettyTypeRow as d
