module Inky.Type.Pretty

import Data.Fin
import Data.Fin.Extra
import Data.List
import Data.String
import Inky.Type
import Text.PrettyPrint.Prettyprinter

asTyChar : Fin 6 -> Char
asTyChar = index' ['X', 'Y', 'Z', 'A', 'B', 'C']

export
typeName : Nat -> String
typeName n with (divMod n 6)
  typeName _ | Fraction _ 6 q r Refl =
    strSnoc
      (if q == 0 then "'" else assert_total (typeName $ pred q))
      (asTyChar r)

arrowPrec, unionPrec, prodPrec, sumPrec, fixPrec : Prec
arrowPrec = Open
unionPrec = User 2
prodPrec = Open
sumPrec = User 1
fixPrec = Open

export
prettyType : {ty : Nat} -> Ty ty -> Prec -> Doc ann
prettyTypeAll : {ty : Nat} -> List (Ty ty) -> Prec -> List (Doc ann)
prettyTypeAll1 : {ty : Nat} -> List1 (Ty ty) -> Prec -> List (Doc ann)

prettyType (TVar i) d = pretty (typeName $ finToNat i)
prettyType TNat d = pretty "Nat"
prettyType (TArrow a b) d =
  parenthesise (d > arrowPrec) $ group $ align $ hang 2 $
    let parts = stripArrow b in
    concatWith (\x, y => x <++> "->" <+> line <+> y) (prettyType a arrowPrec :: parts)
  where
  stripArrow : Ty ty -> List (Doc ann)
  stripArrow (TArrow a b) = prettyType a arrowPrec :: stripArrow b
  stripArrow a = [prettyType a arrowPrec]
prettyType (TUnion (a ::: [])) d =
  parens $ group $ align $ hang 2 $
    prettyType a unionPrec <++> "&"
prettyType (TUnion as) d =
  parenthesise (d >= unionPrec) $ group $ align $ hang 2 $
    let parts = prettyTypeAll1 as unionPrec in
    concatWith (\x, y => x <++> "&" <+> line <+> y) parts
prettyType (TProd [a]) d =
  parens $ group $ align $ hang 2 $
    prettyType a prodPrec <++> ","
prettyType (TProd as) d =
  parens $ group $ align $ hang 2 $
    let parts = prettyTypeAll as prodPrec in
    concatWith (\x, y => x <++> "," <+> line <+> y) parts
prettyType (TSum []) d = "(+)"
prettyType (TSum [a]) d =
  parens $ group $ align $ hang 2 $
    prettyType a sumPrec <++> "+"
prettyType (TSum as) d =
  parenthesise (d >= sumPrec) $ group $ align $ hang 2 $
    let parts = prettyTypeAll as sumPrec in
    concatWith (\x, y => x <++> "+" <+> line <+> y) parts
prettyType (TFix a) d =
  parens $ group $ align $ hang 2 $
    "\\" <+> pretty (typeName ty) <++> "=>" <+> line <+>
    prettyType a fixPrec

prettyTypeAll [] d = []
prettyTypeAll (a :: as) d = prettyType a d :: prettyTypeAll as d

prettyTypeAll1 (a ::: as) d = prettyType a d :: prettyTypeAll as d
