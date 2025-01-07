module Inky.Type.Pretty

import Data.Singleton
import Flap.Decidable
import Inky.Type
import Text.PrettyPrint.Prettyprinter

public export
data InkyPrec = Atom | Prefix | Suffix | App | Annot | Open

%name InkyPrec d

export
Eq InkyPrec where
  Atom == Atom = True
  Prefix == Prefix = True
  Suffix == Suffix = True
  App == App = True
  Annot == Annot = True
  Open == Open = True
  _ == _ = False

export
Ord InkyPrec where
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
prettyType : {ctx : SnocList String} -> Ty ctx -> InkyPrec -> Doc ann
lessPrettyType : {ctx : SnocList String} -> Ty ctx -> InkyPrec -> Doc ann
lessPrettyTypeCtx : {ctx : SnocList String} -> Context (Ty ctx) -> InkyPrec -> SnocList (Doc ann)

prettyType a d =
  if does (alpha {ctx2 = [<]} a TNat)
  then pretty "Nat"
  else case isList a of
    Just b =>
      group $ align $ hang 2 $ parenthesise (d < App) $
        pretty "List" <+> line <+>
        prettyType (assert_smaller a b) Atom
    Nothing => lessPrettyType a d

lessPrettyType (TVar i) d = pretty (unVal $ nameOf i)
lessPrettyType (TArrow a b) d =
  group $ align $ parenthesise (d < Open) $
    let parts = stripArrow b in
    concatWith (surround $ neutral <++> "->" <+> line) (prettyType a App :: parts)
  where
  stripArrow : Ty ctx -> List (Doc ann)
  stripArrow (TArrow a b) = prettyType a App :: stripArrow b
  stripArrow a = [prettyType a App]
lessPrettyType (TProd (MkRow as _)) d =
  let parts = lessPrettyTypeCtx as Open <>> [] in
  group $ align $ enclose "<" ">" $
    flatAlt
      (neutral <++> concatWith (surround $ line <+> ";" <++> neutral) parts <+> line)
      (concatWith (surround $ ";" <++> neutral) parts)
lessPrettyType (TSum (MkRow as _)) d =
  let parts = lessPrettyTypeCtx as Open <>> [] in
  group $ align $ enclose "[" "]" $
    flatAlt
      (neutral <++> concatWith (surround $ line <+> ";" <++> neutral) parts <+> line)
      (concatWith (surround $ ";" <++> neutral) parts)
lessPrettyType (TFix x a) d =
  group $ align $ hang 2 $ parens $
    "\\" <+> pretty x <++> "=>" <+> line <+>
    prettyType a Open

lessPrettyTypeCtx [<] d = [<]
lessPrettyTypeCtx (as :< (x :- a)) d =
  lessPrettyTypeCtx as d :<
  (group $ align $ pretty x <+> ":" <+> line <+> prettyType a d)
