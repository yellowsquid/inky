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
prettyTypeCtx : {ctx : SnocList String} -> Context (Ty ctx) -> InkyPrec -> SnocList (Doc ann)

prettyType (TVar i) d = pretty (unVal $ nameOf i)
prettyType (TArrow a b) d =
  group $ align $ parenthesise (d < Open) $
    let parts = stripArrow b in
    concatWith (surround $ neutral <++> "->" <+> line) (prettyType a App :: parts)
  where
  stripArrow : Ty ctx -> List (Doc ann)
  stripArrow (TArrow a b) = prettyType a App :: stripArrow b
  stripArrow a = [prettyType a App]
prettyType (TProd (MkRow as _)) d =
  let parts = prettyTypeCtx as Open <>> [] in
  group $ align $ enclose "<" ">" $
    flatAlt
      (neutral <++> concatWith (surround $ line <+> ";" <++> neutral) parts <+> line)
      (concatWith (surround $ ";" <++> neutral) parts)
prettyType (TSum (MkRow as _)) d =
  let parts = prettyTypeCtx as Open <>> [] in
  group $ align $ enclose "[" "]" $
    flatAlt
      (neutral <++> concatWith (surround $ line <+> ";" <++> neutral) parts <+> line)
      (concatWith (surround $ ";" <++> neutral) parts)
prettyType (TFix x a) d =
  group $ align $ hang 2 $ parenthesise (d < App) $
    pretty "data" <++> pretty x <+> line <+> prettyType a Atom

prettyTypeCtx [<] d = [<]
prettyTypeCtx (as :< (x :- a)) d =
  prettyTypeCtx as d :<
  (group $ align $ pretty x <+> ":" <+> line <+> prettyType a d)

export
prettyBoundType : {ctx : SnocList String} -> (x ** Ty (ctx :< x)) -> InkyPrec -> Doc ann
prettyBoundType (bound ** a) d = 
  hang 2 $ group $ parenthesise (d < Open) $
   "\\" <+> pretty bound <++> "=>" <+> line <+> 
   prettyType a Open
