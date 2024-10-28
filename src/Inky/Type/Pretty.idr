module Inky.Type.Pretty

import Data.Singleton
import Inky.Decidable
import Inky.Type
import Text.PrettyPrint.Prettyprinter

public export
data TyPrec = Atom | App | Open

%name TyPrec d

Eq TyPrec where
  Atom == Atom = True
  App == App = True
  Open == Open = True
  _ == _ = False

Ord TyPrec where
  compare Atom Atom = EQ
  compare Atom App = LT
  compare Atom Open = LT
  compare App Atom = GT
  compare App App = EQ
  compare App Open = LT
  compare Open Atom = GT
  compare Open App = GT
  compare Open Open = EQ

export
prettyType : {ctx : SnocList String} -> Ty ctx -> TyPrec -> Doc ann
lessPrettyType : {ctx : SnocList String} -> Ty ctx -> TyPrec -> Doc ann
lessPrettyTypeCtx : {ctx : SnocList String} -> Context (Ty ctx) -> TyPrec -> SnocList (Doc ann)

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
      (neutral <++> concatWith (surround $ line' <+> "," <++> neutral) parts <+> line)
      (concatWith (surround $ "," <++> neutral) parts)
lessPrettyType (TSum (MkRow as _)) d =
  let parts = lessPrettyTypeCtx as Open <>> [] in
  group $ align $ enclose "[" "]" $
    flatAlt
      (neutral <++> concatWith (surround $ line' <+> "," <++> neutral) parts <+> line)
      (concatWith (surround $ "," <++> neutral) parts)
lessPrettyType (TFix x a) d =
  group $ align $ hang 2 $ parens $
    "\\" <+> pretty x <++> "=>" <+> line <+>
    prettyType a Open

lessPrettyTypeCtx [<] d = [<]
lessPrettyTypeCtx (as :< (x :- a)) d =
  lessPrettyTypeCtx as d :<
  (group $ align $ hang 2 $ pretty x <+> ":" <+> line <+> prettyType a d)
