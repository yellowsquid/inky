module Inky.Term.Pretty

import Data.Singleton
import Data.String

import Inky.Decidable.Maybe
import Inky.Term
import Inky.Type.Pretty
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
prettyTerm : {tyCtx, tmCtx : SnocList String} -> Term tyCtx tmCtx -> TermPrec -> Doc ann
prettyAllTerm : {tyCtx, tmCtx : SnocList String} -> List (Term tyCtx tmCtx) -> TermPrec -> List (Doc ann)
prettyTermCtx : {tyCtx, tmCtx : SnocList String} -> Context (Term tyCtx tmCtx) -> TermPrec -> SnocList (Doc ann)
prettyCases : {tyCtx, tmCtx : SnocList String} -> Context (x ** Term tyCtx (tmCtx :< x)) -> SnocList (Doc ann)
prettyLet : Doc ann -> Doc ann -> Doc ann
lessPrettyTerm : {tyCtx, tmCtx : SnocList String} -> Term tyCtx tmCtx -> TermPrec -> Doc ann

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
prettyCases (ts :< (l :- (x ** Abs (bound ** t)))) =
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

lessPrettyTerm (Annot t a) d =
  group $ align $ hang 2 $ parenthesise (d < Annot) $
    prettyTerm t App <++> ":" <+> line <+> prettyType a Open
lessPrettyTerm (Var i) d = pretty (unVal $ nameOf i)
lessPrettyTerm (Let e (x ** t)) d =
  -- TODO: pretty print annotated abstraction
  group $ align $ parenthesise (d < Open) $
  prettyLet
    (pretty x <++> "=" <+> line <+> prettyTerm e Open)
    (prettyTerm t Open)
lessPrettyTerm (LetTy a (x ** t)) d =
  group $ align $ parenthesise (d < Open) $
  prettyLet
    (pretty x <++> "=" <+> line <+> prettyType a Open)
    (prettyTerm t Open)
lessPrettyTerm (Abs (bound ** t)) d =
  group $ hang 2 $ parenthesise (d < Open) $
    "\\" <+> concatWith (surround $ "," <+> line) (map pretty bound) <++> "=>" <+> line <+>
    prettyTerm t Open
lessPrettyTerm (App (Map (x ** a) b c) ts) d =
  group $ align $ hang 2 $ parenthesise (d < App) $
    concatWith (surround line)
      (  pretty "map"
      :: parens (group $ align $ hang 2 $ "\\" <+> pretty x <++> "=>" <+> line <+> prettyType a Open)
      :: prettyType b Atom
      :: prettyType c Atom
      :: prettyAllTerm ts Suffix)
lessPrettyTerm (App (GetChildren (x ** a) b) ts) d =
  group $ align $ hang 2 $ parenthesise (d < App) $
    concatWith (surround line)
      (  pretty "getChildren"
      :: parens (group $ align $ hang 2 $ "\\" <+> pretty x <++> "=>" <+> line <+> prettyType a Open)
      :: prettyType b Atom
      :: prettyAllTerm ts Suffix)
lessPrettyTerm (App f ts) d =
  group $ align $ hang 2 $ parenthesise (d < App) $
    concatWith (surround line) (prettyTerm f Suffix :: prettyAllTerm ts Suffix)
lessPrettyTerm (Tup (MkRow ts _)) d =
  let parts = prettyTermCtx ts Open <>> [] in
  group $ align $ enclose "<" ">" $
    flatAlt
      (neutral <++> concatWith (surround $ line' <+> "," <++> neutral) parts <+> line)
      (concatWith (surround $ "," <++> neutral) parts)
lessPrettyTerm (Prj e l) d =
  group $ align $ hang 2 $ parenthesise (d < Suffix) $
    prettyTerm e Suffix <+> line' <+> "." <+> pretty l
lessPrettyTerm (Inj l t) d =
  group $ align $ hang 2 $ parenthesise (d < App) $
    pretty l <+> line <+> prettyTerm t Suffix
lessPrettyTerm (Case e (MkRow ts _)) d =
  let parts = prettyCases ts <>> [] in
  group $ align $ hang 2 $ parenthesise (d < Open) $
    (group $ hang (-2) $ "case" <++> prettyTerm e Open <+> line <+> "of") <+> line <+>
    (braces $
      flatAlt
        (neutral <++> concatWith (surround $ line' <+> ";" <++> neutral) parts <+> line)
        (concatWith (surround $ ";" <++> neutral) parts))
lessPrettyTerm (Roll t) d =
  pretty "~" <+>
  parenthesise (d < Prefix) (group $ align $ hang 2 $ prettyTerm t Prefix)
lessPrettyTerm (Unroll e) d =
  pretty "!" <+>
  parenthesise (d > Prefix) (group $ align $ hang 2 $ prettyTerm e Prefix)
lessPrettyTerm (Fold e (x ** t)) d =
  -- TODO: foldcase
  group $ align $ hang 2 $ parenthesise (d < Open) $
    "fold" <++> prettyTerm e Open <++> "by" <+> hardline <+>
    (group $ align $ hang 2 $ parens $
      "\\" <+> pretty x <++> "=>" <+> line <+> prettyTerm t Open)
lessPrettyTerm (Map (x ** a) b c) d =
  group $ align $ hang 2 $ parenthesise (d < App) $
    concatWith (surround line)
      [ pretty "map"
      , group (align $ hang 2 $ parens $  "\\" <+> pretty x <++> "=>" <+> line <+> prettyType a Open)
      , prettyType b Atom
      , prettyType c Atom
      ]
lessPrettyTerm (GetChildren (x ** a) b) d =
  group $ align $ hang 2 $ parenthesise (d < App) $
    concatWith (surround line)
      [ pretty "getChildren"
      , group (align $ hang 2 $ parens $  "\\" <+> pretty x <++> "=>" <+> line <+> prettyType a Open)
      , prettyType b Atom
      ]
