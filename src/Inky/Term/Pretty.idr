module Inky.Term.Pretty

import Data.Singleton

import Inky.Decidable.Maybe
import Inky.Term
import Inky.Type.Pretty
import Text.PrettyPrint.Prettyprinter

appPrec, prjPrec, unrollPrec, annotPrec,
  letPrec, absPrec, injPrec, tupPrec, casePrec, rollPrec, foldPrec : Prec
appPrec = App
prjPrec = User 9
unrollPrec = PrefixMinus
annotPrec = Equal
letPrec = Open
absPrec = Open
injPrec = App
tupPrec = Open
casePrec = Open
rollPrec = PrefixMinus
foldPrec = Open

export
prettyTerm : {tyCtx, tmCtx : SnocList String} -> Term tyCtx tmCtx -> Prec -> Doc ann
prettyAllTerm : {tyCtx, tmCtx : SnocList String} -> List (Term tyCtx tmCtx) -> Prec -> List (Doc ann)
prettyTermCtx : {tyCtx, tmCtx : SnocList String} -> Context (Term tyCtx tmCtx) -> Prec -> SnocList (Doc ann)
prettyCases : {tyCtx, tmCtx : SnocList String} -> Context (x ** Term tyCtx (tmCtx :< x)) -> SnocList (Doc ann)
lessPrettyTerm : {tyCtx, tmCtx : SnocList String} -> Term tyCtx tmCtx -> Prec -> Doc ann

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
prettyCases (ts :< (l :- (x ** t))) =
  prettyCases ts :< (pretty l <++> pretty x <++> "=>" <++> prettyTerm t Open)


lessPrettyTerm (Annot t a) d =
  parenthesise (d > annotPrec) $ group $ align $ hang 2 $
    prettyTerm t annotPrec <++> ":" <+> line <+> prettyType a annotPrec
lessPrettyTerm (Var i) d = pretty (unVal $ nameOf i)
lessPrettyTerm (Let e (x ** t)) d =
  parenthesise (d > letPrec) $ group $ align $
    (group $ align $ hang 2 $
      pretty x <++> "=" <+> line <+> prettyTerm e letPrec
    ) <+> line <+>
    "in" <+> line <+>
    prettyTerm t letPrec
lessPrettyTerm (LetTy a (x ** t)) d =
  parenthesise (d > letPrec) $ group $ align $
    (group $ align $ hang 2 $
      pretty x <++> "=" <+> line <+> prettyType a letPrec
    ) <+> line <+>
    "in" <+> line <+>
    prettyTerm t letPrec
lessPrettyTerm (Abs (bound ** t)) d =
  parenthesise (d > absPrec) $ group $ hang 2 $
    "\\" <+> concatWith (surround $ "," <+> line) (map pretty bound) <++> "=>" <+> line <+>
    prettyTerm t absPrec
lessPrettyTerm (App (Map (x ** a) b c) ts) d =
  parenthesise (d >= appPrec) $ group $ align $ hang 2 $
    concatWith (surround line)
      (  pretty "map"
      :: parens (group $ align $ hang 2 $ "\\" <+> pretty x <+> "=>" <+> line <+> prettyType a Open)
      :: prettyType b appPrec
      :: prettyType c appPrec
      :: prettyAllTerm ts appPrec)
lessPrettyTerm (App (GetChildren (x ** a) b) ts) d =
  parenthesise (d >= appPrec) $ group $ align $ hang 2 $
    concatWith (surround line)
      (  pretty "getChildren"
      :: parens (group $ align $ hang 2 $ "\\" <+> pretty x <+> "=>" <+> line <+> prettyType a Open)
      :: prettyType b appPrec
      :: prettyAllTerm ts appPrec)
lessPrettyTerm (App f ts) d =
  parenthesise (d >= appPrec) $ group $ align $ hang 2 $
    concatWith (surround line) (prettyTerm f appPrec :: prettyAllTerm ts appPrec)
lessPrettyTerm (Tup (MkRow ts _)) d =
  enclose "<" ">" $ group $ align $ hang 2 $
    concatWith (surround $ "<" <+> line) (prettyTermCtx ts tupPrec <>> [])
lessPrettyTerm (Prj e l) d =
  parenthesise (d > prjPrec) $ group $ align $ hang 2 $
    prettyTerm e prjPrec <+> line' <+> "." <+> pretty l
lessPrettyTerm (Inj l t) d =
  parenthesise (d >= injPrec) $ group $ align $ hang 2 $
    pretty l <+> line <+> prettyTerm t absPrec
lessPrettyTerm (Case e (MkRow ts _)) d =
  parenthesise (d > casePrec) $ group $ align $ hang 2 $
    "case" <++> prettyTerm e casePrec <++> "of" <+> hardline <+>
    (braces $ group $ align $ hang 2 $
      concatWith (surround $ ";" <+> hardline) $
      prettyCases ts <>> [])
lessPrettyTerm (Roll t) d =
  pretty "~" <+>
  (parenthesise (d > rollPrec) $ group $ align $ hang 2 $ prettyTerm t rollPrec)
lessPrettyTerm (Unroll e) d =
  pretty "!" <+>
  (parenthesise (d > unrollPrec) $ group $ align $ hang 2 $ prettyTerm e unrollPrec)
lessPrettyTerm (Fold e (x ** t)) d =
  parenthesise (d > foldPrec) $ group $ align $ hang 2 $
    "fold" <++> prettyTerm e foldPrec <++> "by" <+> hardline <+>
    (parens $ group $ align $ hang 2 $
      "\\" <+> pretty x <++> "=>" <+> line <+> prettyTerm t Open)
lessPrettyTerm (Map (x ** a) b c) d =
  parenthesise (d >= appPrec) $ group $ align $ hang 2 $
    concatWith (surround line)
      [ pretty "map"
      , parens (group $ align $ hang 2 $ "\\" <+> pretty x <+> "=>" <+> line <+> prettyType a Open)
      , prettyType b appPrec
      , prettyType c appPrec
      ]
lessPrettyTerm (GetChildren (x ** a) b) d =
  parenthesise (d >= appPrec) $ group $ align $ hang 2 $
    concatWith (surround line)
      [ pretty "getChildren"
      , parens (group $ align $ hang 2 $ "\\" <+> pretty x <+> "=>" <+> line <+> prettyType a Open)
      , prettyType b appPrec
      ]
