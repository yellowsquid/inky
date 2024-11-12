module Inky.Term.Pretty

import Data.Singleton
import Data.String

import Inky.Term
import Inky.Type.Pretty

import Text.Bounded
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
prettyTerm : {tyCtx, tmCtx : SnocList String} -> Term mode m tyCtx tmCtx -> TermPrec -> Doc ann
prettyAllTerm : {tyCtx, tmCtx : SnocList String} -> List (Term mode m tyCtx tmCtx) -> TermPrec -> List (Doc ann)
prettyTermCtx : {tyCtx, tmCtx : SnocList String} -> Context (Term mode m tyCtx tmCtx) -> TermPrec -> SnocList (Doc ann)
prettyCases : {tyCtx, tmCtx : SnocList String} -> Context (x ** Term mode m tyCtx (tmCtx :< x)) -> SnocList (Doc ann)
prettyLet : Doc ann -> Doc ann -> Doc ann
lessPrettyTerm : {tyCtx, tmCtx : SnocList String} -> Term mode m tyCtx tmCtx -> TermPrec -> Doc ann

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
prettyTermCtx (ts :< (l :- t)) d =
  prettyTermCtx ts d :<
  (group $ hang 2 $ pretty l <+> ":" <+> line <+> prettyTerm t d)

prettyCases [<] = [<]
prettyCases (ts :< (l :- (x ** Abs _ (bound ** t)))) =
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

lessPrettyTerm (Annot _ t a) d =
  group $ align $ parenthesise (d < Annot) $
    prettyTerm t App <+> line <+>
    ":" <++> prettyType a Open
lessPrettyTerm (Var _ i) d = pretty (unVal $ nameOf i)
lessPrettyTerm (Let _ (Annot _ (Abs _ (bound ** e)) a) (x ** t)) d =
  let (binds, cod, rest) = groupBinds bound a in
  let binds = map (\x => parens (pretty x.name <++> ":" <++> prettyType x.value Open)) binds in
  group $ align $ parenthesise (d < Open) $
  prettyLet
    ( (group $ hang 2 $ flatAlt
        ( pretty x <+> line <+>
          concatWith (surround line) binds <+> line <+>
          ":" <++> prettyType cod Open
        )
        (pretty x <++> concatWith (<++>) binds <++> ":" <++> prettyType cod Open)
      ) <++> "=" <+>
      ( if null rest
        then neutral
        else neutral <++> "\\" <+> concatWith (surround $ "," <++> neutral) (map pretty rest) <++> "=>")
      <+> line <+> prettyTerm e Open
    )
    (prettyTerm t Open)
  where
  groupBinds : List String -> Ty tyCtx -> (List (Assoc $ Ty tyCtx), Ty tyCtx, List String)
  groupBinds [] a = ([], a, [])
  groupBinds (x :: xs) (TArrow a b) =
    let (binds, cod, rest) = groupBinds xs b in
    ((x :- a) :: binds, cod, rest)
  groupBinds xs a = ([], a, xs)
lessPrettyTerm (Let _ (Annot _ e a) (x ** t)) d =
  group $ align $ parenthesise (d < Open) $
  prettyLet
    ( pretty x <++> ":" <++> prettyType a Open <++> "=" <+> line <+>
      prettyTerm e Open
    )
    (prettyTerm t Open)
lessPrettyTerm (Let _ e (x ** t)) d =
  group $ align $ parenthesise (d < Open) $
  prettyLet
    (pretty x <++> "=" <+> line <+> prettyTerm e Open)
    (prettyTerm t Open)
lessPrettyTerm (LetTy _ a (x ** t)) d =
  group $ align $ parenthesise (d < Open) $
  prettyLet
    (pretty x <++> "=" <+> line <+> prettyType a Open)
    (prettyTerm t Open)
lessPrettyTerm (Abs _ (bound ** t)) d =
  group $ hang 2 $ parenthesise (d < Open) $
    "\\" <+> concatWith (surround $ "," <++> neutral) (map pretty bound) <++> "=>" <+> line <+>
    prettyTerm t Open
lessPrettyTerm (App _ (Map _ (x ** a) b c) ts) d =
  group $ align $ hang 2 $ parenthesise (d < App) $
    concatWith (surround line)
      (  pretty "map"
      :: parens (group $ align $ hang 2 $ "\\" <+> pretty x <++> "=>" <+> line <+> prettyType a Open)
      :: prettyType b Atom
      :: prettyType c Atom
      :: prettyAllTerm ts Suffix)
lessPrettyTerm (App _ f ts) d =
  group $ align $ hang 2 $ parenthesise (d < App) $
    concatWith (surround line) (prettyTerm f Suffix :: prettyAllTerm ts Suffix)
lessPrettyTerm (Tup _ (MkRow ts _)) d =
  let parts = prettyTermCtx ts Open <>> [] in
  group $ align $ enclose "<" ">" $
    flatAlt
      (neutral <++> concatWith (surround $ line' <+> "," <++> neutral) parts <+> line)
      (concatWith (surround $ "," <++> neutral) parts)
lessPrettyTerm (Prj _ e l) d =
  group $ align $ hang 2 $ parenthesise (d < Suffix) $
    prettyTerm e Suffix <+> line' <+> "." <+> pretty l
lessPrettyTerm (Inj _ l t) d =
  group $ align $ hang 2 $ parenthesise (d < App) $
    pretty l <+> line <+> prettyTerm t Suffix
lessPrettyTerm (Case _ e (MkRow ts _)) d =
  let parts = prettyCases ts <>> [] in
  group $ align $ hang 2 $ parenthesise (d < Open) $
    (group $ hang (-2) $ "case" <++> prettyTerm e Open <+> line <+> "of") <+> line <+>
    (braces $ flatAlt
      (neutral <++> concatWith (surround $ line' <+> ";" <++> neutral) parts <+> line)
      (concatWith (surround $ ";" <++> neutral) parts))
lessPrettyTerm (Roll _ t) d =
  pretty "~" <+>
  parenthesise (d < Prefix) (group $ align $ hang 2 $ prettyTerm t Prefix)
lessPrettyTerm (Unroll _ e) d =
  pretty "!" <+>
  parenthesise (d < Prefix) (group $ align $ hang 2 $ prettyTerm e Prefix)
lessPrettyTerm (Fold _ e ("__tmp" ** Case _ (Var _ ((%%) "__tmp" {pos = Here})) (MkRow ts _))) d =
  let parts = prettyCases ts <>> [] in
  -- XXX: should check for usage of "__tmp" in ts
  group $ align $ hang 2 $ parenthesise (d < Open) $
    (group $ hang (-2) $ "foldcase" <++> prettyTerm e Open <+> line <+> "by") <+> line <+>
    (braces $ flatAlt
      (neutral <++> concatWith (surround $ line' <+> ";" <++> neutral) parts <+> line)
      (concatWith (surround $ ";" <++> neutral) parts))
lessPrettyTerm (Fold _ e (x ** t)) d =
  group $ align $ hang 2 $ parenthesise (d < Open) $
    (group $ hang (-2) $ "fold" <++> prettyTerm e Open <++> "by") <+> line <+>
    (group $ align $ hang 2 $ parens $
      "\\" <+> pretty x <++> "=>" <+> line <+> prettyTerm t Open)
lessPrettyTerm (Map _ (x ** a) b c) d =
  group $ align $ hang 2 $ parenthesise (d < App) $
    concatWith (surround line)
      [ pretty "map"
      , group (align $ hang 2 $ parens $  "\\" <+> pretty x <++> "=>" <+> line <+> prettyType a Open)
      , prettyType b Atom
      , prettyType c Atom
      ]
