module Inky.Term.Pretty

import Data.Singleton
import Data.String

import Inky.Term
import Inky.Type.Pretty

import Text.Bounded
import Text.PrettyPrint.Prettyprinter

export
prettyTerm :
  {tyCtx, tmCtx : SnocList String} ->
  Term m tyCtx tmCtx -> InkyPrec -> Doc ann
prettyAllTerm :
  {tyCtx, tmCtx : SnocList String} ->
  List (Term m tyCtx tmCtx) -> InkyPrec -> List (Doc ann)
prettyTermCtx :
  {tyCtx, tmCtx : SnocList String} ->
  Context (Term m tyCtx tmCtx) -> SnocList (Doc ann)
prettyCases :
  {tyCtx, tmCtx : SnocList String} ->
  Context (x ** Term m tyCtx (tmCtx :< x)) -> SnocList (Doc ann)
prettyLet :
  (eqLine : Doc ann) ->
  (doc : List String) ->
  (bound, body : Doc ann) ->
  Doc ann

prettyAllTerm [] d = []
prettyAllTerm (t :: ts) d = prettyTerm t d :: prettyAllTerm ts d

prettyTermCtx [<] = [<]
prettyTermCtx (ts :< (l :- Abs _ (bound ** t))) =
 prettyTermCtx ts :<
 (align $ group $
   pretty l <+> ":" <++>
     "\\" <+> concatWith (surround $ "," <++> neutral) (map pretty bound) <++> "=>" <+> line <+>
   prettyTerm t Open)
prettyTermCtx (ts :< (l :- t)) =
  prettyTermCtx ts :<
  (align $ group $ pretty l <+> ":" <+> line <+> prettyTerm t Open)

prettyCases [<] = [<]
prettyCases (ts :< (l :- (x ** Abs _ (bound ** t)))) =
  prettyCases ts :<
  (align $ group $
    pretty l <++> pretty x <++> "=>" <++>
      "\\" <+> concatWith (surround $ "," <++> neutral) (map pretty bound) <++> "=>" <+> line <+>
    prettyTerm t Open)
prettyCases (ts :< (l :- (x ** t))) =
  prettyCases ts :<
  (align $ group $
    pretty l <++> pretty x <++> "=>" <+> line <+>
    prettyTerm t Open)

prettyLet eqLine doc bound body =
  align $ group $
    (nest 2
      (group (pretty "let" <++> eqLine) <+> line <+>
        concatMap (enclose "--" hardline . pretty) doc <+>
        bound) <+> line <+>
    "in") <+> line <+>
    group body

prettyTerm (Annot _ t a) d =
  align $ group $ parenthesise (d < Annot) $
    prettyTerm t App <+> line <+>
    ":" <++> prettyType a Open
prettyTerm (Var _ i) d = pretty (unVal $ nameOf i)
prettyTerm (Let meta (Annot _ (Abs _ (bound ** e)) a) (x ** t)) d =
  let (binds, cod, rest) = groupBinds bound a in
  let binds = map (\x => parens (pretty x.name <++> ":" <++> prettyType x.value Open)) binds in
  align $ group $ parenthesise (d < Open) $
  prettyLet
   (hang 2 $ group $ flatAlt
        ( pretty x <+> line <+>
          concatWith (surround line) binds <+> line <+>
          ":" <++> prettyType cod Open <++> "=" <+>
          if null rest then neutral
          else line <+> "\\" <+> concatWith (surround $ "," <++> neutral) (map pretty rest) <++> "=>"
        )
        ( pretty x <++> concatWith (<++>) binds <++> ":" <++> prettyType cod Open <++> "=" <+>
          if null rest then neutral
          else neutral <++> "\\" <+> concatWith (surround $ "," <++> neutral) (map pretty rest) <++> "=>"
        ))
   meta.doc
   (prettyTerm e Open)
   (prettyTerm t Open)
  where
  groupBinds : List String -> Ty tyCtx -> (List (Assoc $ Ty tyCtx), Ty tyCtx, List String)
  groupBinds [] a = ([], a, [])
  groupBinds (x :: xs) (TArrow a b) =
    let (binds, cod, rest) = groupBinds xs b in
    ((x :- a) :: binds, cod, rest)
  groupBinds xs a = ([], a, xs)
prettyTerm (Let meta (Annot _ e a) (x ** t)) d =
  align $ group $ parenthesise (d < Open) $
  prettyLet
    (pretty x <+> line <+> ":" <++> prettyType a Open <++> "=")
    meta.doc
    (prettyTerm e Open)
    (prettyTerm t Open)
prettyTerm (Let meta e (x ** t)) d =
  align $ group $ parenthesise (d < Open) $
  prettyLet
    (pretty x <++> "=")
    meta.doc
    (prettyTerm e Open)
    (prettyTerm t Open)
prettyTerm (LetTy meta a (x ** t)) d =
  align $ group $ parenthesise (d < Open) $
  prettyLet
    (pretty x <++> "=")
    meta.doc
    (prettyType a Open)
    (prettyTerm t Open)
prettyTerm (Abs _ (bound ** t)) d =
  hang 2 $ group $ parenthesise (d < Open) $
    "\\" <+> concatWith (surround $ "," <++> neutral) (map pretty bound) <++> "=>" <+> line <+>
    prettyTerm t Open
prettyTerm (App _ (Map _ a b c) ts) d =
  align $ hang 2 $ group $ parenthesise (d < App) $
    concatWith (surround line)
      (  pretty "map"
      :: prettyBoundType a Suffix
      :: prettyType b Suffix
      :: prettyType c Suffix
      :: prettyAllTerm ts Suffix)
prettyTerm (App _ f ts) d =
  align $ hang 2 $ group $ parenthesise (d < App) $
    concatWith (surround line) (prettyTerm f App :: prettyAllTerm ts Suffix)
prettyTerm (Tup _ (MkRow ts _)) d =
  let parts = prettyTermCtx ts <>> [] in
  align $ group $ enclose "<" ">" $
    flatAlt
      (neutral <++> concatWith (surround $ line' <+> ";" <++> neutral) parts <+> line)
      (concatWith (surround $ ";" <++> neutral) parts)
prettyTerm (Prj _ e l) d =
  align $ hang 2 $ group $ parenthesise (d < Suffix) $
    prettyTerm e Suffix <+> line' <+> "." <+> pretty l
prettyTerm (Inj _ l t) d =
  align $ hang 2 $ group $ parenthesise (d < App) $
    pretty l <+> line <+> prettyTerm t Suffix
prettyTerm (Case _ e (MkRow ts _)) d =
  let parts = prettyCases ts <>> [] in
  align $ hang 2 $ group $ parenthesise (d < Open) $
    (group $ "match" <++> prettyTerm e Open <++> "with") <+> line <+>
    (braces $ flatAlt
      (neutral <++> concatWith (surround $ line' <+> ";" <++> neutral) parts <+> line)
      (concatWith (surround $ ";" <++> neutral) parts))
prettyTerm (Roll _ t) d =
  parenthesise (d < Prefix) $ align $ pretty "~" <+> prettyTerm t Prefix
prettyTerm (Unroll _ e) d =
  parenthesise (d < Prefix) $ align $ pretty "!" <+> prettyTerm e Prefix
prettyTerm (Fold _ e (x ** t)) d =
  align $ hang 2 $ group $ parenthesise (d < Open) $
    (hang (-2) $ group $ "rec" <++> prettyTerm e Open <++> "with") <+> line <+>
    (align $ hang 2 $ group $ parens $
      "\\" <+> pretty x <++> "=>" <+> line <+> prettyTerm t Open)
prettyTerm (Map _ a b c) d =
  align $ hang 2 $ group $ parenthesise (d < App) $
    concatWith (surround line)
      [ pretty "map"
      , prettyBoundType a Suffix
      , prettyType b Suffix
      , prettyType c Suffix
      ]
prettyTerm (FoldCase _ e (MkRow ts _)) d =
  let parts = prettyCases ts <>> [] in
  align $ hang 2 $ group $ parenthesise (d < Open) $
    (group $ "matchrec" <++> prettyTerm e Open <++> "with") <+> line <+>
    (braces $ flatAlt
      (neutral <++> concatWith (surround $ line' <+> ";" <++> neutral) parts <+> line)
      (concatWith (surround $ ";" <++> neutral) parts))
