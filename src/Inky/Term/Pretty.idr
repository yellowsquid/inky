module Inky.Term.Pretty

import Data.Singleton
import Data.String

import Inky.Term
import Inky.Type.Pretty

import Text.Bounded
import Text.PrettyPrint.Prettyprinter

export
prettyTerm :
  {mode : Mode} -> {tyCtx, tmCtx : SnocList String} ->
  Term mode m tyCtx tmCtx -> InkyPrec -> Doc ann
prettyAllTerm :
  {mode : Mode} -> {tyCtx, tmCtx : SnocList String} ->
  List (Term mode m tyCtx tmCtx) -> InkyPrec -> List (Doc ann)
prettyTermCtx :
  {mode : Mode} -> {tyCtx, tmCtx : SnocList String} ->
  Context (Term mode m tyCtx tmCtx) -> SnocList (Doc ann)
prettyCases :
  {mode : Mode} -> {tyCtx, tmCtx : SnocList String} ->
  Context (x ** Term mode m tyCtx (tmCtx :< x)) -> SnocList (Doc ann)
prettyLet :
  (eqLine : Doc ann) ->
  (doc : List String) ->
  (bound, body : Doc ann) ->
  Doc ann
prettyType' :
  (mode : Mode) -> {tyCtx, tmCtx : SnocList String} ->
  Ty' mode m tyCtx tmCtx -> InkyPrec -> Doc ann
prettyBoundType' :
  (mode : Mode) -> {tyCtx, tmCtx : SnocList String} ->
  BoundTy' mode m tyCtx tmCtx -> InkyPrec -> Doc ann

prettyAllTerm [] d = []
prettyAllTerm (t :: ts) d = prettyTerm t d :: prettyAllTerm ts d

prettyTermCtx [<] = [<]
prettyTermCtx (ts :< (l :- Abs _ (bound ** t))) =
 prettyTermCtx ts :<
 (group $ align $
   pretty l <+> ":" <++>
     "\\" <+> concatWith (surround $ "," <++> neutral) (map pretty bound) <++> "=>" <+> line <+>
   prettyTerm t Open)
prettyTermCtx (ts :< (l :- QAbs _ (bound ** t))) =
 prettyTermCtx ts :<
 (group $ align $
   pretty l <+> ":" <++>
     "\\" <+> concatWith (surround $ "," <++> neutral) (map pretty bound) <++> "~>" <+> line <+>
   prettyTerm t Open)
prettyTermCtx (ts :< (l :- t)) =
  prettyTermCtx ts :<
  (group $ align $ pretty l <+> ":" <+> line <+> prettyTerm t Open)

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

prettyLet eqLine [] bound body =
  group $ align $
    (group $
      hang 2
        (group (pretty "let" <++> eqLine) <+> line <+>
         group bound) <+> line <+>
      "in") <+> line <+>
    group body
prettyLet eqLine doc bound body  =
  align $
    (hang 2 $
      group (pretty "let" <++> eqLine) <+> hardline <+>
      concatMap (enclose "--" hardline . pretty) doc <+>
      group bound) <+> hardline <+>
    "in" <+> line <+>
    group body

prettyType' (Quote tyCtx tmCtx) a d = parenthesise (d < Prefix) $ align $ "," <+> prettyTerm a Prefix
prettyType' (Sugar qtCtx) a d = prettyType a d
prettyType' NoSugar a d = prettyType a d

prettyBoundType' (Quote tyCtx tmCtx) a d = parenthesise (d < Prefix) $ align $ "," <+> prettyTerm a Prefix
prettyBoundType' (Sugar qtCtx) (x ** a) d =
  parens $ group $ align $ hang 2 $ "\\" <+> pretty x <++> "=>" <+> line <+> prettyType a Open
prettyBoundType' NoSugar (x ** a) d =
  parens $ group $ align $ hang 2 $ "\\" <+> pretty x <++> "=>" <+> line <+> prettyType a Open

prettyTerm (Annot _ t a) d =
  group $ align $ parenthesise (d < Annot) $
    prettyTerm t App <+> line <+>
    ":" <++> prettyType' mode a Open
prettyTerm (Var _ i) d = pretty (unVal $ nameOf i)
prettyTerm {mode = Sugar _} (Let meta (Annot _ (Abs _ (bound ** e)) a) (x ** t)) d =
  let (binds, cod, rest) = groupBinds bound a in
  let binds = map (\x => parens (pretty x.name <++> ":" <++> prettyType x.value Open)) binds in
  -- NOTE: group breaks comments
  align $ parenthesise (d < Open) $
  prettyLet
   (group $ hang 2 $ flatAlt
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
  -- NOTE: group breaks comments
  align $ parenthesise (d < Open) $
  prettyLet
    (pretty x <+> line <+> ":" <++> prettyType' mode a Open <++> "=")
    meta.doc
    (prettyTerm e Open)
    (prettyTerm t Open)
prettyTerm (Let meta e (x ** t)) d =
  -- NOTE: group breaks comments
  align $ parenthesise (d < Open) $
  prettyLet
    (pretty x <++> "=")
    meta.doc
    (prettyTerm e Open)
    (prettyTerm t Open)
prettyTerm (LetTy meta a (x ** t)) d =
  -- NOTE: group breaks comments
  align $ parenthesise (d < Open) $
  prettyLet
    (pretty x <++> "=")
    meta.doc
    (prettyType a Open)
    (prettyTerm t Open)
prettyTerm (Abs _ (bound ** t)) d =
  group $ hang 2 $ parenthesise (d < Open) $
    "\\" <+> concatWith (surround $ "," <++> neutral) (map pretty bound) <++> "=>" <+> line <+>
    prettyTerm t Open
prettyTerm (App _ (Map _ a b c) ts) d =
  group $ align $ hang 2 $ parenthesise (d < App) $
    concatWith (surround line)
      (  pretty "map"
      :: prettyBoundType' mode a Suffix
      :: prettyType' mode b Suffix
      :: prettyType' mode c Suffix
      :: prettyAllTerm ts Suffix)
prettyTerm (App _ f ts) d =
  group $ align $ hang 2 $ parenthesise (d < App) $
    concatWith (surround line) (prettyTerm f App :: prettyAllTerm ts Suffix)
prettyTerm (Tup _ (MkRow ts _)) d =
  let parts = prettyTermCtx ts <>> [] in
  group $ align $ enclose "<" ">" $
    flatAlt
      (neutral <++> concatWith (surround $ line' <+> ";" <++> neutral) parts <+> line)
      (concatWith (surround $ ";" <++> neutral) parts)
prettyTerm (Prj _ e l) d =
  group $ align $ hang 2 $ parenthesise (d < Suffix) $
    prettyTerm e Suffix <+> line' <+> "." <+> pretty l
prettyTerm (Inj _ l t) d =
  group $ align $ hang 2 $ parenthesise (d < App) $
    pretty l <+> line <+> prettyTerm t Suffix
prettyTerm (Case _ e (MkRow ts _)) d =
  let parts = prettyCases ts <>> [] in
  group $ align $ hang 2 $ parenthesise (d < Open) $
    (group $ "case" <++> prettyTerm e Open <++> "of") <+> line <+>
    (braces $ flatAlt
      (neutral <++> concatWith (surround $ line' <+> ";" <++> neutral) parts <+> line)
      (concatWith (surround $ ";" <++> neutral) parts))
prettyTerm (Roll _ t) d =
  parenthesise (d < Prefix) $ align $ pretty "~" <+> prettyTerm t Prefix
prettyTerm (Unroll _ e) d =
  parenthesise (d < Prefix) $ align $ pretty "!" <+> prettyTerm e Prefix
prettyTerm (Fold _ e (x ** t)) d =
  group $ align $ hang 2 $ parenthesise (d < Open) $
    (group $ hang (-2) $ "fold" <++> prettyTerm e Open <++> "by") <+> line <+>
    (group $ align $ hang 2 $ parens $
      "\\" <+> pretty x <++> "=>" <+> line <+> prettyTerm t Open)
prettyTerm (Map _ a b c) d =
  group $ align $ hang 2 $ parenthesise (d < App) $
    concatWith (surround line)
      [ pretty "map"
      , prettyBoundType' mode a Suffix
      , prettyType' mode  b Suffix
      , prettyType' mode  c Suffix
      ]
prettyTerm (QuasiQuote _ t) d =
  parenthesise (d < Prefix) $ align $ pretty "`" <+> prettyTerm t Prefix
prettyTerm (Unquote _ t) d =
  parenthesise (d < Prefix) $ align $ pretty "," <+> prettyTerm t Prefix
prettyTerm (QAbs _ (bound ** t)) d =
  group $ hang 2 $ parenthesise (d < Open) $
    "\\" <+> concatWith (surround $ "," <++> neutral) (map pretty bound) <++> "~>" <+> line <+>
    prettyTerm t Open
prettyTerm (Lit _ k) d = pretty k
prettyTerm (Suc _ t) d =
  group $ align $ hang 2 $ parenthesise (d < App) $
    concatWith (surround line) [pretty "suc", prettyTerm t Suffix]
prettyTerm (List _ ts) d =
  let parts = prettyAllTerm ts Open in
  group $ align $ enclose "[" "]" $
    flatAlt
      (neutral <++> concatWith (surround $ line' <+> ";" <++> neutral) parts <+> line)
      (concatWith (surround $ ";" <++> neutral) parts)
prettyTerm (Cons _ t u) d =
  group $ align $ hang 2 $ parenthesise (d < App) $
    concatWith (surround line) [pretty "cons", prettyTerm t Suffix, prettyTerm u Suffix]
prettyTerm (Str _ str) d = enclose "\"" "\"" $ pretty str
prettyTerm (FoldCase _ e (MkRow ts _)) d =
  let parts = prettyCases ts <>> [] in
  group $ align $ hang 2 $ parenthesise (d < Open) $
    (group $ "foldcase" <++> prettyTerm e Open <++> "by") <+> line <+>
    (braces $ flatAlt
      (neutral <++> concatWith (surround $ line' <+> ";" <++> neutral) parts <+> line)
      (concatWith (surround $ ";" <++> neutral) parts))
