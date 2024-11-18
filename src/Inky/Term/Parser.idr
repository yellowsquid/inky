module Inky.Term.Parser

import public Inky.Data.Fun

import Data.Either
import Data.Nat
import Data.List1
import Data.String
import Data.String.Extra

import Flap.Data.Context
import Flap.Data.Context.Var
import Flap.Data.SnocList.Var
import Flap.Data.SnocList.Thinning
import Flap.Decidable
import Flap.Decidable.Maybe
import Flap.Parser

import Inky.Data.Row
import Inky.Term
import Inky.Type

import Text.Lexer

-- Lexer -----------------------------------------------------------------------

export
data InkyKind
  = TermIdent
  | TypeIdent
  | Lit
  | Let
  | In
  | Case
  | Of
  | FoldCase
  | Fold
  | By
  | Nat
  | List
  | Suc
  | Map
  | ParenOpen
  | ParenClose
  | BracketOpen
  | BracketClose
  | AngleOpen
  | AngleClose
  | BraceOpen
  | BraceClose
  | Arrow
  | DoubleArrow
  | Bang
  | Tilde
  | Dot
  | Backslash
  | Colon
  | Semicolon
  | Equal
  | Comma
  | Ignore
  | Comment

export
[EqI] Eq InkyKind where
  TermIdent == TermIdent = True
  TypeIdent == TypeIdent = True
  Lit == Lit = True
  Let == Let = True
  In == In = True
  Case == Case = True
  Of == Of = True
  FoldCase == FoldCase = True
  Fold == Fold = True
  By == By = True
  Nat == Nat = True
  List == List = True
  Suc == Suc = True
  Map == Map = True
  ParenOpen == ParenOpen = True
  ParenClose == ParenClose = True
  BracketOpen == BracketOpen = True
  BracketClose == BracketClose = True
  AngleOpen == AngleOpen = True
  AngleClose == AngleClose = True
  BraceOpen == BraceOpen = True
  BraceClose == BraceClose = True
  Arrow == Arrow = True
  DoubleArrow == DoubleArrow = True
  Bang == Bang = True
  Tilde == Tilde = True
  Dot == Dot = True
  Backslash == Backslash = True
  Colon == Colon = True
  Semicolon == Semicolon = True
  Equal == Equal = True
  Comma == Comma = True
  Ignore == Ignore = True
  Comment == Comment = True
  _ == _ = False

export
Interpolation InkyKind where
  interpolate TermIdent = "term name"
  interpolate TypeIdent = "type name"
  interpolate Lit = "number"
  interpolate Let = "'let'"
  interpolate In = "'in'"
  interpolate Case = "'case'"
  interpolate Of = "'of'"
  interpolate FoldCase = "'foldcase'"
  interpolate Fold = "'fold'"
  interpolate By = "'by'"
  interpolate Nat = "'Nat'"
  interpolate List = "'List'"
  interpolate Suc = "'suc'"
  interpolate Map = "'map'"
  interpolate ParenOpen = "'('"
  interpolate ParenClose = "')'"
  interpolate BracketOpen = "'['"
  interpolate BracketClose = "']'"
  interpolate AngleOpen = "'<'"
  interpolate AngleClose = "'>'"
  interpolate BraceOpen = "'{'"
  interpolate BraceClose = "'}'"
  interpolate Arrow = "'->'"
  interpolate DoubleArrow = "'=>'"
  interpolate Bang = "'!'"
  interpolate Tilde = "'~'"
  interpolate Dot = "'.'"
  interpolate Backslash = "'\\'"
  interpolate Colon = "':'"
  interpolate Semicolon = "';'"
  interpolate Equal = "'='"
  interpolate Comma = "','"
  interpolate Ignore = ""
  interpolate Comment = "comment"

TokenKind InkyKind where
  TokType TermIdent = String
  TokType TypeIdent = String
  TokType Lit = Nat
  TokType Comment = String
  TokType _ = ()

  tokValue TermIdent = id
  tokValue TypeIdent = id
  tokValue Lit = stringToNatOrZ
  tokValue Let = const ()
  tokValue In = const ()
  tokValue Case = const ()
  tokValue Of = const ()
  tokValue FoldCase = const ()
  tokValue Fold = const ()
  tokValue By = const ()
  tokValue Nat = const ()
  tokValue List = const ()
  tokValue Suc = const ()
  tokValue Map = const ()
  tokValue ParenOpen = const ()
  tokValue ParenClose = const ()
  tokValue BracketOpen = const ()
  tokValue BracketClose = const ()
  tokValue AngleOpen = const ()
  tokValue AngleClose = const ()
  tokValue BraceOpen = const ()
  tokValue BraceClose = const ()
  tokValue Arrow = const ()
  tokValue DoubleArrow = const ()
  tokValue Bang = const ()
  tokValue Tilde = const ()
  tokValue Dot = const ()
  tokValue Backslash = const ()
  tokValue Colon = const ()
  tokValue Semicolon = const ()
  tokValue Equal = const ()
  tokValue Comma = const ()
  tokValue Ignore = const ()
  tokValue Comment = drop 2

keywords : List (String, InkyKind)
keywords =
  [ ("let", Let)
  , ("in", In)
  , ("case", Case)
  , ("of", Of)
  , ("foldcase", FoldCase)
  , ("fold", Fold)
  , ("by", By)
  , ("Nat", Nat)
  , ("List", List)
  , ("suc", Suc)
  , ("map", Map)
  ]

export
relevant : InkyKind -> Bool
relevant = (/=) @{EqI} Ignore

public export
InkyToken : Type
InkyToken = Token InkyKind

termIdentifier : Lexer
termIdentifier = lower <+> many (alphaNum <|> exact "_")

typeIdentifier : Lexer
typeIdentifier = upper <+> many (alphaNum <|> exact "_")

export
tokenMap : TokenMap InkyToken
tokenMap =
  toTokenMap
    [ (spaces, Ignore)
    , (lineComment $ exact "--", Comment)] ++
  [(termIdentifier, \s =>
    case lookup s keywords of
      Just k => Tok k s
      Nothing => Tok TermIdent s)
  ,(typeIdentifier, \s =>
    case lookup s keywords of
      Just k => Tok k s
      Nothing => Tok TypeIdent s)] ++
  toTokenMap
    [ (digits, Lit)
    , (exact "(", ParenOpen)
    , (exact ")", ParenClose)
    , (exact "[", BracketOpen)
    , (exact "]", BracketClose)
    , (exact "<", AngleOpen)
    , (exact ">", AngleClose)
    , (exact "{", BraceOpen)
    , (exact "}", BraceClose)
    , (exact "->", Arrow)
    , (exact "=>", DoubleArrow)
    , (exact "!", Bang)
    , (exact "~", Tilde)
    , (exact ".", Dot)
    , (exact "\\", Backslash)
    , (exact ":", Colon)
    , (exact ";", Semicolon)
    , (exact "=", Equal)
    , (exact ",", Comma)
    ]

-- Parser ----------------------------------------------------------------------

public export
InkyParser : Bool -> Context Type -> Context Type -> (a : Type) -> Type
InkyParser nil locked free a =
  Parser InkyKind nil
    (map (map (False,)) locked)
    (map (map (False,)) free)
    a

public export
record ParseFun (0 n : Nat) (0 p : Fun (replicate n $ SnocList String) Type) where
  constructor MkParseFun
  try :
    DFun (replicate n $ SnocList String)
      (chain (lengthOfReplicate n $ SnocList String) (Either String) p)

mkVar : ({ctx : _} -> Var ctx -> p ctx) -> WithBounds String -> ParseFun 1 p
mkVar f x =
  MkParseFun
    (\ctx => case Var.lookup x.val ctx of
      Just i => pure (f i)
      Nothing => Left "\{x.bounds}: unbound name \"\{x.val}\"")

mkVar2 :
  ({tyCtx, tmCtx : _} -> WithBounds (Var tmCtx) -> p tyCtx tmCtx) ->
  WithBounds String -> ParseFun 2 p
mkVar2 f x =
  MkParseFun
    (\tyCtx, tmCtx => case Var.lookup x.val tmCtx of
      Just i => pure (f $ i <$ x)
      Nothing => Left "\{x.bounds}: unbound name \"\{x.val}\"")

public export
TypeFun : Type
TypeFun = ParseFun 1 Ty

public export
TermFun : Type
TermFun = ParseFun 2 (Term Sugar Bounds)

public export
TypeParser : SnocList String -> SnocList String -> Type
TypeParser locked free =
  InkyParser False (map (:- TypeFun) locked) (map (:- TypeFun) free) TypeFun

RowOf :
  (0 free : Context Type) ->
  InkyParser False [<] free a ->
  InkyParser True [<] free (List $ WithBounds $ Assoc a)
RowOf free p = sepBy (match Comma) (WithBounds $ mkAssoc <$> Seq [match TypeIdent, match Colon, p])
  where
  mkAssoc : HList [String, (), a] -> Assoc a
  mkAssoc [x, _, v] = x :- v

tryRow :
  List (WithBounds $ Assoc (ParseFun 1 p)) ->
  (ctx : _) -> Either String (Row $ p ctx)
tryRow xs ctx =
  foldlM
    (\row, xf => do
      a <- xf.val.value.try ctx
      let Just row' = extend row (xf.val.name :- a)
        | Nothing => Left "\{xf.bounds}: duplicate name \"\{xf.val.name}\""
      pure row')
    [<]
    xs

tryRow2 :
  List (WithBounds $ Assoc (ParseFun 2 p)) ->
  (tyCtx, tmCtx : _) -> Either String (Row $ p tyCtx tmCtx)
tryRow2 xs tyCtx tmCtx =
  foldlM
    (\row, xf => do
      a <- xf.val.value.try tyCtx tmCtx
      let Just row' = extend row (xf.val.name :- a)
        | Nothing => Left "\{xf.bounds}: duplicate name \"\{xf.val.name}\""
      pure row')
    [<]
    xs

OpenOrFixpointType : TypeParser [<] [<"openType"]
OpenOrFixpointType =
  OneOf
    [ mkFix <$>
      Seq [match Backslash, match TypeIdent, match DoubleArrow, Var (%%% "openType")]
    , Var (%%% "openType")
    ]
  where
  mkFix : HList [(), String, (), TypeFun] -> TypeFun
  mkFix [_, x, _, a] = MkParseFun (\ctx => pure $ TFix x !(a.try (ctx :< x)))

AtomType : TypeParser [<"openType"] [<]
AtomType =
  OneOf
    [ mkVar TVar <$> WithBounds (match TypeIdent)
    , MkParseFun (\_ => pure TNat) <$ match Nat
    , mkProd <$> enclose (match AngleOpen) (match AngleClose) row
    , mkSum <$> enclose (match BracketOpen) (match BracketClose) row
    , enclose (match ParenOpen) (match ParenClose) OpenOrFixpointType
    ]
  where
  row : InkyParser True [<] [<"openType" :- TypeFun] (List $ WithBounds $ Assoc TypeFun)
  row = RowOf [<"openType" :- TypeFun] $ Var (%%% "openType")

  mkProd : List (WithBounds $ Assoc TypeFun) -> TypeFun
  mkProd xs = MkParseFun (\ctx => TProd <$> tryRow xs ctx)

  mkSum : List (WithBounds $ Assoc TypeFun) -> TypeFun
  mkSum xs = MkParseFun (\ctx => TSum <$> tryRow xs ctx)

AppType : TypeParser [<"openType"] [<]
AppType =
  OneOf
    [ AtomType
    , match List **> mkList <$> weaken (S Z) AtomType
    ]
  where
  mkList : TypeFun -> TypeFun
  mkList x = MkParseFun (\ctx => TList <$> x.try ctx)

export
OpenType : TypeParser [<] [<]
OpenType =
  Fix "openType" $ mkArrow <$> sepBy1 (match Arrow) AppType
  where
  mkArrow : List1 TypeFun -> TypeFun
  mkArrow =
    foldr1 {a = TypeFun}
      (\x, y => MkParseFun (\ctx => [| TArrow (x.try ctx) (y.try ctx) |]))

%hint
export
OpenTypeWf : So (wellTyped EqI [<] [<] [<] [<] OpenType)
OpenTypeWf = Oh

-- Terms -----------------------------------------------------------------------

AtomTerm : InkyParser False [<"openTerm" :- TermFun] [<] TermFun
AtomTerm =
  OneOf
    [ mkVar2 (\x => Var x.bounds x.val) <$> WithBounds (match TermIdent)
    , mkLit <$> WithBounds (match Lit)
    , mkSuc <$> WithBounds (match Suc)
    , mkTup <$> WithBounds (enclose (match AngleOpen) (match AngleClose) $
        RowOf [<"openTerm" :- TermFun] (Var (%%% "openTerm")))
    , enclose (match ParenOpen) (match ParenClose) (Var (%%% "openTerm"))
    ]
  where
  mkLit : WithBounds Nat -> TermFun
  mkLit k = MkParseFun (\tyCtx, tmCtx => pure (Lit k.bounds k.val))

  mkSuc : WithBounds () -> TermFun
  mkSuc x = MkParseFun (\_, _ => pure (Suc x.bounds))

  mkTup : WithBounds (List (WithBounds $ Assoc TermFun)) -> TermFun
  mkTup xs = MkParseFun (\tyCtx, tmCtx => Tup xs.bounds <$> tryRow2 xs.val tyCtx tmCtx)

PrefixTerm : InkyParser False [<"openTerm" :- TermFun] [<] TermFun
PrefixTerm =
  Fix "prefixTerm" $ OneOf
    [ mkRoll <$> WithBounds (match Tilde **> Var (%%% "prefixTerm"))
    , mkUnroll <$> WithBounds (match Bang **> Var (%%% "prefixTerm"))
    , rename (Drop Id) Id AtomTerm
    ]
  where
  mkRoll : WithBounds TermFun -> TermFun
  mkRoll x = MkParseFun (\tyCtx, tmCtx => pure $ Roll x.bounds !(x.val.try tyCtx tmCtx))

  mkUnroll : WithBounds TermFun -> TermFun
  mkUnroll x = MkParseFun (\tyCtx, tmCtx => pure $ Unroll x.bounds !(x.val.try tyCtx tmCtx))

SuffixTerm : InkyParser False [<"openTerm" :- TermFun] [<] TermFun
SuffixTerm = mkSuffix <$> Seq [ PrefixTerm , star (match Dot **> WithBounds (match TypeIdent)) ]
  where
  mkSuffix : HList [TermFun, List (WithBounds String)] -> TermFun
  mkSuffix [t, []] = t
  mkSuffix [t, prjs] =
    MkParseFun (\tyCtx, tmCtx =>
      pure $ foldl (\acc, l => Prj l.bounds acc l.val) !(t.try tyCtx tmCtx) prjs)

AppTerm : InkyParser False [<"openTerm" :- TermFun] [<] TermFun
AppTerm =
  OneOf
    [ mkInj <$> Seq
      [ WithBounds (match TypeIdent)
      , weaken (S Z) SuffixTerm
      ]
    , mkApp <$> Seq
      [ OneOf
        [ WithBounds SuffixTerm
        , mkMap <$> Seq
          [ WithBounds (match Map)
          , enclose (match ParenOpen) (match ParenClose) $ Seq
            [ match Backslash
            , match TypeIdent
            , match DoubleArrow
            , rename Id (Drop Id) OpenType
            ]
          , sub [<"openType" :- rename Id (Drop Id) OpenType] [<] AtomType
          , sub [<"openType" :- rename Id (Drop Id) OpenType] [<] AtomType
          ]
        ]
      , star (weaken (S Z) SuffixTerm)
      ]
    ]
  where
  mkInj : HList [WithBounds String, TermFun] -> TermFun
  mkInj [tag, t] = MkParseFun (\tyCtx, tmCtx => Inj tag.bounds tag.val <$> t.try tyCtx tmCtx)

  mkMap : HList [WithBounds (), HList [_, String, _, TypeFun], TypeFun, TypeFun] -> WithBounds TermFun
  mkMap [m, [_, x, _, a], b, c] =
    MkParseFun (\tyCtx, tmCtx =>
      pure $ Map m.bounds (x ** !(a.try (tyCtx :< x))) !(b.try tyCtx) !(c.try tyCtx))
    <$ m

  mkApp : HList [WithBounds TermFun, List TermFun] -> TermFun
  mkApp [t, []] = t.val
  mkApp [fun, (arg :: args)] =
    MkParseFun (\tyCtx, tmCtx =>
      pure $
      App
        fun.bounds
        !(fun.val.try tyCtx tmCtx)
        (  !(arg.try tyCtx tmCtx)
        :: (!(foldlM (\acc, arg => pure $ acc :< !(arg.try tyCtx tmCtx)) [<] args) <>> [])))

AnnotTerm : InkyParser False [<"openTerm" :- TermFun] [<] TermFun
AnnotTerm =
  mkAnnot <$> Seq
    [ AppTerm
    , option (match Colon **> WithBounds (rename Id (Drop Id) OpenType))
    ]
  where
  mkAnnot : HList [TermFun, Maybe (WithBounds TypeFun)] -> TermFun
  mkAnnot [t, Nothing] = t
  mkAnnot [t, Just a] = MkParseFun (\tyCtx, tmCtx =>
    pure $ Annot a.bounds !(t.try tyCtx tmCtx) !(a.val.try tyCtx))

-- Open Terms

LetTerm : InkyParser False [<"openTerm" :- TermFun] [<] TermFun
LetTerm =
  match Let **>
  OneOf
    [ mkLet <$> Seq
      [ WithBounds (match TermIdent)
      , OneOf
        [ mkAnnot <$> Seq
          [ star (enclose (match ParenOpen) (match ParenClose) $
            Seq [ match TermIdent, match Colon, rename Id (Drop Id) OpenType ])
          , WithBounds (match Colon)
          , rename Id (Drop Id) OpenType
          , match Equal
          , star (match Comment)
          , Var (%%% "openTerm")]
        , mkUnannot <$> Seq [match Equal, star (match Comment) , Var (%%% "openTerm")]
        ]
      , match In
      , Var (%%% "openTerm")
      ]
    , mkLetType <$> Seq
      [ WithBounds (match TypeIdent)
      , match Equal
      , star (match Comment)
      , rename Id (Drop Id) OpenType
      , match In
      , Var (%%% "openTerm")
      ]
    ]
  where
  mkLet : HList [WithBounds String, WithDoc TermFun, (), TermFun] -> TermFun
  mkLet [x, AddDoc e doc, _, t] =
    MkParseFun (\tyCtx, tmCtx =>
      pure $
      Let (AddDoc x.bounds doc) !(e.try tyCtx tmCtx) (x.val ** !(t.try tyCtx (tmCtx :< x.val))))

  mkLetType : HList [WithBounds String, (), List String, TypeFun, (), TermFun] -> TermFun
  mkLetType [x, _, doc, a, _, t] =
    MkParseFun (\tyCtx, tmCtx =>
      pure $
      LetTy (AddDoc x.bounds doc) !(a.try tyCtx) (x.val ** !(t.try (tyCtx :< x.val) tmCtx)))

  mkArrow : List TypeFun -> TypeFun -> TypeFun
  mkArrow [] cod = cod
  mkArrow (arg :: args) cod =
    MkParseFun (\ctx => [| TArrow (arg.try ctx) ((mkArrow args cod).try ctx) |])

  mkAnnot :
    HList [List (HList [String, (), TypeFun]), WithBounds (), TypeFun, (), List String, TermFun] ->
    WithDoc TermFun
  mkAnnot [[], m, cod, _, doc, t] =
    AddDoc
      (MkParseFun (\tyCtx, tmCtx =>
        pure $ Annot m.bounds !(t.try tyCtx tmCtx) !(cod.try tyCtx)))
      doc
  mkAnnot [args, m, cod, _, doc, t] =
    let bound = map (\[x, _, a] => x) args in
    let tys = map (\[x, _, a] => a) args in
    AddDoc
      (MkParseFun (\tyCtx, tmCtx =>
        pure $
        Annot m.bounds
          (Abs m.bounds (bound ** !(t.try tyCtx (tmCtx <>< bound))))
          !((mkArrow tys cod).try tyCtx)))
      doc

  mkUnannot : HList [(), List String, TermFun] -> WithDoc TermFun
  mkUnannot [_, doc, e] = AddDoc e doc

AbsTerm : InkyParser False [<"openTerm" :- TermFun] [<] TermFun
AbsTerm =
  mkAbs <$> Seq
    [ WithBounds (match Backslash)
    , sepBy1 (match Comma) (match TermIdent)
    , match DoubleArrow
    , Var (%%% "openTerm")
    ]
  where
  mkAbs : HList [WithBounds (), List1 String, (), TermFun] -> TermFun
  mkAbs [m, args, _, body] =
    MkParseFun (\tyCtx, tmCtx =>
      pure $ Abs m.bounds (forget args ** !(body.try tyCtx (tmCtx <>< forget args))))

CaseTerm : InkyParser False [<"openTerm" :- TermFun] [<] TermFun
CaseTerm =
  (\[f, x] => f x) <$>
  Seq
    [ OneOf
      [ mkCase <$> Seq
        [ WithBounds (match Case)
        , Var (%%% "openTerm")
        , match Of
        ]
      , mkFoldCase <$> Seq
        [ WithBounds (match FoldCase)
        , Var (%%% "openTerm")
        , match By
        ]
      ]
    , enclose (match BraceOpen) (match BraceClose) (
        sepBy (match Semicolon) $
        WithBounds $
        Seq
          [ match TypeIdent
          , match TermIdent
          , match DoubleArrow
          , Var (%%% "openTerm")
          ])
    ]
  where
  Cases : Type
  Cases = List (WithBounds $ HList [String, String, (), TermFun])

  mkBranch :
    HList [String, String, (), TermFun] ->
    Assoc (ParseFun 2 $ \tyCtx, tmCtx => (x ** Term Sugar Bounds tyCtx (tmCtx :< x)))
  mkBranch [tag, bound, _, branch] =
    tag :- MkParseFun (\tyCtx, tmCtx => pure (bound ** !(branch.try tyCtx (tmCtx :< bound))))

  mkCase : HList [WithBounds (), TermFun, _] -> Cases -> TermFun
  mkCase [m, target, _] branches =
    let branches = map (map mkBranch) branches in
    MkParseFun (\tyCtx, tmCtx =>
      pure $ Case m.bounds !(target.try tyCtx tmCtx) !(tryRow2 branches tyCtx tmCtx))

  mkFoldCase : HList [WithBounds (), TermFun, _] -> Cases -> TermFun
  mkFoldCase [m, target, _] branches =
    let branches = map (map mkBranch) branches in
    MkParseFun (\tyCtx, tmCtx =>
      pure $
      Fold
        m.bounds
        !(target.try tyCtx tmCtx)
        ("__tmp" ** Case m.bounds (Var m.bounds $ %% "__tmp") !(tryRow2 branches tyCtx (tmCtx :< "__tmp"))))

FoldTerm : InkyParser False [<"openTerm" :- TermFun] [<] TermFun
FoldTerm =
  mkFold <$> Seq
    [ WithBounds (match Fold)
    , Var (%%% "openTerm")
    , match By
    , enclose (match ParenOpen) (match ParenClose) $
      Seq
        [ match Backslash
        , match TermIdent
        , match DoubleArrow
        , Var (%%% "openTerm")
        ]
    ]
  where
  mkFold : HList [WithBounds (), TermFun, (), HList [(), String, (), TermFun]] -> TermFun
  mkFold [m, target, _, [_, arg, _, body]] =
    MkParseFun (\tyCtx, tmCtx =>
      pure $ Fold m.bounds !(target.try tyCtx tmCtx) (arg ** !(body.try tyCtx (tmCtx :< arg))))

export
OpenTerm : InkyParser False [<] [<] TermFun
OpenTerm =
  Fix "openTerm" $ OneOf
    [ LetTerm
    , AbsTerm
    , CaseTerm
    , FoldTerm
    , AnnotTerm
    ]

%hint
export
OpenTermWf : So (wellTyped EqI [<] [<] [<] [<] OpenTerm)
OpenTermWf = Oh
