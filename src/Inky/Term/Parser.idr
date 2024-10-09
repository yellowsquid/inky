module Inky.Term.Parser

import public Data.Fun

import Data.List1
import Data.String
import Inky.Context
import Inky.Parser
import Inky.Term
import Inky.Thinning
import Inky.Type
import Text.Lexer

-- Lexer -----------------------------------------------------------------------

export
data InkyKind
  = TermIdent
  | TypeIdent
  | Lit
  | Suc
  | Let
  | In
  | Case
  | Of
  | FoldCase
  | Fold
  | By
  | Nat
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

export
[EqI] Eq InkyKind where
  TermIdent == TermIdent = True
  TypeIdent == TypeIdent = True
  Lit == Lit = True
  Suc == Suc = True
  Let == Let = True
  In == In = True
  Case == Case = True
  Of == Of = True
  FoldCase == FoldCase = True
  Fold == Fold = True
  By == By = True
  Nat == Nat = True
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
  _ == _ = False

export
Interpolation InkyKind where
  interpolate TermIdent = "term name"
  interpolate TypeIdent = "type name"
  interpolate Lit = "number"
  interpolate Suc = "'suc'"
  interpolate Let = "'let'"
  interpolate In = "'in'"
  interpolate Case = "'case'"
  interpolate Of = "'of'"
  interpolate FoldCase = "'foldcase'"
  interpolate Fold = "'fold'"
  interpolate By = "'by'"
  interpolate Nat = "'Nat'"
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

TokenKind InkyKind where
  TokType TermIdent = String
  TokType TypeIdent = String
  TokType Lit = Nat
  TokType _ = ()

  tokValue TermIdent = id
  tokValue TypeIdent = id
  tokValue Lit = stringToNatOrZ
  tokValue Suc = const ()
  tokValue Let = const ()
  tokValue In = const ()
  tokValue Case = const ()
  tokValue Of = const ()
  tokValue FoldCase = const ()
  tokValue Fold = const ()
  tokValue By = const ()
  tokValue Nat = const ()
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

keywords : List (String, InkyKind)
keywords =
  [ ("suc", Suc)
  , ("let", Let)
  , ("in", In)
  , ("case", Case)
  , ("of", Of)
  , ("foldcase", FoldCase)
  , ("fold", Fold)
  , ("by", By)
  , ("Nat", Nat)
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
    , (lineComment $ exact "--", Ignore)
    ] ++
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
DFun : (ts : Vect n Type) -> Fun ts Type -> Type
DFun [] r = r
DFun (t :: ts) r = (x : t) -> DFun ts (r x)

public export
DIFun : (ts : Vect n Type) -> Fun ts Type -> Type
DIFun [] r = r
DIFun (t :: ts) r = {x : t} -> DIFun ts (r x)

public export
InkyParser : Bool -> Context Type -> Context Type -> (a : Type) -> Type
InkyParser nil locked free a =
  Parser InkyKind nil
    (map (\a => (False, a)) locked)
    (map (\a => (False, a)) free)
    a

public export
record ParseFun (0 tys: Vect n Type) (0 p : Fun (map Context tys) Type) where
  constructor MkParseFun
  try : DFun (map Context tys) (chain {ts = map Context tys} (Either String) p)

mkVar : ({ctx : Context ()} -> Var ctx () -> p ctx) -> WithBounds String -> ParseFun [()] p
mkVar f x =
  MkParseFun
    (\ctx => case lookup x.val ctx of
      Just (() ** i) => pure (f i)
      Nothing => Left "\{x.bounds}: unbound name \"\{x.val}\"")

mkVar2 :
  ({tyCtx, tmCtx : Context ()} -> Var tmCtx () -> p tyCtx tmCtx) ->
  WithBounds String -> ParseFun [(), ()] p
mkVar2 f x =
  MkParseFun
    (\tyCtx, tmCtx => case lookup x.val tmCtx of
      Just (() ** i) => pure (f i)
      Nothing => Left "\{x.bounds}: unbound name \"\{x.val}\"")

public export
TypeFun : Type
TypeFun = ParseFun [()] (\ctx => Ty ctx ())

public export
SynthFun : Type
SynthFun = ParseFun [(), ()] SynthTerm

public export
CheckFun : Type
CheckFun = ParseFun [(), ()] CheckTerm

public export
TypeParser : Context () -> Context () -> Type
TypeParser locked free =
  InkyParser False (map (const TypeFun) locked) (map (const TypeFun) free) TypeFun

RowOf : (0 free : Context Type) -> InkyParser False [<] free a -> InkyParser True [<] free (List $ WithBounds $ Assoc a)
RowOf free p = sepBy (match Comma) (WithBounds $ mkAssoc <$> Seq [match TypeIdent, match Colon, p])
  where
  mkAssoc : HList [String, (), a] -> Assoc a
  mkAssoc [x, _, v] = x :- v

tryRow :
  List (WithBounds $ Assoc (ParseFun [()] p)) ->
  (ctx : Context ()) -> Either String (Row $ p ctx)
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
  List (WithBounds $ Assoc (ParseFun [(), ()] p)) ->
  (tyCtx, tmCtx : Context ()) -> Either String (Row $ p tyCtx tmCtx)
tryRow2 xs tyCtx tmCtx =
  foldlM
    (\row, xf => do
      a <- xf.val.value.try tyCtx tmCtx
      let Just row' = extend row (xf.val.name :- a)
        | Nothing => Left "\{xf.bounds}: duplicate name \"\{xf.val.name}\""
      pure row')
    [<]
    xs

OpenOrFixpointType : TypeParser [<] [<"openType" :- ()]
OpenOrFixpointType =
  OneOf
    [ mkFix <$>
      Seq [match Backslash, match TypeIdent, match DoubleArrow, Var (%% "openType")]
    , Var (%% "openType")
    ]
  where
  mkFix : HList [(), String, (), TypeFun] -> TypeFun
  mkFix [_, x, _, a] = MkParseFun (\ctx => pure $ TFix x !(a.try (ctx :< (x :- ()))))

AtomType : TypeParser [<"openType" :- ()] [<]
AtomType =
  OneOf
    [ mkVar TVar <$> WithBounds (match TypeIdent)
    , MkParseFun (\_ => pure TNat) <$ match Nat
    , mkProd <$> enclose (match AngleOpen) (match AngleClose) Row
    , mkSum <$> enclose (match BracketOpen) (match BracketClose) Row
    , enclose (match ParenOpen) (match ParenClose) OpenOrFixpointType
    ]
  where
  Row : InkyParser True [<] [<"openType" :- TypeFun] (List $ WithBounds $ Assoc TypeFun)
  Row = RowOf [<"openType" :- TypeFun] $ Var (%% "openType")

  mkProd : List (WithBounds $ Assoc TypeFun) -> TypeFun
  mkProd xs = MkParseFun (\ctx => TProd <$> tryRow xs ctx)

  mkSum : List (WithBounds $ Assoc TypeFun) -> TypeFun
  mkSum xs = MkParseFun (\ctx => TSum <$> tryRow xs ctx)

export
OpenType : TypeParser [<] [<]
OpenType =
  Fix "openType" $ mkArrow <$> sepBy1 (match Arrow) AtomType
  where
  mkArrow : List1 TypeFun -> TypeFun
  mkArrow = foldr1 (\x, y => MkParseFun (\ctx => [| TArrow (x.try ctx) (y.try ctx) |]))

%hint
export
OpenTypeWf : So (wellTyped EqI [<] [<] [<] [<] OpenType)
OpenTypeWf = Oh

-- Terms -----------------------------------------------------------------------

embed : SynthFun -> CheckFun
embed x = MkParseFun (\tyCtx, tmCtx => Embed <$> x.try tyCtx tmCtx)

unembed : WithBounds CheckFun -> SynthFun
unembed x =
  MkParseFun (\tyCtx, tmCtx => do
    t <- x.val.try tyCtx tmCtx
    case t of
      Embed e => pure e
      _ => Left "\{x.bounds}: cannot synthesise type")

AtomCheck : InkyParser False [<"openCheck" :- CheckFun] [<] CheckFun
AtomCheck =
  OneOf
    [ embed <$> mkVar2 Var <$> WithBounds (match TermIdent)
    , embed <$> mkLit <$> match Lit
    , embed <$> MkParseFun (\_, _ => pure Suc) <$ match Suc
    , mkTup <$> (enclose (match AngleOpen) (match AngleClose) $
        RowOf [<"openCheck" :- CheckFun] (Var (%% "openCheck")))
    , enclose (match ParenOpen) (match ParenClose) (Var (%% "openCheck"))
    ]
  where
  mkLit : Nat -> SynthFun
  mkLit k = MkParseFun (\_, _ => pure (Lit k))

  mkTup : List (WithBounds $ Assoc CheckFun) -> CheckFun
  mkTup xs = MkParseFun (\tyCtx, tmCtx => Tup <$> tryRow2 xs tyCtx tmCtx)

PrefixCheck : InkyParser False [<"openCheck" :- CheckFun] [<] CheckFun
PrefixCheck =
  Fix "prefixCheck" $ OneOf
    [ embed <$> mkExpand <$> unembed <$> (match Bang **> WithBounds (Var $ %% "prefixCheck"))
    , mkContract <$> (match Tilde **> Var (%% "prefixCheck"))
    , rename (Drop Id) Id AtomCheck
    ]
  where
  mkExpand : SynthFun -> SynthFun
  mkExpand x = MkParseFun (\tyCtx, tmCtx => [| Expand (x.try tyCtx tmCtx) |])

  mkContract : CheckFun -> CheckFun
  mkContract x = MkParseFun (\tyCtx, tmCtx => [| Contract (x.try tyCtx tmCtx) |])

SuffixCheck : InkyParser False [<"openCheck" :- CheckFun] [<] CheckFun
SuffixCheck = mkSuffix <$> Seq [ WithBounds PrefixCheck , star (match Dot **> match TypeIdent) ]
  where
  mkSuffix : HList [WithBounds CheckFun, List String] -> CheckFun
  mkSuffix [t, []] = t.val
  mkSuffix [t, prjs] =
    embed $
    MkParseFun (\tyCtx, tmCtx => pure $ foldl Prj !((unembed t).try tyCtx tmCtx) prjs)

AppCheck : InkyParser False [<"openCheck" :- CheckFun] [<] CheckFun
AppCheck =
  OneOf
    [ mkInj <$> Seq
      [ match TypeIdent
      , weaken (S Z) SuffixCheck
      ]
    , mkApp <$> Seq [ WithBounds SuffixCheck , star (weaken (S Z) SuffixCheck) ]
    ]
  where
  mkInj : HList [String, CheckFun] -> CheckFun
  mkInj [tag, t] = MkParseFun (\tyCtx, tmCtx => Inj tag <$> t.try tyCtx tmCtx)

  mkApp : HList [WithBounds CheckFun, List CheckFun] -> CheckFun
  mkApp [t, []] = t.val
  mkApp [fun, (arg :: args)] =
    MkParseFun (\tyCtx, tmCtx =>
      pure $ Embed $
      App
        !((unembed fun).try tyCtx tmCtx)
        (  !(arg.try tyCtx tmCtx)
        :: (!(foldlM (\acc, arg => pure $ acc :< !(arg.try tyCtx tmCtx)) [<] args) <>> [])))

AnnotCheck : InkyParser False [<"openCheck" :- CheckFun] [<] CheckFun
AnnotCheck =
  mkAnnot <$> Seq
    [ AppCheck
    , option (match Colon **> rename Id (Drop Id) OpenType)
    ]
  where
  mkAnnot : HList [CheckFun, Maybe TypeFun] -> CheckFun
  mkAnnot [t, Nothing] = t
  mkAnnot [t, Just a] = embed $ MkParseFun (\tyCtx, tmCtx => [| Annot (t.try tyCtx tmCtx) (a.try tyCtx) |])

-- Open Terms

LetCheck : InkyParser False [<"openCheck" :- CheckFun] [<] CheckFun
LetCheck =
  match Let **>
  OneOf
    [ mkLet <$> Seq
      [ match TermIdent
      , OneOf
        [ mkBound <$> Seq
          [ star (enclose (match ParenOpen) (match ParenClose) $
            Seq [ match TermIdent, match Colon, rename Id (Drop Id) OpenType ])
          , match Colon
          , rename Id (Drop Id) OpenType
          , match Equal
          , Var (%% "openCheck")]
        , match Equal **> unembed <$> WithBounds (Var (%% "openCheck"))
        ]
      , match In
      , Var (%% "openCheck")
      ]
    , mkLetType <$> Seq
      [ match TypeIdent
      , match Equal
      , rename Id (Drop Id) OpenType
      , match In
      , Var (%% "openCheck")
      ]
    ]
  where
  mkLet : HList [String, SynthFun, (), CheckFun] -> CheckFun
  mkLet [x, e, _, t] = MkParseFun (\tyCtx, tmCtx => pure $ Let x !(e.try tyCtx tmCtx) !(t.try tyCtx (tmCtx :< (x :- ()))))

  mkLetType : HList [String, (), TypeFun, (), CheckFun] -> CheckFun
  mkLetType [x, _, a, _, t] =
    MkParseFun (\tyCtx, tmCtx => pure $ LetTy x !(a.try tyCtx) !(t.try (tyCtx :< (x :- ())) tmCtx))

  mkArrow : List TypeFun -> TypeFun -> TypeFun
  mkArrow [] cod = cod
  mkArrow (arg :: args) cod =
    MkParseFun (\ctx => [| TArrow (arg.try ctx) ((mkArrow args cod).try ctx) |])

  mkBound : HList [List (HList [String, (), TypeFun]), (), TypeFun, (), CheckFun] -> SynthFun
  mkBound [[], _, cod, _, t] =
    MkParseFun (\tyCtx, tmCtx =>
      pure $
      Annot !(t.try tyCtx tmCtx) !(cod.try tyCtx))
  mkBound [args, _, cod, _, t] =
    let dom = foldl (\dom, [x, _, a] => dom :< (x :- ())) [<] args in
    MkParseFun (\tyCtx, tmCtx =>
      pure $
      Annot (Abs dom !(t.try tyCtx (tmCtx ++ dom))) !((mkArrow (map (\[x, _, a] => a) args) cod).try tyCtx))

AbsCheck : InkyParser False [<"openCheck" :- CheckFun] [<] CheckFun
AbsCheck =
  mkAbs <$> Seq
    [ match Backslash
    , sepBy1 (match Comma) (match TermIdent)
    , match DoubleArrow
    , Var (%% "openCheck")
    ]
  where
  mkAbs : HList [(), List1 String, (), CheckFun] -> CheckFun
  mkAbs [_, args, _, body] =
    let args = foldl (\args, x => args :< (x :- ())) [<] args in
    MkParseFun (\tyCtx, tmCtx => Abs args <$> body.try tyCtx (tmCtx ++ args))

CaseCheck : InkyParser False [<"openCheck" :- CheckFun] [<] CheckFun
CaseCheck =
  (\[f, x] => f x) <$>
  Seq
    [ OneOf
      [ mkCase <$> Seq
        [ match Case
        , unembed <$> WithBounds (Var $ %% "openCheck")
        , match Of
        ]
      , mkFoldCase <$> Seq
        [ match FoldCase
        , unembed <$> WithBounds (Var $ %% "openCheck")
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
          , Var (%% "openCheck")
          ])
    ]
  where
  Cases : Type
  Cases = List (WithBounds $ HList [String, String, (), CheckFun])

  mkBranch :
    HList [String, String, (), CheckFun] ->
    Assoc (ParseFun [(), ()] $ \tyCtx, tmCtx => (x ** CheckTerm tyCtx (tmCtx :< (x :- ()))))
  mkBranch [tag, bound, _, branch] =
    tag :- MkParseFun (\tyCtx, tmCtx => pure (bound ** !(branch.try tyCtx (tmCtx :< (bound :- ())))))

  mkCase : HList [_, SynthFun, _] -> Cases -> CheckFun
  mkCase [_, target, _] branches =
    let branches = map (map mkBranch) branches in
    MkParseFun (\tyCtx, tmCtx =>
      [| Case (target.try tyCtx tmCtx) (tryRow2 branches tyCtx tmCtx) |])

  mkFoldCase : HList [_, SynthFun, _] -> Cases -> CheckFun
  mkFoldCase [_, target, _] branches =
    let branches = map (map mkBranch) branches in
    MkParseFun (\tyCtx, tmCtx =>
      pure $
      Fold
        !(target.try tyCtx tmCtx)
        "__tmp"
        (Case (Var $ %% "__tmp") !(tryRow2 branches tyCtx (tmCtx :< ("__tmp" :- ())))))

FoldCheck : InkyParser False [<"openCheck" :- CheckFun] [<] CheckFun
FoldCheck =
  mkFold <$> Seq
    [ match Fold
    , unembed <$> WithBounds (Var (%% "openCheck"))
    , match By
    , enclose (match ParenOpen) (match ParenClose) $
      Seq
        [ match Backslash
        , match TermIdent
        , match DoubleArrow
        , Var (%% "openCheck")
        ]
    ]
  where
  mkFold : HList [(), SynthFun, (), HList [(), String, (), CheckFun]] -> CheckFun
  mkFold [_, target, _, [_, arg, _, body]] =
    MkParseFun (\tyCtx, tmCtx => pure $ Fold !(target.try tyCtx tmCtx) arg !(body.try tyCtx (tmCtx :< (arg :- ()))))

export
OpenCheck : InkyParser False [<] [<] CheckFun
OpenCheck =
  Fix "openCheck" $ OneOf
    [ LetCheck
    , AbsCheck
    , CaseCheck
    , FoldCheck
    , AnnotCheck
    ]

%hint
export
OpenCheckWf : So (wellTyped EqI [<] [<] [<] [<] OpenCheck)
OpenCheckWf = ?d -- Oh
