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
  | StringLit
  | Lit
  | Let
  | In
  | Case
  | Of
  | FoldCase
  | Fold
  | By
  | Data
  | Nat
  | List
  | Suc
  | Cons
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
  | WaveArrow
  | Bang
  | Tilde
  | Backtick
  | Dot
  | Backslash
  | Colon
  | Semicolon
  | Equal
  | Comma
  | Ignore
  | Comment

export
Eq InkyKind where
  TermIdent == TermIdent = True
  TypeIdent == TypeIdent = True
  StringLit == StringLit = True
  Lit == Lit = True
  Let == Let = True
  In == In = True
  Case == Case = True
  Of == Of = True
  FoldCase == FoldCase = True
  Fold == Fold = True
  By == By = True
  Data == Data = True
  Nat == Nat = True
  List == List = True
  Suc == Suc = True
  Cons == Cons = True
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
  WaveArrow == WaveArrow = True
  Bang == Bang = True
  Tilde == Tilde = True
  Backtick == Backtick = True
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
  interpolate StringLit = "string"
  interpolate Lit = "number"
  interpolate Let = "'let'"
  interpolate In = "'in'"
  interpolate Case = "'case'"
  interpolate Of = "'of'"
  interpolate FoldCase = "'foldcase'"
  interpolate Fold = "'fold'"
  interpolate By = "'by'"
  interpolate Data = "'Data'"
  interpolate Nat = "'Nat'"
  interpolate List = "'List'"
  interpolate Suc = "'suc'"
  interpolate Cons = "'cons'"
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
  interpolate WaveArrow = "'~>'"
  interpolate Bang = "'!'"
  interpolate Tilde = "'~'"
  interpolate Backtick = "'`'"
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
  TokType StringLit = String
  TokType Lit = Nat
  TokType Comment = String
  TokType _ = ()

  tokValue TermIdent = id
  tokValue TypeIdent = id
  tokValue StringLit = \str => substr 1 (length str `minus` 2) str
  tokValue Lit = stringToNatOrZ
  tokValue Let = const ()
  tokValue In = const ()
  tokValue Case = const ()
  tokValue Of = const ()
  tokValue FoldCase = const ()
  tokValue Fold = const ()
  tokValue By = const ()
  tokValue Data = const ()
  tokValue Nat = const ()
  tokValue List = const ()
  tokValue Suc = const ()
  tokValue Cons = const ()
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
  tokValue WaveArrow = const ()
  tokValue Bang = const ()
  tokValue Tilde = const ()
  tokValue Backtick = const ()
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
  , ("data", Data)
  , ("Nat", Nat)
  , ("List", List)
  , ("suc", Suc)
  , ("cons", Cons)
  , ("map", Map)
  ]

export
relevant : InkyKind -> Bool
relevant = (/=) Ignore

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
    [ (quote (is '"') alpha, StringLit)
    , (digits, Lit)
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
    , (exact "~>", WaveArrow)
    , (exact "!", Bang)
    , (exact "~", Tilde)
    , (exact "`", Backtick)
    , (exact ".", Dot)
    , (exact "\\", Backslash)
    , (exact ":", Colon)
    , (exact ";", Semicolon)
    , (exact "=", Equal)
    , (exact ",", Comma)
    ]

-- Error Monad -----------------------------------------------------------------

public export
data Result : (a : Type) -> Type where
  Ok : a -> Result a
  Errs : (msgs : List1 (WithBounds String)) -> Result a

export
Functor Result where
  map f (Ok x) = Ok (f x)
  map f (Errs msgs) = Errs msgs

export
Applicative Result where
  pure = Ok

  Ok f <*> Ok x = Ok (f x)
  Ok f <*> Errs msgs = Errs msgs
  Errs msgs <*> Ok x = Errs msgs
  Errs msgs1 <*> Errs msgs2 = Errs (msgs1 ++ msgs2)

export
Monad Result where
  Ok x >>= f = f x
  Errs msgs >>= f = Errs msgs

  join (Ok x) = x
  join (Errs msgs) = Errs msgs

export
extendResult : Row a -> WithBounds (Assoc (Result a)) -> Result (Row a)
extendResult row x =
  case (isFresh row.names x.val.name) of
    True `Because` prf => Ok ((:<) row (x.val.name :- !x.val.value) @{prf})
    False `Because` _ =>
      [| const (Errs $ singleton $ "duplicate name \"\{x.val.name}\"" <$ x) x.val.value |]

-- Parser ----------------------------------------------------------------------

public export
InkyParser : Bool -> Context Type -> Context Type -> (a : Type) -> Type
InkyParser nil locked free a =
  Parser InkyKind nil
    (map (map (False,)) locked)
    (map (map (False,)) free)
    a

public export
record ParseFun (as : SnocList Type) (0 p : Fun as Type) where
  constructor MkParseFun
  try : DFun as (chain (lengthOf as) Parser.Result p)

mkVar : ({ctx : _} -> Var ctx -> p ctx) -> WithBounds String -> ParseFun [<SnocList String] p
mkVar f x =
  MkParseFun
    (\ctx => case Var.lookup x.val ctx of
      Just i => Ok (f i)
      Nothing => Errs (singleton $ "unbound name \"\{x.val}\"" <$ x))

mkVar3 :
  ({ctx1 : a} -> {ctx2 : b} -> {ctx3 : SnocList String} ->
    WithBounds (Var ctx3) ->
    p ctx1 ctx2 ctx3) ->
  WithBounds String -> ParseFun [<a, b, SnocList String] p
mkVar3 f x =
  MkParseFun
    (\ctx1, ctx2, ctx3 => case Var.lookup x.val ctx3 of
      Just i => Ok (f $ i <$ x)
      Nothing => Errs (singleton $ "unbound name \"\{x.val}\"" <$ x))

public export
TypeFun : Type
TypeFun = ParseFun [<SnocList String] Ty

Type'Fun : Type
Type'Fun = ParseFun [<Mode, SnocList String, SnocList String] (\mode => Ty' mode Bounds)

BoundType'Fun : Type
BoundType'Fun = ParseFun [<Mode, SnocList String, SnocList String] (\mode => BoundTy' mode Bounds)

public export
TermFun : Type
TermFun = ParseFun [<Mode, SnocList String, SnocList String] (\mode => Term mode Bounds)

public export
TypeParser : SnocList String -> SnocList String -> Type
TypeParser locked free =
  InkyParser False (map (:- TypeFun) locked) (map (:- TypeFun) free) TypeFun

RowOf :
  (0 free : Context Type) ->
  InkyParser False [<] free a ->
  InkyParser True [<] free (List $ WithBounds $ Assoc a)
RowOf free p =
  sepBy (match Semicolon) (WithBounds $ mkAssoc <$> Seq [match TypeIdent, match Colon, p])
  where
  mkAssoc : HList [String, (), a] -> Assoc a
  mkAssoc [x, _, v] = x :- v

parseRow :
  List (WithBounds $ Assoc (ParseFun [<a] p)) ->
  ParseFun [<a] (Row . p)
parseRow xs =
  MkParseFun (\ctx =>
    foldlM
      (\row => extendResult row . map (\(n :- x) => n :- x.try ctx))
      [<]
      xs)

parseRow3 :
  List (WithBounds $ Assoc (ParseFun [<a,b,c] p)) ->
  ParseFun [<a, b, c] (\ctx1, ctx2, ctx3 => Row $ p ctx1 ctx2 ctx3)
parseRow3 xs =
  MkParseFun (\ctx1, ctx2, ctx3 =>
    foldlM
      (\row => extendResult row . map (\(n :- x) => n :- x.try ctx1 ctx2 ctx3))
      [<]
      xs)

parseList3 :
  List (ParseFun [<a,b,c] p) ->
  ParseFun [<a, b, c] (\ctx1, ctx2, ctx3 => List $ p ctx1 ctx2 ctx3)
parseList3 [] = MkParseFun (\ctx1, ctx2, ctx3 => Ok [])
parseList3 (x :: xs) =
  MkParseFun (\ctx1, ctx2, ctx3 =>
    [| x.try ctx1 ctx2 ctx3 :: (parseList3 xs).try ctx1 ctx2 ctx3 |])

-- Types -----------------------------------------------------------------------

AtomType : TypeParser [<"openType"] [<]
AtomType =
  OneOf
    [ mkVar TVar <$> WithBounds (match TypeIdent)
    , MkParseFun (\_ => Ok TNat) <$ match Nat
    , mkProd <$> enclose (match AngleOpen) (match AngleClose) row
    , mkSum <$> enclose (match BracketOpen) (match BracketClose) row
    , enclose (match ParenOpen) (match ParenClose) (Var (%%% "openType"))
    ]
  where
  row : InkyParser True [<] [<"openType" :- TypeFun] (List $ WithBounds $ Assoc TypeFun)
  row = RowOf [<"openType" :- TypeFun] $ Var (%%% "openType")

  mkProd : List (WithBounds $ Assoc TypeFun) -> TypeFun
  mkProd xs = MkParseFun (\ctx => TProd <$> (parseRow xs).try ctx)

  mkSum : List (WithBounds $ Assoc TypeFun) -> TypeFun
  mkSum xs = MkParseFun (\ctx => TSum <$> (parseRow xs).try ctx)

AppType : TypeParser [<"openType"] [<]
AppType =
  OneOf
    [ AtomType
    , match List **> mkList <$> weaken (S Z) AtomType
    , mkFix <$> Seq
      [ match Data
      , match TypeIdent
      , weaken (S Z) AtomType
      ]
    ]
  where
  mkList : TypeFun -> TypeFun
  mkList x = MkParseFun (\ctx => TList <$> x.try ctx)

  mkFix : HList [(), String, TypeFun] -> TypeFun
  mkFix [_, x, a] = MkParseFun (\ctx => TFix x <$> a.try (ctx :< x))

export
OpenType : TypeParser [<] [<]
OpenType =
  Fix "openType" $ mkArrow <$> sepBy1 (match Arrow) AppType
  where
  mkArrow : List1 TypeFun -> TypeFun
  mkArrow =
    foldr1 {a = TypeFun}
      (\x, y => MkParseFun (\ctx => [| TArrow (x.try ctx) (y.try ctx) |]))

export
[ListSet] Eq a => Set a (List a) where
  singleton x = [x]

  member x xs = elem x xs

  intersect xs = filter (\x => elem x xs)

  toList = id

%hint
export
OpenTypeWf : collectTypeErrs @{ListSet} [<] [<] [<] [<] OpenType = []
OpenTypeWf = Refl

-- Terms -----------------------------------------------------------------------

NoSugarMsg : String
NoSugarMsg = "sugar is not allowed here"

NoUnquoteMsg : String
NoUnquoteMsg = "cannot unquote outside of quote"

NoQuoteMsg : String
NoQuoteMsg = "cannot quote inside of quote"

NoQuoteTypesMsg : String
NoQuoteTypesMsg = "cannot quote types"

NoLetTyMsg : String
NoLetTyMsg = "cannot bind type inside of quote"

NoQAbsMsg : String
NoQAbsMsg = "cannot bind term name inside of quote"

AtomTerm : InkyParser False [<"openTerm" :- TermFun] [<] TermFun
AtomTerm =
  OneOf
    [ mkVar3 (\x => Var x.bounds x.val) <$> WithBounds (match TermIdent)
    , mkStrLit <$> WithBounds (match StringLit)
    , mkLit <$> WithBounds (match Lit)
    , mkList <$> WithBounds (
        enclose (match BracketOpen) (match BracketClose) $
        sepBy (match Semicolon) $
        Var (%%% "openTerm"))
    , mkTup <$> WithBounds (enclose (match AngleOpen) (match AngleClose) $
        RowOf [<"openTerm" :- TermFun] (Var (%%% "openTerm")))
    , enclose (match ParenOpen) (match ParenClose) (Var (%%% "openTerm"))
    ]
  where
  mkStrLit : WithBounds String -> TermFun
  mkStrLit k = MkParseFun (\mode, tyCtx, tmCtx =>
    case mode of
      NoSugar => Errs (singleton $ NoSugarMsg <$ k)
      Sugar qtCtx => Ok (Str k.bounds k.val)
      Quote ctx1 ctx2 => Errs (singleton $ NoSugarMsg <$ k))

  mkLit : WithBounds Nat -> TermFun
  mkLit k = MkParseFun (\mode, tyCtx, tmCtx =>
    case mode of
      NoSugar => Errs (singleton $ NoSugarMsg <$ k)
      Sugar qtCtx => Ok (Lit k.bounds k.val)
      Quote ctx1 ctx2 => Errs (singleton $ NoSugarMsg <$ k))

  mkList : WithBounds (List TermFun) -> TermFun
  mkList xs = MkParseFun (\mode, tyCtx, tmCtx =>
    case mode of
      NoSugar => Errs (singleton $ NoSugarMsg <$ xs)
      Sugar ctx => List xs.bounds <$> (parseList3 xs.val).try (Sugar ctx) tyCtx tmCtx
      Quote ctx1 ctx2 => Errs (singleton $ NoSugarMsg <$ xs))

  mkTup : WithBounds (List (WithBounds $ Assoc TermFun)) -> TermFun
  mkTup xs =
    MkParseFun (\mode, tyCtx, tmCtx =>
      Tup xs.bounds <$> (parseRow3 xs.val).try mode tyCtx tmCtx)

PrefixTerm : InkyParser False [<"openTerm" :- TermFun] [<] TermFun
PrefixTerm =
  Fix "prefixTerm" $ OneOf
    [ mkRoll <$> WithBounds (match Tilde **> Var (%%% "prefixTerm"))
    , mkUnroll <$> WithBounds (match Bang **> Var (%%% "prefixTerm"))
    , mkQuote <$> WithBounds (match Backtick **> Var (%%% "prefixTerm"))
    , mkUnquote <$> WithBounds (match Comma **> Var (%%% "prefixTerm"))
    , rename (Drop Id) Id AtomTerm
    ]
  where
  mkRoll : WithBounds TermFun -> TermFun
  mkRoll x = MkParseFun (\mode, tyCtx, tmCtx => Roll x.bounds <$> x.val.try mode tyCtx tmCtx)

  mkUnroll : WithBounds TermFun -> TermFun
  mkUnroll x = MkParseFun (\mode, tyCtx, tmCtx => Unroll x.bounds <$> x.val.try mode tyCtx tmCtx)

  mkQuote : WithBounds TermFun -> TermFun
  mkQuote x =
    MkParseFun (\mode, tyCtx, tmCtx =>
      case mode of
        Quote ctx1 ctx2 => Errs (singleton $ NoQuoteMsg <$ x)
        Sugar ctx => QuasiQuote x.bounds <$> x.val.try (Quote tyCtx tmCtx) [<] ctx
        NoSugar => Errs (singleton $ NoSugarMsg <$ x))

  mkUnquote : WithBounds TermFun -> TermFun
  mkUnquote x =
    MkParseFun (\mode, tyCtx, tmCtx =>
      case mode of
        Quote ctx1 ctx2 =>
          case tyCtx of
            [<] => Unquote x.bounds <$> x.val.try (Sugar tmCtx) ctx1 ctx2
            _ => Errs (singleton $ "internal error 0001" <$ x)
        Sugar ctx => Errs (singleton $ NoUnquoteMsg <$ x)
        NoSugar => Errs (singleton $ NoSugarMsg <$ x))

SuffixTerm : InkyParser False [<"openTerm" :- TermFun] [<] TermFun
SuffixTerm = mkSuffix <$> Seq [ PrefixTerm , star (match Dot **> WithBounds (match TypeIdent)) ]
  where
  mkSuffix : HList [TermFun, List (WithBounds String)] -> TermFun
  mkSuffix [t, []] = t
  mkSuffix [t, prjs] =
    MkParseFun (\mode, tyCtx, tmCtx =>
      Ok $ foldl (\acc, l => Prj l.bounds acc l.val) !(t.try mode tyCtx tmCtx) prjs)

SuffixTy' : InkyParser False [<"openTerm" :- TermFun] [<] Type'Fun
SuffixTy' =
  OneOf
    [ mkTy <$> WithBounds (sub [<"openType" :- rename Id (Drop Id) OpenType] [<] AtomType)
    , mkTm <$> WithBounds (match Comma **> weaken (S Z) PrefixTerm)
    ]
  where
  mkTy : WithBounds TypeFun -> Type'Fun
  mkTy x =
    MkParseFun (\mode, tyCtx, tmCtx =>
      case mode of
        Quote ctx1 ctx2 => Errs (singleton $ NoQuoteTypesMsg <$ x)
        Sugar ctx => x.val.try tyCtx
        NoSugar => x.val.try tyCtx)

  mkTm : WithBounds TermFun -> Type'Fun
  mkTm x =
    MkParseFun (\mode, tyCtx, tmCtx =>
      case mode of
        Quote ctx1 ctx2 => x.val.try (Sugar tmCtx) ctx1 ctx2
        Sugar ctx => Errs (singleton $ NoUnquoteMsg <$ x)
        NoSugar => Errs (singleton $ NoSugarMsg <$ x))

SuffixBoundTy' : InkyParser False [<"openTerm" :- TermFun] [<] BoundType'Fun
SuffixBoundTy' =
  OneOf
    [ mkTy <$> enclose (match ParenOpen) (match ParenClose) (Seq
      [ WithBounds (match Backslash)
      , match TypeIdent
      , match DoubleArrow
      , rename Id (Drop Id) OpenType
      ])
    , mkTm <$> WithBounds (match Comma **> weaken (S Z) PrefixTerm)
    ]
  where
  mkTy : HList [WithBounds _, String, _, TypeFun] -> BoundType'Fun
  mkTy [x, n, _, a] =
    MkParseFun (\mode, tyCtx, tmCtx =>
      case mode of
        Quote ctx1 ctx2 => Errs (singleton $ NoQuoteTypesMsg <$ x)
        Sugar ctx => MkDPair n <$> a.try (tyCtx :< n)
        NoSugar => MkDPair n <$> a.try (tyCtx :< n))

  mkTm : WithBounds TermFun -> BoundType'Fun
  mkTm x =
    MkParseFun (\mode, tyCtx, tmCtx =>
      case mode of
        Quote ctx1 ctx2 => x.val.try (Sugar tmCtx) ctx1 ctx2
        Sugar ctx => Errs (singleton $ NoUnquoteMsg <$ x)
        NoSugar => Errs (singleton $ NoSugarMsg <$ x))

AppTerm : InkyParser False [<"openTerm" :- TermFun] [<] TermFun
AppTerm =
  OneOf
    [ mkInj <$> Seq
      [ WithBounds (match TypeIdent)
      , weaken (S Z) SuffixTerm
      ]
    , mkSuc <$> Seq
      [ WithBounds (match Suc)
      , weaken (S Z) SuffixTerm
      ]
    , mkCons <$> Seq
      [ WithBounds (match Cons)
      , weaken (S Z) SuffixTerm
      , weaken (S Z) SuffixTerm
      ]
    , mkApp <$> Seq
      [ OneOf
        [ WithBounds SuffixTerm
        , mkMap <$> Seq
          [ WithBounds (match Map)
          , weaken (S Z) SuffixBoundTy'
          , weaken (S Z) SuffixTy'
          , weaken (S Z) SuffixTy'
          ]
        ]
      , star (weaken (S Z) SuffixTerm)
      ]
    ]
  where
  mkInj : HList [WithBounds String, TermFun] -> TermFun
  mkInj [tag, t] =
    MkParseFun (\mode, tyCtx, tmCtx =>
      Inj tag.bounds tag.val <$> t.try mode tyCtx tmCtx)

  mkSuc : HList [WithBounds _, TermFun] -> TermFun
  mkSuc [x, t] =
    MkParseFun (\mode, tyCtx, tmCtx =>
      case mode of
        Quote ctx1 ctx2 => Errs (singleton $ NoSugarMsg <$ x)
        Sugar ctx => Suc x.bounds <$> t.try (Sugar ctx) tyCtx tmCtx
        NoSugar => Errs (singleton $ NoSugarMsg <$ x))

  mkCons : HList [WithBounds _, TermFun, TermFun] -> TermFun
  mkCons [x, t, u] =
    MkParseFun (\mode, tyCtx, tmCtx =>
      case mode of
        Quote ctx1 ctx2 => Errs (singleton $ NoSugarMsg <$ x)
        Sugar ctx =>
          [| Cons (pure x.bounds)
               (t.try (Sugar ctx) tyCtx tmCtx)
               (u.try (Sugar ctx) tyCtx tmCtx)
          |]
        NoSugar => Errs (singleton $ NoSugarMsg <$ x))

  mkMap :
    HList [WithBounds (), BoundType'Fun, Type'Fun, Type'Fun] ->
    WithBounds TermFun
  mkMap [m, a, b, c] =
    MkParseFun (\mode, tyCtx, tmCtx => do
      (a, b, c) <-
        [| (a.try mode tyCtx tmCtx, [|(b.try mode tyCtx tmCtx, c.try mode tyCtx tmCtx)|]) |]
      Ok $ Map m.bounds a b c)
    <$ m

  mkApp : HList [WithBounds TermFun, List TermFun] -> TermFun
  mkApp [t, []] = t.val
  mkApp [fun, args] =
    MkParseFun (\mode, tyCtx, tmCtx => do
      (funVal, args) <-
        [| (fun.val.try mode tyCtx tmCtx, (parseList3 args).try mode tyCtx tmCtx) |]
      Ok $ App fun.bounds funVal args)

OpenTy' : InkyParser False [<"openTerm" :- TermFun] [<] Type'Fun
OpenTy' =
  OneOf
    [ mkTy <$> WithBounds (rename (Drop Id) Id OpenType)
    , mkTm <$> WithBounds (match Comma **> weaken (S Z) PrefixTerm)
    ]
  where
  mkTy : WithBounds TypeFun -> Type'Fun
  mkTy x =
    MkParseFun (\mode, tyCtx, tmCtx =>
      case mode of
        Quote ctx1 ctx2 => Errs (singleton $ NoQuoteTypesMsg <$ x)
        Sugar ctx => x.val.try tyCtx
        NoSugar => x.val.try tyCtx)

  mkTm : WithBounds TermFun -> Type'Fun
  mkTm x =
    MkParseFun (\mode, tyCtx, tmCtx =>
      case mode of
        Quote ctx1 ctx2 => x.val.try (Sugar tmCtx) ctx1 ctx2
        Sugar ctx => Errs (singleton $ NoUnquoteMsg <$ x)
        NoSugar => Errs (singleton $ NoSugarMsg <$ x))

AnnotTerm : InkyParser False [<"openTerm" :- TermFun] [<] TermFun
AnnotTerm =
  mkAnnot <$> Seq
    [ AppTerm
    , option (match Colon **> WithBounds (weaken (S Z) OpenTy'))
    ]
  where
  mkAnnot : HList [TermFun, Maybe (WithBounds Type'Fun)] -> TermFun
  mkAnnot [t, Nothing] = t
  mkAnnot [t, Just a] = MkParseFun (\mode, tyCtx, tmCtx =>
    [| Annot (pure a.bounds) (t.try mode tyCtx tmCtx) (a.val.try mode tyCtx tmCtx) |])

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
            Seq [ match TermIdent, match Colon, weaken (S Z) OpenTy' ])
          , WithBounds (match Colon)
          , weaken (S Z) OpenTy'
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
    MkParseFun (\mode, tyCtx, tmCtx =>
      [| (\e, t => Let (AddDoc x.bounds doc) e (x.val ** t))
         (e.try mode tyCtx tmCtx)
         (t.try mode tyCtx (tmCtx :< x.val))
      |])

  mkLetType : HList [WithBounds String, (), List String, TypeFun, (), TermFun] -> TermFun
  mkLetType [x, _, doc, a, _, t] =
    MkParseFun (\mode, tyCtx, tmCtx =>
      case mode of
        Quote ctx1 ctx2 => Errs (singleton $ NoLetTyMsg <$ x)
        Sugar ctx =>
          [| (\a, t => LetTy (AddDoc x.bounds doc) a (x.val ** t))
             (a.try tyCtx)
             (t.try (Sugar ctx) (tyCtx :< x.val) tmCtx)
          |]
        NoSugar =>
          [| (\a, t => LetTy (AddDoc x.bounds doc) a (x.val ** t))
             (a.try tyCtx)
             (t.try NoSugar (tyCtx :< x.val) tmCtx)
          |])

  mkArrow : (meta : Bounds) -> List Type'Fun -> Type'Fun -> Type'Fun
  mkArrow meta [] cod = cod
  mkArrow meta (arg :: args) cod =
    let
      arrowTm :
        Term mode Bounds tyCtx tmCtx ->
        Term mode Bounds tyCtx tmCtx ->
        Term mode Bounds tyCtx tmCtx
      arrowTm =
        \t, u => Roll meta $ Inj meta "TArrow" $ Tup meta [<"Dom" :- t, "Cod" :- u]
    in
    MkParseFun (\mode, tyCtx, tmCtx =>
      case mode of
        Quote ctx1 ctx2 =>
          [| arrowTm
             (arg.try (Quote ctx1 ctx2) tyCtx tmCtx)
             ((mkArrow meta args cod).try (Quote ctx1 ctx2) tyCtx tmCtx)
          |]
        Sugar ctx =>
          [| TArrow
             (arg.try (Sugar ctx) tyCtx tmCtx)
             ((mkArrow meta args cod).try (Sugar ctx) tyCtx tmCtx)
          |]
        NoSugar =>
          [| TArrow
             (arg.try NoSugar tyCtx tmCtx)
             ((mkArrow meta args cod).try NoSugar tyCtx tmCtx)
          |])

  mkAnnot :
    HList [List (HList [String, (), Type'Fun]), WithBounds (), Type'Fun, (), List String, TermFun] ->
    WithDoc TermFun
  mkAnnot [[], m, cod, _, doc, t] =
    AddDoc
      (MkParseFun (\mode, tyCtx, tmCtx =>
        [| Annot (pure m.bounds) (t.try mode tyCtx tmCtx) (cod.try mode tyCtx tmCtx) |]))
      doc
  mkAnnot [args, m, cod, _, doc, t] =
    let bound = map (\[x, _, a] => x) args in
    let tys = map (\[x, _, a] => a) args in
    AddDoc
      (MkParseFun (\mode, tyCtx, tmCtx =>
        [| (\t, a => Annot m.bounds (Abs m.bounds (bound ** t)) a)
           (t.try mode tyCtx (tmCtx <>< bound))
           ((mkArrow m.bounds tys cod).try mode tyCtx tmCtx)
        |]))
      doc

  mkUnannot : HList [(), List String, TermFun] -> WithDoc TermFun
  mkUnannot [_, doc, e] = AddDoc e doc

AbsTerm : InkyParser False [<"openTerm" :- TermFun] [<] TermFun
AbsTerm =
  mkAbs <$> Seq
    [ WithBounds (match Backslash)
    , sepBy1 (match Comma) (match TermIdent)
    , (match DoubleArrow <||> match WaveArrow)
    , Var (%%% "openTerm")
    ]
  where
  mkAbs : HList [WithBounds (), List1 String, Either () (), TermFun] -> TermFun
  mkAbs [m, args, Left _, body] =
    MkParseFun (\mode, tyCtx, tmCtx =>
      [| (\t => Abs m.bounds (forget args ** t))
         (body.try mode tyCtx (tmCtx <>< forget args))
      |])
  mkAbs [m, args, Right _, body] =
    MkParseFun (\mode, tyCtx, tmCtx =>
      case mode of
        Quote ctx1 ctx2 => Errs (singleton $ NoQAbsMsg <$ m)
        Sugar ctx =>
          [| (\t => QAbs m.bounds (forget args ** t))
             (body.try (Sugar (ctx <>< forget args)) tyCtx tmCtx)
          |]
        NoSugar => Errs (singleton $ NoSugarMsg <$ m))

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
    Assoc
      (ParseFun [<Mode, SnocList String, SnocList String] $
       \mode, tyCtx, tmCtx => (x ** Term mode Bounds tyCtx (tmCtx :< x)))
  mkBranch [tag, bound, _, branch] =
    tag :-
    MkParseFun (\mode, tyCtx, tmCtx =>
      [| (\t => MkDPair bound t) (branch.try mode tyCtx (tmCtx :< bound)) |])

  mkCase : HList [WithBounds (), TermFun, _] -> Cases -> TermFun
  mkCase [m, target, _] branches =
    let branches = map (map mkBranch) branches in
    MkParseFun (\mode, tyCtx, tmCtx =>
      [| Case (pure m.bounds)
           (target.try mode tyCtx tmCtx)
           ((parseRow3 branches).try mode tyCtx tmCtx)
      |])

  mkFoldCase : HList [WithBounds (), TermFun, _] -> Cases -> TermFun
  mkFoldCase [m, target, _] branches =
    let branches = map (map mkBranch) branches in
    MkParseFun (\mode, tyCtx, tmCtx =>
      [| (\t, ts => Fold m.bounds t ("__tmp" ** Case m.bounds (Var m.bounds $ %% "__tmp") ts))
         (target.try mode tyCtx tmCtx)
         ((parseRow3 branches).try mode tyCtx (tmCtx :< "__tmp"))
      |])

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
    MkParseFun (\mode, tyCtx, tmCtx =>
      [| (\e, t => Fold m.bounds e (arg ** t))
         (target.try mode tyCtx tmCtx)
         (body.try mode tyCtx (tmCtx :< arg))
      |])

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
OpenTermWf : collectTypeErrs @{ListSet} [<] [<] [<] [<] OpenTerm = []
OpenTermWf = Refl
