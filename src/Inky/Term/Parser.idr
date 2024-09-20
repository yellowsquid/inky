module Inky.Term.Parser

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
  | Backslash
  | Colon
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
  Backslash == Backslash = True
  Colon == Colon = True
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
  interpolate Backslash = "'\\'"
  interpolate Colon = "':'"
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
  tokValue Backslash = const ()
  tokValue Colon = const ()
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
  toTokenMap [(spaces, Ignore)] ++
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
    , (exact "\\", Backslash)
    , (exact ":", Colon)
    , (exact "=", Equal)
    , (exact ",", Comma)
    ]

-- Parser ----------------------------------------------------------------------

public export
InkyParser : Bool -> Context Type -> Context Type -> (a : Type) -> Type
InkyParser nil locked free a =
  Parser InkyKind nil
    (map (\a => (False, a)) locked)
    (map (\a => (False, a)) free)
    a

public export
record TypeFun where
  constructor MkTypeFun
  try : (ctx : Context ()) -> Either String (Ty ctx ())

public export
TypeParser : Context () -> Context () -> Type
TypeParser locked free =
  InkyParser False (map (const TypeFun) locked) (map (const TypeFun) free) TypeFun

Row : InkyParser True [<] [<"openType" :- TypeFun] (List $ Assoc TypeFun)
Row =
  sepBy (match Comma)
    (mkAssoc <$> Seq [match TypeIdent, match Colon, Var (%% "openType")])
  where
  mkAssoc : HList [String, (), TypeFun] -> Assoc TypeFun
  mkAssoc [x, _, v] = x :- v

tryRow : WithBounds (List $ Assoc TypeFun) -> (ctx : Context ()) -> Either String (Row (Ty ctx ()))
tryRow xs ctx =
  foldlM
    (\row, xf => do
      a <- xf.value.try ctx
      let Just row' = extend row (xf.name :- a)
        | Nothing => Left "\{xs.bounds}: duplicate name \"\{xf.name}\""
      pure row')
    [<]
    xs.val

OpenOrFixpointType : TypeParser [<] [<"openType" :- ()]
OpenOrFixpointType =
  OneOf
    [ mkFix <$>
      Seq [match Backslash, match TypeIdent, match DoubleArrow, Var (%% "openType")]
    , Var (%% "openType")
    ]
  where
  mkFix : HList [(), String, (), TypeFun] -> TypeFun
  mkFix [_, x, _, a] = MkTypeFun (\ctx => pure $ TFix x !(a.try (ctx :< (x :- ()))))

AtomType : TypeParser [<"openType" :- ()] [<]
AtomType =
  OneOf
    [
      mkVar <$> WithBounds (match TypeIdent)
    , MkTypeFun (\_ => pure TNat) <$ match Nat
    , mkProd <$> enclose (match AngleOpen) (match AngleClose) (WithBounds Row)
    , mkSum <$> enclose (match BracketOpen) (match BracketClose) (WithBounds Row)
    , enclose (match ParenOpen) (match ParenClose) OpenOrFixpointType
    ]
  where
  mkVar : WithBounds String -> TypeFun
  mkVar x =
    MkTypeFun
      (\ctx => case lookup x.val ctx of
        Just (() ** i) => pure (TVar i)
        Nothing => Left "\{x.bounds}: unbound name \"\{x.val}\"")

  mkProd : WithBounds (List $ Assoc TypeFun) -> TypeFun
  mkProd xs = MkTypeFun (\ctx => TProd <$> tryRow xs ctx)

  mkSum : WithBounds (List $ Assoc TypeFun) -> TypeFun
  mkSum xs = MkTypeFun (\ctx => TSum <$> tryRow xs ctx)

export
OpenType : TypeParser [<] [<]
OpenType =
  Fix "openType" $ mkArrow <$> sepBy1 (match Arrow) AtomType
  where
  mkArrow : List1 TypeFun -> TypeFun
  mkArrow = foldr1 (\x, y => MkTypeFun (\ctx => [| TArrow (x.try ctx) (y.try ctx) |]))

%hint
export
OpenTypeWf : So (wellTyped EqI [<] [<] [<] [<] OpenType)
OpenTypeWf = Oh
