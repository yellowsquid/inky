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
data InkyError : Type where
  UnboundTyVar : String -> SnocList String -> InkyError
  UnboundTmVar : String -> SnocList String -> InkyError
  DuplicateLabel : String -> SnocList String -> InkyError
  NeedsSugar : Mode -> InkyError
  NeedsQuote : Mode -> InkyError
  NoQuotedTypes : InkyError

-- Parser ----------------------------------------------------------------------

%inline
public export
TermState : Type
TermState = (Mode, SnocList String, SnocList String)

%inline
public export
Term' : (Mode, SnocList String, SnocList String) -> Type
Term' state = Term (fst state) Bounds (fst $ snd state) (snd $ snd state)

%inline
public export
InkyParser :
  {state : Type} -> (nil : Bool) ->
  (locked, free : Context (state -> Type)) -> (a : state -> Type) -> Type
InkyParser nil locked free a =
  Parser state (WithBounds InkyError) InkyKind nil
    (map (map (False,)) locked)
    (map (map (False,)) free)
    a

%inline
public export
TypeParser : SnocList String -> SnocList String -> Type
TypeParser locked free = InkyParser False (map (:- Ty) locked) (map (:- Ty) free) Ty

%inline
public export
TermParser : SnocList String -> SnocList String -> Type
TermParser locked free = InkyParser False (map (:- Term') locked) (map (:- Term') free) Term'

mkTyVar : {ctx : _} -> WithBounds String -> Either (WithBounds InkyError) (Ty ctx)
mkTyVar x =
  case Var.lookup x.val ctx of
    Just i => pure (TVar i)
    Nothing => Left (UnboundTyVar x.val ctx <$ x)

mkTmVar :
  {state : _} ->
  WithBounds String ->
  Either (WithBounds InkyError) (Term' state)
mkTmVar {state = (mode, tyCtx, tmCtx)} x =
  case Var.lookup x.val tmCtx of
    Just i => pure (Var x.bounds i)
    Nothing => Left (UnboundTmVar x.val tmCtx <$ x)

RowOf :
  (0 free : Context (state -> Type)) ->
  InkyParser False [<] free a ->
  InkyParser True [<] free (List . WithBounds . Assoc . a)
RowOf free p =
  sepBy (match Semicolon)
    (WithBounds $ (\[x, _, v] => x :- v) <$> Seq [match TypeIdent, match Colon, p])

mkRow :
  List (WithBounds $ Assoc a) ->
  Either (WithBounds InkyError) (Row a)
mkRow =
  foldlM
    (\row, x => case extend row x.val of
      Just row => pure row
      Nothing => Left (DuplicateLabel x.val.name row.names <$ x))
    [<]

-- Types -----------------------------------------------------------------------

AtomType : TypeParser [<"openType"] [<]
AtomType =
  OneOf
    [ Map mkTyVar $ WithBounds (match TypeIdent)
    , TNat <$ match Nat
    , TProd <$> enclose (match AngleOpen) (match AngleClose) row
    , TSum <$> enclose (match BracketOpen) (match BracketClose) row
    , enclose (match ParenOpen) (match ParenClose) (Var (%%% "openType"))
    ]
  where
  row : InkyParser True [<] [<"openType" :- Ty] (Row . Ty)
  row = Map mkRow $ RowOf [<"openType" :- Ty] $ Var (%%% "openType")

AppType : TypeParser [<"openType"] [<]
AppType =
  OneOf
    [ AtomType
    , match List *> TList <$> weaken (S Z) AtomType
    , match Data *> (\[x, t] => TFix x t) <$>
        Seq (Update (match TypeIdent) (Just (:<)) [weaken (S Z) AtomType])
    ]
  where

export
OpenType : TypeParser [<] [<]
OpenType =
  Fix "openType" $ foldr1 TArrow <$> sepBy1 (match Arrow) AppType

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

Type' : (Mode, SnocList String, SnocList String) -> Type
Type' state = Ty' (fst state) Bounds (fst $ snd state) (snd $ snd state)

BoundType' : (Mode, SnocList String, SnocList String) -> Type
BoundType' state = BoundTy' (fst state) Bounds (fst $ snd state) (snd $ snd state)

sugarOnly :
  (0 a, b : (Mode, SnocList String, SnocList String) -> Type) ->
  ({qtCtx, tyCtx, tmCtx : _} ->
    WithBounds (a (Sugar qtCtx, tyCtx, tmCtx)) ->
    b (Sugar qtCtx, tyCtx, tmCtx)) ->
  {state : _} -> WithBounds (a state) -> Either (WithBounds InkyError) (b state)
sugarOnly a b f {state = (Sugar qtCtx, tyCtx, tmCtx)} x = pure (f x)
sugarOnly a b f {state = (mode, tyCtx, tmCtx)} x = Left (NeedsSugar mode <$ x)

quoteOnly :
  (0 a, b : (Mode, SnocList String, SnocList String) -> Type) ->
  ({ctx1, ctx2, tmCtx : _} ->
    WithBounds (a (Quote ctx1 ctx2, [<], tmCtx)) ->
    b (Quote ctx1 ctx2, [<], tmCtx)) ->
  {state : _} -> WithBounds (a state) -> Either (WithBounds InkyError) (b state)
-- HACK: should special case for tyCtx /= [<]. But this case is "impossible", so it doesn't matter
quoteOnly a b f {state = (Quote ctx1 ctx2, [<], tmCtx)} x = pure (f x)
quoteOnly a b f {state = (mode, tyCtx, tmCtx)} x = Left (NeedsQuote mode <$ x)

forceQuote :
  (Mode, SnocList String, SnocList String) -> (Mode, SnocList String, SnocList String)
forceQuote (Sugar qtCtx, tyCtx, tmCtx) = (Quote tyCtx tmCtx, [<], qtCtx)
forceQuote state = state

forceSugar :
  (Mode, SnocList String, SnocList String) -> (Mode, SnocList String, SnocList String)
forceSugar (Quote ctx1 ctx2, tyCtx, tmCtx) = (Sugar tmCtx, ctx1, ctx2)
forceSugar state = state

embedType :
  {state : _} ->
  WithBounds (Ty (fst $ snd state)) ->
  Either (WithBounds InkyError) (Type' state)
embedType {state = (Quote ctx1 ctx2, tyCtx, tmCtx)} t = Left (NoQuotedTypes <$ t)
embedType {state = (Sugar qtCtx, tyCtx, tmCtx)} t = Right t.val
embedType {state = (NoSugar, tyCtx, tmCtx)} t = Right t.val

AtomTerm : TermParser [<"openTerm"] [<]
AtomTerm =
  OneOf
    [ Map mkTmVar $ WithBounds (match TermIdent)
    , Map (sugarOnly (const String) Term' (\k => Str k.bounds k.val)) $
      WithBounds (match StringLit)
    , Map (sugarOnly (const Nat) Term' (\k => Lit k.bounds k.val)) $
      WithBounds (match Lit)
    , Map (sugarOnly (List . Term') Term' (\ts => List ts.bounds ts.val)) $ WithBounds (
        enclose (match BracketOpen) (match BracketClose) $
        sepBy (match Semicolon) $ Var (%%% "openTerm"))
    , (\row => Tup row.bounds row.val) <$> WithBounds (
        enclose (match AngleOpen) (match AngleClose) $
        Map mkRow $ RowOf [<"openTerm" :- Term'] (Var (%%% "openTerm")))
    , enclose (match ParenOpen) (match ParenClose) (Var (%%% "openTerm"))
    ]

PrefixTerm : TermParser [<"openTerm"] [<]
PrefixTerm =
  Fix "prefixTerm" $ OneOf
    [ (\t => Roll t.bounds t.val) <$> WithBounds (match Tilde *> Var (%%% "prefixTerm"))
    , (\t => Unroll t.bounds t.val) <$> WithBounds (match Bang *> Var (%%% "prefixTerm"))
    , Map (sugarOnly (Term' . forceQuote) Term' (\t => QuasiQuote t.bounds t.val)) $
        WithBounds $ (\[_, t] => t) <$>
        Seq (Update (match Backtick) (Just $ const . forceQuote) [Var (%%% "prefixTerm")])
    , Map (quoteOnly (Term' . forceSugar) Term' (\t => Unquote t.bounds t.val)) $
        WithBounds $ (\[_, t] => t) <$>
        Seq (Update (match Comma) (Just $ const . forceSugar) [Var (%%% "prefixTerm")])
    , rename (Drop Id) Id AtomTerm
    ]

SuffixTerm : TermParser [<"openTerm"] [<]
SuffixTerm =
  (\[t, prjs] => foldl (\t, l => Prj l.bounds t l.val) t prjs) <$>
  Seq [PrefixTerm , star (match Dot *> WithBounds (match TypeIdent)) ]

SuffixTy' : InkyParser False [<"openTerm" :- Term'] [<] Type'
SuffixTy' =
  OneOf
    [ Map embedType $ Forget (fst . snd) $ WithBounds $ sub [<"openType" :- OpenType] [<] AtomType
    , Map (quoteOnly (Term' . forceSugar) Type' val) $
        WithBounds $ (\[_, t] => t) <$>
        Seq (Update (match Comma) (Just $ const . forceSugar) [weaken (S Z) PrefixTerm])
    ]

SuffixBoundTy' : InkyParser False [<"openTerm" :- Term'] [<] BoundType'
SuffixBoundTy' =
  OneOf {nils = [False, False]}
    [ enclose (match ParenOpen) (match ParenClose) $
      Map embedBoundType $
      Forget (fst . snd) $
      WithBounds {a = \ctx => (x ** Ty (ctx :< x))} $
      (\[n, t] => (n ** t)) <$>
      Seq (Update (match Backslash *> match TypeIdent <* match DoubleArrow) (Just (:<)) [OpenType])
    , Map (quoteOnly (Term' . forceSugar) BoundType' val) $
        WithBounds $ (\[_, t] => t) <$>
        Seq (Update (match Comma) (Just $ const . forceSugar) [weaken (S Z) PrefixTerm])
    ]
  where
  embedBoundType :
    {state : _} ->
    WithBounds (x ** Ty (fst (snd state) :< x)) ->
    Either (WithBounds InkyError) (BoundType' state)
  embedBoundType {state = (Quote ctx1 ctx2, tyCtx, tmCtx)} t = Left (NoQuotedTypes <$ t)
  embedBoundType {state = (Sugar qtCtx, tyCtx, tmCtx)} t = Right t.val
  embedBoundType {state = (NoSugar, tyCtx, tmCtx)} t = Right t.val

AppTerm : TermParser [<"openTerm"] [<]
AppTerm =
  OneOf
    [ (\lt => Inj lt.bounds (fst lt.val) (snd lt.val)) <$>
      WithBounds (match TypeIdent <**> weaken (S Z) SuffixTerm)
    , Map (sugarOnly Term' Term' (\t => Suc t.bounds t.val)) $
      WithBounds $ match Suc *> weaken (S Z) SuffixTerm
    , Map (sugarOnly (\s => (Term' s, Term' s)) Term'
        (\tu => Cons tu.bounds (fst tu.val) (snd tu.val))) $
      WithBounds $ match Cons *> weaken (S Z) SuffixTerm <**> weaken (S Z) SuffixTerm
    , (\case
        [f, []] => f.val
        [f, args] => App f.bounds f.val args) <$>
      Seq
        [ OneOf
          [ WithBounds SuffixTerm
          , (\[x, f, a, b] => Map x.bounds f a b <$ x) <$> Seq
            [ WithBounds (match Map)
            , weaken (S Z) SuffixBoundTy'
            , weaken (S Z) SuffixTy'
            , weaken (S Z) SuffixTy'
            ]
          ]
        , star (weaken (S Z) SuffixTerm)
        ]
    ]

OpenTy' : InkyParser False [<"openTerm" :- Term'] [<] Type'
OpenTy' =
  OneOf
    [ Map embedType $ Forget (fst . snd) $ WithBounds OpenType
    , Map (quoteOnly (Term' . forceSugar) Type' val) $
      WithBounds $ (\[_, t] => t) <$>
      Seq (Update (match Comma) (Just $ const . forceSugar) [weaken (S Z) PrefixTerm])
    ]

-- Open Terms

AnnotTerm : TermParser [<"openTerm"] [<]
AnnotTerm =
  (\case
    (t, Nothing) => t
    (t, Just a) => Annot a.bounds t a.val) <$>
  (AppTerm <**> option (WithBounds $ match Colon *> weaken (S Z) OpenTy'))

LetTerm : TermParser [<"openTerm"] [<]
LetTerm =
  match Let *>
  OneOf
    [ mkLet _ <$> Seq
      (Update
        (WithBounds (match TermIdent) <**> OneOf
          [ mkAnnot _ <$>
            Seq (Update
              (Seq
                [ star (enclose (match ParenOpen) (match ParenClose)
                  (match TermIdent <* match Colon <**> weaken (S Z) OpenTy'))
                , WithBounds (match Colon)
                , weaken (S Z) OpenTy'
                , match Equal
                , star (match Comment)
                ])
              (Just GetArgs)
              [Var (%%% "openTerm")])
          , (\[_, doc, body] => AddDoc body doc) <$>
            Seq [match Equal, star (match Comment), Var (%%% "openTerm")]
          ])
        (Just $ \state, v => mapSnd (mapSnd (:< (fst v).val)) state)
        [match In *> Var (%%% "openTerm")])
    , Map (mkLetTy _) $ Seq
      (Update
        (WithBounds (match TypeIdent) <**>
          uncurry (flip AddDoc) <$>
          (match Equal *> (star (match Comment) <**> Forget (fst . snd) OpenType)))
        (Just $ \state, v => mapSnd (mapFst (:< (fst v).val)) state)
        [match In *> Var (%%% "openTerm")])

    ]
  where
  AnnotSeq : List (Stage TermState)
  AnnotSeq = map (\a => MkStage a Nothing)
    [ (\s => List (String, Type' s))
    , const (WithBounds ())
    , Type'
    , const ()
    , const (List String)
    ]

  LetSeq : List (Stage TermState)
  LetSeq =
    [ MkStage (\s => (WithBounds String, WithDoc (Term' s)))
        (Just $ \s, v => mapSnd (mapSnd (:< (fst v).val)) s)
    , MkStage Term' Nothing
    ]

  LetTySeq : List (Stage TermState)
  LetTySeq =
    [ MkStage (\s => (WithBounds String, WithDoc (Ty $ fst $ snd s)))
        (Just $ \s, v => mapSnd (mapFst (:< (fst v).val)) s)
    , MkStage Term' Nothing
    ]

  GetArgs : (state : TermState) -> Sequence state AnnotSeq -> TermState
  GetArgs state [args, _, _, _, _] = mapSnd (mapSnd (<>< map fst args)) state

  MkArrow : (meta : Bounds) -> (state : TermState) -> Type' state -> Type' state -> Type' state
  MkArrow meta (Quote ctx1 ctx2, _, _) = \dom, cod =>
    Roll meta $ Inj meta "TArrow" $ Tup meta [<"Dom" :- dom, "Cod" :- cod]
  MkArrow meta (Sugar qtCtx, _, _) = TArrow
  MkArrow meta (NoSugar, _, _) = TArrow

  mkAnnot :
    (state : TermState) ->
    Sequence state [MkStage (flip Sequence AnnotSeq) (Just GetArgs), MkStage Term' Nothing] ->
    WithDoc (Term' state)
  mkAnnot (_, _, _) [[[], colon, ret, _, docs], body] =
    AddDoc (Annot colon.bounds body ret) docs
  mkAnnot (mode, tyCtx, tmCtx) [[(arg :: args), colon, ret, _, docs], body] =
    AddDoc
      (Annot colon.bounds
        (Abs colon.bounds (fst arg :: map fst args ** body))
        (foldr (MkArrow colon.bounds (mode, tyCtx, tmCtx)) ret (snd arg ::: map snd args)))
      docs

  mkLet : (state : TermState) -> Sequence state LetSeq -> Term' state
  mkLet (_, _, _) [(x, body), rest] = Let (AddDoc x.bounds body.doc) body.value (x.val ** rest)

  mkLetTy :
    (state : TermState) ->
    Sequence state LetTySeq ->
    Either (WithBounds InkyError) (Term' state)
  mkLetTy (Quote ctx1 ctx2, _, _) [(x, ty), rest] = Left (NoQuotedTypes <$ x)
  mkLetTy (Sugar qtCtx, _, _) [(x, ty), rest] =
    pure $ LetTy (AddDoc x.bounds ty.doc) ty.value (x.val ** rest)
  mkLetTy (NoSugar, _, _) [(x, ty), rest] =
    pure $ LetTy (AddDoc x.bounds ty.doc) ty.value (x.val ** rest)

AbsTerm : TermParser [<"openTerm"] [<]
AbsTerm =
  Map (mkAbs _) $
  Seq
    (Update
      (WithBounds (match Backslash *> sepBy1 (match Comma) (match TermIdent)) <**>
        (match DoubleArrow <||> match WaveArrow))
      (Just UpdateCtx)
      [Var (%%% "openTerm")])
  where
  UpdateCtx : (state : TermState) -> (WithBounds (List1 String), Either () ()) -> TermState
  UpdateCtx state (args, Left abs) = mapSnd (mapSnd (<>< forget args.val)) state
  UpdateCtx state (args, Right quot) = case fst state of
    Sugar qtCtx => (Sugar (qtCtx <>< forget args.val), snd state)
    _ => state

  mkAbs :
    (state : TermState) ->
    Sequence state
      [ MkStage (const $ (WithBounds (List1 String), Either () ())) (Just UpdateCtx)
      , MkStage Term' Nothing
      ] ->
    Either (WithBounds InkyError) (Term' state)
  mkAbs (mode, tyCtx, tmCtx) [(args, Left abs), body] = pure (Abs args.bounds (forget args.val ** body))
  mkAbs (mode, tyCtx, tmCtx) [(args, Right quot), body] =
    case mode of
      Sugar qtCtx => pure (QAbs args.bounds (forget args.val ** body))
      _ => Left (NeedsSugar mode <$ args)

CaseTerm : TermParser [<"openTerm"] [<]
CaseTerm =
  Map (uncurry $ mkCase _) $
      WithBounds (
         (match Case *> Var (%%% "openTerm") <* match Of) <||>
         (match FoldCase *> Var (%%% "openTerm") <* match By))
  <**> Map mkRow
    (enclose (match BraceOpen) (match BraceClose)
      (sepBy (match Semicolon) $
        WithBounds $
        (\[(label, x), body] => label :- (x ** body)) <$>
        Seq (Update
          (match TypeIdent <**> match TermIdent <* match DoubleArrow)
          (Just $ \state, x => mapSnd (mapSnd (:< snd x)) state)
          [Var (%%% "openTerm")])))
  where
  mkCase :
    (state : TermState) ->
    WithBounds (Either (Term' state) (Term' state)) ->
    Row (x ** Term' (mapSnd (mapSnd (:< x)) state)) ->
    Either (WithBounds InkyError) (Term' state)
  mkCase (mode, _, _) x branches = case x.val of
    Left target => pure $ Case x.bounds target branches
    Right target => case mode of
      Sugar _ => pure $ FoldCase x.bounds target branches
      _ => Left (NeedsSugar mode <$ x)

FoldTerm : TermParser [<"openTerm"] [<]
FoldTerm =
  mkFold _ <$>
    ( WithBounds (match Fold *> Var (%%% "openTerm") <* match By)
    <**>
      (\[x, u] => (x ** u)) <$>
      enclose (match ParenOpen) (match ParenClose)
      (Seq $ Update
        (match Backslash *> match TermIdent <* match DoubleArrow)
        (Just $ \state, x => mapSnd (mapSnd (:< x)) state)
        [Var (%%% "openTerm")]))
  where
  mkFold :
    (state : TermState) ->
    (WithBounds (Term' state), (x ** Term' (mapSnd (mapSnd (:< x)) state))) ->
    Term' state
  mkFold (_, _, _) (t, rest) = Fold t.bounds t.val rest

export
OpenTerm : TermParser [<] [<]
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
