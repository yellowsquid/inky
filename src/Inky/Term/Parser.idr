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
import Inky.Term.Rename
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

-- Parser ----------------------------------------------------------------------

%inline
public export
TermState : Type
TermState = (SnocList String, SnocList String)

%inline
public export
Term' : (SnocList String, SnocList String) -> Type
Term' state = Term Bounds (fst state) (snd state)

%inline
public export
Ty' : (SnocList String, SnocList String) -> Type
Ty' state = Ty (fst state)

%inline
public export
BoundTy' : (SnocList String, SnocList String) -> Type
BoundTy' state = (x ** Ty (fst state :< x))

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
mkTmVar {state = (tyCtx, tmCtx)} x =
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

AtomTerm : TermParser [<"openTerm"] [<]
AtomTerm =
  OneOf
    [ Map mkTmVar $ WithBounds (match TermIdent)
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
    , rename (Drop Id) Id AtomTerm
    ]

SuffixTerm : TermParser [<"openTerm"] [<]
SuffixTerm =
  (\[t, prjs] => foldl (\t, l => Prj l.bounds t l.val) t prjs) <$>
  Seq [PrefixTerm , star (match Dot *> WithBounds (match TypeIdent)) ]

SuffixTy' : InkyParser False [<] [<] Ty'
SuffixTy' = Forget fst $ sub [<"openType" :- OpenType] [<] AtomType

SuffixBoundTy' : InkyParser False [<] [<] BoundTy'
SuffixBoundTy' =
  enclose (match ParenOpen) (match ParenClose) $
  Forget {a = \tyCtx => (x ** Ty (tyCtx :< x))} fst $
  (\[n, t] => (n ** t)) <$>
  Seq (Update (match Backslash *> match TypeIdent <* match DoubleArrow) (Just (:<)) [OpenType])

AppTerm : TermParser [<"openTerm"] [<]
AppTerm =
  OneOf
    [ (\lt => Inj lt.bounds (fst lt.val) (snd lt.val)) <$>
      WithBounds (match TypeIdent <**> weaken (S Z) SuffixTerm)
    , (\case
        [f, []] => f.val
        [f, args] => App f.bounds f.val args) <$>
      Seq
        [ OneOf
          [ WithBounds SuffixTerm
          , (\[x, f, a, b] => Map x.bounds f a b <$ x) <$> Seq
            [ WithBounds (match Map)
            , sub [<] [<] SuffixBoundTy'
            , sub [<] [<] SuffixTy'
            , sub [<] [<] SuffixTy'
            ]
          ]
        , star (weaken (S Z) SuffixTerm)
        ]
    ]

OpenTy' : InkyParser False [<"openTerm" :- Term'] [<] Ty'
OpenTy' = Forget fst $ OpenType

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
        (Just $ \state, v => mapSnd (:< (fst v).val) state)
        [match In *> Var (%%% "openTerm")])
    , Map (mkLetTy _) $ Seq
      (Update
        (WithBounds (match TypeIdent) <**>
          uncurry (flip AddDoc) <$>
          (match Equal *> (star (match Comment) <**> Forget fst OpenType)))
        (Just $ \state, v => mapFst (:< (fst v).val) state)
        [match In *> Var (%%% "openTerm")])

    ]
  where
  AnnotSeq : List (Stage TermState)
  AnnotSeq = map (\a => MkStage a Nothing)
    [ (\s => List (String, Ty' s))
    , const (WithBounds ())
    , Ty'
    , const ()
    , const (List String)
    ]

  LetSeq : List (Stage TermState)
  LetSeq =
    [ MkStage (\s => (WithBounds String, WithDoc (Term' s)))
        (Just $ \s, v => mapSnd (:< (fst v).val) s)
    , MkStage Term' Nothing
    ]

  LetTySeq : List (Stage TermState)
  LetTySeq =
    [ MkStage (\s => (WithBounds String, WithDoc (Ty $ fst s)))
        (Just $ \s, v => mapFst (:< (fst v).val) s)
    , MkStage Term' Nothing
    ]

  GetArgs : (state : TermState) -> Sequence state AnnotSeq -> TermState
  GetArgs state [args, _, _, _, _] = mapSnd (<>< map fst args) state

  mkAnnot :
    (state : TermState) ->
    Sequence state [MkStage (flip Sequence AnnotSeq) (Just GetArgs), MkStage Term' Nothing] ->
    WithDoc (Term' state)
  mkAnnot (_, _) [[[], colon, ret, _, docs], body] =
    AddDoc (Annot colon.bounds body ret) docs
  mkAnnot (_, _) [[(arg :: args), colon, ret, _, docs], body] =
    AddDoc
      (Annot colon.bounds
        (Abs colon.bounds (fst arg :: map fst args ** body))
        (foldr TArrow ret (snd arg ::: map snd args)))
      docs

  mkLet : (state : TermState) -> Sequence state LetSeq -> Term' state
  mkLet (_, _) [(x, body), rest] = Let (AddDoc x.bounds body.doc) body.value (x.val ** rest)

  mkLetTy :
    (state : TermState) ->
    Sequence state LetTySeq ->
    Either (WithBounds InkyError) (Term' state)
  mkLetTy (_, _) [(x, ty), rest] =
    pure $ LetTy (AddDoc x.bounds ty.doc) ty.value (x.val ** rest)

AbsTerm : TermParser [<"openTerm"] [<]
AbsTerm =
  Map (mkAbs _) $
  Seq
    (Update
      (WithBounds (match Backslash *> sepBy1 (match Comma) (match TermIdent) <* match DoubleArrow))
      (Just UpdateCtx)
      [Var (%%% "openTerm")])
  where
  UpdateCtx : (state : TermState) -> (WithBounds (List1 String)) -> TermState
  UpdateCtx state args = mapSnd (<>< forget args.val) state

  mkAbs :
    (state : TermState) ->
    Sequence state
      [ MkStage (const $ (WithBounds (List1 String))) (Just UpdateCtx)
      , MkStage Term' Nothing
      ] ->
    Either (WithBounds InkyError) (Term' state)
  mkAbs (tyCtx, tmCtx) [args, body] = pure (Abs args.bounds (forget args.val ** body))

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
          (Just $ \state, x => mapSnd (:< snd x) state)
          [Var (%%% "openTerm")])))
  where
  mkCase :
    (state : TermState) ->
    WithBounds (Either (Term' state) (Term' state)) ->
    Row (x ** Term' (mapSnd (:< x) state)) ->
    Either (WithBounds InkyError) (Term' state)
  mkCase (_,_) tgt branches = case tgt.val of
    Left target => pure $ Case tgt.bounds target branches
    Right target => pure $ FoldCase tgt.bounds target branches

FoldTerm : TermParser [<"openTerm"] [<]
FoldTerm =
  mkFold _ <$>
    ( WithBounds (match Fold *> Var (%%% "openTerm") <* match By)
    <**>
      (\[x, u] => (x ** u)) <$>
      enclose (match ParenOpen) (match ParenClose)
      (Seq $ Update
        (match Backslash *> match TermIdent <* match DoubleArrow)
        (Just $ \state, x => mapSnd (:< x) state)
        [Var (%%% "openTerm")]))
  where
  mkFold :
    (state : TermState) ->
    (WithBounds (Term' state), (x ** Term' (mapSnd (:< x) state))) ->
    Term' state
  mkFold (_, _) (t, rest) = Fold t.bounds t.val rest

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
