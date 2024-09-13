module Inky.Parser

import Control.WellFounded
import Data.Bool
import Data.List
import Data.List.Elem
import Data.List1
import Data.Nat
import Data.So

-- Contexts --------------------------------------------------------------------

export
infix 2 :-

export
prefix 2 %%

public export
record Assoc (a : Type) where
  constructor (:-)
  0 name : String
  value : a

public export
data Context : Type -> Type where
  Lin : Context a
  (:<) : Context a -> Assoc a -> Context a

%name Context ctx

public export
data Length : Context a -> Type where
  Z : Length [<]
  S : Length ctx -> Length (ctx :< x)

%name Length len

public export
(++) : Context a -> Context a -> Context a
ctx ++ [<] = ctx
ctx ++ ctx' :< x = (ctx ++ ctx') :< x

lengthAppend : Length ctx1 -> Length ctx2 -> Length (ctx1 ++ ctx2)
lengthAppend len1 Z = len1
lengthAppend len1 (S len2) = S (lengthAppend len1 len2)

-- Variableents

public export
data VariablePos : Context a -> (0 x : String) -> a -> Type where
  [search x]
  Here : VariablePos (ctx :< (x :- v)) x v
  There : VariablePos ctx x v -> VariablePos (ctx :< y) x v

public export
record Variable (ctx : Context a) (v : a) where
  constructor (%%)
  0 name : String
  {auto pos : VariablePos ctx name v}

toVar : VariablePos ctx x v -> Variable ctx v
toVar pos = (%%) x {pos}

wknLPos : VariablePos ctx1 x v -> Length ctx2 -> VariablePos (ctx1 ++ ctx2) x v
wknLPos x Z = x
wknLPos x (S len) = There (wknLPos x len)

wknRPos : VariablePos ctx2 x v -> VariablePos (ctx1 ++ ctx2) x v
wknRPos Here = Here
wknRPos (There x) = There (wknRPos x)

splitPos : Length ctx2 -> VariablePos (ctx1 ++ ctx2) x v -> Either (VariablePos ctx1 x v) (VariablePos ctx2 x v)
splitPos Z x = Left x
splitPos (S len) Here = Right Here
splitPos (S len) (There x) = mapSnd There $ splitPos len x

wknL : {auto len : Length ctx2} -> Variable ctx1 v -> Variable (ctx1 ++ ctx2) v
wknL x = (%%) x.name {pos = wknLPos x.pos len}

wknR : Variable ctx2 v -> Variable (ctx1 ++ ctx2) v
wknR x = (%%) x.name {pos = wknRPos x.pos}

split : {auto len : Length ctx2} -> Variable (ctx1 ++ ctx2) x -> Either (Variable ctx1 x) (Variable ctx2 x)
split x = bimap toVar toVar $ splitPos len x.pos

lift :
  {auto len : Length ctx} ->
  (forall x. Variable ctx1 x -> Variable ctx2 x) ->
  Variable (ctx1 ++ ctx) x -> Variable (ctx2 ++ ctx) x
lift f = either (wknL {len} . f) wknR . split {len}

-- Environments

namespace Quantifier
  public export
  data All : (0 p : a -> Type) -> Context a -> Type where
    Lin : All p [<]
    (:<) : All p ctx -> (px : p x.value) -> All p (ctx :< x)

  %name Quantifier.All env

  indexAllPos : VariablePos ctx x v -> All p ctx -> p v
  indexAllPos Here (env :< px) = px
  indexAllPos (There x) (env :< px) = indexAllPos x env

  export
  indexAll : Variable ctx v -> All p ctx -> p v
  indexAll x env = indexAllPos x.pos env

  export
  mapProperty : ({0 x : a} -> p x -> q x) -> All p ctx -> All q ctx
  mapProperty f [<] = [<]
  mapProperty f (env :< px) = mapProperty f env :< f px

  export
  (++) : All p ctx1 -> All p ctx2 -> All p (ctx1 ++ ctx2)
  env1 ++ [<] = env1
  env1 ++ env2 :< px = (env1 ++ env2) :< px

-- Parser Expressions ----------------------------------------------------------

export
infixl 3 <**>, **>, <**
infixr 2 <||>

public export
linUnless : Bool -> Context a -> Context a
linUnless False ctx = [<]
linUnless True ctx = ctx

public export
data Parser : (i : Type) -> (nil : Bool) -> (locked, free : Context (Bool, Type)) -> Type -> Type where
  Var : (f : a -> b) -> Variable free (nil, a) -> Parser i nil locked free b
  Fail : (msg : String) -> Parser i False locked free a
  Empty : (x : a) -> Parser i True locked free a
  Lit : (text : i) -> (x : a) -> Parser i False locked free a
  (<**>) :
    {nil1, nil2 : Bool} ->
    Parser i nil1 locked free (a -> b) ->
    Parser i nil2 (linUnless nil1 locked) (free ++ linUnless (not nil1) locked) a ->
    Parser i (nil1 && nil2) locked free b
  (<|>) :
    {nil1, nil2 : Bool} ->
    Parser i nil1 locked free a -> Parser i nil2 locked free a ->
    So (not (nil1 && nil2)) =>
    Parser i (nil1 || nil2) locked free a
  Fix :
    (0 x : String) ->
    (f : a -> b) ->
    Parser i nil (locked :< (x :- (nil, a))) free a ->
    Parser i nil locked free b

%name Parser p, q

public export
Functor (Parser i nil locked free) where
  map f (Var g x) = Var (f . g) x
  map f (Fail msg) = Fail msg
  map f (Empty x) = Empty (f x)
  map f (Lit text x) = Lit text (f x)
  map f ((<**>) {nil1 = True} p q) = map (f .) p <**> q
  map f ((<**>) {nil1 = False} p q) = map (f .) p <**> q
  map f (p <|> q) = map f p <|> map f q
  map f (Fix x g p) = Fix x (f . g) p

public export
Applicative (Parser i True locked free) where
  pure = Empty
  (<*>) = (<**>)

-- Typing ----------------------------------------------------------------------

export
peek :
  (env : All (const (List i)) free) ->
  Parser i nil locked free a -> List i
peek env (Var f x) = indexAll x env
peek env (Fail msg) = []
peek env (Empty x) = []
peek env (Lit text x) = [text]
peek env ((<**>) {nil1 = False} p q) = peek env p
peek env ((<**>) {nil1 = True} p q) = peek env p ++ peek env q
peek env (p <|> q) = peek env p ++ peek env q
peek env (Fix x f p) = peek env p

export
follow :
  (penv1 : All (const (List i)) locked) ->
  (penv2 : All (const (List i)) free) ->
  (fenv1 : All (const (List i)) locked) ->
  (fenv2 : All (const (List i)) free) ->
  Parser i nil locked free a -> List i
follow penv1 penv2 fenv1 fenv2 (Var f x) = indexAll x fenv2
follow penv1 penv2 fenv1 fenv2 (Fail msg) = empty
follow penv1 penv2 fenv1 fenv2 (Empty x) = empty
follow penv1 penv2 fenv1 fenv2 (Lit text x) = empty
follow penv1 penv2 fenv1 fenv2 ((<**>) {nil1 = False} p q) =
  follow [<] (penv2 ++ penv1) [<] (fenv2 ++ fenv1) q
follow penv1 penv2 fenv1 fenv2 ((<**>) {nil1 = True} p q) =
  peek penv2 q ++
  follow penv1 penv2 fenv1 fenv2 p ++
  follow penv1 penv2 fenv1 fenv2 q
follow penv1 penv2 fenv1 fenv2 (p <|> q) =
  follow penv1 penv2 fenv1 fenv2 p ++
  follow penv1 penv2 fenv1 fenv2 q
follow penv1 penv2 fenv1 fenv2 (Fix x f p) =
  -- Conjecture: The fix point converges after one step
  -- Proof:
  --   - we always add information
  --   - no step depends on existing information
  follow (penv1 :< peek penv2 p) penv2 (fenv1 :< empty) fenv2 p

export
WellTyped :
  Eq i =>
  (penv1 : All (const (List i)) locked) ->
  (penv2 : All (const (List i)) free) ->
  (fenv1 : All (const (List i)) locked) ->
  (fenv2 : All (const (List i)) free) ->
  Parser i nil locked free a -> Type
WellTyped penv1 penv2 fenv1 fenv2 (Var f x) = ()
WellTyped penv1 penv2 fenv1 fenv2 (Fail msg) = ()
WellTyped penv1 penv2 fenv1 fenv2 (Empty x) = ()
WellTyped penv1 penv2 fenv1 fenv2 (Lit text x) = ()
WellTyped penv1 penv2 fenv1 fenv2 ((<**>) {nil1 = False} p q) =
  let set1 = follow penv1 penv2 fenv1 fenv2 p in
  let set2 = peek (penv2 ++ penv1) q in
  ( WellTyped penv1 penv2 fenv1 fenv2 p
  , WellTyped [<] (penv2 ++ penv1) [<] (fenv2 ++ fenv1) q
  , So (not $ any (`elem` set2) set1)
  )
WellTyped penv1 penv2 fenv1 fenv2 ((<**>) {nil1 = True} p q) =
  let set1 = follow penv1 penv2 fenv1 fenv2 p in
  let set2 = peek penv2 q in
  ( WellTyped penv1 penv2 fenv1 fenv2 p
  , WellTyped penv1 penv2 fenv1 fenv2 q
  , So (not $ any (`elem` set2) set1)
  )
WellTyped penv1 penv2 fenv1 fenv2 (p <|> q) =
  let set1 = peek penv2 p in
  let set2 = peek penv2 q in
  ( WellTyped penv1 penv2 fenv1 fenv2 p
  , WellTyped penv1 penv2 fenv1 fenv2 q
  , So (not $ any (`elem` set2) set1)
  )
WellTyped penv1 penv2 fenv1 fenv2 (Fix x f p) =
  let fst = peek penv2 p in
  let flw = follow (penv1 :< fst) penv2 (fenv1 :< empty) fenv2 p in
  WellTyped (penv1 :< fst) penv2 (fenv1 :< flw) fenv2 p

-- Parsing Function ------------------------------------------------------------

-- Utilty for recursion

public export
data SmallerX : Bool -> List a -> List a -> Type where
  Strict : {0 xs, ys : List a} -> xs `Smaller` ys -> SmallerX False xs ys
  Lax : {0 xs, ys : List a} -> size xs `LTE` size ys -> SmallerX True xs ys

transX :
  {xs, ys, zs : List a} ->
  SmallerX b1 xs ys -> SmallerX b2 ys zs -> SmallerX (b1 && b2) xs zs
transX (Strict prf1) (Strict prf2) = Strict (transitive prf1 (lteSuccLeft prf2))
transX (Strict prf1) (Lax prf2) = Strict (transitive prf1 prf2)
transX (Lax prf1) (Strict prf2) = Strict (transitive (LTESucc prf1) prf2)
transX (Lax prf1) (Lax prf2) = Lax (transitive prf1 prf2)

ofSmaller : {b : Bool} -> {0 xs, ys : List a} -> xs `Smaller` ys -> SmallerX b xs ys
ofSmaller {b = False} prf = Strict prf
ofSmaller {b = True} prf = Lax (lteSuccLeft prf)

wknSmallerL : SmallerX b1 xs ys -> (b2 : Bool) -> SmallerX (b1 || b2) xs ys
wknSmallerL (Strict prf) _ = ofSmaller prf
wknSmallerL (Lax prf) _ = Lax prf

wknSmallerR : (b1 : Bool) -> SmallerX b2 xs ys -> SmallerX (b1 || b2) xs ys
wknSmallerR b1 (Strict prf) = rewrite orFalseNeutral b1 in ofSmaller prf
wknSmallerR b1 (Lax prf) = rewrite orTrueTrue b1 in Lax prf

forget : SmallerX b xs ys -> SmallerX True xs ys
forget = wknSmallerR True

toSmaller : {xs, ys : List a} -> (0 _ : SmallerX False xs ys) -> xs `Smaller` ys
toSmaller {xs = []} {ys = []} (Strict prf) impossible
toSmaller {xs = []} {ys = (y :: ys)} (Strict prf) = LTESucc LTEZero
toSmaller {xs = (x :: xs)} {ys = []} (Strict prf) impossible
toSmaller {xs = (x :: xs)} {ys = (y :: ys)} (Strict (LTESucc prf)) = LTESucc (toSmaller (Strict prf))

-- Return Type

namespace M
  public export
  data M : List a -> Bool -> Type -> Type where
    Err : String -> M xs nil b
    Ok : (res : b) -> (ys : List a) -> (0 prf : SmallerX nil ys xs) -> M xs nil b

  export
  Functor (M xs nil) where
    map f (Err msg) = Err msg
    map f (Ok res ys prf) = Ok (f res) ys prf

  export
  wknL : M xs b1 a -> (b2 : Bool) -> M xs (b1 || b2) a
  wknL (Err msg) b2 = Err msg
  wknL (Ok res ys prf) b2 = Ok res ys (wknSmallerL prf b2)

  export
  wknR : (b1 : Bool) -> M xs b2 a -> M xs (b1 || b2) a
  wknR b1 (Err msg) = Err msg
  wknR b1 (Ok res ys prf) = Ok res ys (wknSmallerR b1 prf)

-- The Big Function

parser :
  Eq i => Interpolation i =>
  (p : Parser i nil locked free a) ->
  (penv1 : _) ->
  (penv2 : _) ->
  (fenv1 : _) ->
  (fenv2 : _) ->
  {auto 0 wf : WellTyped penv1 penv2 fenv1 fenv2 p} ->
  (xs : List i) ->
  All (\x => (ys : List i) -> (0 _ : SmallerX False ys xs) -> uncurry (M ys) x) locked ->
  All (\x => (ys : List i) -> (0 _ : SmallerX True ys xs) -> uncurry (M ys) x) free ->
  M xs nil a
parser (Var f x) penv1 penv2 fenv1 fenv2 xs env1 env2 =
  f <$> indexAll x env2 xs (Lax reflexive)
parser (Fail msg) penv1 penv2 fenv1 fenv2 xs env1 env2 =
  Err msg
parser (Empty x) penv1 penv2 fenv1 fenv2 xs env1 env2 =
  Ok x xs (Lax reflexive)
parser (Lit text x) penv1 penv2 fenv1 fenv2 xs env1 env2 =
  case xs of
    [] => Err "expected \{text}, got end of file"
    y :: ys =>
      if y == text
      then Ok x ys (Strict reflexive)
      else Err "expected \{text}, got \{y}"
parser ((<**>) {nil1 = False, nil2} p q) penv1 penv2 fenv1 fenv2 xs env1 env2 =
  case parser p penv1 penv2 fenv1 fenv2 xs env1 env2 of
    Err msg => Err msg
    Ok f ys lt =>
      case
        parser q [<] (penv2 ++ penv1) [<] (fenv2 ++ fenv1)
          ys
          [<]
          (  mapProperty (\f, zs, 0 prf => f zs $ forget $ transX prf lt) env2
          ++ mapProperty (\f, zs, 0 prf => f zs $ transX prf lt) env1
          )
      of
        Err msg => Err msg
        Ok x zs prf => Ok (f x) zs (rewrite sym $ andFalseFalse nil2 in transX prf lt)
parser ((<**>) {nil1 = True, nil2} p q) penv1 penv2 fenv1 fenv2 xs env1 env2 =
  case parser p penv1 penv2 fenv1 fenv2 xs env1 env2 of
    Err msg => Err msg
    Ok f ys lte =>
      case
        parser q penv1 penv2 fenv1 fenv2
          ys
          (mapProperty (\f, zs, prf => f zs $ transX prf lte) env1)
          (mapProperty (\f, zs, prf => f zs $ transX prf lte) env2)
      of
        Err msg => Err msg
        Ok x zs prf => Ok (f x) zs (rewrite sym $ andTrueNeutral nil2 in transX prf lte)
parser ((<|>) {nil1, nil2} p q) penv1 penv2 fenv1 fenv2 xs env1 env2 =
  case xs of
    [] =>
      if nil1
      then parser p penv1 penv2 fenv1 fenv2 [] env1 env2
      else if nil2
      then parser q penv1 penv2 fenv1 fenv2 [] env1 env2
      else Err "unexpected end of input"
    x :: xs =>
      if elem x (peek penv2 p)
      then wknL (parser p penv1 penv2 fenv1 fenv2 (x :: xs) env1 env2) nil2
      else if elem x (peek penv2 q)
      then wknR nil1 (parser q penv1 penv2 fenv1 fenv2 (x :: xs) env1 env2)
      else if nil1
      then parser p penv1 penv2 fenv1 fenv2 (x :: xs) env1 env2
      else if nil2
      then parser q penv1 penv2 fenv1 fenv2 (x :: xs) env1 env2
      else Err "unexpected token \{x}"
parser (Fix {a, b, nil} x f p) penv1 penv2 fenv1 fenv2 xs env1 env2 =
  let g = parser p _ _ _ _ {wf} in
  let
    res : M xs nil a
    res =
      sizeInd {P = \ys => (0 prf : SmallerX True ys xs) -> M ys nil a}
        (\ys, rec, lte =>
          g ys
            (  mapProperty (\f, zs, 0 prf => f zs $ transX prf lte) env1
            :< (\zs, prf => rec zs (toSmaller prf) (forget $ transX prf lte))
            )
            (mapProperty (\f, zs, prf => f zs $ transX prf lte) env2))
        xs
        (Lax reflexive)
  in
  f <$> res

export
parse :
  Eq i => Interpolation i =>
  (p : Parser i nil [<] [<] a) ->
  {auto 0 wf : WellTyped [<] [<] [<] [<] p} ->
  (xs : List i) -> M xs nil a
parse p xs = parser p [<] [<] [<] [<] xs [<] [<]

-- Weakening -------------------------------------------------------------------

public export
rename :
  (len1 : Length locked1) ->
  (len2 : Length locked2) ->
  (forall x. Variable locked1 x -> Variable locked2 x) ->
  (forall x. Variable free1 x -> Variable free2 x) ->
  Parser i nil locked1 free1 a -> Parser i nil locked2 free2 a
rename len1 len2 ren1 ren2 (Var f x) = Var f (ren2 x)
rename len1 len2 ren1 ren2 (Fail msg) = Fail msg
rename len1 len2 ren1 ren2 (Empty x) = Empty x
rename len1 len2 ren1 ren2 (Lit text x) = Lit text x
rename len1 len2 ren1 ren2 ((<**>) {nil1 = False} p q) =
  rename len1 len2 ren1 ren2 p <**>
  rename Z Z id (either (wknL {len = len2} . ren2) (wknR . ren1) . split) q
rename len1 len2 ren1 ren2 ((<**>) {nil1 = True} p q) =
  rename len1 len2 ren1 ren2 p <**> rename len1 len2 ren1 ren2 q
rename len1 len2 ren1 ren2 (p <|> q) =
  rename len1 len2 ren1 ren2 p <|> rename len1 len2 ren1 ren2 q
rename len1 len2 ren1 ren2 (Fix x f p) =
  Fix x f (rename (S len1) (S len2) (lift {len = S Z} ren1) ren2 p)

public export
shift :
  {auto len1 : Length locked1} ->
  (len2 : Length locked2) ->
  (len3 : Length free2) ->
  Parser i nil locked1 free1 a -> Parser i nil (locked1 ++ locked2) (free1 ++ free2) a
shift len2 len3 = rename len1 (lengthAppend len1 len2) wknL wknL

-- Combinator ------------------------------------------------------------------

public export
(<||>) :
  {nil1, nil2 : Bool} ->
  Parser i nil1 locked free a ->
  Parser i nil2 locked free b ->
  So (not (nil1 && nil2)) =>
  Parser i (nil1 || nil2) locked free (Either a b)
p <||> q = Left <$> p <|> Right <$> q

public export
(**>) :
  {nil1, nil2 : Bool} ->
  Parser i nil1 locked free a ->
  Parser i nil2 (linUnless nil1 locked) (free ++ linUnless (not nil1) locked) b ->
  Parser i (nil1 && nil2) locked free b
p **> q = (\_ => id) <$> p <**> q

public export
(<**) :
  {nil1, nil2 : Bool} ->
  Parser i nil1 locked free a ->
  Parser i nil2 (linUnless nil1 locked) (free ++ linUnless (not nil1) locked) b ->
  Parser i (nil1 && nil2) locked free a
p <** q = const <$> p <**> q

public export
match : i -> Parser i False locked free ()
match x = Lit x ()

public export
oneOf : (xs : List i) -> {auto 0 _ : NonEmpty xs} -> Parser i False locked free (x ** Elem x xs)
oneOf [x] = (x ** Here) <$ match x
oneOf (x :: xs@(_ :: _)) =
  (x ** Here) <$ match x <|>
  (\y => (y.fst ** There y.snd)) <$> oneOf xs

public export
option : Parser i False locked free a -> Parser i True locked free (Maybe a)
option p = (Just <$> p) <|> pure Nothing

public export
plus :
  {auto len : Length locked} ->
  Parser i False locked free a ->
  Parser i False locked free (List1 a)
plus p =
  Fix "plus" id
    (    (:::) <$> shift (S Z) Z p
    <**> maybe [] forget <$> option (Var id (%% "plus")))

public export
star :
  {auto len : Length locked} ->
  Parser i False locked free a ->
  Parser i True locked free (List a)
star p =
  Fix "star" id
    (maybe [] id <$> option ((::) <$> shift (S Z) Z p <**> Var id (%% "star")))
