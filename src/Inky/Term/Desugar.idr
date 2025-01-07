module Inky.Term.Desugar

import Control.Monad.State
import Data.SortedMap
import Inky.Term

-- Other Sugar -----------------------------------------------------------------

suc : m -> Term NoSugar m tyCtx tmCtx -> Term NoSugar m tyCtx tmCtx
suc meta t = Roll meta $ Inj meta "S" t

lit : m -> Nat -> Term NoSugar m tyCtx tmCtx
lit meta 0 = Roll meta $ Inj meta "Z" $ Tup meta [<]
lit meta (S k) = suc meta (lit meta k)

cons : m -> Term NoSugar m tyCtx tmCtx -> Term NoSugar m tyCtx tmCtx -> Term NoSugar m tyCtx tmCtx
cons meta t u = Roll meta $ Inj meta "C" $ Tup meta [<"H" :- t, "T" :- u]

list : m -> List (Term NoSugar m tyCtx tmCtx) -> Term NoSugar m tyCtx tmCtx
list meta [] = Roll meta $ Inj meta "N" $ Tup meta [<]
list meta (t :: ts) = cons meta t (list meta ts)

record Cache (a : Type) where
  constructor MkCache
  max : Nat
  vals : SortedMap a Nat

miss : Ord a => a -> Cache a -> (Cache a, Nat)
miss x cache =
  let newVals = insert x cache.max cache.vals in
  let newMax = S cache.max in
  (MkCache newMax newVals, cache.max)

lookup : Ord a => MonadState (Cache a) m => a -> m Nat
lookup x = do
  cache <- get
  case lookup x cache.vals of
    Nothing => state (miss x)
    Just n => pure n

string : MonadState (Cache String) f => m -> String -> f (Term NoSugar m tyCtx tmCtx)
string meta str = do
  n <- lookup str
  pure $ lit meta n

-- Desugar ---------------------------------------------------------------------

desugar' :
  MonadState (Cache String) f =>
  Term (Sugar qtCtx) m tyCtx tmCtx -> f (Term NoSugar m tyCtx tmCtx)
desugarAll :
  MonadState (Cache String) f =>
  List (Term (Sugar qtCtx) m tyCtx tmCtx) ->
  f (List $ Term NoSugar m tyCtx tmCtx)
desugarCtx :
  MonadState (Cache String) f =>
  (ctx : Context (Term (Sugar qtCtx) m tyCtx tmCtx)) ->
  f (All (Assoc0 $ Term NoSugar m tyCtx tmCtx) ctx.names)
desugarBranches :
  MonadState (Cache String) f =>
  (ctx : Context (x ** Term (Sugar qtCtx) m tyCtx (tmCtx :< x))) ->
  f (All (Assoc0 (x ** Term NoSugar m tyCtx (tmCtx :< x))) ctx.names)

quote :
  MonadState (Cache String) f =>
  Term (Quote tyCtx tmCtx) m [<] qtCtx ->
  f (Term NoSugar m tyCtx tmCtx)
quoteAll :
  MonadState (Cache String) f =>
  List (Term (Quote tyCtx tmCtx) m [<] qtCtx) ->
  f (List $ Term NoSugar m tyCtx tmCtx)
quoteCtx :
  MonadState (Cache String) f =>
  (meta : m) =>
  Context (Term (Quote tyCtx tmCtx) m [<] qtCtx) ->
  f (List $ Term NoSugar m tyCtx tmCtx)
quoteBranches :
  MonadState (Cache String) f =>
  (meta : m) =>
  Context (x ** Term (Quote tyCtx tmCtx) m [<] (qtCtx :< x)) ->
  f (List $ Term NoSugar m tyCtx tmCtx)

desugar' (Annot meta t a) =
  let f = \t => Annot meta t a in
  [| f (desugar' t) |]
desugar' (Var meta i) = pure (Var meta i)
desugar' (Let meta e (x ** t)) =
  let f = \e, t => Let meta e (x ** t) in
  [| f (desugar' e) (desugar' t) |]
desugar' (LetTy meta a (x ** t)) =
  let f = \t => LetTy meta a (x ** t) in
  [| f (desugar' t) |]
desugar' (Abs meta (bound ** t)) =
  let f = \t => Abs meta (bound ** t) in
  [| f (desugar' t) |]
desugar' (App meta e ts) =
  let f = \e, ts => App meta e ts in
  [| f (desugar' e) (desugarAll ts) |]
desugar' (Tup meta (MkRow ts fresh)) =
  let f = \ts => Tup meta (fromAll ts fresh) in
  [| f (desugarCtx ts) |]
desugar' (Prj meta e l) =
  let f = \e => Prj meta e l in
  [| f (desugar' e) |]
desugar' (Inj meta l t) =
  let f = Inj meta l in
  [| f (desugar' t) |]
desugar' (Case meta e (MkRow ts fresh)) =
  let f = \e, ts => Case meta e (fromAll ts fresh) in
  [| f (desugar' e) (desugarBranches ts) |]
desugar' (Roll meta t) =
  let f = Roll meta in
  [| f (desugar' t) |]
desugar' (Unroll meta e) =
  let f = Unroll meta in
  [| f (desugar' e) |]
desugar' (Fold meta e (x ** t)) =
  let f = \e, t => Fold meta e (x ** t) in
  [| f (desugar' e) (desugar' t) |]
desugar' (Map meta (x ** a) b c) = pure $ Map meta (x ** a) b c
desugar' (QuasiQuote meta t) = quote t
desugar' (QAbs meta (bound ** t)) = desugar' t
desugar' (Lit meta k) = pure $ lit meta k
desugar' (Suc meta t) =
  let f = suc meta in
  [| f (desugar' t) |]
desugar' (List meta ts) =
  let f = list meta in
  [| f (desugarAll ts) |]
desugar' (Cons meta t u) =
  let f = cons meta in
  [| f (desugar' t) (desugar' u) |]
desugar' (Str meta str) = string meta str

desugarAll [] = pure []
desugarAll (t :: ts) = [| desugar' t :: desugarAll ts |]

desugarCtx [<] = pure [<]
desugarCtx (ts :< (l :- t)) =
  let f = \ts, t => ts :< (l :- t) in
  [| f (desugarCtx ts) (desugar' t) |]

desugarBranches [<] = pure [<]
desugarBranches (ts :< (l :- (x ** t))) =
  let f = \ts, t => ts :< (l :- (x ** t)) in
  [| f (desugarBranches ts) (desugar' t) |]

quote (Annot meta t a) =
  let f = \t, a => Roll meta $ Inj meta "Annot" $ Tup meta [<"Body" :- t, "Ty" :- a] in
  [| f (quote t) (desugar' a) |]
quote (Var meta i) = pure $ Roll meta $ Inj meta "Var" $ lit meta (elemToNat i.pos)
quote (Let meta e (x ** t)) =
  let
    f = \e, t =>
      Roll meta.value $ Inj meta.value "Let" $
      Tup meta.value [<"Value" :- e, "Body" :- t]
  in
  [| f (quote e) (quote t) |]
quote (Abs meta (bound ** t)) =
  let
    f = \t => Roll meta $ Inj meta "Abs" $
    Tup meta [<"Bound" :- lit meta (length bound), "Body" :- t]
  in
  [| f (quote t) |]
quote (App meta e ts) =
  let
    f = \e, ts =>
      Roll meta $ Inj meta "App" $
      Tup meta [<"Fun" :- e, "Args" :- list meta ts]
  in
  [| f (quote e) (quoteAll ts) |]
quote (Tup meta (MkRow ts _)) =
  let f = Roll meta . Inj meta "Tup" . list meta in
  [| f (quoteCtx ts) |]
quote (Prj meta e l) =
  let f = \e, l => Roll meta $ Inj meta "Prj" $ Tup meta [<"Target" :- e, "Label" :- l] in
  [| f (quote e) (string meta l) |]
quote (Inj meta l t) =
  let f = \t, l => Roll meta $ Inj meta "Inj" $ Tup meta [<"Value" :- t, "Label" :- l] in
  [| f (quote t) (string meta l) |]
quote (Case meta e (MkRow ts _)) =
  let
    f = \e, ts =>
      Roll meta $ Inj meta "Case" $
      Tup meta [<"Target" :- e, "Branches" :- list meta ts]
  in
  [| f (quote e) (quoteBranches ts) |]
quote (Roll meta t) =
  let f = Roll meta . Inj meta "Roll" in
  [| f (quote t) |]
quote (Unroll meta e) =
  let f = Roll meta . Inj meta "Unroll" in
  [| f (quote e) |]
quote (Fold meta e (x ** t)) =
  let f = \e, t => Roll meta $ Inj meta "Fold" $ Tup meta [<"Target" :- e, "Body" :- t] in
  [| f (quote e) (quote t) |]
quote (Map meta a b c) =
  let
    f = \a, b, c =>
      Roll meta $ Inj meta "Map" $
      Tup meta [<"Functor" :- a, "Source" :- b, "Target" :- c]
  in
  [| f (desugar' a) (desugar' b) (desugar' c) |]
quote (Unquote meta t) = desugar' t

quoteAll [] = pure []
quoteAll (t :: ts) = [| quote t :: quoteAll ts |]

quoteCtx [<] = pure []
quoteCtx (ts :< (l :- t)) =
  let f = \ts, l, t => Tup meta [<"Label" :- l, "Value" :- t] :: ts in
  [| f (quoteCtx ts) (string meta l) (quote t) |]

quoteBranches [<] = pure []
quoteBranches (ts :< (l :- (x ** t))) =
  let f = \ts, l, t => Tup meta [<"Label" :- l, "Body" :- t] :: ts in
  [| f (quoteBranches ts) (string meta l) (quote t) |]

export
desugar : Term (Sugar qtCtx) m tyCtx tmCtx -> Term NoSugar m tyCtx tmCtx
desugar t =
  let
    cache : Cache String
    cache = MkCache {max = 0, vals = empty}
  in
  evalState cache (desugar' t)
