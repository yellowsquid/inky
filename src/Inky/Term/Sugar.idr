module Inky.Term.Sugar

import Flap.Decidable
import Inky.Term

-- Naturals --------------------------------------------------------------------

export
Zero : m -> Term mode m tyCtx tmCtx
Zero meta = Roll meta (Inj meta "Z" $ Tup meta [<])

export
Suc : m -> Term mode m tyCtx tmCtx -> Term mode m tyCtx tmCtx
Suc meta t = Roll meta (Inj meta "S" t)

export
isZero : Term mode m tyCtx tmCtx -> Bool
isZero (Roll _ (Inj _ "Z" $ Tup _ $ MkRow [<] _)) = True
isZero _ = False

export
isSuc : Term mode m tyCtx tmCtx -> Maybe (Term mode m tyCtx tmCtx)
isSuc (Roll _ (Inj _ "S" t)) = Just t
isSuc _ = Nothing

export
Lit : m -> Nat -> Term mode m tyCtx tmCtx
Lit meta 0 = Roll meta (Inj meta "Z" $ Tup meta [<])
Lit meta (S n) = Suc meta (Lit meta n)

export
isLit : Term mode m tyCtx tmCtx -> Maybe Nat
isLit t =
  if isZero t then Just 0
  else do
    u <- isSuc t
    k <- isLit (assert_smaller t u)
    pure (S k)

-- Lists -----------------------------------------------------------------------

export
Nil : m -> Term mode m tyCtx tmCtx
Nil meta = Roll meta (Inj meta "N" $ Tup meta [<])

export
Cons : m -> Term mode m tyCtx tmCtx -> Term mode m tyCtx tmCtx -> Term mode m tyCtx tmCtx
Cons meta t ts = Roll meta (Inj meta "C" $ Tup meta [<"H" :- t, "T" :- ts])

export
fromList : m -> List (Term mode m tyCtx tmCtx) -> Term mode m tyCtx tmCtx
fromList meta [] = Nil meta
fromList meta (t :: ts) = Cons meta t (fromList meta ts)

export
isNil : Term mode m tyCtx tmCtx -> Bool
isNil (Roll _ (Inj _ "N" $ Tup _ $ MkRow [<] _)) = True
isNil _ = False

export
isCons : Term mode m tyCtx tmCtx -> Maybe (Term mode m tyCtx tmCtx, Term mode m tyCtx tmCtx)
isCons (Roll _ (Inj _ "C" $ Tup meta $ MkRow [<"H" :- t, "T" :- ts] _)) = Just (t, ts)
isCons (Roll _ (Inj _ "C" $ Tup meta $ MkRow [<"T" :- ts, "H" :- t] _)) = Just (t, ts)
isCons _ = Nothing

export
isList : Term mode m tyCtx tmCtx -> Maybe (List $ Term mode m tyCtx tmCtx)
isList t =
  if isNil t then Just []
  else do
    (hd, tl) <- isCons t
    tl <- isList (assert_smaller t tl)
    pure (hd :: tl)
