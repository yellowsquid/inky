module Inky.Data.SnocList.Quantifiers

import public Data.SnocList.Quantifiers

import Data.List.Quantifiers
import Inky.Data.Irrelevant
import Inky.Data.SnocList
import Inky.Data.SnocList.Elem
import Inky.Decidable

public export
(<><) : All p xs -> All p sx -> All p (xs <>< sx)
sxp <>< [] = sxp
sxp <>< (px :: pxs) = (sxp :< px) <>< pxs

public export
head : All p (sx :< x) -> p x
head (prfs :< px) = px

public export
tail : All p (sx :< x) -> All p sx
tail (prfs :< px) = prfs

public export
HSnocList : SnocList Type -> Type
HSnocList = All id

public export
all : ((x : a) -> Dec' (p x)) -> (sx : SnocList a) -> LazyEither (All p sx) (Any (Not . p) sx)
all f [<] = True `Because` [<]
all f (sx :< x) =
  map (\prfs => snd prfs :< fst prfs) (either Here There) $
  both (f x) (all f sx)

public export
irrelevant : {0 sx : SnocList a} -> All (Irrelevant . p) sx -> Irrelevant (All p sx)
irrelevant [<] = Forget [<]
irrelevant (prfs :< px) = [| irrelevant prfs :< px |]

public export
relevant : (sx : SnocList a) -> (0 prfs : All p sx) -> All (Irrelevant . p) sx
relevant [<] _ = [<]
relevant (sx :< x) prfs = relevant sx (tail prfs) :< Forget (head prfs)

public export
tabulate : LengthOf sx -> (forall x. Elem x sx -> p x) -> All p sx
tabulate Z f = [<]
tabulate (S len) f = tabulate len (f . There) :< f Here

public export
data Pairwise : (a -> a -> Type) -> SnocList a -> Type where
  Lin : Pairwise r [<]
  (:<) : Pairwise r sx -> All (flip r x) sx -> Pairwise r (sx :< x)
