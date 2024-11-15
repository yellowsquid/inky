module Inky.Data.Fun

import public Flap.Data.SnocList.Quantifiers
import Flap.Data.SnocList

public export
Fun : SnocList Type -> Type -> Type
Fun [<] b = b
Fun (as :< a) b = Fun as (a -> b)

public export
chain : (len : LengthOf as) -> (b -> c) -> Fun as b -> Fun as c
chain Z f x = f x
chain (S len) f g = chain len (f .) g

public export
DFun : (as : SnocList Type) -> Fun as Type -> Type
DFun [<] p = p
DFun (as :< a) p = DFun as (chain (lengthOf as) (\f => (x : a) -> f x) p)

public export
DIFun : (as : SnocList Type) -> Fun as Type -> Type
DIFun [<] p = p
DIFun (as :< a) p = DIFun as (chain (lengthOf as) (\f => {x : a} -> f x) p)

public export
curry : (len : LengthOf as) -> (HSnocList as -> b) -> Fun as b
curry Z f = f [<]
curry (S len) f = curry len (f .: (:<))

public export
uncurry : Fun as b -> HSnocList as -> b
uncurry f [<] = f
uncurry f (sx :< x) = uncurry f sx x

export
uncurryChain :
  (0 g : b -> c) -> (0 f : Fun as b) -> (xs : HSnocList as) ->
  uncurry (chain (lengthOf as) g f) xs = g (uncurry f xs)
uncurryChain g f [<] = Refl
uncurryChain g f (sx :< x) = cong (\f => f x) (uncurryChain (g .) f sx)

export
dcurry : (len : LengthOf as) -> ((xs : HSnocList as) -> uncurry p xs) -> DFun as p
dcurry Z f = f [<]
dcurry (S len) f =
  dcurry len (\sx =>
    replace {p = id} (sym $ uncurryChain (\f => (x : _) -> f x) p sx)
      (\x => f (sx :< x)))

export
duncurry : DFun as p -> (sx : HSnocList as) -> uncurry p sx
duncurry f [<] = f
duncurry f (sx :< x) =
  replace {p = id} (uncurryChain (\f => (x : _) -> f x) p sx) (duncurry f sx) x
