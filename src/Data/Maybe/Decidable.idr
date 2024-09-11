module Data.Maybe.Decidable

public export
data OnlyWhen : (p : a -> Type) -> Maybe a -> Type where
  RJust : forall x. (px : p x) -> p `OnlyWhen` Just x
  RNothing : (false : (x : a) -> Not (p x)) -> p `OnlyWhen` Nothing
