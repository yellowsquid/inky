module Inky.Erased

public export
record Erased (t : Type) where
  constructor Forget
  0 val : t
