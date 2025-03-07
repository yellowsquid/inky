module Inky.Term.Rename

import Inky.Term
import Flap.Data.List
import Flap.Data.SnocList.Thinning

public export
data Thins : Mode -> Mode -> Type where
  NoSugar : NoSugar `Thins` NoSugar
  Sugar : qtCtx1 `Thins` qtCtx2 -> Sugar qtCtx1 `Thins` Sugar qtCtx2
  Quote : ctx2 `Thins` ctx3 -> Quote ctx1 ctx2 `Thins` Quote ctx1 ctx3

export
rename :
  mode `Thins` mode' -> tmCtx `Thins` tmCtx' ->
  Term mode meta tyCtx tmCtx ->
  Term mode' meta tyCtx tmCtx'
renameList :
  mode `Thins` mode' -> tmCtx `Thins` tmCtx' ->
  List (Term mode meta tyCtx tmCtx) ->
  List (Term mode' meta tyCtx tmCtx')
renameAll :
  mode `Thins` mode' -> tmCtx `Thins` tmCtx' ->
  (ts : Context (Term mode meta tyCtx tmCtx)) ->
  All (Assoc0 $ Term mode' meta tyCtx tmCtx') ts.names
renameBranches :
  mode `Thins` mode' -> tmCtx `Thins` tmCtx' ->
  (ts : Context (x ** Term mode meta tyCtx (tmCtx :< x))) ->
  All (Assoc0 (x ** Term mode' meta tyCtx (tmCtx' :< x))) ts.names
renameTy' :
  mode `Thins` mode' -> tmCtx `Thins` tmCtx' ->
  Ty' mode meta tyCtx tmCtx ->
  Ty' mode' meta tyCtx tmCtx'
renameBoundTy' :
  mode `Thins` mode' -> tmCtx `Thins` tmCtx' ->
  BoundTy' mode meta tyCtx tmCtx ->
  BoundTy' mode' meta tyCtx tmCtx'

rename f g (Annot m e a) = Annot m (rename f g e) (renameTy' f g a)
rename f g (Var m i) = Var m (index g i)
rename f g (Let m e (x ** t)) = Let m (rename f g e) (x ** rename f (Keep g) t)
rename f g (LetTy m a (x ** t)) =
  case f of
    NoSugar => LetTy m a (x ** rename f g t)
    Sugar _ => LetTy m a (x ** rename f g t)
rename f g (Abs m (bound ** t)) = Abs m (bound ** rename f (g <>< lengthOf bound) t)
rename f g (App m e ts) = App m (rename f g e) (renameList f g ts)
rename f g (Tup m (MkRow ts fresh)) = Tup m (fromAll (renameAll f g ts) fresh)
rename f g (Prj m e l) = Prj m (rename f g e) l
rename f g (Inj m l t) = Inj m l (rename f g t)
rename f g (Case m e (MkRow ts fresh)) =
  Case m (rename f g e) (fromAll (renameBranches f g ts) fresh)
rename f g (Roll m t) = Roll m (rename f g t)
rename f g (Unroll m e) = Unroll m (rename f g e)
rename f g (Fold m e (x ** t)) = Fold m (rename f g e) (x ** rename f (Keep g) t)
rename f g (Map m a b c) = Map m (renameBoundTy' f g a) (renameTy' f g b) (renameTy' f g c)
rename (Sugar f) g (QuasiQuote m t) = QuasiQuote m (rename (Quote g) f t)
rename (Quote f) g (Unquote m t) = Unquote m (rename (Sugar g) f t)
rename (Sugar f) g (QAbs m (bound ** t)) =
  QAbs m (bound ** rename (Sugar (f <>< lengthOf bound)) g t)
rename (Sugar f) g (Lit m k) = Lit m k
rename (Sugar f) g (Suc m t) = Suc m (rename (Sugar f) g t)
rename (Sugar f) g (List m ts) = List m (renameList (Sugar f) g ts)
rename (Sugar f) g (Cons m t u) = Cons m (rename (Sugar f) g t) (rename (Sugar f) g u)
rename (Sugar f) g (Str m str) = Str m str
rename (Sugar f) g (FoldCase m e (MkRow ts fresh)) =
  FoldCase m (rename (Sugar f) g e) (fromAll (renameBranches (Sugar f) g ts) fresh)

renameList f g [] = []
renameList f g (t :: ts) = rename f g t :: renameList f g ts

renameAll f g [<] = [<]
renameAll f g (ts :< (x :- t)) = renameAll f g ts :< (x :- rename f g t)

renameBranches f g [<] = [<]
renameBranches f g (ts :< (l :- (x ** t))) =
  renameBranches f g ts :< (l :- (x ** rename f (Keep g) t))

renameTy' NoSugar g a = a
renameTy' (Sugar f) g a = a
renameTy' (Quote f) g t = rename (Sugar g) f t

renameBoundTy' NoSugar g xa = xa
renameBoundTy' (Sugar f) g xa = xa
renameBoundTy' (Quote f) g t = rename (Sugar g) f t
