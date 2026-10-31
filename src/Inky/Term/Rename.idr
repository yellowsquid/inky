module Inky.Term.Rename

import Inky.Term
import Flap.Data.List
import Flap.Data.SnocList.Thinning

export
rename :
  tmCtx `Thins` tmCtx' ->
  Term meta tyCtx tmCtx ->
  Term meta tyCtx tmCtx'
renameList :
  tmCtx `Thins` tmCtx' ->
  List (Term meta tyCtx tmCtx) ->
  List (Term meta tyCtx tmCtx')
renameAll :
  tmCtx `Thins` tmCtx' ->
  (ts : Context (Term meta tyCtx tmCtx)) ->
  All (Assoc0 $ Term meta tyCtx tmCtx') ts.names
renameBranches :
  tmCtx `Thins` tmCtx' ->
  (ts : Context (x ** Term meta tyCtx (tmCtx :< x))) ->
  All (Assoc0 (x ** Term meta tyCtx (tmCtx' :< x))) ts.names

rename g (Annot m e a) = Annot m (rename g e) a
rename g (Var m i) = Var m (index g i)
rename g (Let m e (x ** t)) = Let m (rename g e) (x ** rename (Keep g) t)
rename g (LetTy m a (x ** t)) = LetTy m a (x ** rename g t)
rename g (Abs m (bound ** t)) = Abs m (bound ** rename (g <>< lengthOf bound) t)
rename g (App m e ts) = App m (rename g e) (renameList g ts)
rename g (Tup m (MkRow ts fresh)) = Tup m (fromAll (renameAll g ts) fresh)
rename g (Prj m e l) = Prj m (rename g e) l
rename g (Inj m l t) = Inj m l (rename g t)
rename g (Case m e (MkRow ts fresh)) =
  Case m (rename g e) (fromAll (renameBranches g ts) fresh)
rename g (Roll m t) = Roll m (rename g t)
rename g (Unroll m e) = Unroll m (rename g e)
rename g (Fold m e (x ** t)) = Fold m (rename g e) (x ** rename (Keep g) t)
rename g (Map m a b c) = Map m a b c
rename g (FoldCase m e (MkRow ts fresh)) =
  FoldCase m (rename g e) (fromAll (renameBranches g ts) fresh)

renameList g [] = []
renameList g (t :: ts) = rename g t :: renameList g ts

renameAll g [<] = [<]
renameAll g (ts :< (x :- t)) = renameAll g ts :< (x :- rename g t)

renameBranches g [<] = [<]
renameBranches g (ts :< (l :- (x ** t))) =
  renameBranches g ts :< (l :- (x ** rename (Keep g) t))
