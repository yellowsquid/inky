module Inky.Term.Substitution

import Data.List.Quantifiers
import Flap.Data.List
import Inky.Term

public export
thin : ctx1 `Thins` ctx2 -> Term mode m tyCtx ctx1 -> Term mode m tyCtx ctx2
public export
thinList : ctx1 `Thins` ctx2 -> List (Term mode m tyCtx ctx1) -> List (Term mode m tyCtx ctx2)
public export
thinAll : ctx1 `Thins` ctx2 -> Context (Term mode m tyCtx ctx1) -> Context (Term mode m tyCtx ctx2)
public export
thinAllNames :
  (f : ctx1 `Thins` ctx2) -> (ts : Context (Term mode m tyCtx ctx1)) ->
  (thinAll f ts).names = ts.names
public export
thinBranches :
  ctx1 `Thins` ctx2 ->
  Context (x ** Term mode m tyCtx (ctx1 :< x)) ->
  Context (x ** Term mode m tyCtx (ctx2 :< x))
public export
thinBranchesNames :
  (f : ctx1 `Thins` ctx2) -> (ts : Context (x ** Term mode m tyCtx (ctx1 :< x))) ->
  (thinBranches f ts).names = ts.names

thin f (Annot meta t a) = Annot meta (thin f t) a
thin f (Var meta i) = Var meta (index f i)
thin f (Let meta e (x ** t)) = Let meta (thin f e) (x ** thin (Keep f) t)
thin f (LetTy meta a (x ** t)) = LetTy meta a (x ** thin f t)
thin f (Abs meta (bound ** t)) = Abs meta (bound ** thin (f <>< lengthOf bound) t)
thin f (App meta e ts) = App meta (thin f e) (thinList f ts)
thin f (Tup meta (MkRow ts fresh)) =
  Tup meta (MkRow (thinAll f ts) (rewrite thinAllNames f ts in fresh))
thin f (Prj meta e l) = Prj meta (thin f e) l
thin f (Inj meta l t) = Inj meta l (thin f t)
thin f (Case meta t (MkRow ts fresh)) =
  Case meta (thin f t) (MkRow (thinBranches f ts) (rewrite thinBranchesNames f ts in fresh))
thin f (Roll meta t) = Roll meta (thin f t)
thin f (Unroll meta e) = Unroll meta (thin f e)
thin f (Fold meta e (x ** t)) = Fold meta (thin f e) (x ** thin (Keep f) t)
thin f (Map meta (x ** a) b c) = Map meta (x ** a) b c

thinList f [] = []
thinList f (t :: ts) = thin f t :: thinList f ts

thinAll f [<] = [<]
thinAll f (ts :< (l :- t)) = thinAll f ts :< (l :- thin f t)

thinAllNames f [<] = Refl
thinAllNames f (ts :< (l :- t)) = cong (:< l) $ thinAllNames f ts

thinBranches f [<] = [<]
thinBranches f (ts :< (l :- (x ** t))) = thinBranches f ts :< (l :- (x ** thin (Keep f) t))

thinBranchesNames f [<] = Refl
thinBranchesNames f (ts :< (l :- (x ** t))) = cong (:< l) $ thinBranchesNames f ts

public export
thinTy : ctx1 `Thins` ctx2 -> Term mode m ctx1 tmCtx -> Term mode m ctx2 tmCtx
public export
thinTyList : ctx1 `Thins` ctx2 -> List (Term mode m ctx1 tmCtx) -> List (Term mode m ctx2 tmCtx)
public export
thinTyAll : ctx1 `Thins` ctx2 -> Context (Term mode m ctx1 tmCtx) -> Context (Term mode m ctx2 tmCtx)
public export
thinTyAllNames :
  (f : ctx1 `Thins` ctx2) -> (ts : Context (Term mode m ctx1 tmCtx)) ->
  (thinTyAll f ts).names = ts.names
public export
thinTyBranches :
  ctx1 `Thins` ctx2 ->
  Context (x ** Term mode m ctx1 (tmCtx :< x)) ->
  Context (x ** Term mode m ctx2 (tmCtx :< x))
public export
thinTyBranchesNames :
  (f : ctx1 `Thins` ctx2) -> (ts : Context (x ** Term mode m ctx1 (tmCtx :< x))) ->
  (thinTyBranches f ts).names = ts.names

thinTy f (Annot meta t a) = Annot meta (thinTy f t) (rename f a)
thinTy f (Var meta i) = Var meta i
thinTy f (Let meta e (x ** t)) = Let meta (thinTy f e) (x ** thinTy f t)
thinTy f (LetTy meta a (x ** t)) = LetTy meta (rename f a) (x ** thinTy (Keep f) t)
thinTy f (Abs meta (bound ** t)) = Abs meta (bound ** thinTy f t)
thinTy f (App meta e ts) = App meta (thinTy f e) (thinTyList f ts)
thinTy f (Tup meta (MkRow ts fresh)) =
  Tup meta (MkRow (thinTyAll f ts) (rewrite thinTyAllNames f ts in fresh))
thinTy f (Prj meta e l) = Prj meta (thinTy f e) l
thinTy f (Inj meta l t) = Inj meta l (thinTy f t)
thinTy f (Case meta t (MkRow ts fresh)) =
  Case meta (thinTy f t) (MkRow (thinTyBranches f ts) (rewrite thinTyBranchesNames f ts in fresh))
thinTy f (Roll meta t) = Roll meta (thinTy f t)
thinTy f (Unroll meta e) = Unroll meta (thinTy f e)
thinTy f (Fold meta e (x ** t)) = Fold meta (thinTy f e) (x ** thinTy f t)
thinTy f (Map meta (x ** a) b c) = Map meta (x ** rename (Keep f) a) (rename f b) (rename f c)

thinTyList f [] = []
thinTyList f (t :: ts) = thinTy f t :: thinTyList f ts

thinTyAll f [<] = [<]
thinTyAll f (ts :< (l :- t)) = thinTyAll f ts :< (l :- thinTy f t)

thinTyAllNames f [<] = Refl
thinTyAllNames f (ts :< (l :- t)) = cong (:< l) $ thinTyAllNames f ts

thinTyBranches f [<] = [<]
thinTyBranches f (ts :< (l :- (x ** t))) = thinTyBranches f ts :< (l :- (x ** thinTy f t))

thinTyBranchesNames f [<] = Refl
thinTyBranchesNames f (ts :< (l :- (x ** t))) = cong (:< l) $ thinTyBranchesNames f ts

public export
Env : Mode -> Type -> SnocList String -> SnocList String -> SnocList String -> Type
Env mode m tyCtx ctx1 ctx2 = All (Assoc0 $ Either (Var ctx2) (Term mode m tyCtx ctx2)) ctx1

public export
Env' : Mode -> Type -> SnocList String -> List String -> SnocList String -> Type
Env' mode m tyCtx ctx1 ctx2 = All (Assoc0 $ Either (Var ctx2) (Term mode m tyCtx ctx2)) ctx1

public export
thinEnv :
  ctx2 `Thins` ctx3 ->
  Env mode m tyCtx ctx1 ctx2 ->
  Env mode m tyCtx ctx1 ctx3
thinEnv f = mapProperty (map $ bimap (index f) (thin $ f))

public export
lift :
  Env mode m tyCtx ctx1 ctx2 ->
  Env mode m tyCtx (ctx1 :< x) (ctx2 :< x)
lift f = thinEnv (Drop Id) f :< (x :- Left (%% x))

public export
sub :
  Env mode m tyCtx ctx1 ctx2 ->
  Term mode m tyCtx ctx1 -> Term mode m tyCtx ctx2
public export
subList :
  Env mode m tyCtx ctx1 ctx2 ->
  List (Term mode m tyCtx ctx1) -> List (Term mode m tyCtx ctx2)
public export
subAll :
  Env mode m tyCtx ctx1 ctx2 ->
  Context (Term mode m tyCtx ctx1) -> Context (Term mode m tyCtx ctx2)
public export
subAllNames :
  (f : Env mode m tyCtx ctx1 ctx2) ->
  (ts : Context (Term mode m tyCtx ctx1)) -> (subAll f ts).names = ts.names
public export
subBranches :
  Env mode m tyCtx ctx1 ctx2 ->
  Context (x ** Term mode m tyCtx (ctx1 :< x)) ->
  Context (x ** Term mode m tyCtx (ctx2 :< x))
public export
subBranchesNames :
  (f : Env mode m tyCtx ctx1 ctx2) ->
  (ts : Context (x ** Term mode m tyCtx (ctx1 :< x))) -> (subBranches f ts).names = ts.names

public export
keepBound :
  forall ctx. {0 bound : List String} ->
  LengthOf bound -> Env' mode m tyCtx bound (ctx <>< bound)
keepBound Z = []
keepBound (S len) = (_ :- Left (index (dropFish Id len) (toVar Here))) :: keepBound len

sub f (Annot meta t a) = Annot meta (sub f t) a
sub f (Var meta i) = either (Var meta) id (indexAll i.pos f).value
sub f (Let meta e (x ** t)) = Let meta (sub f e) (x ** sub (lift f) t)
sub f (LetTy meta a (x ** t)) = LetTy meta a (x ** sub (mapProperty (map $ map $ thinTy (Drop Id)) f) t)
sub f (Abs meta (bound ** t)) =
  let len = lengthOf bound in
  Abs meta (bound ** sub (thinEnv (dropFish Id len) f <>< keepBound len) t)
sub f (App meta e ts) = App meta (sub f e) (subList f ts)
sub f (Tup meta (MkRow ts fresh)) =
  Tup meta (MkRow (subAll f ts) (rewrite subAllNames f ts in fresh))
sub f (Prj meta e l) = Prj meta (sub f e) l
sub f (Inj meta l t) = Inj meta l (sub f t)
sub f (Case meta t (MkRow ts fresh)) =
  Case meta (sub f t) (MkRow (subBranches f ts) (rewrite subBranchesNames f ts in fresh))
sub f (Roll meta t) = Roll meta (sub f t)
sub f (Unroll meta e) = Unroll meta (sub f e)
sub f (Fold meta e (x ** t)) = Fold meta (sub f e) (x ** sub (lift f) t)
sub f (Map meta (x ** a) b c) = Map meta (x ** a) b c

subList f [] = []
subList f (t :: ts) = sub f t :: subList f ts

subAll f [<] = [<]
subAll f (ts :< (l :- t)) = subAll f ts :< (l :- sub f t)

subAllNames f [<] = Refl
subAllNames f (ts :< (l :- t)) = cong (:< l) $ subAllNames f ts

subBranches f [<] = [<]
subBranches f (ts :< (l :- (x ** t))) = subBranches f ts :< (l :- (x ** sub (lift f) t))

subBranchesNames f [<] = Refl
subBranchesNames f (ts :< (l :- (x ** t))) = cong (:< l) $ subBranchesNames f ts
