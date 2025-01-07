module Inky.Term.Compile

-- For DAll
import public Inky.Type.Substitution

import Data.Maybe
import Data.List.Quantifiers
import Data.Singleton
import Flap.Decidable
import Flap.Decidable.Maybe
import Inky.Term
import Inky.Term.Recompute
import Text.PrettyPrint.Prettyprinter

-- Utilities -------------------------------------------------------------------

mkLet : (bind, val, body: Doc ann) -> Doc ann
mkLet bind val body =
  parens $ align $ hang 1 $
    "let" <++> parens (group $ parens $ align $ bind <++> group val) <++>
    group body

mkAbs : (bind, body: Doc ann) -> Doc ann
mkAbs bind body =
  parens $ align $ hang 1 $
    "lambda" <++> parens bind <++>
    group body

mkTup : Context (Doc ann) -> Doc ann
mkTup parts =
  let
    f = \lx =>
      group $ parens $ align $ hang 2 $
        pretty lx.name <++> "." <++> "," <+> group lx.value
  in
  "`" <+> group (parens $ align $ concatWith (<++>) $ map f parts <>> [])

mkPrj : Doc ann -> String -> Doc ann
mkPrj x l =
  parens $ align $
    pretty "assq-ref" <++>
    group x <++>
    pretty "'" <+> pretty l

mkInj : String -> Doc ann -> Doc ann
mkInj l x =
  parens $ align $
    "cons" <++>
    "'" <+> pretty l <++>
    group x

mkCase : Doc ann -> Context (Doc ann, Doc ann) -> Doc ann
mkCase target branches =
  let
    f = \lxy =>
      group $ parens $ align $
        parens ("'" <+> pretty lxy.name <++> "." <++> fst lxy.value) <++>
        group (snd lxy.value)
  in
  parens $ align $ hang 2 $
    "match" <++>
    group target <++>
    concatWith (<++>) (map f branches <>> [])

-- Create a "unique" name from a type ------------------------------------------

hashType : Ty tyCtx -> String
hashTypes : Context (Ty tyCtx) -> List String

hashType (TVar i) = "V" ++ show i
hashType (TArrow a b) = concat ["A", hashType a, hashType b]
hashType (TProd (MkRow as _)) = concat ("P" :: hashTypes as)
hashType (TSum (MkRow as _)) = concat ("S" :: hashTypes as)
hashType (TFix x a) = concat ["F", hashType a]

hashTypes [<] = ["N"]
hashTypes (as :< (l :- a)) = ["L", l, hashType a] ++ hashTypes as

-- Compile map and fold --------------------------------------------------------

compileMap :
  {a : Ty tyCtx} ->
  (0 wf : WellFormed a) -> (i : Var tyCtx) ->
  (0 prf : i `StrictlyPositiveIn` a) ->
  (f, t : Doc ann) -> Doc ann
eagerCompileMap :
  {a : Ty tyCtx} ->
  (0 wf : WellFormed a) -> (i : Var tyCtx) ->
  (0 prf : i `StrictlyPositiveIn` a) ->
  (f, t : Doc ann) -> Doc ann
compileMapTuple :
  {as : Context (Ty tyCtx)} ->
  (0 wf : AllWellFormed as) -> (i : Var tyCtx) ->
  (0 prfs : i `StrictlyPositiveInAll` as) ->
  (f, t : Doc ann) -> All (Assoc0 $ Doc ann) as.names
compileMapCase :
  {as : Context (Ty tyCtx)} ->
  (0 wf : AllWellFormed as) -> (i : Var tyCtx) ->
  (0 prfs : i `StrictlyPositiveInAll` as) ->
  (fun : Doc ann) -> All (Assoc0 $ (Doc ann, Doc ann)) as.names

compileFold :
  {a : Ty (tyCtx :< x)} ->
  (0 wf : WellFormed a) ->
  (0 prf : %% x `StrictlyPositiveIn` a) ->
  (target, bind, body : Doc ann) -> Doc ann

compileMap wf i prf f t =
  if isJust (does $ strengthen i a)
  then t
  else eagerCompileMap wf i prf f t

eagerCompileMap (TVar {i = j}) i TVar f t with (i `decEq` j)
  _ | True `Because` _ = parens (f <++> t)
  _ | False `Because` _ = t
eagerCompileMap (TArrow _ _) i (TArrow prf) f t = t
eagerCompileMap (TProd wfs) i (TProd prfs) f t =
  mkTup $ fromAll $ compileMapTuple wfs i prfs f t
eagerCompileMap (TSum wfs) i (TSum prfs) f t =
  mkCase t $ fromAll $ compileMapCase wfs i prfs f
eagerCompileMap (TFix sp wf) i (TFix prf) f t =
  compileFold wf sp t (pretty "_eta") $
  eagerCompileMap wf (ThereVar i) prf f (pretty "_eta")

compileMapTuple [<] i [<] f t = [<]
compileMapTuple ((:<) wfs {n} wf) i (prfs :< prf) f t =
  compileMapTuple wfs i prfs f t :<
  (n :- compileMap wf i prf f (mkPrj t n))

compileMapCase [<] i [<] f = [<]
compileMapCase ((:<) wfs {n} wf) i (prfs :< prf) f =
  compileMapCase wfs i prfs f :<
  (n :- (pretty "_eta", mkInj n (compileMap wf i prf f $ pretty "_eta")))

compileFold {a} wf prf target bind body =
  let name = pretty "fold-" <+> pretty (hashType a) in
  let
    fun = parens $ align $ hang 1 $
      "define" <++> parens (name <++> name <+> "-arg") <++>
      group (mkLet bind (compileMap wf (%% x) prf name (name <+> "-arg")) body)
  in
  parens $ align $ hang 1 $
    "begin" <++>
    group fun <++>
    parens (name <++> target)

-- Compile any term ------------------------------------------------------------

export
compileSynths :
  {tmCtx : SnocList String} ->
  {t : Term NoSugar m tyCtx tmCtx} ->
  {tyEnv : All (Assoc0 $ Ty [<]) tyCtx} ->
  {tmEnv : All (Assoc0 $ Ty [<]) tmCtx} ->
  (0 tyWf : DAll WellFormed tyEnv) ->
  (0 tmWf : DAll WellFormed tmEnv) ->
  (0 _ : Synths tyEnv tmEnv t a) ->
  Doc ann
export
compileChecks :
  {tmCtx : SnocList String} ->
  {t : Term NoSugar m tyCtx tmCtx} ->
  {tyEnv : All (Assoc0 $ Ty [<]) tyCtx} ->
  {tmEnv : All (Assoc0 $ Ty [<]) tmCtx} ->
  (0 tyWf : DAll WellFormed tyEnv) ->
  (0 tmWf : DAll WellFormed tmEnv) ->
  {a : Ty [<]} ->
  (0 wf : WellFormed a) ->
  (0 _ : Checks tyEnv tmEnv a t) ->
  Doc ann
compileSpine :
  {tmCtx : SnocList String} ->
  {ts : List (Term NoSugar m tyCtx tmCtx)} ->
  {tyEnv : All (Assoc0 $ Ty [<]) tyCtx} ->
  {tmEnv : All (Assoc0 $ Ty [<]) tmCtx} ->
  (0 tyWf : DAll WellFormed tyEnv) ->
  (0 tmWf : DAll WellFormed tmEnv) ->
  {a : Ty [<]} ->
  (0 wf : WellFormed a) ->
  (0 _ : CheckSpine tyEnv tmEnv a ts b) ->
  (fun : Doc ann) ->
  Doc ann
compileAllSynths :
  {tmCtx : SnocList String} ->
  {ts : Context (Term NoSugar m tyCtx tmCtx)} ->
  {tyEnv : All (Assoc0 $ Ty [<]) tyCtx} ->
  {tmEnv : All (Assoc0 $ Ty [<]) tmCtx} ->
  (0 tyWf : DAll WellFormed tyEnv) ->
  (0 tmWf : DAll WellFormed tmEnv) ->
  (0 _ : AllSynths tyEnv tmEnv ts as) ->
  All (Assoc0 $ Doc ann) ts.names
compileAllChecks :
  {tmCtx : SnocList String} ->
  {ts : Context (Term NoSugar m tyCtx tmCtx)} ->
  {tyEnv : All (Assoc0 $ Ty [<]) tyCtx} ->
  {tmEnv : All (Assoc0 $ Ty [<]) tmCtx} ->
  (0 tyWf : DAll WellFormed tyEnv) ->
  (0 tmWf : DAll WellFormed tmEnv) ->
  {as : Context (Ty [<])} ->
  (0 fresh : AllFresh as.names) ->
  (0 wfs : AllWellFormed as) ->
  (0 _ : AllChecks tyEnv tmEnv as ts) ->
  All (Assoc0 $ Doc ann) ts.names
compileAllBranches :
  {tmCtx : SnocList String} ->
  {ts : Context (x ** Term NoSugar m tyCtx (tmCtx :< x))} ->
  {tyEnv : All (Assoc0 $ Ty [<]) tyCtx} ->
  {tmEnv : All (Assoc0 $ Ty [<]) tmCtx} ->
  (0 tyWf : DAll WellFormed tyEnv) ->
  (0 tmWf : DAll WellFormed tmEnv) ->
  {as : Context (Ty [<])} ->
  {a : Ty [<]} ->
  (0 fresh : AllFresh as.names) ->
  (0 wfs : AllWellFormed as) ->
  (0 wf : WellFormed a) ->
  (0 _ : AllBranches tyEnv tmEnv as a ts) ->
  All (Assoc0 (Doc ann, Doc ann)) ts.names

compileSynths tyWf tmWf (AnnotS wf prf) = compileChecks tyWf tmWf (subWf tyWf wf) prf
compileSynths tyWf tmWf (VarS {i}) = pretty (unVal $ nameOf i.pos)
compileSynths tyWf tmWf (LetS {x} prf1 prf2) =
  case synthsRecompute prf1 of
    Val _ =>
      mkLet (pretty x)
        (compileSynths tyWf tmWf prf1)
        (compileSynths tyWf (tmWf :< (x :- synthsWf tyWf tmWf prf1)) prf2)
compileSynths tyWf tmWf (LetTyS {x} wf prf) =
  compileSynths (tyWf :< (x :- subWf tyWf wf)) tmWf prf
compileSynths tyWf tmWf (AppS prf prfs) =
  case synthsRecompute prf of
    Val _ => compileSpine tyWf tmWf (synthsWf tyWf tmWf prf) prfs (compileSynths tyWf tmWf prf)
compileSynths tyWf tmWf (TupS prfs) = mkTup $ fromAll $ compileAllSynths tyWf tmWf prfs
compileSynths tyWf tmWf (PrjS {l} prf i) = mkPrj (compileSynths tyWf tmWf prf) l
compileSynths tyWf tmWf (UnrollS prf) = compileSynths tyWf tmWf prf
compileSynths tyWf tmWf (MapS (TFix {x} sp wf1) wf2 wf3) =
  mkAbs (pretty "_fun") $
  mkAbs (pretty "_arg") $
  compileMap wf1 (%% x) sp (pretty "_fun") (pretty "_arg")

compileChecks tyWf tmWf wf (AnnotC prf1 prf2) = compileSynths tyWf tmWf prf1
compileChecks tyWf tmWf wf (VarC prf1 prf2) = compileSynths tyWf tmWf prf1
compileChecks tyWf tmWf wf (LetC {x} prf1 prf2) =
  case synthsRecompute prf1 of
    Val _ =>
      mkLet (pretty x)
        (compileSynths tyWf tmWf prf1)
        (compileChecks tyWf (tmWf :< (x :- synthsWf tyWf tmWf prf1)) wf prf2)
compileChecks tyWf tmWf wf (LetTyC wf' {x} prf) =
  compileChecks (tyWf :< (x :- subWf tyWf wf')) tmWf wf prf
compileChecks tyWf tmWf wf (AbsC {bound} prf1 prf2) =
  case isFunctionRecompute prf1 of
    (Val _, Val _) =>
      let 0 wfs = isFunctionWf prf1 wf in
      foldr
        (mkAbs . pretty)
        (compileChecks tyWf (tmWf <>< fst wfs) (snd wfs) prf2)
        bound
compileChecks tyWf tmWf wf (AppC prf1 prf2) = compileSynths tyWf tmWf prf1
compileChecks tyWf tmWf (TProd {as = MkRow as fresh} wfs) (TupC prfs) =
  mkTup $ fromAll $ compileAllChecks tyWf tmWf fresh wfs prfs
compileChecks tyWf tmWf wf (PrjC prf1 prf2) = compileSynths tyWf tmWf prf1
compileChecks tyWf tmWf (TSum wfs) (InjC {l, as} i prf) =
  case lookupRecompute as i of
    Val i => case nameOf i of
      Val _ => mkInj l $ compileChecks tyWf tmWf (indexAllWellFormed wfs i) prf
compileChecks tyWf tmWf wf (CaseC {as = MkRow as fresh} prf prfs) =
  case synthsRecompute prf of
    Val _ =>
      let
        0 wfs : AllWellFormed as
        wfs = case synthsWf tyWf tmWf prf of TSum prfs => prfs
      in
      mkCase
        (compileSynths tyWf tmWf prf)
        (fromAll $ compileAllBranches tyWf tmWf fresh wfs wf prfs)
compileChecks tyWf tmWf (TFix {x} sp wf) (RollC prf) =
  compileChecks tyWf tmWf (subWf [<x :- TFix sp wf] wf) prf
compileChecks tyWf tmWf wf (UnrollC prf1 prf2) = compileSynths tyWf tmWf prf1
compileChecks tyWf tmWf wf (FoldC {x, a, y} prf1 prf2) =
  case synthsRecompute prf1 of
    Val (TFix x a) =>
      let
        0 spwf : (%% x `StrictlyPositiveIn` a, WellFormed a)
        spwf = case synthsWf tyWf tmWf prf1 of TFix sp wf => (sp, wf)
      in
      compileFold (snd spwf) (fst spwf)
        (compileSynths tyWf tmWf prf1)
        (pretty y)
        (compileChecks tyWf (tmWf :< (y :- (subWf [<x :- wf] $ snd spwf))) wf prf2)
compileChecks tyWf tmWf wf (MapC prf1 prf2) = compileSynths tyWf tmWf prf1

compileSpine tyWf tmWf wf [] fun = fun
compileSpine tyWf tmWf (TArrow wf1 wf2) (prf :: prfs) fun =
  let arg = compileChecks tyWf tmWf wf1 prf in
  let fun = compileSpine tyWf tmWf wf2 prfs fun in
  parens $ align $ hang 1 $ group fun <++> group arg

compileAllSynths tyWf tmWf [<] = [<]
compileAllSynths tyWf tmWf ((:<) prfs {l} prf) =
  compileAllSynths tyWf tmWf prfs :< (l :- compileSynths tyWf tmWf prf)

compileAllChecks tyWf tmWf fresh wfs Base = [<]
compileAllChecks tyWf tmWf fresh wfs (Step {l, as} i prf prfs) =
  case lookupRecompute (MkRow as fresh) i of
    Val i => case nameOf i of
      Val _ =>
        compileAllChecks tyWf tmWf (dropElemFresh as fresh i) (dropAllWellFormed wfs i) prfs :<
        (l :- compileChecks tyWf tmWf (indexAllWellFormed wfs i) prf)

compileAllBranches tyWf tmWf fresh wfs wf Base = [<]
compileAllBranches tyWf tmWf fresh wfs wf (Step {l, x, as} i prf prfs) =
  case lookupRecompute (MkRow as fresh) i of
    Val i => case nameOf i of
      Val _ =>
        compileAllBranches tyWf tmWf (dropElemFresh as fresh i) (dropAllWellFormed wfs i) wf prfs :<
        (l :- (pretty x, compileChecks tyWf (tmWf :< (x :- indexAllWellFormed wfs i)) wf prf))
