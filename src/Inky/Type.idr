module Inky.Type

import Data.Bool.Decidable
import public Data.DPair
import public Data.List.Quantifiers
import Inky.Binding
import Inky.Env
import Inky.Kind
import Inky.OnlyWhen

namespace Raw
  public export
  data RawSTy : World -> Type

  public export
  data RawCTy : World -> Type

  data RawSTy where
    TVar : (x : Name w) -> RawSTy w
    TNat : RawSTy w
    TArrow : RawCTy w -> RawCTy w -> RawSTy w
    TSum : List (RawCTy w) -> RawSTy w
    TProd : List (RawCTy w) -> RawSTy w
    TApp : RawSTy w -> RawCTy w -> RawSTy w
    TAnnot : RawCTy w -> Kind -> RawSTy w

  data RawCTy where
    TFix : (x : Binder) -> RawCTy (w :< x) -> RawCTy w
    TEmbed : RawSTy w -> RawCTy w

public export
data SynthKind : Env Kind w -> RawSTy w -> Kind -> Type where
public export
data CheckKind : Env Kind w -> Kind -> RawCTy w -> Type where

data SynthKind where
  TVar : SynthKind env (TVar x) (lookup env x)
  TNat : SynthKind env TNat KStar
  TArrow : CheckKind env KStar t -> CheckKind env KStar u -> SynthKind env (t `TArrow` u) KStar
  TSum : All (CheckKind env KStar) ts -> SynthKind env (TSum ts) KStar
  TProd : All (CheckKind env KStar) ts -> SynthKind env (TProd ts) KStar
  TApp : SynthKind env f (k `KArrow` j) -> CheckKind env k t -> SynthKind env (f `TApp` t) j
  TAnnot : CheckKind env k t -> SynthKind env (TAnnot t k) k

data CheckKind where
  TFix : CheckKind (env :< (x :~ k)) k t -> CheckKind env k (TFix x t)
  TEmbed : SynthKind env a j -> k = j -> CheckKind env k (TEmbed a)

export
synthKindUniq : SynthKind env t k -> SynthKind env t j -> k = j
synthKindUniq TVar TVar = Refl
synthKindUniq TNat TNat = Refl
synthKindUniq (TArrow p1 p2) (TArrow p3 p4) = Refl
synthKindUniq (TSum ps1) (TSum ps2) = Refl
synthKindUniq (TProd ps1) (TProd ps2) = Refl
synthKindUniq (TApp p1 p2) (TApp p3 p4) = case (synthKindUniq p1 p3) of Refl => Refl
synthKindUniq (TAnnot p1) (TAnnot p2) = Refl

export
synthKind : (env : Env Kind w) -> (a : RawSTy w) -> Maybe Kind
export
checkKind : (env : Env Kind w) -> (k : Kind) -> (t : RawCTy w) -> Bool

checkAllKinds : (env : Env Kind w) -> (k : Kind) -> (ts : List (RawCTy w)) -> Bool

synthKind env (TVar x) = Just (lookup env x)
synthKind env TNat = Just KStar
synthKind env (TArrow t u) = do
  guard (checkKind env KStar t)
  guard (checkKind env KStar u)
  Just KStar
synthKind env (TSum ts) = do
  guard (checkAllKinds env KStar ts)
  Just KStar
synthKind env (TProd ts) = do
  guard (checkAllKinds env KStar ts)
  Just KStar
synthKind env (TApp f t) = do
  dom `KArrow` cod <- synthKind env f
    | _ => Nothing
  guard (checkKind env dom t)
  Just cod
synthKind env (TAnnot t k) = do
  guard (checkKind env k t)
  Just k

checkKind env k (TFix x t) = checkKind (env :< (x :~ k)) k t
checkKind env k (TEmbed a) =
  case synthKind env a of
    Nothing => False
    Just k' => k == k'

checkAllKinds env k [] = True
checkAllKinds env k (t :: ts) = checkKind env k t && checkAllKinds env k ts

export
synthKindPrf : (env : Env Kind w) -> (a : RawSTy w) -> synthKind env a `OnlyWhen` SynthKind env a
export
checkKindPrf : (env : Env Kind w) -> (k : Kind) -> (t : RawCTy w) -> CheckKind env k t `Reflects` checkKind env k t
checkAllKindsPrf :
  (env : Env Kind w) -> (k : Kind) ->
  (ts : List (RawCTy w)) -> All (CheckKind env k) ts `Reflects` checkAllKinds env k ts

synthKindPrf env (TVar x) = Yes TVar
synthKindPrf env TNat = Yes TNat
synthKindPrf env (TArrow t u) with (checkKindPrf env KStar t) | (checkKind env KStar t)
  _ | RTrue tStar | _ with (checkKindPrf env KStar u) | (checkKind env KStar u)
    _ | RTrue uStar | _ = Yes (TArrow tStar uStar)
    _ | RFalse uUnstar | _ = No (\_ => \case TArrow _ uStar => uUnstar uStar)
  _ | RFalse tUnstar | _ = No (\_ => \case TArrow tStar _ => tUnstar tStar)
synthKindPrf env (TSum ts) with (checkAllKindsPrf env KStar ts) | (checkAllKinds env KStar ts)
  _ | RTrue tsStar | _ = Yes (TSum tsStar)
  _ | RFalse tsUnstar | _ = No (\_ => \case TSum tsStar => tsUnstar tsStar)
synthKindPrf env (TProd ts) with (checkAllKindsPrf env KStar ts) | (checkAllKinds env KStar ts)
  _ | RTrue tsStar | _ = Yes (TProd tsStar)
  _ | RFalse tsUnstar | _ = No (\_ => \case TProd tsStar => tsUnstar tsStar)
synthKindPrf env (TApp f t) with (synthKindPrf env f) | (synthKind env f)
  _ | Yes fArrow | Just (KArrow dom cod) with (checkKindPrf env dom t) | (checkKind env dom t)
    _ | RTrue uDom | _ = Yes (TApp fArrow uDom)
    _ | RFalse uUndom | _ =
      No (\_ => \case
        TApp fKind uDom => case synthKindUniq fArrow fKind of
          Refl => uUndom uDom)
  _ | Yes fStar | Just KStar = No (\_ => \case TApp fArrow _ => absurd (synthKindUniq fStar fArrow))
  _ | No fUnkind | Nothing = No (\_ => \case TApp fKind _ => void (fUnkind _ fKind))
synthKindPrf env (TAnnot t k) with (checkKindPrf env k t) | (checkKind env k t)
  _ | RTrue tKind | _ = Yes (TAnnot tKind)
  _ | RFalse tUnkind | _ = No (\_ => \case TAnnot tKind => tUnkind tKind)

checkKindPrf env k (TFix x t) with (checkKindPrf (env :< (x :~ k)) k t) | (checkKind (env :< (x :~ k)) k t)
  _ | RTrue tKind | _ = RTrue (TFix tKind)
  _ | RFalse tUnkind | _ = RFalse (\case TFix tKind => tUnkind tKind)
checkKindPrf env k (TEmbed a) with (synthKindPrf env a) | (synthKind env a)
  _ | Yes aKind | Just k' with (decEqReflects k k') | (k == k')
    _ | RTrue eq | _ = RTrue (TEmbed aKind eq)
    _ | RFalse neq | _ = RFalse (\case TEmbed aKind' eq => neq $ trans eq $ synthKindUniq aKind' aKind)
  _ | No aUnkind | _ = RFalse (\case TEmbed aKind Refl => aUnkind _ aKind)

checkAllKindsPrf env k [] = RTrue []
checkAllKindsPrf env k (t :: ts) with (checkKindPrf env k t) | (checkKind env k t)
  _ | RFalse tUnkind | _ = RFalse (\case (tKind :: _) => tUnkind tKind)
  _ | RTrue tKind | _  with (checkAllKindsPrf env k ts) | (checkAllKinds env k ts)
    _ | RTrue tsKinds | _ = RTrue (tKind :: tsKinds)
    _ | RFalse tsUnkinds | _ = RFalse (\case (_ :: tsKinds) => tsUnkinds tsKinds)

public export
ATy : {w : World} -> Env Kind w -> Type
ATy env = Subset (RawCTy w) (CheckKind env KStar)
