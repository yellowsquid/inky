module Inky.OnlyWhen

import Data.DPair

public export
data OnlyWhen : Maybe a -> (a -> Type) -> Type where
  Yes : forall x. (px : p x) -> Just x `OnlyWhen` p
  No : ((x : a) -> Not (p x)) -> Nothing `OnlyWhen` p

public export
decDPair : (v **  v `OnlyWhen` p) <=> Dec (x : a ** p x)
decDPair =
  MkEquivalence
    { leftToRight = \case
      (Just x ** Yes px) => Yes (x ** px)
      (Nothing ** No prf) => No (\(x ** px) => prf x px)
    , rightToLeft = \case
      Yes (x ** px) => (Just x ** Yes px)
      No prf => (Nothing ** No (\x, px => prf (x ** px)))
    }

public export
decExists : Exists (`OnlyWhen` p) <=> Dec (Exists p)
decExists =
  MkEquivalence
    { leftToRight = \case
      Evidence .(Just x) (Yes px) => Yes (Evidence x px)
      Evidence .(Nothing) (No prf) => No (\(Evidence x px) => void (prf x px))
    , rightToLeft = \case
      Yes (Evidence x px) => Evidence (Just x) (Yes px)
      No prf => Evidence Nothing (No (\x, px => prf (Evidence x px)))
    }

public export
decSubset : Subset (Maybe a) (`OnlyWhen` p) <=> Dec (Subset a p)
decSubset =
  MkEquivalence
    { leftToRight = \case
      Element (Just x) prf => Yes (Element x (case prf of Yes px => px))
      Element Nothing prf => No (\(Element x px) => void (case prf of No prf => prf x px))
    , rightToLeft = \case
      Yes (Element x px) => Element (Just x) (Yes px)
      No prf => Element Nothing (No (\x, px => prf (Element x px)))
    }
