module Data.These.Decidable

import Data.Bool.Decidable
import Data.These

export
viaEquivalence : a <=> b -> a `Reflects` x -> b `Reflects` x
viaEquivalence eq (RTrue x) = RTrue (eq.leftToRight x)
viaEquivalence eq (RFalse f) = RFalse (f . eq.rightToLeft)

export
reflectThese : a `Reflects` x -> b `Reflects` y -> These a b `Reflects` x || y
reflectThese (RTrue x) (RTrue y) = RTrue (Both x y)
reflectThese (RTrue x) (RFalse ny) = RTrue (This x)
reflectThese (RFalse nx) (RTrue y) = RTrue (That y)
reflectThese (RFalse nx) (RFalse ny) = RFalse (these nx ny $ const ny)
