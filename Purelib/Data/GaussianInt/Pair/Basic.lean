module

public import Purelib.Data.GaussianInt.Fraction.Basic

meta import Purelib.Elab.Deriving.Repr
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data.GaussianInt.Fraction.Basic

public section
namespace Purelib.Data.GaussianInt.Pair.Basic

set_option genInjectivity false in
/-- Retain an integral numerator and denominator as an ordered Gaussian-integer pair.

Both original coordinates are executable data. The record does not require a nonzero
denominator, so it also represents boundary pairs used in finite recurrences. -/
structure ConvergentPair where
  /-- The retained integral numerator coordinate. -/ numerator : Data.GaussianInt.Fraction.Basic.Integer
  /-- The retained integral denominator coordinate, which may be zero. -/
  denominator : Data.GaussianInt.Fraction.Basic.Integer
deriving DecidableEq

constructive_injectivity ConvergentPair

derive_exposed_repr ConvergentPair

end Purelib.Data.GaussianInt.Pair.Basic
end
