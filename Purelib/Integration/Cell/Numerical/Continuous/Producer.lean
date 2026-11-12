module
public import Purelib.Integration.Cell.Numerical.Continuous
public import Purelib.Integration.Cell.Numerical.Producer

/-! The effective numerical constructor supplies the persistent source producer. -/

public section

namespace Purelib.Integration.NumericalFrontier.Continuous

open Purelib.Approximation
open Purelib.Data.Rat

/-- Use the actual numerical continuous construction for persistent source requests. -/
@[expose] def producer {source : Fraction.Rational → BoundProcess} (modulus : Rational.Uniform.Numerical source) :
    NumericalFrontier.Producer source where
  Output := Result modulus
  request := build modulus
  frontier := Result.frontier
  accurate := fun request => (build modulus request).accurate
  CachedOutput := CachedResult modulus
  requestCached := CachedResult.build modulus
  cachedFrontier := CachedResult.frontier
  cachedAccurate := fun cached request => (CachedResult.build modulus cached request).accurate

end Purelib.Integration.NumericalFrontier.Continuous

end
