module
public import Purelib.Integration.Cell.Source.Continuous
public import Purelib.Integration.Cell.Source.Producer

/-! The effective continuous constructor supplies the shared source-frontier producer. -/

public section

namespace Purelib.Integration.SourceFrontier.Continuous

open Purelib.Approximation
open Purelib.Data.Rat

/-- Use the original continuous construction as a persistent source-frontier producer. -/
@[expose] def producer {source : Fraction.Rational → Fraction.Rational} (modulus : Rational.Uniform.Modulus source) :
    SourceFrontier.Producer source where
  Output := Result modulus
  request := build modulus
  requestCached := buildCached modulus
  requestCached_eq := buildCached_eq modulus
  frontier := Result.frontier
  accurate := fun request => (build modulus request).accurate

end Purelib.Integration.SourceFrontier.Continuous

end
