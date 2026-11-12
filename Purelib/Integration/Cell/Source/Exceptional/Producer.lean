module
public import Purelib.Integration.Cell.Source.Exceptional
public import Purelib.Integration.Cell.Source.Producer

/-! The finite exceptional-source construction supplies the shared source-frontier producer. -/

public section

namespace Purelib.Integration.SourceFrontier.Exceptional

open Purelib.Approximation
open Purelib.Data.Rat

/-- Use the original finite-exception construction as a persistent source-frontier producer. -/
@[expose] def producer {source : Fraction.Rational → Fraction.Rational}
    (modulus : Rational.Exceptional.Modulus source) :
    SourceFrontier.Producer source where
  Output := Result modulus
  request := build modulus
  requestCached := buildCached modulus
  requestCached_eq := buildCached_eq modulus
  frontier := Result.frontier
  accurate := fun request => (build modulus request).accurate

end Purelib.Integration.SourceFrontier.Exceptional

end
