module
public import Purelib.Approximation.Gaussian.Name.Arithmetic.Power
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Process.Coherence.Basic
public import Purelib.Approximation.Gaussian.Process.Coherence.Multiplication

import Purelib.Tactic.QuotientFreeOmega
import Init.Prelude

open Purelib.Approximation.Gaussian.Process.Coherence.Basic (Coherent)

section
@[expose] public section

/-!
# Finite coherence of progressive transcendental outputs

The local exponential and logarithm algorithms first build limit-free
`Approximation` sidechannels.  Their CCL processes are therefore coherent by
construction.  This module propagates that certificate through global dyadic
range reduction, repeated squaring, and the finite correction arithmetic.

These are statements about every finite rational process branch.  They do not
assert that a completed exponential or logarithm value has been selected.
-/

namespace Purelib.Approximation.Gaussian.Name.Arithmetic.Power.Coherent

/-- Repeated squaring preserves finite process coherence. -/
def squareIterateCoherent : (exponent : Nat) →
  (value : Purelib.Approximation.Gaussian.Name.Basic.Named) →
    Coherent value.process →
      Coherent
        (Purelib.Approximation.Gaussian.Name.Arithmetic.Power.squareIterate exponent value).process
  | 0, _value, coherent => coherent
  | exponent + 1, value, coherent => by
      let previous :=
        Purelib.Approximation.Gaussian.Name.Arithmetic.Power.squareIterate exponent value
      let previousCoherent := squareIterateCoherent
        exponent value coherent
      exact Coherent.mul
        previousCoherent previousCoherent
end Purelib.Approximation.Gaussian.Name.Arithmetic.Power.Coherent

end
