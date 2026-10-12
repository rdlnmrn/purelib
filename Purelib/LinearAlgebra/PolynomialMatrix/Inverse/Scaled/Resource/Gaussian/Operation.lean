module

public import Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Resource.Gaussian.Slots
import Purelib.Tactic.QuotientFreeOmega

open Purelib.LinearAlgebra

section
@[expose] public section

/-!
# RFAP-I calculation-size certificate

This module composes the normalized eliminant/Bézout, Sturm endpoint,
safe-cut, winding, coefficient-clearing, and repeated-subdivision envelopes.
The resulting `T` and `B` are finite recurrences in displayed input data.
-/

namespace Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Resource.Gaussian.Operation

/-- Count resource-growth steps in the recursive inverse-data envelope.

The recurrence pays for the Schur stage, the smaller doubled slot bound, and the final block reconstruction. -/
def dataEnvelopeAdvanceBudget :
  Nat → Nat → Nat
  | 0, _ => 0
  | count + 1, slots =>
      (2 * slots + 2) +
        dataEnvelopeAdvanceBudget
        count (2 * slots) +
        8 * (slots +
          PolynomialMatrix.Inverse.Scaled.Resource.Gaussian.Slots.dataSlotEnvelope count (2 * slots) +
          count + 1)
end Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Resource.Gaussian.Operation

end
