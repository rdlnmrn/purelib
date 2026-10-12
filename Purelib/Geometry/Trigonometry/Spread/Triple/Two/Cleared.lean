module
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Field.ExplicitField
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init

section
@[expose] public section

/-!
# Divine Proportions, Chapter 25: resection and Hansen's problem

The large rational calculations are represented by common-denominator
integer certificates.  The general resection theorem is proved from the
denominator-free Four-point polynomial, so neither a root search nor a
completed coordinate field is used.
-/

namespace Purelib.Geometry.Trigonometry.Spread.Triple.Two.Cleared

section

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- The cleared residual for a common third spread of two spread triples.

The four input spread numerators share the supplied denominator. The output numerator and denominator are retained
separately, so the comparison uses polynomial arithmetic only. -/
def clearedTwoSpreadTriplesValue
    (denominator first second third fourth
      outputNumerator outputDenominator : K) : K :=
  outputDenominator * ((first - second) ^ 2 - (third - fourth) ^ 2) -
    outputNumerator * 2 *
      (denominator * (first + second - third - fourth) -
        2 * first * second + 2 * third * fourth)
end
end Purelib.Geometry.Trigonometry.Spread.Triple.Two.Cleared

end
