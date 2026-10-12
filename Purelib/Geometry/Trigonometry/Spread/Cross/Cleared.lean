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

namespace Purelib.Geometry.Trigonometry.Spread.Cross.Cleared

section

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-! ## Example 25.1 -/

/-- The denominator-cleared Cross-law spread residual.

The first and third quadrances share a denominator, while the opposite quadrance and proposed spread numerator and
denominator remain explicit. -/
def clearedCrossSpread
    (commonDenominator firstNumerator thirdNumerator opposite
      spreadNumerator spreadDenominator : K) : K :=
  spreadDenominator *
      (4 * firstNumerator * thirdNumerator -
        (firstNumerator + thirdNumerator - opposite * commonDenominator) ^ 2) -
    spreadNumerator * (4 * firstNumerator * thirdNumerator)
end
end Purelib.Geometry.Trigonometry.Spread.Cross.Cleared

end
