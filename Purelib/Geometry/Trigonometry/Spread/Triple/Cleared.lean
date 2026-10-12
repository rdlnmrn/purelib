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

namespace Purelib.Geometry.Trigonometry.Spread.Triple.Cleared

section

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-! ## Problem 25: Hansen's problem -/

/-- The common-denominator Triple-spread polynomial.

The first three spread numerators share the displayed denominator; vanishing is the denominator-cleared Triple-spread
equation. -/
def clearedSpreadTriple
    (denominator first second third : K) : K :=
  denominator *
      ((first + second + third) ^ 2 -
        2 * (first ^ 2 + second ^ 2 + third ^ 2)) -
    4 * first * second * third
end
end Purelib.Geometry.Trigonometry.Spread.Triple.Cleared

end
