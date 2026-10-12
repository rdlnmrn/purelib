module
public import Purelib.Algebra.Field.ExplicitField
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs

section
@[expose] public section

/-!
# Divine Proportions, Chapter 6: spread, cross, and twist

The ratio notions carry explicit non-null/non-perpendicular certificates for
their denominators.  They are otherwise ordinary finite field expressions.
-/

namespace Purelib.Geometry.Trigonometry.Spread.Number.Basic

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- A spread number carries the square witness in `s(1-s) = r²`. -/
def IsSpreadNumber (value : K) : Prop :=
  ∃ root : K, value * (1 - value) = root ^ 2
end Purelib.Geometry.Trigonometry.Spread.Number.Basic

end
