module
public import Purelib.Algebra.Field.ExplicitField

open Purelib.Algebra.Field

section
@[expose] public section

/-!
# Rational rotations, section 8: handedness

Handedness is stored as the determinant of the displayed frame formed by an
anchor axis, a perpendicular vector, and its rotated image.  The determinant
formula is valid over every explicit field.  Positivity is separated into a
small coherent ordered-field interface so the algebraic theorem remains
available over finite fields.
-/

namespace Purelib.Algebra.Field.ExplicitOrder.Basic

variable {K : Type*} [ExplicitField K]

/-- An explicit field with supplied strict positivity laws.

The class retains decidable equality and positivity certificates for one, sums, products, nonzero squares and inverses;
it does not assume a complete ordered-field hierarchy. -/
class OrderedExplicitField (K : Type*) extends ExplicitField K, LT K
  where
  /-- The retained decision procedure for scalar equality. -/ eq_decidable : DecidableEq K
  /-- The unit is positive. -/ zero_lt_one_direct : 0 < (1 : K)
  /-- The sum of two positive scalars is positive. -/ add_pos_direct : ∀ {left right : K},
    0 < left → 0 < right → 0 < left + right
  /-- The product of two positive scalars is positive. -/ mul_pos_direct : ∀ {left right : K},
    0 < left → 0 < right → 0 < left * right
  /-- The square of every nonzero scalar is positive. -/ mul_self_pos_direct : ∀ {value : K}, value ≠ 0 → 0 < value *
    value
  /-- The total inverse of a positive scalar is positive. -/ inv_pos_direct : ∀ {value : K}, 0 < value → 0 < value⁻¹

section Ordered

variable {F : Type*} [Purelib.Algebra.Field.ExplicitOrder.Basic.OrderedExplicitField F]

open Purelib.Algebra.Field.ExplicitOrder.Basic in
/-- Use the decidable equality retained by the ordered explicit field. -/
local instance : DecidableEq F := OrderedExplicitField.eq_decidable

namespace OrderedExplicitField
open Purelib.Algebra.Field.ExplicitOrder.Basic in
/-- Adding any square to a positive scalar gives a positive scalar.

Decidable equality separates the zero square from a strictly positive nonzero square. -/
public theorem add_mul_self_pos {base : F} (value : F)
    (basePositive : 0 < base) : 0 < base + value * value := by
  by_cases valueZero : value = 0
  · rw [valueZero, zero_mul, add_zero]
    exact basePositive
  · exact OrderedExplicitField.add_pos_direct basePositive
      (OrderedExplicitField.mul_self_pos_direct valueZero)
end OrderedExplicitField

end Ordered

end Purelib.Algebra.Field.ExplicitOrder.Basic

end
