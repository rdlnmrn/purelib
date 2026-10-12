module
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Field.ExplicitField
import Purelib.Tactic.Ring

open Purelib.Algebra.Field

section
@[expose] public section

/-!
# Divine Proportions, Chapter 23: physics applications

The calculus passages in the source are retained through their finite
polynomial stationarity equations.  Extremum conclusions are separated from
those equations, so no completed real line, limit, or general derivative
operator enters the formalization.
-/

namespace Purelib.Algebra.Field.Quadratic.EqualSplit

section PhysicsApplications

variable {K : Type*} [ExplicitField K]

/-- Splitting a scalar equally preserves its sum and attains the square-product identity.

Two is nonzero in the explicit field, so the two halves add to the original value and four times their product is its
square. -/
theorem fixed_sum_equal_split (V : K) (twoNonzero : (2 : K) ≠ 0) :
    V / 2 + V / 2 = V ∧
      4 * (V / 2) * (V / 2) = V ^ 2 := by
  have cancel := ExplicitField.div_mul_cancel V twoNonzero
  constructor
  · calc
      V / 2 + V / 2 = (V / 2) * 2 := by ring1
      _ = V := cancel
  · have twoInverse : (2 : K) * (2 : K)⁻¹ = 1 :=
      ExplicitField.mul_inv_cancel 2 twoNonzero
    simp only [ExplicitField.div_eq_mul_inv]
    calc
      4 * (V * (2 : K)⁻¹) * (V * (2 : K)⁻¹) =
          V ^ 2 * (2 * (2 : K)⁻¹) ^ 2 := by ring1
      _ = V ^ 2 := by rw [twoInverse]; ring1
end PhysicsApplications
end Purelib.Algebra.Field.Quadratic.EqualSplit

end
