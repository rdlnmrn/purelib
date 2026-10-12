module
public import Purelib.Algebra.Field.ExplicitField
public import Purelib.Algebra.Group.Negation
public import Purelib.Data.Nat.Order
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring

/-!
# Scalar midpoint identities

Displayed half sums and their differences retain the supplied nonzero-two
certificate for clearing their denominators.
-/

section
open Purelib
open Purelib.Algebra.Field
open scoped Purelib.Data.Nat
open Purelib.Algebra.Group in
attribute [local instance high] Negation.subNegZeroMonoid
public section
namespace Purelib.Algebra.Field.Midpoint

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- Twice the half-sum minus a target equals the sum minus twice that target.

The nonzero-two certificate justifies cancelling the midpoint denominator. -/
public theorem half_sum_sub_target_mul_two
    (left right target : K) (twoNonzero : (2 : K) ≠ 0) :
    ((left + right) / 2 - target) * 2 =
      left + right - 2 * target := by
  calc
    ((left + right) / 2 - target) * 2 =
        ((left + right) / 2) * 2 - target * 2 := by ring1
    _ = left + right - target * 2 := by
      rw [ExplicitField.div_mul_cancel _ twoNonzero]
    _ = left + right - 2 * target := by ring1

/-- Twice a target minus a half-sum equals twice the target minus the two summands.

The nonzero-two certificate justifies cancelling the midpoint denominator. -/
public theorem target_sub_half_sum_mul_two
    (left right target : K) (twoNonzero : (2 : K) ≠ 0) :
    (target - (left + right) / 2) * 2 =
      2 * target - left - right := by
  calc
    (target - (left + right) / 2) * 2 =
        target * 2 - ((left + right) / 2) * 2 := by ring1
    _ = target * 2 - (left + right) := by
      rw [ExplicitField.div_mul_cancel _ twoNonzero]
    _ = 2 * target - left - right := by ring1

/-- The left scalar minus the midpoint is half the left-minus-right difference.

The nonzero-two certificate justifies the displayed divisions. -/
public theorem left_sub_midpoint_coordinate (left
  right : K)
    (twoNonzero : (2 : K) ≠ 0) :
    left - (left + right) / 2 = (left - right) / 2 := by
  have twoInverse : (2 : K) * (2 : K)⁻¹ = 1 :=
    ExplicitField.mul_inv_cancel 2 twoNonzero
  simp only [ExplicitField.div_eq_mul_inv]
  calc
    left - (left + right) * (2 : K)⁻¹ =
        (left - right) * (2 : K)⁻¹ +
          left * (1 - 2 * (2 : K)⁻¹) := by ring1
    _ = (left - right) * (2 : K)⁻¹ := by rw [twoInverse]; ring1

/-- The right scalar minus the midpoint is half the right-minus-left difference.

The nonzero-two certificate justifies the displayed divisions. -/
public theorem right_sub_midpoint_coordinate (left
  right : K)
    (twoNonzero : (2 : K) ≠ 0) :
    right - (left + right) / 2 = (right - left) / 2 := by
  have twoInverse : (2 : K) * (2 : K)⁻¹ = 1 :=
    ExplicitField.mul_inv_cancel 2 twoNonzero
  simp only [ExplicitField.div_eq_mul_inv]
  calc
    right - (left + right) * (2 : K)⁻¹ =
        (right - left) * (2 : K)⁻¹ +
          right * (1 - 2 * (2 : K)⁻¹) := by ring1
    _ = (right - left) * (2 : K)⁻¹ := by rw [twoInverse]; ring1

end Purelib.Algebra.Field.Midpoint
end
