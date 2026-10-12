module

import Purelib.Algebra.Group.Negation
public import Purelib.Algebra.Field.ExplicitField
import Purelib.Tactic.Ring
public import Purelib.Data.Nat.Order

open Purelib.Algebra.Field

section
@[expose] public section

/-!
# Rational rotations, section 7: recovering the anchor

The paper's boxed antisymmetric formula is the executable definition of a
rotation's anchor.  An explicit adjugate inverse for `I + ρ` ties that cached
value to the big Cayley transform; downstream proofs use the cached formula
rather than recomputing the inverse.
-/

namespace Purelib.Rotations

variable {K : Type*} [ExplicitField K]

section

/-- One retains the owned nonzero-successor certificate. -/
local instance oneNeZero : NeZero (1 : Nat) :=
  Purelib.Data.Nat.successorNeZero (value := 0)

end

end Purelib.Rotations

end

section
open Purelib
open Purelib.Algebra.Field
open scoped Purelib.Data.Nat
open Purelib.Algebra.Group in
attribute [local instance high] Negation.subNegZeroMonoid
public section
namespace Purelib.Algebra.Field.Inverse

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- Put a quadratic expression in the inverse denominator over its square.

The denominator is nonzero; the common numerator is the quadratic coefficient plus the linear coefficient times the
denominator plus the constant times its square. -/
public theorem clear_quadratic_denominator
    {denominator quadratic linear constant : K}
    (denominatorNonzero : denominator ≠ 0) :
    quadratic * denominator⁻¹ ^ 2 + linear * denominator⁻¹ + constant =
      (quadratic + linear * denominator + constant * denominator ^ 2) *
        denominator⁻¹ ^ 2 := by
  have cancel : denominator * denominator⁻¹ = (1 : K) :=
    ExplicitField.mul_inv_cancel denominator denominatorNonzero
  calc
    quadratic * denominator⁻¹ ^ 2 + linear * denominator⁻¹ + constant =
        (quadratic + linear * denominator + constant * denominator ^ 2) *
            denominator⁻¹ ^ 2 +
          linear * denominator⁻¹ *
            (1 - denominator * denominator⁻¹) +
          constant * (1 - (denominator * denominator⁻¹) ^ 2) := by
      ring1
    _ = (quadratic + linear * denominator + constant * denominator ^ 2) *
        denominator⁻¹ ^ 2 := by rw [cancel]; ring1

/-- A nonzero denominator times its inverse square equals its inverse. -/
public theorem
  inverse_eq_mul_inverse_square
    {denominator : K} (denominatorNonzero : denominator ≠ 0) :
    denominator⁻¹ = denominator * denominator⁻¹ ^ 2 := by
  have cancel : denominator * denominator⁻¹ = (1 : K) :=
    ExplicitField.mul_inv_cancel denominator denominatorNonzero
  calc
    denominator⁻¹ = 1 * denominator⁻¹ := by ring1
    _ = (denominator * denominator⁻¹) * denominator⁻¹ := by
      rw [cancel]
    _ = denominator * denominator⁻¹ ^ 2 := by ring1

/-- The square of a nonzero denominator times its inverse square equals one. -/
public theorem
  one_eq_square_mul_inverse_square
    {denominator : K} (denominatorNonzero : denominator ≠ 0) :
    (1 : K) = denominator ^ 2 * denominator⁻¹ ^ 2 := by
  have cancel : denominator * denominator⁻¹ = (1 : K) :=
    ExplicitField.mul_inv_cancel denominator denominatorNonzero
  calc
    (1 : K) = (denominator * denominator⁻¹) ^ 2 := by
      rw [cancel]
      ring1
    _ = denominator ^ 2 * denominator⁻¹ ^ 2 := by ring1

/-- Divide a retained numerator-product equation by its nonzero denominator.

The numerator divided by the denominator equals the supplied remaining factor. -/
public theorem div_eq_of_eq_mul_right
    {numerator denominator value : K}
    (denominatorNonzero : denominator ≠ 0)
    (equation : numerator = denominator * value) :
    numerator / denominator = value := by
  have denominatorCancel :
      denominator * denominator⁻¹ = (1 : K) :=
    ExplicitField.mul_inv_cancel denominator denominatorNonzero
  rw [ExplicitField.div_eq_mul_inv, equation]
  calc
    denominator * value * denominator⁻¹ =
        value * (denominator * denominator⁻¹) := by ring1
    _ = value := by rw [denominatorCancel]; ring1

end Purelib.Algebra.Field.Inverse
end

end

section
public section
namespace Purelib.Algebra.Field.Inverse

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- Equal ratios have equal cross products when both denominators are nonzero. -/
public theorem cross_mul_of_div_eq_div
    {leftNumerator rightNumerator leftDenominator rightDenominator : K}
    (leftNonzero : leftDenominator ≠ 0)
    (rightNonzero : rightDenominator ≠ 0)
    (equal : leftNumerator / leftDenominator =
      rightNumerator / rightDenominator) :
    leftNumerator * rightDenominator =
      rightNumerator * leftDenominator := by
  have leftCancel := Algebra.Field.ExplicitField.mul_inv_cancel
    leftDenominator leftNonzero
  have rightCancel := Algebra.Field.ExplicitField.mul_inv_cancel
    rightDenominator rightNonzero
  calc
    leftNumerator * rightDenominator =
        leftNumerator *
          (leftDenominator * leftDenominator⁻¹) * rightDenominator := by
            rw [leftCancel]
            ring1
    _ =
        (leftNumerator / leftDenominator) *
          (leftDenominator * rightDenominator) := by
            simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
            ring1
    _ = (rightNumerator / rightDenominator) *
          (leftDenominator * rightDenominator) := by rw [equal]
    _ = rightNumerator * leftDenominator := by
      simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
      calc
        rightNumerator * rightDenominator⁻¹ *
            (leftDenominator * rightDenominator) =
          rightNumerator *
            (rightDenominator * rightDenominator⁻¹) * leftDenominator := by
              ring1
        _ = rightNumerator * leftDenominator := by
          rw [rightCancel]
          ring1

/-- An equation with nonzero right denominator yields the corresponding quotient formula. -/
public theorem eq_div_of_mul_eq {left right
  denominator : K}
    (denominatorNonzero : denominator ≠ 0)
    (product : left * denominator = right) :
    left = right / denominator := by
  have cancel := Algebra.Field.ExplicitField.mul_inv_cancel denominator
    denominatorNonzero
  simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
  calc
    left = left * (denominator * denominator⁻¹) := by rw [cancel, mul_one]
    _ = (left * denominator) * denominator⁻¹ := by ring1
    _ = right * denominator⁻¹ := by rw [product]

/-- The inverse of one is one when one is nonzero. -/
public theorem inverse_one (oneNonzero : (1 : K) ≠ 0) :
    (1 : K)⁻¹ = 1 := by
  have cancel := Algebra.Field.ExplicitField.mul_inv_cancel (1 : K) oneNonzero
  simpa only [one_mul] using cancel

/-- Identify the total inverse from a product equal to one.

The scalar is supplied as nonzero, so inverse cancellation forces the displayed candidate to be its inverse. -/
public theorem inverse_eq_of_mul_eq_one {value
  candidate : K}
    (valueNonzero : value ≠ 0) (certificate : value * candidate = 1) :
    value⁻¹ = candidate := by
  have cancel := ExplicitField.mul_inv_cancel value valueNonzero
  calc
    value⁻¹ = value⁻¹ * 1 := by rw [mul_one]
    _ = value⁻¹ * (value * candidate) := by rw [certificate]
    _ = (value * value⁻¹) * candidate := by ring1
    _ = candidate := by rw [cancel, one_mul]

/-- The inverse of a product of two nonzero scalars is the product of their inverses.

The two supplied nonzero certificates justify cancellation of each factor. -/
public theorem inverse_product {left right : K}
    (leftNonzero : left ≠ 0) (rightNonzero : right ≠ 0) :
    (left * right)⁻¹ = left⁻¹ * right⁻¹ := open Purelib in by
  apply Purelib.Algebra.Field.Inverse.inverse_eq_of_mul_eq_one
    (ExplicitField.mul_ne_zero leftNonzero rightNonzero)
  have leftCancel := ExplicitField.mul_inv_cancel left leftNonzero
  have rightCancel := ExplicitField.mul_inv_cancel right rightNonzero
  calc
    left * right * (left⁻¹ * right⁻¹) =
        (left * left⁻¹) * (right * right⁻¹) := by ring1
    _ = 1 := by rw [leftCancel, rightCancel, one_mul]

/-- The inverse of a nonzero scalar's square is the square of its inverse. -/
public theorem inverse_square {value : K} (valueNonzero : value ≠
  0) :
    (value ^ 2)⁻¹ = value⁻¹ ^ 2 := by
  simpa only [pow_two] using Purelib.Algebra.Field.Inverse.inverse_product valueNonzero valueNonzero

/-- Equal cross products give equal ratios with nonzero denominators.

Each denominator carries its own nonzero certificate, which justifies cancelling the two divisions. -/
public theorem div_eq_div_of_cross_mul
    {leftNumerator rightNumerator leftDenominator rightDenominator : K}
    (leftNonzero : leftDenominator ≠ 0)
    (rightNonzero : rightDenominator ≠ 0)
    (crossProduct :
      leftNumerator * rightDenominator =
        rightNumerator * leftDenominator) :
    leftNumerator / leftDenominator =
      rightNumerator / rightDenominator := by
  have leftCancel := ExplicitField.mul_inv_cancel
    leftDenominator leftNonzero
  have rightCancel := ExplicitField.mul_inv_cancel
    rightDenominator rightNonzero
  simp only [ExplicitField.div_eq_mul_inv]
  calc
    leftNumerator * leftDenominator⁻¹ =
        leftNumerator * leftDenominator⁻¹ *
          (rightDenominator * rightDenominator⁻¹) := by
            rw [rightCancel, mul_one]
    _ = (leftNumerator * rightDenominator) *
        (leftDenominator⁻¹ * rightDenominator⁻¹) := by ring1
    _ = (rightNumerator * leftDenominator) *
        (leftDenominator⁻¹ * rightDenominator⁻¹) := by rw [crossProduct]
    _ = rightNumerator *
        (leftDenominator * leftDenominator⁻¹) *
          rightDenominator⁻¹ := by ring1
    _ = rightNumerator * rightDenominator⁻¹ := by
      rw [leftCancel, mul_one]

end Purelib.Algebra.Field.Inverse
end

end

section
open Purelib
open Purelib.Algebra.Field
namespace Purelib.Algebra.Field.Inverse
variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- Recover an entry from its pivot-product identity when the pivot is nonzero. -/
public theorem eq_one_div_mul_of_mul_eq {pivot target left right : K}
    (pivotNonzero : pivot ≠ 0)
    (minor : pivot * target = left * right) :
    target = (1 / pivot) * (left * right) := by
  have cancel := ExplicitField.mul_inv_cancel pivot pivotNonzero
  simp only [ExplicitField.div_eq_mul_inv]
  calc
    target = 1 * target := by rw [one_mul]
    _ = (pivot * pivot⁻¹) * target := by rw [cancel]
    _ = pivot⁻¹ * (pivot * target) := by ring1
    _ = pivot⁻¹ * (left * right) := by rw [minor]
    _ = 1 * pivot⁻¹ * (left * right) := by ring1

/-- The scalar expression `1 - 1^2 / (14 * 6)` equals `83/84` when 84 is nonzero. -/
public theorem
  one_sub_div_fourteen_six
    {F : Type*} [ExplicitField F] (eightyFourNonzero : (84 : F) ≠ 0) :
    1 - (1 : F) ^ 2 / (14 * 6) = 83 / 84 := by
  have denominator : (14 : F) * 6 = 84 := by ring1
  have cancel := ExplicitField.mul_inv_cancel (84 : F)
    eightyFourNonzero
  rw [denominator]
  simp only [ExplicitField.div_eq_mul_inv]
  calc
    1 - 1 ^ 2 * (84 : F)⁻¹ =
        84 * (84 : F)⁻¹ - 1 ^ 2 * (84 : F)⁻¹ := by
          rw [cancel]
    _ = 83 * (84 : F)⁻¹ := by ring1

/-- The scalar identity `1 + (-63)/67 = 4/67` holds when 67 is nonzero. -/
public theorem
  one_add_neg_sixtyThree_div_sixtySeven
    {F : Type*} [ExplicitField F] (denominatorNonzero : (67 : F) ≠ 0) :
    1 + (-63 : F) / 67 = 4 / 67 := by
  have cancel := ExplicitField.mul_inv_cancel (67 : F)
    denominatorNonzero
  simp only [ExplicitField.div_eq_mul_inv]
  calc
    1 + (-63 : F) * (67 : F)⁻¹ =
        67 * (67 : F)⁻¹ + (-63 : F) * (67 : F)⁻¹ := by
          rw [cancel]
    _ = 4 * (67 : F)⁻¹ := by ring1

end Purelib.Algebra.Field.Inverse
end
