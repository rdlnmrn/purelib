module
public import Purelib.Approximation.Gaussian.Exponential.Horner.Real
public import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Gaussian.Norm.Coordinates
import Purelib.Data.Rat.Bounds.Abs
import Purelib.Tactic.Ring

/-!
# Finite exponential reading discrepancies

The original Gaussian squared-error allowance is converted to a rational
coordinate radius with a finite half-power. No square root or completed
exponential value is selected.
-/

public section

namespace Purelib.Approximation.Gaussian.Exponential.Horner.Real

open Purelib.Approximation.Rational
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order

/-- A rational coordinate radius for the original scale-ten quarter-radius at this finite depth. -/
@[expose] def tailRadius (depth : Nat) : Fraction.Rational := 4 * (1 / 2 : Fraction.Rational) ^ depth

/-- The retained coordinate radius is nonnegative at every finite depth. -/
theorem tailRadius_nonnegative (depth : Nat) : 0 ≤ tailRadius depth :=
  Arithmetic.mul_nonneg_direct (by decide)
    (Arithmetic.pow_nonneg_direct (by decide) depth)

/-- Squaring the finite half-power gives the corresponding finite quarter-power. -/
private theorem halfPower_sq : ∀ depth : Nat,
    ((1 / 2 : Fraction.Rational) ^ depth) ^ 2 = (1 / 4 : Fraction.Rational) ^ depth
  | 0 => by decide
  | depth + 1 => by
      rw [pow_succ, pow_succ]
      calc
        _ = ((1 / 2 : Fraction.Rational) ^ depth) ^ 2 * (1 / 2 : Fraction.Rational) ^ 2 := by ring1
        _ = (1 / 4 : Fraction.Rational) ^ depth * (1 / 4 : Fraction.Rational) := by
          rw [halfPower_sq depth, show (1 / 2 : Fraction.Rational) ^ 2 = 1 / 4 by decide]

/-- The original Gaussian quarter-radius is paid by the square of the retained coordinate radius. -/
theorem quarterRadius_le_tailRadius_sq (depth : Nat) :
    Geometric.Basic.quarterRadius 10 depth ≤ (tailRadius depth) ^ 2 := by
  rw [Geometric.Basic.quarterRadius_eq_mul_pow]
  have scaled := Arithmetic.mul_le_mul_of_nonneg_right_direct
    (by decide : (10 : Fraction.Rational) ≤ 16)
    (Arithmetic.pow_nonneg_direct (by decide : (0 : Fraction.Rational) ≤ 1 / 4) depth)
  calc
    _ ≤ 16 * (1 / 4 : Fraction.Rational) ^ depth := scaled
    _ = (tailRadius depth) ^ 2 := by
      unfold tailRadius
      rw [← halfPower_sq depth]
      ring1

/-- Later and earlier original finite Horner readings differ by the earlier coordinate radius. -/
theorem finite_later_difference (earlier later : Nat) (order : earlier ≤ later) (point : Fraction.Rational)
    (lower : 0 ≤ point) (upper : point ≤ 1) :
    Fraction.abs (finiteSource later point - finiteSource earlier point) ≤ tailRadius earlier := by
  let input := RationalEmbedding.realPoint point
  let laterValue := Sample.sample input later
  let earlierValue := Sample.sample input earlier
  have gaussian := Sample.sample_later_close input (unit_input point ⟨lower, upper⟩) order
  have coordinate := Norm.Coordinates.re_sub_sq_le_basic_normSq laterValue earlierValue
  have squared := coordinate.trans (gaussian.trans (quarterRadius_le_tailRadius_sq earlier))
  have first := Arithmetic.le_of_sq_le_sq_direct (tailRadius_nonnegative earlier) squared
  have secondLower := Arithmetic.neg_le_of_sq_le_sq_direct (tailRadius_nonnegative earlier) squared
  have second := Arithmetic.neg_le_neg_direct secondLower
  have opposite : -(-tailRadius earlier) = tailRadius earlier := by ring1
  rw [opposite] at second
  change max (laterValue.re - earlierValue.re) (-(laterValue.re - earlierValue.re)) ≤ tailRadius earlier
  exact Fraction.Order.Basic.max_le first second

/-- Any two original finite Horner readings differ by the sum of their two retained coordinate radii. -/
theorem finite_difference (left right : Nat) (point : Fraction.Rational) (lower : 0 ≤ point) (upper : point ≤ 1) :
    Fraction.abs (finiteSource left point - finiteSource right point) ≤ tailRadius left + tailRadius right := by
  by_cases order : left ≤ right
  · have later := finite_later_difference left right order point lower upper
    have paid := Arithmetic.add_le_add_right_direct (tailRadius_nonnegative right) (tailRadius left)
    have zero : (0 : Fraction.Rational) + tailRadius left = tailRadius left := by ring1
    have commute : tailRadius right + tailRadius left = tailRadius left + tailRadius right := by ring1
    rw [zero, commute] at paid
    rw [Bounds.Abs.abs_sub_comm_direct]
    exact later.trans paid
  · have reverseOrder : right ≤ left := Nat.le_of_not_ge order
    have later := finite_later_difference right left reverseOrder point lower upper
    have paid := Arithmetic.add_le_add_right_direct (tailRadius_nonnegative left) (tailRadius right)
    have zero : (0 : Fraction.Rational) + tailRadius right = tailRadius right := by ring1
    rw [zero] at paid
    exact later.trans paid

end Purelib.Approximation.Gaussian.Exponential.Horner.Real

end
