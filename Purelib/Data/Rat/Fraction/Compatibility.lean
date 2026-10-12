module
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Nat.Order

public import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

/-!
# Direct arithmetic laws for constructive rational fractions

These scalar laws retain the total quotient operations and explicit nonzero or
positive-denominator evidence. Cross-product equalities and inequalities identify
and compare the original quotients without selecting alternative representatives.
-/

open Purelib.Data.Rat
open scoped Purelib.Data.Nat

@[expose] public section

namespace Purelib.CCL.Transcendental.Coherence

/-- Twice the sum of two quarters of a rational recovers that rational. -/
private theorem two_quarter_sums (target : Fraction.Rational) :
    2 * (target / 4 + target / 4) = target := by
  calc
    2 * (target / 4 + target / 4) = (target / 4) * 4 := by ring1
    _ = target :=
      Fraction.Field.div_mul_cancel_of_ne target 4 (by decide)

end Purelib.CCL.Transcendental.Coherence

namespace Purelib.Data.Rat.Fraction.Compatibility

/-- Adding a nonnegative rational on the right cannot decrease a rational value. -/
public theorem coordinate_le_add_of_nonneg_right
    (a b : Fraction.Rational) (nonnegative : 0 ≤ b) : a ≤ a + b := by
  calc
    a = 0 + a := (Fraction.Field.zero_add _).symm
    _ ≤ b + a :=
      Fraction.Order.Arithmetic.add_le_add_right_direct nonnegative a
    _ = a + b := _root_.add_comm _ _

/-- Adding a nonnegative rational on the left cannot decrease a rational value. -/
public theorem coordinate_le_add_of_nonneg_left
    (a b : Fraction.Rational) (nonnegative : 0 ≤ b) : a ≤ b + a := by
  calc
    a = 0 + a := (Fraction.Field.zero_add _).symm
    _ ≤ b + a :=
      Fraction.Order.Arithmetic.add_le_add_right_direct nonnegative a

/-- Twice the sum of two quarters of a rational recovers that rational. -/
public theorem two_quarter_sums
    (target : Fraction.Rational) :
    2 * (target / 4 + target / 4) = target := by
  apply Fraction.Field.mul_right_cancel_of_ne
    (show (4 : Fraction.Rational) ≠ 0 by decide)
  calc
    (2 * (target / 4 + target / 4)) * 4 =
        2 * ((target / 4) * 4 + (target / 4) * 4) := by ring1
    _ = 2 * (target + target) := by
      rw [show target / 4 * 4 = target from
        Fraction.Field.div_mul_cancel_of_ne target 4 (by decide)]
    _ = target * 4 := by ring1

/-- The product of two rational unit fractions equals the unit fraction of their product. -/
public theorem one_div_mul_one_div (left right : Fraction.Rational) :
    (1 / left) * (1 / right) = 1 / (left * right) := by
  calc
    (1 / left) * (1 / right) = (1 * 1) / (left * right) :=
      Fraction.Field.div_mul_div_direct 1 left 1 right
    _ = 1 / (left * right) := by
      rw [_root_.one_mul]

/-- Four times a rational quarter recovers the original rational. -/
public theorem four_mul_quarter_scale (scale : Fraction.Rational) :
    4 * (scale / 4) = scale := by
  calc
    4 * (scale / 4) = scale / 4 * 4 :=
      Fraction.Field.mul_comm _ _
    _ = scale :=
      Fraction.Field.div_mul_cancel_of_ne scale 4 (by decide)

/-- Twice a rational doubled by addition is four times that rational. -/
public theorem two_double_scale (scale : Fraction.Rational) :
    2 * (scale + scale) = 4 * scale := by ring1

/-- Multiply two successive rational ratios and cancel their retained nonzero middle value. -/
public theorem div_mul_div_telescope
    (numerator middle denominator : Fraction.Rational)
    (middleNonzero : middle ≠ 0) (denominatorNonzero : denominator ≠ 0) :
    (numerator / middle) * (middle / denominator) =
      numerator / denominator := by
  calc
    (numerator / middle) * (middle / denominator) =
        (numerator * middle) / (middle * denominator) :=
      Fraction.Field.div_mul_div_direct _ _ _ _
    _ = numerator / denominator := by
      apply Fraction.Field.div_eq_div_of_cross _ _ _ _
        (Fraction.Field.mul_ne_zero_direct middleNonzero
          denominatorNonzero)
        denominatorNonzero
      ring1

/-- Multiplying a quotient by its retained nonzero scale recovers the numerator. -/
public theorem scale_mul_div_cancel (scale target : Fraction.Rational)
    (scale_ne : scale ≠ 0) : scale * (target / scale) = target := by
  rw [Fraction.Field.mul_comm]
  exact Fraction.Field.div_mul_cancel_of_ne target scale scale_ne

/-- Equal cross-products identify rational quotients with positive natural denominators. -/
public theorem divEqOfNatDenominators
    {left right : Fraction.Rational} {leftDenominator rightDenominator : Nat}
    (leftPositive : 0 < leftDenominator)
    (rightPositive : 0 < rightDenominator)
    (cross : left * (rightDenominator : Fraction.Rational) =
      right * (leftDenominator : Fraction.Rational)) :
    left / (leftDenominator : Fraction.Rational) = right / (rightDenominator : Fraction.Rational) := by
  exact Fraction.Field.div_eq_div_of_cross_mul
    (Fraction.Cast.Order.natCast_pos_direct (n := leftDenominator) leftPositive).ne'
    (Fraction.Cast.Order.natCast_pos_direct (n := rightDenominator) rightPositive).ne' cross

/-- Weak cross-product comparison implies weak comparison of rational quotients with positive denominators. -/
public theorem divLeDivOfCrossMul
    {leftNumerator leftDenominator rightNumerator rightDenominator : Fraction.Rational}
    (leftPositive : 0 < leftDenominator)
    (rightPositive : 0 < rightDenominator)
    (cross : leftNumerator * rightDenominator ≤
      rightNumerator * leftDenominator) :
    leftNumerator / leftDenominator ≤
      rightNumerator / rightDenominator := by
  apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct
    (c := leftDenominator * rightDenominator) _
    (Fraction.Order.Arithmetic.mul_pos_direct leftPositive rightPositive)
  calc
    leftNumerator / leftDenominator *
        (leftDenominator * rightDenominator) =
      (leftNumerator / leftDenominator * leftDenominator) *
        rightDenominator := by ring1
    _ = leftNumerator * rightDenominator := by
      rw [Fraction.Field.div_mul_cancel_of_ne _ _
        leftPositive.ne']
    _ ≤ rightNumerator * leftDenominator := cross
    _ = (rightNumerator / rightDenominator * rightDenominator) *
        leftDenominator := by
      rw [Fraction.Field.div_mul_cancel_of_ne _ _
        rightPositive.ne']
    _ = rightNumerator / rightDenominator *
        (leftDenominator * rightDenominator) := by ring1

/-- Add two rational quotients with a common nonzero denominator by adding their numerators. -/
public theorem addSameDenominator (left right denominator :
  Fraction.Rational)
    (nonzero : denominator ≠ 0) :
    left / denominator + right / denominator =
      (left + right) / denominator := by
  apply Fraction.Field.mul_right_cancel_of_ne nonzero
  calc
    (left / denominator + right / denominator) * denominator =
        (left / denominator) * denominator +
          (right / denominator) * denominator := by ring1
    _ = left + right := by
      rw [Fraction.Field.div_mul_cancel_of_ne _ _ nonzero,
        Fraction.Field.div_mul_cancel_of_ne _ _ nonzero]
    _ = ((left + right) / denominator) * denominator :=
      (Fraction.Field.div_mul_cancel_of_ne _ _ nonzero).symm

/-- Multiplication on the right of a rational quotient can be moved into its numerator. -/
public theorem divMul (left denominator right : Fraction.Rational) :
    (left / denominator) * right = (left * right) / denominator := by
  simp only [Fraction.Field.div_eq_mul_inv_direct]
  ring1

/-- Subtract two rational quotients with a common nonzero denominator by subtracting their numerators. -/
public theorem subSameDenominator (left right denominator :
  Fraction.Rational)
    (nonzero : denominator ≠ 0) :
    left / denominator - right / denominator =
      (left - right) / denominator := by
  apply Fraction.Field.mul_right_cancel_of_ne nonzero
  calc
    (left / denominator - right / denominator) * denominator =
        (left / denominator) * denominator -
          (right / denominator) * denominator := by ring1
    _ = left - right := by
      rw [Fraction.Field.div_mul_cancel_of_ne _ _ nonzero,
        Fraction.Field.div_mul_cancel_of_ne _ _ nonzero]
    _ = ((left - right) / denominator) * denominator :=
      (Fraction.Field.div_mul_cancel_of_ne _ _ nonzero).symm

/-- Negating a rational numerator negates its quotient, including the total zero-denominator case. -/
public theorem negativeDiv (numerator denominator : Fraction.Rational) :
    (-numerator) / denominator = -(numerator / denominator) := by
  simp only [Fraction.Field.div_eq_mul_inv_direct]
  ring1

/-- Move the left factor of a rational product through its displayed quotient. -/
public theorem mul_div_reassociate (a b c :
  Fraction.Rational) :
    a * (b / c) = (a / c) * b := by
  change a * (b * c⁻¹) = (a * c⁻¹) * b
  ring1

/-- Move the first numerator factor to the right of a rational quotient. -/
private theorem mul_mul_div_reassociate (a b c :
  Fraction.Rational) :
    a * b / c = (b / c) * a := by
  change (a * b) * c⁻¹ = (b * c⁻¹) * a
  ring1

end Purelib.Data.Rat.Fraction.Compatibility

namespace Purelib.Data.Rat.Fraction.Compatibility.ExplicitQuarticPreparedALeftSampleCertificatesPart1

/-- The total canonical reciprocal of one is one. -/
theorem
  aLeftBoundaryInvOne
  : (1 : Fraction.Rational)⁻¹ = 1 := by decide

end Purelib.Data.Rat.Fraction.Compatibility.ExplicitQuarticPreparedALeftSampleCertificatesPart1

namespace Purelib.Data.Rat.Fraction.Compatibility.ExplicitQuarticPreparedARightSampleCertificatesPart1

/-- The total canonical reciprocal of one is one. -/
theorem
  aRightBoundaryInvOne
  : (1 : Fraction.Rational)⁻¹ = 1 := by decide

end Purelib.Data.Rat.Fraction.Compatibility.ExplicitQuarticPreparedARightSampleCertificatesPart1

namespace Purelib.Polynomial.Clearance.Box.Boundary.Basic.BoundaryClearance

/-- The sum of two rational quarters equals one rational half. -/
private theorem quarter_add_quarter (target :
  Fraction.Rational) :
    target / 4 + target / 4 = target / 2 := by
  apply Fraction.Field.mul_right_cancel_of_ne
    (show (4 : Fraction.Rational) ≠ 0 by decide)
  calc
    (target / 4 + target / 4) * 4 =
        (target / 4) * 4 + (target / 4) * 4 := by rw [add_mul]
    _ = target + target := by
      rw [show target / 4 * 4 = target from
        Fraction.Field.div_mul_cancel_of_ne target 4 (by decide)]
    _ = target * 2 := by ring1
    _ = ((target / 2) * 2) * 2 := by
      rw [show target / 2 * 2 = target from
        Fraction.Field.div_mul_cancel_of_ne target 2 (by decide)]
    _ = (target / 2) * (2 * 2) :=
      Fraction.Field.mul_assoc (target / 2) 2 2
    _ = (target / 2) * 4 := by
      rw [show (2 : Fraction.Rational) * 2 = 4 by decide]

/-- Twice a rational half recovers the original rational. -/
private theorem two_mul_half (target :
  Fraction.Rational) :
    2 * (target / 2) = target := by
  calc
    2 * (target / 2) = (target / 2) * 2 :=
      Fraction.Field.mul_comm 2 (target / 2)
    _ = target :=
      Fraction.Field.div_mul_cancel_of_ne target 2 (by decide)

end Purelib.Polynomial.Clearance.Box.Boundary.Basic.BoundaryClearance
