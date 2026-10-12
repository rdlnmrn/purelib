module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

section
@[expose] public section

/-!
# Root-free finite Lp bounds

Square roots of rational second moments need not be rational.  The primitive
L2 quantity here is therefore the exact powered norm `integral (f^2)`.  Its
Cauchy--Schwarz inequality is stated after squaring, and so remains wholly
rational and executable.
-/

namespace Purelib.Data.Rat

open Purelib.Data.Rat in
/-- An everywhere nonnegative rational binary quadratic form has mixed coefficient square at most the product of its
diagonal coefficients.

The nonnegative diagonal coefficients and universal nonnegativity hypothesis cover all rational pairs of scaling
factors. Explicit factor choices, with separate zero-diagonal cases, force the determinant bound without choosing a
square root. -/
theorem quadratic_cauchy_sq_le
    (leftSq rightSq mixed : Fraction.Rational)
    (leftNonnegative : 0 ≤ leftSq)
    (rightNonnegative : 0 ≤ rightSq)
    (quadraticNonnegative : ∀ leftFactor rightFactor : Fraction.Rational,
      0 ≤ leftFactor ^ 2 * leftSq + rightFactor ^ 2 * rightSq +
        2 * leftFactor * rightFactor * mixed) :
    mixed ^ 2 ≤ leftSq * rightSq := by
  by_cases rightZero : rightSq = 0
  · by_cases leftZero : leftSq = 0
    · have plusNonnegative := quadraticNonnegative 1 1
      have minusNonnegative := quadraticNonnegative 1 (-1)
      rw [leftZero, rightZero] at plusNonnegative minusNonnegative
      have plusFormula :
          (1 : Fraction.Rational) ^ 2 * 0 + 1 ^ 2 * 0 +
              2 * 1 * 1 * mixed = 2 * mixed := by
        ring1
      have minusFormula :
          (1 : Fraction.Rational) ^ 2 * 0 + (-1) ^ 2 * 0 +
              2 * 1 * (-1) * mixed = -2 * mixed := by
        ring1
      rw [plusFormula] at plusNonnegative
      rw [minusFormula] at minusNonnegative
      have mixedNonnegative : 0 ≤ mixed := by
        apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct
          (c := (2 : Fraction.Rational))
        · calc
            0 * 2 = 0 := by ring1
            _ ≤ 2 * mixed := plusNonnegative
            _ = mixed * 2 := by ring1
        · decide
      have mixedNonpositive : mixed ≤ 0 := by
        apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct
          (c := (2 : Fraction.Rational))
        · have doubledNonpositive : 2 * mixed ≤ 0 :=
            Fraction.Order.Arithmetic.le_of_sub_nonneg_direct (by
              calc
                0 ≤ -2 * mixed := minusNonnegative
                _ = 0 - 2 * mixed := by ring1)
          calc
            mixed * 2 = 2 * mixed := by ring1
            _ ≤ 0 := doubledNonpositive
            _ = 0 * 2 := by ring1
        · decide
      have mixedZero : mixed = 0 :=
        Fraction.Order.Basic.Compatibility.le_antisymm _ _
          mixedNonpositive mixedNonnegative
      rw [mixedZero, leftZero, rightZero]
      exact le_rfl
    · have leftPositive : 0 < leftSq :=
        lt_of_le_of_ne leftNonnegative (Ne.symm leftZero)
      have combinationNonnegative := quadraticNonnegative (-mixed) leftSq
      have factored :
          (-mixed) ^ 2 * leftSq + leftSq ^ 2 * rightSq +
                2 * (-mixed) * leftSq * mixed =
            (leftSq * rightSq - mixed ^ 2) * leftSq := by
        ring1
      rw [factored] at combinationNonnegative
      have differenceNonnegative :
          0 ≤ leftSq * rightSq - mixed ^ 2 := by
        apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct
          (c := leftSq)
        · simpa only [zero_mul] using combinationNonnegative
        · exact leftPositive
      exact Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
        differenceNonnegative
  · have rightPositive : 0 < rightSq :=
      lt_of_le_of_ne rightNonnegative (Ne.symm rightZero)
    have combinationNonnegative := quadraticNonnegative rightSq (-mixed)
    have factored :
        rightSq ^ 2 * leftSq + (-mixed) ^ 2 * rightSq +
              2 * rightSq * (-mixed) * mixed =
          (leftSq * rightSq - mixed ^ 2) * rightSq := by
      ring1
    rw [factored] at combinationNonnegative
    have differenceNonnegative :
        0 ≤ leftSq * rightSq - mixed ^ 2 := by
      apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct
        (c := rightSq)
      · simpa only [zero_mul] using combinationNonnegative
      · exact rightPositive
    exact Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
      differenceNonnegative

end Purelib.Data.Rat

end
