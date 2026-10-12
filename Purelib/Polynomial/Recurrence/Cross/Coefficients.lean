module
import Purelib.Polynomial.Recurrence.Spread.Basic

import Purelib.Algebra.Field.ExplicitField
public import Purelib.Algebra.Field.Finite.Five
public import Purelib.Polynomial.Recurrence.Cross.Basic
import Purelib.Polynomial.Recurrence.Cross.Spread
public import Purelib.Polynomial.Recurrence.Spread.Coefficients.Scaled
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

open Purelib.Algebra.Field

open Purelib.Polynomial

section
@[expose] public section

/-!
# Divine Proportions, Chapter 8: scaled cross coefficients

Exercise 8.20 asks how the coefficients of `Cₙ*(r)=4Cₙ(r/4)` are read
from the spread array.  Odd rows are copied with alternating signs.  Even rows
are subtracted from the constant `4`.  The scaling calculation is first proved
without division for an arbitrary commutative ring.
-/

namespace Purelib.Polynomial.Recurrence.Cross.Coefficients

open Purelib.Algebra

/-- The scaled even cross polynomial is four minus the corresponding alternating spread-coefficient expansion.

The formula evaluates at one quarter of the displayed argument and requires four to be nonzero in the explicit
coefficient field. -/
theorem exercise_8_20_even
    {K : Type*} [ExplicitField K]
    (half : Nat) (value : K) (fourNonzero : (4 : K) ≠ 0) :
    4 * Recurrence.Cross.Basic.crossPolynomial (half + half) (value / 4) =
      4 - Recurrence.Spread.Coefficients.Scaled.scaledSpreadCoefficientExpansion (half + half) value := by
  rw [(Recurrence.Cross.Spread.crossPolynomial_even_and_odd half (value / 4)).1]
  calc
    4 * (1 - Recurrence.Spread.Basic.spreadPolynomial (half + half) (value / 4)) =
        4 - 4 * Recurrence.Spread.Basic.spreadPolynomial (half + half) (value / 4) := by ring1
    _ = 4 - Recurrence.Spread.Coefficients.Scaled.scaledSpreadCoefficientExpansion (half + half) value := by
      rw [Recurrence.Spread.Coefficients.Scaled.scaledSpreadCoefficientExpansion_source
        (half + half) value fourNonzero]

/-- The scaled odd cross polynomial equals the corresponding alternating spread-coefficient expansion.

The formula evaluates at one quarter of the displayed argument and requires four to be nonzero in the explicit
coefficient field. -/
theorem exercise_8_20_odd
    {K : Type*} [ExplicitField K]
    (half : Nat) (value : K) (fourNonzero : (4 : K) ≠ 0) :
    4 * Recurrence.Cross.Basic.crossPolynomial (half + half + 1) (value / 4) =
      Recurrence.Spread.Coefficients.Scaled.scaledSpreadCoefficientExpansion (half + half + 1) value := by
  rw [(Recurrence.Cross.Spread.crossPolynomial_even_and_odd half (value / 4)).2]
  exact Recurrence.Spread.Coefficients.Scaled.scaledSpreadCoefficientExpansion_source
    (half + half + 1) value fourNonzero

/-- The first four scaled cross polynomials illustrate the two rules exactly:
`r`, `4-4r+r²`, `9r-6r²+r³`, and
`4-16r+20r²-8r³+r⁴`. -/
theorem scaledCrossPolynomial_first_four
    {K : Type*} [ExplicitField K]
    (value : K) (fourNonzero : (4 : K) ≠ 0) :
    4 * Recurrence.Cross.Basic.crossPolynomial 1 (value / 4) = value ∧
      4 * Recurrence.Cross.Basic.crossPolynomial 2 (value / 4) =
        4 - 4 * value + value ^ 2 ∧
      4 * Recurrence.Cross.Basic.crossPolynomial 3 (value / 4) =
        9 * value - 6 * value ^ 2 + value ^ 3 ∧
      4 * Recurrence.Cross.Basic.crossPolynomial 4 (value / 4) =
        4 - 16 * value + 20 * value ^ 2 - 8 * value ^ 3 + value ^ 4 := by
  let quarter := value / 4
  have recoverValue : value = 4 * quarter := by
    unfold quarter
    calc
      value = value / 4 * 4 :=
        (ExplicitField.div_mul_cancel value fourNonzero).symm
      _ = 4 * (value / 4) := by ring1
  change
    4 * Recurrence.Cross.Basic.crossPolynomial 1 quarter = value ∧
      4 * Recurrence.Cross.Basic.crossPolynomial 2 quarter =
        4 - 4 * value + value ^ 2 ∧
      4 * Recurrence.Cross.Basic.crossPolynomial 3 quarter =
        9 * value - 6 * value ^ 2 + value ^ 3 ∧
      4 * Recurrence.Cross.Basic.crossPolynomial 4 quarter =
        4 - 16 * value + 20 * value ^ 2 - 8 * value ^ 3 + value ^ 4
  rw [recoverValue]
  constructor
  · simp only [Recurrence.Cross.Basic.crossPolynomial, -eq_self, -iff_self]
    rfl
  constructor
  · simp only [Recurrence.Cross.Basic.crossPolynomial]
    ring1
  constructor
  · simp only [Recurrence.Cross.Basic.crossPolynomial]
    ring1
  · simp only [Recurrence.Cross.Basic.crossPolynomial]
    ring1

end Purelib.Polynomial.Recurrence.Cross.Coefficients

end
