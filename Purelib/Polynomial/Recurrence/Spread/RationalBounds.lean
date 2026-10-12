module
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Polynomial.Recurrence.Chebyshev.First.Basic
public import Purelib.Polynomial.Recurrence.Spread.Basic
import Purelib.Polynomial.Recurrence.Spread.Chebyshev

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Polynomial.Recurrence.Chebyshev.First.RationalBounds
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Field
public import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Algebra.Field

open Purelib.Data.Rat

open Purelib.Polynomial

section
@[expose] public section

/-!
# Divine Proportions, Chapter 8: constructive rational spread bounds

Exercise 8.3 is retained over the source's rational field.  The proof uses a
finite Chebyshev square invariant and the project-owned constructive order on
explicit fractions; it introduces neither completed real numbers nor limits.
-/

namespace Purelib.Polynomial.Recurrence.Spread.RationalBounds.ExerciseEightThree

variable {K : Type*} [ExplicitField K]
section

/-- Exercise 8.3 over the exact constructive rational field: every requested
finite spread-polynomial evaluation maps `[0,1]` into `[0,1]`. -/
theorem exercise_8_3
    (index : Nat) (value : Fraction.Rational)
    (lowerBound : 0 ≤ value) (upperBound : value ≤ 1) :
    0 ≤ Recurrence.Spread.Basic.spreadPolynomial index value ∧
      Recurrence.Spread.Basic.spreadPolynomial index value ≤ 1 := by
  have twoNonnegative : (0 : Fraction.Rational) ≤ 2 := by decide
  have oneMinusValueNonnegative : 0 ≤ (1 : Fraction.Rational) - value :=
    Fraction.Order.Arithmetic.sub_nonneg_direct upperBound
  have transformedUpper : (1 : Fraction.Rational) - 2 * value ≤ 1 := by
    apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
    calc
      0 ≤ (2 : Fraction.Rational) * value :=
        Fraction.Order.Arithmetic.mul_nonneg_direct twoNonnegative lowerBound
      _ = 1 - (1 - 2 * value) := by ring1
  have transformedLower : (-1 : Fraction.Rational) ≤ 1 - 2 * value := by
    apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
    calc
      0 ≤ (2 : Fraction.Rational) * (1 - value) :=
        Fraction.Order.Arithmetic.mul_nonneg_direct twoNonnegative
          oneMinusValueNonnegative
      _ = (1 - 2 * value) - (-1) := by ring1
  rcases Recurrence.Chebyshev.First.RationalBounds.ExerciseEightThree.chebyshevFirst_mem_unitInterval index (1 - 2 *
    value)
      transformedLower transformedUpper with
    ⟨chebyshevLower, chebyshevUpper⟩
  have cleared := Recurrence.Spread.Chebyshev.exercise_8_4_cleared index value
  have twoPositive : (0 : Fraction.Rational) < 2 := by decide
  constructor
  · apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct _
      twoPositive
    calc
      (0 : Fraction.Rational) * 2 = 0 := by ring1
      _ ≤ 1 - Recurrence.Chebyshev.First.Basic.chebyshevFirst index (1 - 2 * value) :=
        Fraction.Order.Arithmetic.sub_nonneg_direct chebyshevUpper
      _ = Recurrence.Spread.Basic.spreadPolynomial index value * 2 := by rw [← cleared]; ring1
  · apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct _
      twoPositive
    calc
      Recurrence.Spread.Basic.spreadPolynomial index value * 2 =
          1 - Recurrence.Chebyshev.First.Basic.chebyshevFirst index (1 - 2 * value) := by rw [← cleared]; ring1
      _ ≤ 2 := by
        apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
        have shifted :=
          Fraction.Order.Arithmetic.sub_nonneg_direct chebyshevLower
        calc
          0 ≤ Recurrence.Chebyshev.First.Basic.chebyshevFirst index (1 - 2 * value) - (-1 : Fraction.Rational) :=
            shifted
          _ = 2 - (1 - Recurrence.Chebyshev.First.Basic.chebyshevFirst index (1 - 2 * value)) := by ring1
      _ = (1 : Fraction.Rational) * 2 := by ring1

end

end Purelib.Polynomial.Recurrence.Spread.RationalBounds.ExerciseEightThree

end
