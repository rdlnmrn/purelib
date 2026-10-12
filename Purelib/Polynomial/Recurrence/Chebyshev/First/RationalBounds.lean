module
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Polynomial.Recurrence.Chebyshev.First.Basic
import Purelib.Polynomial.Recurrence.Chebyshev.SecondPrevious.Basic
import Purelib.Polynomial.Recurrence.Chebyshev.Transitions

import Purelib.Tactic.QuotientFreeOmega
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

namespace Purelib.Polynomial.Recurrence.Chebyshev.First.RationalBounds.ExerciseEightThree

variable {K : Type*} [ExplicitField K]
section

/-- A Chebyshev value at a constructive rational input in `[-1,1]` remains
in `[-1,1]`.  The square invariant supplies both bounds directly. -/
theorem
  chebyshevFirst_mem_unitInterval
    (index : Nat) (value : Fraction.Rational)
    (lowerBound : -1 ≤ value) (upperBound : value ≤ 1) :
    -1 ≤ Recurrence.Chebyshev.First.Basic.chebyshevFirst index value ∧
      Recurrence.Chebyshev.First.Basic.chebyshevFirst index value ≤ 1 := by
  have leftFactorNonnegative : 0 ≤ (1 : Fraction.Rational) - value :=
    Fraction.Order.Arithmetic.sub_nonneg_direct upperBound
  have rightFactorNonnegative : 0 ≤ (1 : Fraction.Rational) + value := by
    have shifted :=
      Fraction.Order.Arithmetic.sub_nonneg_direct lowerBound
    calc
      0 ≤ value - (-1 : Fraction.Rational) := shifted
      _ = 1 + value := by ring1
  have radialFactorNonnegative : 0 ≤ (1 : Fraction.Rational) - value ^ 2 := by
    calc
      0 ≤ (1 - value) * (1 + value) :=
        Fraction.Order.Arithmetic.mul_nonneg_direct
          leftFactorNonnegative rightFactorNonnegative
      _ = 1 - value ^ 2 := by ring1
  have residualNonnegative :
      0 ≤ ((1 : Fraction.Rational) - value ^ 2) *
        Recurrence.Chebyshev.SecondPrevious.Basic.chebyshevSecondPrevious index value ^ 2 :=
    Fraction.Order.Arithmetic.mul_nonneg_direct radialFactorNonnegative
      (Fraction.Order.Arithmetic.sq_nonneg_direct _)
  have squareDifferenceNonnegative :
      0 ≤ (1 : Fraction.Rational) - Recurrence.Chebyshev.First.Basic.chebyshevFirst index value ^ 2 := by
    calc
      0 ≤ ((1 : Fraction.Rational) - value ^ 2) *
          Recurrence.Chebyshev.SecondPrevious.Basic.chebyshevSecondPrevious index value ^ 2 := residualNonnegative
      _ = 1 - Recurrence.Chebyshev.First.Basic.chebyshevFirst index value ^ 2 := by
        calc
          ((1 : Fraction.Rational) - value ^ 2) *
                Recurrence.Chebyshev.SecondPrevious.Basic.chebyshevSecondPrevious index value ^ 2 =
              (Recurrence.Chebyshev.First.Basic.chebyshevFirst index value ^ 2 +
                  (1 - value ^ 2) *
                    Recurrence.Chebyshev.SecondPrevious.Basic.chebyshevSecondPrevious index value ^ 2) -
                Recurrence.Chebyshev.First.Basic.chebyshevFirst index value ^ 2 := by ring1
          _ = 1 - Recurrence.Chebyshev.First.Basic.chebyshevFirst index value ^ 2 := by
            rw [Recurrence.Chebyshev.Transitions.chebyshevFirst_square_invariant]
  have squareBound :
      Recurrence.Chebyshev.First.Basic.chebyshevFirst index value ^ 2 ≤ (1 : Fraction.Rational) ^ 2 := by
    have raw := Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
      squareDifferenceNonnegative
    simpa only [one_pow] using raw
  have oneNonnegative : (0 : Fraction.Rational) ≤ 1 := by decide
  exact ⟨
    Fraction.Order.Arithmetic.neg_le_of_sq_le_sq_direct
      oneNonnegative squareBound,
    Fraction.Order.Arithmetic.le_of_sq_le_sq_direct
      oneNonnegative squareBound⟩
end

end Purelib.Polynomial.Recurrence.Chebyshev.First.RationalBounds.ExerciseEightThree

end
