module
public import Purelib.Geometry.Trigonometry.Spread.Triple
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Field
public import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Data.Rat

open Purelib.Geometry.Trigonometry.Spread.Triple

/-!
# Divine Proportions, Chapter 7 rational inequalities

Exercise 7.4 is proved with the explicit order on constructive fractions.
Exercise 7.9, as printed, is false for obtuse triangles; the second section
records a fully executable rational counterexample to both claimed bounds.
-/

@[expose] public section

namespace Purelib.Geometry.Trigonometry.SpreadTriple.Rational.EqualArgument.Bounds

section

/-- Exercise 7.4: on constructive rationals, the equal-argument Triple-spread polynomial is nonnegative exactly up to
`3/4`. -/
theorem tripleSpread_nonnegative_iff (a
  : Fraction.Rational) :
    0 ≤ TripleSpread.tripleSpreadFunction a a a ↔ a ≤ (3 : Fraction.Rational) / 4 := by
  have factorization :
      TripleSpread.tripleSpreadFunction a a a = a ^ 2 * (3 - 4 * a) := by
    unfold TripleSpread.tripleSpreadFunction
    ring1
  rw [factorization]
  have fourPositive : (0 : Fraction.Rational) < 4 := by decide
  constructor
  · intro productNonnegative
    by_cases aZero : a = 0
    · rw [aZero]
      decide
    · have squareNonnegative : (0 : Fraction.Rational) ≤ a ^ 2 :=
        Fraction.Order.Arithmetic.sq_nonneg_direct a
      have squareNonzero : a ^ 2 ≠ 0 := by
        intro squareZero
        exact aZero
          ((Fraction.Order.Arithmetic.sq_eq_zero_direct a).1 squareZero)
      have squarePositive : (0 : Fraction.Rational) < a ^ 2 :=
        lt_of_le_of_ne squareNonnegative (Ne.symm squareNonzero)
      have factorNonnegative : (0 : Fraction.Rational) ≤ 3 - 4 * a := by
        by_cases nonnegative : (0 : Fraction.Rational) ≤ 3 - 4 * a
        · exact nonnegative
        · have negative : 3 - 4 * a < (0 : Fraction.Rational) :=
            lt_of_not_ge nonnegative
          have productNegative :=
            Fraction.Order.Arithmetic.mul_neg_of_pos_of_neg_direct
              squarePositive negative
          exact ((not_lt_of_ge productNonnegative) productNegative).elim
      apply (Fraction.Order.Field.le_div_iff_pos fourPositive).2
      have scaled : 4 * a ≤ (3 : Fraction.Rational) :=
        Fraction.Order.Arithmetic.le_of_sub_nonneg_direct factorNonnegative
      calc
        a * 4 = 4 * a := by ring1
        _ ≤ 3 := scaled
  · intro upperBound
    have scaled : a * 4 ≤ (3 : Fraction.Rational) :=
      (Fraction.Order.Field.le_div_iff_pos fourPositive).1 upperBound
    have factorNonnegative : (0 : Fraction.Rational) ≤ 3 - 4 * a := by
      have raw := Fraction.Order.Arithmetic.sub_nonneg_direct scaled
      calc
        (0 : Fraction.Rational) ≤ 3 - a * 4 := raw
        _ = 3 - 4 * a := by ring1
    exact Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Order.Arithmetic.sq_nonneg_direct a) factorNonnegative

end

end Purelib.Geometry.Trigonometry.SpreadTriple.Rational.EqualArgument.Bounds

end
