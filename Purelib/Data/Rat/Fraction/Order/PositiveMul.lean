module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

section
@[expose] public section

/-!
# Divine Proportions, Chapter 20: finite triangle spread rules

The order-sensitive statements are made over the project's executable
constructive rationals.  Absolute-value bounds are kept in their equivalent
two-sided additive form, so the proofs use only decidable rational order and
finite field arithmetic.
-/

namespace Purelib.Data.Rat.Fraction.Order.PositiveMul

open Purelib.Data.Rat
/-- Multiplication by a positive rational preserves and reflects nonnegativity. -/
public theorem nonnegative_mul_iff_of_positive
    (factor value : Fraction.Rational) (factorPositive : 0 < factor) :
    0 ≤ factor * value ↔ 0 ≤ value := by
  constructor
  · intro productNonnegative
    by_cases valueNonnegative : 0 ≤ value
    · exact valueNonnegative
    · have valueNegative : value < 0 :=
        Fraction.Order.Arithmetic.lt_of_not_ge_direct valueNonnegative
      have productNegative :=
        Fraction.Order.Arithmetic.mul_neg_of_pos_of_neg_direct
          factorPositive valueNegative
      exact ((not_lt_of_ge productNonnegative) productNegative).elim
  · intro valueNonnegative
    exact Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Order.Arithmetic.le_of_lt_direct factorPositive)
      valueNonnegative

/-- Multiplication by a positive rational preserves and reflects nonpositivity. -/
public theorem nonpositive_mul_iff_of_positive
    (factor value : Fraction.Rational) (factorPositive : 0 < factor) :
    factor * value ≤ 0 ↔ value ≤ 0 := by
  constructor
  · intro productNonpositive
    by_cases valueNonpositive : value ≤ 0
    · exact valueNonpositive
    · have valuePositive : 0 < value :=
        Fraction.Order.Arithmetic.lt_of_not_ge_direct valueNonpositive
      have productPositive :=
        Fraction.Order.Arithmetic.mul_pos_direct factorPositive valuePositive
      exact ((not_lt_of_ge productNonpositive) productPositive).elim
  · intro valueNonpositive
    have negativeValueNonnegative : 0 ≤ -value := by
      have reversed := Fraction.Order.Arithmetic.neg_le_neg_direct
        valueNonpositive
      simpa only [neg_zero] using reversed
    have negativeProductNonnegative : 0 ≤ factor * (-value) :=
      Fraction.Order.Arithmetic.mul_nonneg_direct
        (Fraction.Order.Arithmetic.le_of_lt_direct factorPositive)
        negativeValueNonnegative
    have reversed := Fraction.Order.Arithmetic.neg_le_neg_direct
      negativeProductNonnegative
    calc
      factor * value = -(factor * (-value)) := by ring1
      _ ≤ 0 := by simpa only [neg_zero] using reversed

end Purelib.Data.Rat.Fraction.Order.PositiveMul

end
