module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast.Order
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Basic

/-! Lower bounds for canonical rational quotients with positive denominators. -/

namespace Purelib.Data.Rat.Bounds.Division

/-- A positive natural denominator at most twice the numerator gives a rational quotient at least one half. -/
public theorem half_le_nat_ratio
    (numerator denominator : Nat)
    (denominatorPositive : 0 < denominator)
    (denominatorAtMostTwiceNumerator :
      (denominator : Fraction.Rational) ≤ (numerator : Fraction.Rational) * 2) :
    (1 : Fraction.Rational) / 2 ≤ numerator / denominator := by
  have twoPositive : (0 : Fraction.Rational) < 2 := by decide
  have castDenominatorPositive : (0 : Fraction.Rational) < denominator :=
    Fraction.Cast.Order.natCast_pos_direct denominatorPositive
  apply (Fraction.Order.Field.le_div_iff_pos
    castDenominatorPositive).2
  calc
    ((1 : Fraction.Rational) / 2) * denominator =
        (denominator : Fraction.Rational) / 2 := by
          rw [Fraction.Field.div_eq_mul_inv_direct,
            Fraction.Field.div_eq_mul_inv_direct]
          rw [one_mul, mul_comm]
    _ ≤ numerator :=
      (Fraction.Order.Field.div_le_iff_pos twoPositive).2
        denominatorAtMostTwiceNumerator

end Purelib.Data.Rat.Bounds.Division
