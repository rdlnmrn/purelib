module
import Purelib.Data.Nat.Order
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

/-!
# Rational bounds for scaled reciprocals

The original positive rational scalar determines its nonzero scaled
denominator. Exact fraction cancellation bounds the product with that
reciprocal by the same fixed rational fraction.
-/

open scoped Purelib.Data.Nat

namespace Purelib.Data.Rat.Bounds.InverseScale

open Purelib.Data.Rat

/-- A positive rational times the reciprocal of sixteen times itself is at most one sixteenth.

The input positivity certifies the scaled denominator is nonzero.
Cancellation after multiplication by sixteen gives the displayed rational bound. -/
public theorem majorant_mul_scaled_inverse_le
    {majorant : Fraction.Rational} (positive : 0 < majorant) :
    majorant * (1 / (16 * majorant)) ≤ (1 / 16 : Fraction.Rational) := by
  apply (Fraction.Order.Field.le_div_iff_pos
    (show (0 : Fraction.Rational) < 16 by decide)).mpr
  calc
    (majorant * (1 / (16 * majorant))) * 16 =
        (1 / (16 * majorant)) * (16 * majorant) := by ring1
    _ = 1 := Fraction.Field.div_mul_cancel_of_ne 1
      (16 * majorant)
      (ne_of_gt (Fraction.Order.Arithmetic.mul_pos_direct
        (by decide) positive))
    _ ≤ 1 := le_rfl

end Purelib.Data.Rat.Bounds.InverseScale
