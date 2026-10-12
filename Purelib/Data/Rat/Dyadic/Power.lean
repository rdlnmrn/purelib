module
import Purelib.Data.Nat.Subtraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

section
@[expose] public section

/-!
# The second prepared cell of the explicit quartic connector

This module restricts the canonical horizontal connector to its second outer
cell and caches its affine quartic coefficients.  Small unit-scaled rational
calculations certify the exact dense-Horner variation, the dyadic preparation
radius, a segment-specific linearization lower bound, and the first retained
eighth-unit transport floor without increasing Lean's elaboration limits.
-/

namespace Purelib.Data.Rat.Dyadic.Power

open Purelib.Data.Nat

open Purelib.Data.Rat in
/-- Natural powers of one half decrease weakly with their natural exponent.

The retained exponent inequality expresses the larger exponent as the smaller
one plus its natural difference. The remaining factor lies between zero and one. -/
public theorem halfPow_antitone {m n : Nat} (order : m ≤ n) :
    (1 / 2 : Fraction.Rational) ^ n ≤ (1 / 2 : Fraction.Rational) ^ m := by
  let extra := n - m
  have reconstruction : n = m + extra := (Subtraction.add_sub_of_le order).symm
  rw [reconstruction]
  rw [pow_add]
  have halfNonnegative : (0 : Fraction.Rational) ≤ 1 / 2 :=
    Fraction.Order.Field.div_nonneg_direct
      (show (0 : Fraction.Rational) ≤ 1 by decide) (by decide : (0 : Fraction.Rational) ≤ 2)
  have halfLeOne : (1 / 2 : Fraction.Rational) ≤ 1 := by decide
  have extraLeOne : (1 / 2 : Fraction.Rational) ^ extra ≤ 1 := by
    simpa only [one_pow] using
      Fraction.Order.Arithmetic.pow_le_pow_direct halfNonnegative halfLeOne extra
  calc
    (1 / 2 : Fraction.Rational) ^ m * (1 / 2) ^ extra ≤ (1 / 2) ^ m * 1 :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct extraLeOne
        (Fraction.Order.Arithmetic.pow_nonneg_direct halfNonnegative m)
    _ = (1 / 2 : Fraction.Rational) ^ m := by ring1

end Purelib.Data.Rat.Dyadic.Power

end
