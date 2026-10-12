module

import Purelib.Data.Rat.Fraction
import Purelib.Data.Nat.Subtraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Tactic.Ring

/-!
# Scalar bounds for positive rational powers

Finite positive exponents retain predecessor powers and compare the original
nonnegative rational with its displayed power bounds.
-/

open Purelib.Data.Rat
open Purelib.Data.Nat

namespace Purelib.Data.Rat.Fraction.Power.Order

/-- A positive power of a nonnegative rational at least one quarter has predecessor power at least one eighth.

The retained positive exponent reconstructs its predecessor by bounded natural subtraction, and scalar power comparison
preserves the stated eighth bound. -/
private theorem one_eighth_le_power_predecessor
    {value : Fraction.Rational} {exponent : Nat}
    (exponentPositive : 0 < exponent)
    (quarterLePower : (1 / 4 : Fraction.Rational) ≤ value ^ exponent)
    (nonnegative : 0 ≤ value) :
    (1 / 8 : Fraction.Rational) ≤ value ^ (exponent - 1) := by
  have predecessorSplit : exponent - 1 + 1 = exponent :=
    (Nat.add_comm _ _).trans (Subtraction.add_sub_of_le exponentPositive)
  have powerSplit : value ^ exponent = value ^ (exponent - 1) * value := by
    calc
      value ^ exponent = value ^ (exponent - 1 + 1) := by
        rw [predecessorSplit]
      _ = value ^ (exponent - 1) * value := by rw [pow_succ]
  by_cases atMostOne : value ≤ 1
  · have powerLePredecessor : value ^ exponent ≤
        value ^ (exponent - 1) := by
      rw [powerSplit]
      calc
        value ^ (exponent - 1) * value ≤
            value ^ (exponent - 1) * 1 :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            atMostOne
            (Fraction.Order.Arithmetic.pow_nonneg_direct nonnegative _)
        _ = value ^ (exponent - 1) := by ring1
    exact (show (1 / 8 : Fraction.Rational) ≤ 1 / 4 by decide).trans
      (quarterLePower.trans powerLePredecessor)
  · have oneLe : (1 : Fraction.Rational) ≤ value :=
      (Fraction.Order.Arithmetic.lt_of_not_ge_direct atMostOne).le
    have oneLePower : (1 : Fraction.Rational) ≤ value ^ (exponent - 1) := by
      have powered := Fraction.Order.Arithmetic.pow_le_pow_direct
        (show (0 : Fraction.Rational) ≤ 1 by decide) oneLe (exponent - 1)
      simpa only [one_pow] using powered
    exact (show (1 / 8 : Fraction.Rational) ≤ 1 by decide).trans oneLePower

/-- The bound one at most twice the sum of a rational and one quarter forces that rational to be at least one quarter.
-/
private theorem one_fourth_le_of_unit_triangle
    {powerNorm : Fraction.Rational}
    (bounded : (1 : Fraction.Rational) ≤
      2 * (powerNorm + (1 / 4 : Fraction.Rational))) :
    (1 / 4 : Fraction.Rational) ≤ powerNorm := by
  have halfLe : (1 / 2 : Fraction.Rational) ≤ powerNorm + 1 / 4 := by
    apply (Fraction.Order.Field.div_le_iff_pos
      (show (0 : Fraction.Rational) < 2 by decide)).2
    calc
      (1 : Fraction.Rational) ≤ 2 * (powerNorm + (1 / 4 : Fraction.Rational)) := bounded
      _ = (powerNorm + 1 / 4) * 2 := by ring1
  have shifted := Fraction.Order.Arithmetic.sub_le_sub_right_direct
    halfLe (1 / 4 : Fraction.Rational)
  calc
    (1 / 4 : Fraction.Rational) = 1 / 2 - 1 / 4 := by decide
    _ ≤ (powerNorm + 1 / 4) - 1 / 4 := shifted
    _ = powerNorm := by ring1

/-- A positive power of a rational in the unit interval is at most that rational. -/
private theorem pow_le_self_of_nonnegative_le_one
    {value : Fraction.Rational} (nonnegative : 0 ≤ value) (atMostOne : value ≤ 1)
    {exponent : Nat} (positive : 0 < exponent) : value ^ exponent ≤ value := by
  obtain ⟨preceding, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt positive)
  rw [pow_succ]
  have precedingPower := Fraction.Order.Arithmetic.pow_le_pow_direct
    nonnegative atMostOne preceding
  calc
    value ^ preceding * value ≤ 1 * value :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        (by simpa only [one_pow] using precedingPower) nonnegative
    _ = value := by ring1

/-- A nonnegative rational whose positive power is at most five halves is itself at most five halves.

The positive exponent retains its predecessor; the unit comparison then bounds the same rational by its displayed power.
-/
private theorem value_le_five_halves_of_power_le
    {value : Fraction.Rational} {exponent : Nat}
    (exponentPositive : 0 < exponent) (nonnegative : 0 ≤ value)
    (powerUpper : value ^ exponent ≤ (5 / 2 : Fraction.Rational)) :
    value ≤ 5 / 2 := by
  by_cases atMostOne : value ≤ 1
  · exact atMostOne.trans (by decide)
  · have oneLe : (1 : Fraction.Rational) ≤ value :=
      (Fraction.Order.Arithmetic.lt_of_not_ge_direct atMostOne).le
    have predecessorOne : (1 : Fraction.Rational) ≤ value ^ (exponent - 1) := by
      have powered := Fraction.Order.Arithmetic.pow_le_pow_direct
        (show (0 : Fraction.Rational) ≤ 1 by decide) oneLe (exponent - 1)
      simpa only [one_pow] using powered
    have split : exponent - 1 + 1 = exponent :=
      (Nat.add_comm _ _).trans (Subtraction.add_sub_of_le exponentPositive)
    have powerSplit : value ^ exponent =
        value ^ (exponent - 1) * value := by
      calc
        value ^ exponent = value ^ (exponent - 1 + 1) := by rw [split]
        _ = value ^ (exponent - 1) * value := by rw [pow_succ]
    have valueLePower : value ≤ value ^ exponent := by
      calc
        value = value * 1 := by ring1
        _ ≤ value * value ^ (exponent - 1) :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            predecessorOne nonnegative
        _ = value ^ (exponent - 1) * value := by ring1
        _ = value ^ exponent := powerSplit.symm
    exact valueLePower.trans powerUpper

end Purelib.Data.Rat.Fraction.Power.Order
