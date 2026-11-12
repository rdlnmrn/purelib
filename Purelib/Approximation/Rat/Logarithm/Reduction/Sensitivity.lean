module
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Rat.Logarithm.Reduction
import Purelib.Data.Rat.Bounds.Square
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Data.Rat.Fraction.Order

open Purelib

open Purelib.Approximation.Rat.Logarithm

open Purelib.Data.Rat

section
public section

/-!
# Finite logarithm input sensitivity

All estimates compare two displayed rational inputs and two finite Horner
programs.  The overlapping input chart `[1/2,2]` supplies explicit rational
denominator and contraction bounds; there is no continuity axiom or completed
function value.
-/

namespace Purelib.Approximation.Rat.Logarithm.Reduction.Sensitivity

/-- Inputs at least one half give a reduced-logarithm denominator product of at least two. -/
theorem denominator_product_lower {x y : Fraction.Rational}
    (xHalf : 1 / 2 ≤ x) (yHalf : 1 / 2 ≤ y) :
    2 ≤ (x + 1) * (y + 1) := by
  have xLower : (3 / 2 : Fraction.Rational) ≤ x + 1 := by
    calc
      (3 / 2 : Fraction.Rational) = 1 / 2 + 1 := by decide
      _ ≤ x + 1 := add_le_add xHalf le_rfl
  have yLower : (3 / 2 : Fraction.Rational) ≤ y + 1 := by
    calc
      (3 / 2 : Fraction.Rational) = 1 / 2 + 1 := by decide
      _ ≤ y + 1 := add_le_add yHalf le_rfl
  have productLower := Arithmetic.mul_le_mul_direct
    xLower yLower (by decide : (0 : Fraction.Rational) ≤ 3 / 2)
    ((by decide : (0 : Fraction.Rational) ≤ 3 / 2).trans xLower)
  calc
    (2 : Fraction.Rational) ≤ (3 / 2 : Fraction.Rational) * (3 / 2) := by decide
    _ ≤ (x + 1) * (y + 1) := productLower

/-- The difference of two reduced logarithm arguments factors through the original input difference.

Both rational inputs are at least one half, ensuring nonzero displayed denominators. -/
theorem reducedArgument_sub {x y : Fraction.Rational}
    (xHalf : 1 / 2 ≤ x) (yHalf : 1 / 2 ≤ y) :
    reducedArgument x - reducedArgument y =
      2 * (x - y) / ((x + 1) * (y + 1)) := by
  rw [reducedArgument, reducedArgument]
  calc
    (x - 1) / (x + 1) - (y - 1) / (y + 1) =
        ((x - 1) * (y + 1) - (y - 1) * (x + 1)) /
          ((x + 1) * (y + 1)) :=
      Fraction.Field.div_sub_div_direct _ _ _ _
        (denominator_pos xHalf).ne' (denominator_pos yHalf).ne'
    _ = 2 * (x - y) / ((x + 1) * (y + 1)) := by
      congr 1
      ring1

/-- The exact rational difference factor two divided by the product of the shifted inputs. -/
@[expose] def reducedArgumentSlope (x y : Fraction.Rational) : Fraction.Rational :=
  2 / ((x + 1) * (y + 1))

/-- For inputs at least one half, the reduced-argument difference factor is nonnegative. -/
theorem reducedArgumentSlope_nonneg {x y : Fraction.Rational}
    (xHalf : 1 / 2 ≤ x) (yHalf : 1 / 2 ≤ y) :
    0 ≤ reducedArgumentSlope x y := by
  have productPositive := Arithmetic.mul_pos_direct
    (denominator_pos xHalf) (denominator_pos yHalf)
  exact Field.div_nonneg_direct (by decide)
    productPositive.le

/-- For inputs at least one half, the reduced-argument difference factor is at most one. -/
theorem reducedArgumentSlope_le_one {x y : Fraction.Rational}
    (xHalf : 1 / 2 ≤ x) (yHalf : 1 / 2 ≤ y) :
    reducedArgumentSlope x y ≤ 1 := by
  have productPositive := Arithmetic.mul_pos_direct
    (denominator_pos xHalf) (denominator_pos yHalf)
  apply (Field.div_le_iff_pos productPositive).mpr
  rw [Fraction.Field.one_mul]
  exact denominator_product_lower xHalf yHalf

/-- Logarithm argument reduction does not increase squared differences between inputs at least one half. -/
theorem reducedArgument_sub_sq_le {x y : Fraction.Rational}
    (xHalf : 1 / 2 ≤ x) (yHalf : 1 / 2 ≤ y) :
    (reducedArgument x - reducedArgument y) ^ 2 ≤ (x - y) ^ 2 := by
  have slopeSq : reducedArgumentSlope x y ^ 2 ≤ 1 := by
    have bound := Arithmetic.pow_le_pow_direct
      (reducedArgumentSlope_nonneg xHalf yHalf)
      (reducedArgumentSlope_le_one xHalf yHalf) 2
    simpa only [one_pow] using bound
  have factorization :
      2 * (x - y) / ((x + 1) * (y + 1)) =
        reducedArgumentSlope x y * (x - y) := by
    rw [reducedArgumentSlope]
    change (2 * (x - y)) * ((x + 1) * (y + 1))⁻¹ =
      (2 * ((x + 1) * (y + 1))⁻¹) * (x - y)
    calc
      (2 * (x - y)) * ((x + 1) * (y + 1))⁻¹ =
          2 * ((x - y) * ((x + 1) * (y + 1))⁻¹) :=
        Fraction.Field.mul_assoc _ _ _
      _ = 2 * (((x + 1) * (y + 1))⁻¹ * (x - y)) := by
        rw [Fraction.Field.mul_comm (x - y)]
      _ = (2 * ((x + 1) * (y + 1))⁻¹) * (x - y) :=
        (Fraction.Field.mul_assoc _ _ _).symm
  rw [reducedArgument_sub xHalf yHalf, factorization]
  rewrite [show (reducedArgumentSlope x y * (x - y)) ^ 2 =
    reducedArgumentSlope x y ^ 2 * (x - y) ^ 2 by ring1]
  have multiplied := Arithmetic.mul_le_mul_of_nonneg_right_direct
    slopeSq (Arithmetic.sq_nonneg_direct (x - y))
  simpa only [Fraction.Field.one_mul] using multiplied

/-- The squared logarithm argument does not increase squared input differences on the interval from one half to two. -/
theorem squaredArgument_sub_sq_le {x y : Fraction.Rational}
    (xHalf : 1 / 2 ≤ x) (xTwo : x ≤ 2)
    (yHalf : 1 / 2 ≤ y) (yTwo : y ≤ 2) :
    (squaredArgument x - squaredArgument y) ^ 2 ≤ (x - y) ^ 2 := by
  let zx := reducedArgument x
  let zy := reducedArgument y
  have sumSq : (zx + zy) ^ 2 ≤ 1 := by
    calc
      (zx + zy) ^ 2 ≤ 2 * (zx ^ 2 + zy ^ 2) := Bounds.Square.sq_add_le_two zx zy
      _ ≤ 2 * ((1 / 9 : Fraction.Rational) + 1 / 9) :=
        Arithmetic.mul_le_mul_of_nonneg_left_direct
          (add_le_add (squaredArgument_le_ninth xHalf xTwo)
            (squaredArgument_le_ninth yHalf yTwo)) (by decide)
      _ ≤ 1 := by decide
  have differenceSq := reducedArgument_sub_sq_le xHalf yHalf
  have identity : squaredArgument x - squaredArgument y =
      (zx - zy) * (zx + zy) := by
    dsimp only [squaredArgument, zx, zy]
    ring1
  rw [identity]
  rewrite [show ((zx - zy) * (zx + zy)) ^ 2 = (zx - zy) ^ 2 * (zx + zy) ^ 2 by ring1]
  have multiplied := Arithmetic.mul_le_mul_direct
    differenceSq sumSq (Arithmetic.sq_nonneg_direct (zx + zy))
    (Arithmetic.sq_nonneg_direct (x - y))
  simpa only [Fraction.Field.mul_one_direct] using multiplied
end Purelib.Approximation.Rat.Logarithm.Reduction.Sensitivity

end
