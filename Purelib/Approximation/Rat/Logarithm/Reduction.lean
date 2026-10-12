module
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Data.Rat

section
public section

/-!
# Finite logarithm Horner approximation

For a displayed positive rational input in `[1/2,2]`, this module computes only
finite truncations of `2z(1 + z²/3 + z⁴/5 + ⋯)`, where
`z = (x - 1)/(x + 1)`.  The ellipsis is descriptive only: every definition
below is structural recursion with a natural depth, and every semantic
predicate has an explicit later finite index witness.  No completed logarithm,
infinite series, or limit is introduced.
-/

namespace Purelib.Approximation.Rat.Logarithm.Reduction

/-- Compute the rational fractional reduction `(x - 1) / (x + 1)`.

On the displayed interval from one half to two, this maps the input into the interval from minus one third to one third.
-/
@[expose] def reducedArgument (x : Fraction.Rational) : Fraction.Rational :=
  (x - 1) / (x + 1)

/-- Square the rational reduced logarithm argument. -/
@[expose] def squaredArgument (x : Fraction.Rational) : Fraction.Rational :=
  Approximation.Rat.Logarithm.Reduction.reducedArgument x ^ 2

/-- An input at least one half has positive reduction denominator. -/
theorem denominator_pos {x : Fraction.Rational} (halfLe : 1 / 2 ≤ x) :
    0 < x + 1 := by
  exact Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct
    ((by decide : (0 : Fraction.Rational) ≤ 1 / 2).trans halfLe)
    (by decide)

/-- For an input between one half and two, the reduced argument is at most one third. -/
theorem reducedArgument_le_third {x : Fraction.Rational} (halfLe : 1 / 2 ≤ x)
    (leTwo : x ≤ 2) :
    Approximation.Rat.Logarithm.Reduction.reducedArgument x ≤ 1 / 3 := by
  apply (Fraction.Order.Field.div_le_iff_pos (Approximation.Rat.Logarithm.Reduction.denominator_pos halfLe)).mpr
  apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct
    (c := (3 : Fraction.Rational)) _ (by decide)
  have twice : 2 * x ≤ 2 * 2 :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct leTwo (by decide)
  have rightCancel : (1 / 3 * (x + 1)) * (3 : Fraction.Rational) = x + 1 := by
    calc
      (1 / 3 * (x + 1)) * (3 : Fraction.Rational) =
          (x + 1) * ((1 / 3 : Fraction.Rational) * 3) := by ring1
      _ = (x + 1) * 1 := by rw [show (1 / 3 : Fraction.Rational) * 3 = 1 by decide]
      _ = x + 1 := Fraction.Field.mul_one_direct _
  apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
  calc
    0 ≤ 2 * 2 - 2 * x := Fraction.Order.Arithmetic.sub_nonneg_direct twice
    _ = (x + 1) - (x - 1) * 3 := by ring1
    _ = (1 / 3 * (x + 1)) * 3 - (x - 1) * 3 := by rw [rightCancel]

/-- An input at least one half has reduced argument at least minus one third. -/
theorem neg_third_le_reducedArgument {x : Fraction.Rational} (halfLe : 1 / 2 ≤ x) :
    -(1 / 3 : Fraction.Rational) ≤ Approximation.Rat.Logarithm.Reduction.reducedArgument x := by
  apply (Fraction.Order.Field.le_div_iff_pos
    (Approximation.Rat.Logarithm.Reduction.denominator_pos halfLe)).mpr
  apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct
    (c := (3 : Fraction.Rational)) _ (by decide)
  have scaledHalf := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    halfLe (by decide : (0 : Fraction.Rational) ≤ 4)
  have twoLeFourX : (2 : Fraction.Rational) ≤ 4 * x := by
    calc
      (2 : Fraction.Rational) = 4 * (1 / 2) := by decide
      _ ≤ 4 * x := scaledHalf
  have leftCancel :
      (-(1 / 3 : Fraction.Rational) * (x + 1)) * 3 = -(x + 1) := by
    calc
      (-(1 / 3 : Fraction.Rational) * (x + 1)) * 3 =
          (x + 1) * (-(1 / 3 : Fraction.Rational) * 3) := by ring1
      _ = (x + 1) * -1 := by
        rw [show -(1 / 3 : Fraction.Rational) * 3 = -1 by decide]
      _ = -(x + 1) := by ring1
  apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
  calc
    0 ≤ 4 * x - 2 := Fraction.Order.Arithmetic.sub_nonneg_direct twoLeFourX
    _ = (x - 1) * 3 - -(x + 1) := by ring1
    _ = (x - 1) * 3 - (-(1 / 3 : Fraction.Rational) * (x + 1)) * 3 := by
      rw [leftCancel]

/-- The squared reduced argument is nonnegative. -/
theorem squaredArgument_nonneg (x : Fraction.Rational) :
    0 ≤ Approximation.Rat.Logarithm.Reduction.squaredArgument x :=
  Fraction.Order.Arithmetic.sq_nonneg_direct (Approximation.Rat.Logarithm.Reduction.reducedArgument x)

/-- For an input between one half and two, the squared reduced argument is at most one ninth. -/
theorem squaredArgument_le_ninth {x : Fraction.Rational} (halfLe : 1 / 2 ≤ x)
    (leTwo : x ≤ 2) :
    Approximation.Rat.Logarithm.Reduction.squaredArgument x ≤ 1 / 9 := by
  have leftNonnegative : 0 ≤ Approximation.Rat.Logarithm.Reduction.reducedArgument x + 1 / 3 := by
    have shifted := Fraction.Order.Arithmetic.add_le_add_right_direct
      (Approximation.Rat.Logarithm.Reduction.neg_third_le_reducedArgument halfLe)
      (1 / 3 : Fraction.Rational)
    calc
      0 = -(1 / 3 : Fraction.Rational) + 1 / 3 := by ring1
      _ ≤ Approximation.Rat.Logarithm.Reduction.reducedArgument x + 1 / 3 := shifted
  have rightNonnegative : 0 ≤ 1 / 3 - Approximation.Rat.Logarithm.Reduction.reducedArgument x :=
    Fraction.Order.Arithmetic.sub_nonneg_direct (Approximation.Rat.Logarithm.Reduction.reducedArgument_le_third halfLe
      leTwo)
  have productNonnegative := Fraction.Order.Arithmetic.mul_nonneg_direct
    leftNonnegative rightNonnegative
  apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
  calc
    0 ≤ (Approximation.Rat.Logarithm.Reduction.reducedArgument x + 1 / 3) *
        (1 / 3 - Approximation.Rat.Logarithm.Reduction.reducedArgument x) := productNonnegative
    _ = (1 / 3 : Fraction.Rational) ^ 2 - Approximation.Rat.Logarithm.Reduction.reducedArgument x ^ 2 := by ring1
    _ = 1 / 9 - Approximation.Rat.Logarithm.Reduction.squaredArgument x := by
      rw [show (1 / 3 : Fraction.Rational) ^ 2 = 1 / 9 by decide]
      rfl
end Purelib.Approximation.Rat.Logarithm.Reduction

end
