module
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Gaussian.Logarithm.Local.Polynomial
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
public import Purelib.Data.Rat.Geometric.Quarter
import Purelib.Polynomial.Ascending.Rational.Evaluation

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

section
public section

/-! Approximation Gaussian Logarithm Local Polynomial Majorant and its finite structural certificates. -/

namespace Purelib.Approximation.Gaussian.Logarithm.Local.Polynomial.Majorant

open Purelib
open Purelib.Approximation.Gaussian.Logarithm.Local
open Purelib.Data.Rat
open Purelib.Data.Rat.Geometric
open Purelib.Polynomial.Ascending.Rational

/-- Every positive odd reciprocal coefficient of the finite local logarithm is at most two. -/
theorem localLogCoefficient_le_two (index : Nat) :
    2 / (2 * (index : Fraction.Rational) + 1) ≤ 2 := by
  have indexNonnegative : (0 : Fraction.Rational) ≤ (index : Fraction.Rational) := by
    have castBound := Fraction.Cast.Order.natCast_le_direct
      (Nat.zero_le index)
    simpa only [Nat.cast_zero] using castBound
  have denominatorPositive : 0 < 2 * (index : Fraction.Rational) + 1 :=
    Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        indexNonnegative)
      (by decide)
  apply (Fraction.Order.Field.div_le_iff_pos denominatorPositive).mpr
  have denominatorAtLeastOne :
      (1 : Fraction.Rational) ≤ 2 * (index : Fraction.Rational) + 1 := by
    calc
      (1 : Fraction.Rational) = 0 + 1 := by ring1
      _ ≤ 2 * (index : Fraction.Rational) + 1 :=
        Fraction.Order.Arithmetic.add_le_add_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
          indexNonnegative) (Fraction.Order.Basic.le_refl _)
  calc
    (2 : Fraction.Rational) ≤ 2 * 1 := by
      rw [Fraction.Field.mul_one_direct]
    _ ≤ 2 * (2 * (index : Fraction.Rational) + 1) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        denominatorAtLeastOne (by decide)

/-- The finite local logarithm polynomial at one half is bounded by the matching quarter-geometric sum. -/
theorem scalarEval_localLog_half_le_quarterSum : ∀ depth,
    Evaluation.scalarEval (1 / 2) (Polynomial.localLog depth) ≤ Quarter.quarterSum (depth + 1)
  | 0 => by
      rw [Polynomial.localLog, Evaluation.scalarEval_monomial, Quarter.quarterSum, Quarter.quarterSum]
      decide
  | depth + 1 => by
      rw [Polynomial.localLog, Evaluation.scalarEval_add, Evaluation.scalarEval_monomial,
        Quarter.quarterSum]
      apply Fraction.Order.Arithmetic.add_le_add_direct
        (Purelib.Approximation.Gaussian.Logarithm.Local.Polynomial.Majorant.scalarEval_localLog_half_le_quarterSum
        depth)
      calc
        (2 / (2 * ((depth + 1 : Nat) : Fraction.Rational) + 1)) *
            (1 / 2 : Fraction.Rational) ^ (2 * (depth + 1) + 1) ≤
            2 * (1 / 2 : Fraction.Rational) ^ (2 * (depth + 1) + 1) :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
            (Approximation.Gaussian.Logarithm.Local.Polynomial.Majorant.localLogCoefficient_le_two (depth + 1))
            (Fraction.Order.Arithmetic.pow_nonneg_direct (by decide) _)
        _ = (1 / 4 : Fraction.Rational) ^ (depth + 1) :=
          Quarter.twice_half_odd_power (depth + 1)

/-- Every finite local logarithm polynomial at one half is at most four thirds. -/
theorem scalarEval_localLog_half_le (depth : Nat) :
    Evaluation.scalarEval (1 / 2) (Polynomial.localLog depth) ≤ 4 / 3 :=
  (Approximation.Gaussian.Logarithm.Local.Polynomial.Majorant.scalarEval_localLog_half_le_quarterSum depth).trans
    (Quarter.quarterSum_le (depth + 1))
end Purelib.Approximation.Gaussian.Logarithm.Local.Polynomial.Majorant

end
