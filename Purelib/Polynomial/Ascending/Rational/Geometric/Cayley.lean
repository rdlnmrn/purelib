module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Division
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Power
import Purelib.Data.Gaussian.Scale
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Projective.Homography.Cayley.Bounds
public import Purelib.Polynomial.Ascending.Rational.GaussianEvaluation
public import Purelib.Polynomial.Ascending.Rational.Geometric
import Purelib.Polynomial.Ascending.Rational.Geometric.GaussianEvaluation

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Polynomial

section
@[expose] public section

/-!
# Low-to-high finite polynomials for transcendental identities

This is a deliberately small, executable polynomial kernel.  A polynomial is
only a displayed finite list of rational coefficients, stored from constant
term upward.  It exists to prove finite Taylor identities without importing a
sparse-polynomial or formal-power-series API.
-/

namespace Purelib.Polynomial.Ascending.Rational.Geometric.Cayley

/-- The geometric prefix differs from `(1 + z)/(1 - z)` by its explicit finite remainder.

When `1 - z` is nonzero, that remainder is `-2z^(degree + 1)/(1 - z)`. -/
theorem geometricPrefix_sub_chart (z :
  Gaussian.Basic.Canonical) (degree : Nat)
    (denominatorNonzero : 1 - z ≠ 0) :
    Ascending.Rational.GaussianEvaluation.eval (Ascending.Rational.Geometric.geometricPrefix degree) z - (1 + z) / (1 -
      z) =
      Gaussian.Scale.scale (-2) (z ^ (degree + 1)) /
        (1 - z) := by
  apply Gaussian.Field.mul_right_cancel_of_ne
    denominatorNonzero
  calc
    (Ascending.Rational.GaussianEvaluation.eval (Ascending.Rational.Geometric.geometricPrefix degree) z - (1 + z) / (1 -
      z)) * (1 - z) =
        Ascending.Rational.GaussianEvaluation.eval (Ascending.Rational.Geometric.geometricPrefix degree) z * (1 - z) -
          ((1 + z) / (1 - z)) * (1 - z) := by
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Basic.sub_re, Gaussian.Basic.sub_im, Gaussian.Basic.mul_re, Gaussian.Basic.mul_im] <;> ring1
    _ = Ascending.Rational.GaussianEvaluation.eval (Ascending.Rational.Geometric.geometricPrefix degree) z * (1 - z) -
      (1 + z) := by
      rw [Gaussian.Division.gaussian_div_mul_cancel _ _ denominatorNonzero]
    _ = Gaussian.Scale.scale (-2) (z ^ (degree + 1)) := by
      rw [Gaussian.Basic.mul_comm,
        Ascending.Rational.Geometric.GaussianEvaluation.one_sub_mul_geometricPrefix]
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Basic.add_re, Gaussian.Basic.add_im, Gaussian.Basic.sub_re, Gaussian.Basic.sub_im] <;> ring1
    _ = (Gaussian.Scale.scale (-2) (z ^ (degree + 1)) /
          (1 - z)) * (1 - z) :=
      (Gaussian.Division.gaussian_div_mul_cancel _ _ denominatorNonzero).symm

/-- Bound the squared error of the geometric prefix against the Cayley quotient.

If the squared norm of `z` is at most `1/9`, the error squared is at most `9 * (1/9)^(degree + 1)`, using the
denominator lower bound `4/9`. -/
theorem geometricPrefix_chart_error {z :
  Gaussian.Basic.Canonical}
    (bound : Data.Gaussian.Norm.Basic.normSq z ≤ 1 / 9) (degree : Nat) :
    Data.Gaussian.Norm.Basic.normSq (Ascending.Rational.GaussianEvaluation.eval
      (Ascending.Rational.Geometric.geometricPrefix degree) z - (1 + z) / (1 - z)) ≤
      9 * (1 / 9 : Fraction.Rational) ^ (degree + 1) := open Purelib in by
  let denominator := 1 - z
  have denominatorLower : (4 / 9 : Fraction.Rational) ≤ Data.Gaussian.Norm.Basic.normSq denominator :=
    Geometry.Projective.Homography.Cayley.Bounds.one_sub_normSq_lower bound
  have denominatorPositive : 0 < Data.Gaussian.Norm.Basic.normSq denominator :=
    (by decide : (0 : Fraction.Rational) < 4 / 9).trans_le denominatorLower
  rw [geometricPrefix_sub_chart z degree
    (Geometry.Projective.Homography.Cayley.Bounds.one_sub_ne_zero bound),
    Gaussian.Field.normSq_div _ _
      (Geometry.Projective.Homography.Cayley.Bounds.one_sub_ne_zero bound),
    Gaussian.Scale.normSq_scale,
    Gaussian.Power.normSq_pow]
  rw [show ((-2 : Fraction.Rational) ^ 2) = 4 by decide]
  apply (Fraction.Order.Field.div_le_iff_pos denominatorPositive).mpr
  have powerBound := Fraction.Order.Arithmetic.pow_le_pow_direct
    (Gaussian.Norm.Basic.normSq_nonneg z) bound (degree + 1)
  calc
    4 * Data.Gaussian.Norm.Basic.normSq z ^ (degree + 1) ≤
        4 * (1 / 9 : Fraction.Rational) ^ (degree + 1) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct powerBound
        (by decide)
    _ = (9 * (1 / 9 : Fraction.Rational) ^ (degree + 1)) * (4 / 9) := by
      calc
        4 * (1 / 9 : Fraction.Rational) ^ (degree + 1) =
            (1 / 9 : Fraction.Rational) ^ (degree + 1) * 4 := by ring1
        _ = (1 / 9 : Fraction.Rational) ^ (degree + 1) *
              (9 * (4 / 9)) := by
          rw [show (9 : Fraction.Rational) * (4 / 9) = 4 by decide]
        _ = (9 * (1 / 9 : Fraction.Rational) ^ (degree + 1)) * (4 / 9) := by
          ring1
    _ ≤ (9 * (1 / 9 : Fraction.Rational) ^ (degree + 1)) *
          Data.Gaussian.Norm.Basic.normSq denominator :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        denominatorLower
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
          (Fraction.Order.Arithmetic.pow_nonneg_direct (by decide) _))
end Purelib.Polynomial.Ascending.Rational.Geometric.Cayley

end
