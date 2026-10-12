module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Scale
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Polynomial.Ascending.Rational.Basic
import Purelib.Polynomial.Ascending.Rational.Evaluation
public import Purelib.Polynomial.Ascending.Rational.GaussianEvaluation
public import Purelib.Polynomial.Ascending.Rational.Nonnegative
import Purelib.Polynomial.Ascending.Rational.Nonnegative.Evaluation

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
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

namespace Purelib.Polynomial.Ascending.Rational.GaussianMajorant

/-- A nonnegative rational coefficient table has its Gaussian value bounded by its scalar value at `1/2`.

When the input quadrance is at most `1/9`, the Gaussian value's quadrance is at most twice the square of that scalar
Horner value. The estimate follows the displayed finite coefficient recursion. -/
theorem evalCoefficients_normSq_le_scalarHalf : ∀
  coefficients
    (z : Gaussian.Basic.Canonical), Data.Gaussian.Norm.Basic.normSq z ≤ 1 / 9 →
    (∀ degree, 0 ≤ Ascending.Rational.Basic.coefficientCoefficients coefficients degree) →
    Data.Gaussian.Norm.Basic.normSq (Ascending.Rational.GaussianEvaluation.evalCoefficients z coefficients) ≤
      2 * Ascending.Rational.Evaluation.scalarEvalCoefficients (1 / 2) coefficients ^ 2
  | [], z, zBound, coefficientsNonnegative => by
      rw [Ascending.Rational.GaussianEvaluation.evalCoefficients, Gaussian.Norm.Basic.normSq_zero,
        Ascending.Rational.Evaluation.scalarEvalCoefficients]
      decide
  | coefficient :: remaining, z, zBound, coefficientsNonnegative => by
      let tailMagnitude := Ascending.Rational.Evaluation.scalarEvalCoefficients (1 / 2) remaining
      have coefficientNonnegative : 0 ≤ coefficient :=
        coefficientsNonnegative 0
      have tailNonnegative : 0 ≤ tailMagnitude :=
        Ascending.Rational.Nonnegative.Evaluation.scalarEvalCoefficients_nonnegative (by decide) remaining
          (fun degree => coefficientsNonnegative (degree + 1))
      have tailBound := evalCoefficients_normSq_le_scalarHalf
        remaining z
        zBound (fun degree => coefficientsNonnegative (degree + 1))
      have productBound :
          Data.Gaussian.Norm.Basic.normSq (z * Ascending.Rational.GaussianEvaluation.evalCoefficients z remaining) ≤
            (2 / 9 : Fraction.Rational) * tailMagnitude ^ 2 := by
        rw [Gaussian.Norm.Basic.normSq_mul]
        calc
          Data.Gaussian.Norm.Basic.normSq z * Data.Gaussian.Norm.Basic.normSq
            (Ascending.Rational.GaussianEvaluation.evalCoefficients z remaining) ≤
              (1 / 9 : Fraction.Rational) *
                (2 * tailMagnitude ^ 2) :=
            Fraction.Order.Arithmetic.mul_le_mul_direct zBound tailBound
              (Gaussian.Norm.Basic.normSq_nonneg _) (by decide)
          _ = ((1 / 9 : Fraction.Rational) * 2) * tailMagnitude ^ 2 := by ring1
          _ = (2 / 9 : Fraction.Rational) * tailMagnitude ^ 2 := by
            rw [show (1 / 9 : Fraction.Rational) * 2 = 2 / 9 by
              rw [Fraction.Field.div_eq_mul_inv_direct,
                Fraction.Field.div_eq_mul_inv_direct]
              ring1]
      have insideBound :
          coefficient ^ 2 + (2 / 9 : Fraction.Rational) * tailMagnitude ^ 2 ≤
            (coefficient + (1 / 2 : Fraction.Rational) * tailMagnitude) ^ 2 := by
        have remainderNonnegative :
            0 ≤ coefficient * tailMagnitude +
              (1 / 36 : Fraction.Rational) * tailMagnitude ^ 2 :=
          add_nonneg
            (Fraction.Order.Arithmetic.mul_nonneg_direct
              coefficientNonnegative tailNonnegative)
            (Fraction.Order.Arithmetic.mul_nonneg_direct
              (Fraction.Order.Field.div_nonneg_direct
                (Fraction.Cast.Order.natCast_pos_direct
                  (n := 1) (by decide)).le
                (Fraction.Cast.Order.natCast_pos_direct
                  (n := 36) (by decide)).le)
              (Fraction.Order.Arithmetic.sq_nonneg_direct tailMagnitude))
        calc
          coefficient ^ 2 + (2 / 9 : Fraction.Rational) * tailMagnitude ^ 2 ≤
              (coefficient ^ 2 + (2 / 9 : Fraction.Rational) * tailMagnitude ^ 2) +
                (coefficient * tailMagnitude +
                  (1 / 36 : Fraction.Rational) * tailMagnitude ^ 2) :=
            le_add_of_nonneg_right remainderNonnegative
          _ = coefficient ^ 2 + coefficient * tailMagnitude +
                ((2 / 9 : Fraction.Rational) + 1 / 36) * tailMagnitude ^ 2 := by
            ring1
          _ = coefficient ^ 2 + coefficient * tailMagnitude +
                (1 / 4 : Fraction.Rational) * tailMagnitude ^ 2 := by
            rw [show (2 / 9 : Fraction.Rational) + 1 / 36 = 1 / 4 by
              have nineNonzero : (9 : Fraction.Rational) ≠ 0 :=
                (Fraction.Cast.Order.natCast_pos_direct
                  (n := 9) (by decide)).ne'
              have thirtySixNonzero : (36 : Fraction.Rational) ≠ 0 :=
                (Fraction.Cast.Order.natCast_pos_direct
                  (n := 36) (by decide)).ne'
              have fourNonzero : (4 : Fraction.Rational) ≠ 0 :=
                (Fraction.Cast.Order.natCast_pos_direct
                  (n := 4) (by decide)).ne'
              have first : (2 / 9 : Fraction.Rational) = 8 / 36 := by
                apply Fraction.Field.div_eq_div_of_cross_mul
                  nineNonzero thirtySixNonzero
                ring1
              have last : (9 / 36 : Fraction.Rational) = 1 / 4 := by
                apply Fraction.Field.div_eq_div_of_cross_mul
                  thirtySixNonzero fourNonzero
                ring1
              rw [first]
              calc
                (8 / 36 : Fraction.Rational) + 1 / 36 = 9 / 36 := by
                  rw [Fraction.Field.div_eq_mul_inv_direct,
                    Fraction.Field.div_eq_mul_inv_direct,
                    Fraction.Field.div_eq_mul_inv_direct]
                  ring1
                _ = 1 / 4 := last]
          _ = coefficient ^ 2 +
                (2 * (1 / 2 : Fraction.Rational)) * coefficient * tailMagnitude +
                (1 / 2 : Fraction.Rational) ^ 2 * tailMagnitude ^ 2 := by
            rw [show (2 : Fraction.Rational) * (1 / 2) = 1 by
                calc
                  (2 : Fraction.Rational) * (1 / 2) = (1 / 2) * 2 := by ring1
                  _ = 1 := Fraction.Field.div_mul_cancel_of_ne
                    1 2 (Fraction.Cast.Order.natCast_pos_direct
                      (n := 2) (by decide)).ne',
              show (1 / 2 : Fraction.Rational) ^ 2 = 1 / 4 by
                rw [pow_two, Fraction.Field.div_mul_div_direct]
                apply Fraction.Field.div_eq_div_of_cross_mul
                · exact Fraction.Field.mul_ne_zero_direct
                    (Fraction.Cast.Order.natCast_pos_direct
                      (n := 2) (by decide)).ne'
                    (Fraction.Cast.Order.natCast_pos_direct
                      (n := 2) (by decide)).ne'
                · exact (Fraction.Cast.Order.natCast_pos_direct
                    (n := 4) (by decide)).ne'
                · ring1]
            ring1
          _ = (coefficient + (1 / 2 : Fraction.Rational) * tailMagnitude) ^ 2 := by
            ring1
      rw [Ascending.Rational.GaussianEvaluation.evalCoefficients, Ascending.Rational.Evaluation.scalarEvalCoefficients]
      calc
        Data.Gaussian.Norm.Basic.normSq
            (Gaussian.Scale.scale coefficient 1 +
              z * Ascending.Rational.GaussianEvaluation.evalCoefficients z remaining) ≤
            2 * (Data.Gaussian.Norm.Basic.normSq (Gaussian.Scale.scale coefficient 1) +
              Data.Gaussian.Norm.Basic.normSq (z * Ascending.Rational.GaussianEvaluation.evalCoefficients z
                remaining)) :=
          Gaussian.Norm.Bounds.normSq_add_le_two _ _
        _ ≤ 2 * (coefficient ^ 2 +
              (2 / 9 : Fraction.Rational) * tailMagnitude ^ 2) := by
          have headNorm :
              Data.Gaussian.Norm.Basic.normSq (Gaussian.Scale.scale coefficient 1) =
                coefficient ^ 2 := by
            rw [Gaussian.Scale.normSq_scale, Gaussian.Norm.Basic.normSq_one]
            ring1
          rw [headNorm]
          apply Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            (add_le_add le_rfl productBound) (by decide)
        _ ≤ 2 *
            (coefficient + (1 / 2 : Fraction.Rational) * tailMagnitude) ^ 2 :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            insideBound (by decide)

/-- Bound a nonnegative-coefficient polynomial's Gaussian value by its rational half-radius value.

For input quadrance at most `1/9`, the output quadrance is at most `2 * scalarEval (1/2) polynomial ^ 2`. -/
theorem eval_normSq_le_scalarHalf {polynomial :
  Ascending.Rational.Basic.CoefficientPolynomial}
    (nonnegative : Ascending.Rational.Nonnegative.CoefficientsNonnegative polynomial) {z : Gaussian.Basic.Canonical}
    (zBound : Data.Gaussian.Norm.Basic.normSq z ≤ 1 / 9) :
    Data.Gaussian.Norm.Basic.normSq (Ascending.Rational.GaussianEvaluation.eval polynomial z) ≤ 2 *
      Ascending.Rational.Evaluation.scalarEval (1 / 2) polynomial ^ 2 :=
  evalCoefficients_normSq_le_scalarHalf polynomial.coefficients z zBound
    nonnegative
end Purelib.Polynomial.Ascending.Rational.GaussianMajorant

end
