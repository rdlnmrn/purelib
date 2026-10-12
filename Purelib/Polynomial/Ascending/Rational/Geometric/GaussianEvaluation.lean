module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Scale
import Purelib.Polynomial.Ascending.Rational.Basic
import Purelib.Polynomial.Ascending.Rational.GaussianEvaluation
public import Purelib.Polynomial.Ascending.Rational.GaussianEvaluation.Truncation
public import Purelib.Polynomial.Ascending.Rational.Geometric
import Purelib.Polynomial.Ascending.Rational.Truncation

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

section
public section

/-! Polynomial Ascending Rational Geometric GaussianEvaluation and its finite structural certificates. -/

namespace Purelib.Polynomial.Ascending.Rational.Geometric.GaussianEvaluation

open Purelib.Data
open Purelib.Polynomial

/-- Multiplying the geometric prefix value by `1 - z` leaves `1 + z - 2z^(degree + 1)`.

The identity is a finite telescoping calculation and does not require `1 - z` to be nonzero. -/
theorem one_sub_mul_geometricPrefix (z : Gaussian.Basic.Canonical) : ∀ degree,
    (1 - z) * Ascending.Rational.GaussianEvaluation.eval (Ascending.Rational.Geometric.geometricPrefix degree) z =
      1 + z + Gaussian.Scale.scale (-2) (z ^ (degree + 1))
  | 0 => by
      rw [Ascending.Rational.Geometric.geometricPrefix]
      rw [show z ^ (0 + 1) = z by
        rw [Nat.zero_add, pow_one]]
      change (1 - z) *
          (Gaussian.Scale.scale 1 1 + z * 0) = _
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Scale.scale_re,
          Gaussian.Scale.scale_im, Gaussian.Basic.add_re, Gaussian.Basic.add_im, Gaussian.Basic.sub_re,
            Gaussian.Basic.sub_im,
          Gaussian.Basic.mul_re, Gaussian.Basic.mul_im, Gaussian.Basic.zero_re, Gaussian.Basic.zero_im,
            Gaussian.Basic.one_re, Gaussian.Basic.one_im] <;> ring1
  | degree + 1 => by
      rw [Ascending.Rational.Geometric.geometricPrefix, Ascending.Rational.GaussianEvaluation.eval_add,
        Ascending.Rational.GaussianEvaluation.eval_monomial, pow_succ]
      calc
        (1 - z) *
            (Ascending.Rational.GaussianEvaluation.eval (Ascending.Rational.Geometric.geometricPrefix degree) z +
              Gaussian.Scale.scale 2 (z ^ degree * z)) =
            (1 - z) * Ascending.Rational.GaussianEvaluation.eval (Ascending.Rational.Geometric.geometricPrefix degree) z
              +
              (1 - z) *
                Gaussian.Scale.scale 2 (z ^ degree * z) := by
          apply Gaussian.Basic.ext <;>
            simp only [Gaussian.Scale.scale_re,
              Gaussian.Scale.scale_im, Gaussian.Basic.add_re, Gaussian.Basic.add_im, Gaussian.Basic.sub_re,
              Gaussian.Basic.sub_im, Gaussian.Basic.mul_re, Gaussian.Basic.mul_im] <;> ring1
        _ = (1 + z +
              Gaussian.Scale.scale (-2) (z ^ (degree + 1))) +
            (1 - z) *
              Gaussian.Scale.scale 2 (z ^ degree * z) := by
          rw [Purelib.Polynomial.Ascending.Rational.Geometric.GaussianEvaluation.one_sub_mul_geometricPrefix z degree]
        _ = 1 + z +
            Gaussian.Scale.scale (-2)
              (z ^ (degree + 1 + 1)) := by
          have nextPower :
              z ^ (degree + 1 + 1) = (z ^ degree * z) * z := by
            rw [pow_succ, pow_succ]
          have currentPower : z ^ (degree + 1) = z ^ degree * z := by
            rw [pow_succ]
          rw [nextPower, currentPower]
          apply Gaussian.Basic.ext <;>
            simp only [Gaussian.Scale.scale_re,
              Gaussian.Scale.scale_im, Gaussian.Basic.add_re, Gaussian.Basic.add_im, Gaussian.Basic.sub_re,
              Gaussian.Basic.sub_im, Gaussian.Basic.mul_re, Gaussian.Basic.mul_im, Gaussian.Basic.one_re,
                Gaussian.Basic.one_im] <;> ring1

/-- The full geometric prefix value equals its evaluation through its displayed degree.

All coefficients in the dropped tail vanish. -/
theorem geometricPrefix_eval_eq_prefix (z : Gaussian.Basic.Canonical) (degree : Nat) :
    Ascending.Rational.GaussianEvaluation.eval (Ascending.Rational.Geometric.geometricPrefix degree) z =
      Ascending.Rational.GaussianEvaluation.Truncation.prefixEval z (Ascending.Rational.Geometric.geometricPrefix
        degree) (degree + 1) := by
  rw [Ascending.Rational.GaussianEvaluation.Truncation.eval_split]
  have tailZero :
      Ascending.Rational.GaussianEvaluation.eval
        ⟨(Ascending.Rational.Geometric.geometricPrefix degree).coefficients.drop (degree + 1)⟩ z = 0 := by
    apply Ascending.Rational.GaussianEvaluation.evalCoefficients_zero_of_coefficients_zero
    intro tailDegree
    rw [Ascending.Rational.Truncation.coefficientCoefficients_drop]
    change Ascending.Rational.Basic.coefficient (Ascending.Rational.Geometric.geometricPrefix degree) (degree + 1 +
      tailDegree) = 0
    rw [Ascending.Rational.Geometric.geometricPrefix_coefficient, if_neg (by omega), if_neg (by omega)]
  rw [tailZero]
  apply Gaussian.Basic.ext <;>
    simp only [Gaussian.Basic.add_re, Gaussian.Basic.add_im, Gaussian.Basic.mul_re, Gaussian.Basic.mul_im,
      Gaussian.Basic.zero_re, Gaussian.Basic.zero_im] <;> ring1
end Purelib.Polynomial.Ascending.Rational.Geometric.GaussianEvaluation

end
