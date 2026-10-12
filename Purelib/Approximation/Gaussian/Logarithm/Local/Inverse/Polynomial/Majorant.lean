module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Exponential.Taylor.Polynomial.Majorant
public import Purelib.Approximation.Gaussian.Logarithm.Local.Inverse.Polynomial
import Purelib.Approximation.Gaussian.Logarithm.Local.Polynomial
import Purelib.Approximation.Gaussian.Logarithm.Local.Polynomial.Majorant
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Power
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Geometric.Bounds
import Purelib.Polynomial.Ascending.Rational.Basic
import Purelib.Polynomial.Ascending.Rational.Evaluation
import Purelib.Polynomial.Ascending.Rational.Evaluation.Composition
import Purelib.Polynomial.Ascending.Rational.GaussianEvaluation
import Purelib.Polynomial.Ascending.Rational.GaussianMajorant
import Purelib.Polynomial.Ascending.Rational.Geometric
import Purelib.Polynomial.Ascending.Rational.Nonnegative
import Purelib.Polynomial.Ascending.Rational.Nonnegative.Evaluation
import Purelib.Polynomial.Ascending.Rational.Truncation

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

section
public section

/-! Approximation Gaussian Logarithm Local Inverse Polynomial Majorant and its finite structural certificates. -/

namespace Purelib.Approximation.Gaussian.Logarithm.Local.Inverse.Polynomial.Majorant

open Purelib
open Purelib.Approximation.Gaussian.Exponential.Taylor.Polynomial
open Purelib.Approximation.Gaussian.Logarithm.Local
open Purelib.Approximation.Gaussian.Logarithm.Local.Inverse
open Purelib.Approximation.Gaussian.Logarithm.Local.Polynomial
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Polynomial.Ascending
open Purelib.Polynomial.Ascending.Rational
open Purelib.Polynomial.Ascending.Rational.Evaluation
open Purelib.Polynomial.Ascending.Rational.Nonnegative

/-- Every finite exponential–local-logarithm composition evaluated at one half is at most five. -/
theorem scalarEval_exponentialLocalLog_half_le_five
    (expDegree logDepth : Nat) :
    Evaluation.scalarEval (1 / 2) (Polynomial.exponentialLocalLog expDegree logDepth) ≤ 5 := by
  rw [Polynomial.exponentialLocalLog, Composition.scalarEval_compose]
  apply Majorant.scalarEval_exponential_le_five
  · exact Evaluation.scalarEvalCoefficients_nonnegative (by decide)
      (Polynomial.localLog logDepth).coefficients
      (Polynomial.coefficientsNonnegative_localLog logDepth)
  · exact Majorant.scalarEval_localLog_half_le logDepth

/-- On the one-ninth quadrance disk, the synchronized composition's remainder beyond its geometric prefix has squared
norm at most fifty times the displayed four-ninths power.

The bound uses the retained nonnegative coefficient tail of the actual finite composition. -/
theorem exponentialLocalLog_highTail_bound {z : Data.Gaussian.Basic.Canonical}
    (zBound : Data.Gaussian.Norm.Basic.normSq z ≤ 1 / 9) (depth : Nat) :
    Data.Gaussian.Norm.Basic.normSq
      (GaussianEvaluation.eval (Polynomial.exponentialLocalLog (2 * depth + 2) depth) z -
        GaussianEvaluation.eval (Geometric.geometricPrefix (2 * depth + 2)) z) ≤
      (5 * 10) * (4 / 9 : Fraction.Rational) ^ (2 * depth + 3) := by
  let polynomial := Polynomial.exponentialLocalLog (2 * depth + 2) depth
  let count := 2 * depth + 3
  let tail : Rational.Basic.CoefficientPolynomial := ⟨polynomial.coefficients.drop count⟩
  let tailMagnitude := Evaluation.scalarEval (1 / 2) tail
  let fullMagnitude := Evaluation.scalarEval (1 / 2) polynomial
  have polynomialNonnegative : Nonnegative.CoefficientsNonnegative polynomial :=
    Polynomial.coefficientsNonnegative_exponentialLocalLog _ _
  have tailNonnegative : Nonnegative.CoefficientsNonnegative tail := by
    intro degree
    change 0 ≤ Rational.Basic.coefficientCoefficients (polynomial.coefficients.drop count) degree
    rw [Truncation.coefficientCoefficients_drop]
    exact polynomialNonnegative (count + degree)
  have tailMagnitudeNonnegative : 0 ≤ tailMagnitude :=
    Evaluation.scalarEvalCoefficients_nonnegative (by decide) tail.coefficients
      tailNonnegative
  have fullMagnitudeNonnegative : 0 ≤ fullMagnitude :=
    Evaluation.scalarEvalCoefficients_nonnegative (by decide) polynomial.coefficients
      polynomialNonnegative
  have fullMagnitudeBound : fullMagnitude ≤ 5 :=
    Approximation.Gaussian.Logarithm.Local.Inverse.Polynomial.Majorant.scalarEval_exponentialLocalLog_half_le_five _ _
  have scaledTailBound :
      (1 / 2 : Fraction.Rational) ^ count * tailMagnitude ≤ fullMagnitude := by
    exact Evaluation.scalarEvalCoefficients_drop_scaled_le (by decide)
      polynomial.coefficients count polynomialNonnegative
  have scaledTailNonnegative :
      0 ≤ (1 / 2 : Fraction.Rational) ^ count * tailMagnitude :=
    Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Order.Arithmetic.pow_nonneg_direct (by decide) count)
      tailMagnitudeNonnegative
  have scaledTailSquare :
      (((1 / 2 : Fraction.Rational) ^ count * tailMagnitude) ^ 2) ≤
        fullMagnitude ^ 2 :=
    Fraction.Order.Arithmetic.pow_le_pow_direct scaledTailNonnegative
      scaledTailBound 2
  have fullMagnitudeSquare : fullMagnitude ^ 2 ≤ 25 := by
    have square := Fraction.Order.Arithmetic.pow_le_pow_direct
      fullMagnitudeNonnegative fullMagnitudeBound 2
    simpa only [show (5 : Fraction.Rational) ^ 2 = 25 by decide] using square
  rw [Polynomial.exponentialLocalLog_sub_prefix z depth,
    Data.Gaussian.Norm.Basic.normSq_mul, Power.normSq_pow]
  have tailNorm := GaussianMajorant.eval_normSq_le_scalarHalf tailNonnegative zBound
  calc
    Data.Gaussian.Norm.Basic.normSq z ^ count * Data.Gaussian.Norm.Basic.normSq
      (GaussianEvaluation.eval tail z) ≤
        (1 / 9 : Fraction.Rational) ^ count * (2 * tailMagnitude ^ 2) :=
      Fraction.Order.Arithmetic.mul_le_mul_direct
        (Fraction.Order.Arithmetic.pow_le_pow_direct
          (Data.Gaussian.Norm.Basic.normSq_nonneg z) zBound count)
        tailNorm (Data.Gaussian.Norm.Basic.normSq_nonneg _)
        (Fraction.Order.Arithmetic.pow_nonneg_direct
          (by decide : (0 : Fraction.Rational) ≤ 1 / 9) count)
    _ = 2 * (4 / 9 : Fraction.Rational) ^ count *
          (((1 / 2 : Fraction.Rational) ^ count * tailMagnitude) ^ 2) :=
      Geometric.Bounds.highTail_power_identity count tailMagnitude
    _ ≤ 2 * (4 / 9 : Fraction.Rational) ^ count * fullMagnitude ^ 2 :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        scaledTailSquare
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
          (Fraction.Order.Arithmetic.pow_nonneg_direct (by decide) count))
    _ ≤ 2 * (4 / 9 : Fraction.Rational) ^ count * 25 :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        fullMagnitudeSquare
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
          (Fraction.Order.Arithmetic.pow_nonneg_direct (by decide) count))
    _ = (5 * 10) * (4 / 9 : Fraction.Rational) ^ (2 * depth + 3) := by
      dsimp only [count]
      ring1
end Purelib.Approximation.Gaussian.Logarithm.Local.Inverse.Polynomial.Majorant

end
