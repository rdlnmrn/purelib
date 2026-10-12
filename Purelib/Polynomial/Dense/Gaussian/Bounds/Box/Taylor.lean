module

import Purelib.Data.Gaussian.Basic
public import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Derivative
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Taylor
-- Reduce the original private coefficient-fold specification in the retained jet proofs.
import all Purelib.Polynomial.Dense.Gaussian.Bounds.Taylor

public import Purelib.Polynomial.Dense.Gaussian.GCD
import Purelib.Tactic.Ring
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

/-!
# Taylor bounds over rational boxes

The finite Horner jet uses the same retained box norm ceiling for value,
slope and quadratic remainder. Its computed remainder coefficient is raised to at least one.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Taylor

open Purelib.Data
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction
open Purelib.Polynomial
open Purelib
open Purelib.Algebra.Polynomial.DensePolynomial

/-- Compute value, slope and quadratic-remainder bounds over a displayed rational box.

The coefficient fold starts from the zero jet and advances using the box
norm ceiling. Its three retained components bound value, slope and remainder. -/
@[expose] public def denseHornerTaylorNormBounds (p : Basic.CanonicalCoefficients.CoefficientPolynomial) (B :
  Geometry.Rational.Box) :
    Dense.Gaussian.Bounds.Taylor.HornerTaylorNormBounds :=
  p.coeffs.foldl (Dense.Gaussian.Bounds.Taylor.HornerTaylorNormBounds.step B.normSqBound) ⟨0, 0, 0⟩

/-- The squared Taylor-remainder coefficient returned by the box Horner fold.

The remainder projection belongs to the same coefficient-fold jet as its
value and slope bounds. It is the coefficient for squared displacement. -/
@[expose] public def denseEvalTaylorRemainderBound
    (p : Basic.CanonicalCoefficients.CoefficientPolynomial) (B : Geometry.Rational.Box) : Fraction.Rational :=
  (denseHornerTaylorNormBounds p B).remainder

/-- All three box Horner bounds are nonnegative.

The zero initial jet and the nonnegative box norm ceiling give nonnegative
value, slope and remainder components throughout the coefficient fold. -/
public theorem denseHornerTaylorNormBounds_nonneg
    (p : Basic.CanonicalCoefficients.CoefficientPolynomial) (B : Geometry.Rational.Box) :
    0 ≤ (denseHornerTaylorNormBounds p B).value ∧
      0 ≤ (denseHornerTaylorNormBounds p B).slope ∧
      0 ≤ denseEvalTaylorRemainderBound p B := by
  have specification := Purelib.Polynomial.Dense.Gaussian.Bounds.Taylor.evalTaylorNormBoundsCoeffs_spec p.coeffs
    (radiusSq := B.normSqBound) (x := 0) (y := 0)
    B.normSqBound_nonneg
    (by rw [Gaussian.Norm.Basic.normSq_zero]; exact B.normSqBound_nonneg)
    (by rw [Gaussian.Norm.Basic.normSq_zero]; exact B.normSqBound_nonneg)
    0 0 0 ⟨0, 0, 0⟩ (by decide) (by decide) (by decide)
    (by rw [Gaussian.Norm.Basic.normSq_zero]) (by rw [Gaussian.Norm.Basic.normSq_zero])
    (by
      change (0 : Fraction.Rational) ≤ 0 * Data.Gaussian.Norm.Basic.normSq ((0 : Gaussian.Basic.Canonical) - 0)
      have product : (0 : Fraction.Rational) * Data.Gaussian.Norm.Basic.normSq ((0 : Gaussian.Basic.Canonical) - 0)
        = 0 := by
        ring1
      rw [product])
    (by
      change (0 : Fraction.Rational) ≤ 0 * Data.Gaussian.Norm.Basic.normSq ((0 : Gaussian.Basic.Canonical) - 0) ^ 2
      have product :
          (0 : Fraction.Rational) * Data.Gaussian.Norm.Basic.normSq ((0 : Gaussian.Basic.Canonical) - 0) ^ 2 = 0 :=
            by
        ring1
      rw [product])
  exact ⟨specification.1, specification.2.1, specification.2.2.1⟩

/-- Raise the computed squared Taylor-remainder coefficient to at least one.

The maximum retains the computed remainder coefficient and the positive
initial floor one, with the original executable rational comparison. -/
@[expose] public def denseTaylorRemainderBound
    (p : Basic.CanonicalCoefficients.CoefficientPolynomial) (B : Geometry.Rational.Box) : Fraction.Rational :=
  max 1 (denseEvalTaylorRemainderBound p B)

/-- The enlarged box Taylor-remainder coefficient is positive.

The retained maximum bounds the positive floor one. Thus positivity does
not require the polynomial to have a nonzero remainder coefficient. -/
public theorem denseTaylorRemainderBound_pos
    (p : Basic.CanonicalCoefficients.CoefficientPolynomial) (B : Geometry.Rational.Box) :
    0 < denseTaylorRemainderBound p B :=
  (by decide : (0 : Fraction.Rational) < 1).trans_le (Order.Basic.le_max_left _ _)

/-- Bound the squared first-order Taylor error between two points in the same box.

The coefficient-computed bound multiplies the square of the displacement quadrance. -/
public theorem normSq_dense_taylor_remainder_le
    (p : Basic.CanonicalCoefficients.CoefficientPolynomial) {B : Geometry.Rational.Box} {z w :
      Gaussian.Basic.Canonical}
    (zInside : B.Contains z) (wInside : B.Contains w) :
    Data.Gaussian.Norm.Basic.normSq (p.eval z - p.eval w -
        (Dense.Gaussian.GCD.derivative p).eval w * (z - w)) ≤
      denseEvalTaylorRemainderBound p B * Data.Gaussian.Norm.Basic.normSq (z - w) ^ 2 := by
  have specification := Purelib.Polynomial.Dense.Gaussian.Bounds.Taylor.evalTaylorNormBoundsCoeffs_spec p.coeffs
    (radiusSq := B.normSqBound) (x := z) (y := w)
    B.normSqBound_nonneg (B.normSq_le_normSqBound zInside)
    (B.normSq_le_normSqBound wInside)
    0 0 0 ⟨0, 0, 0⟩ (by decide) (by decide) (by decide)
    (by rw [Gaussian.Norm.Basic.normSq_zero]) (by rw [Gaussian.Norm.Basic.normSq_zero])
    (by
      change (0 : Fraction.Rational) ≤ 0 * Data.Gaussian.Norm.Basic.normSq (z - w)
      have product : (0 : Fraction.Rational) * Data.Gaussian.Norm.Basic.normSq (z - w) = 0 := by ring1
      rw [product])
    (by
      have zeroError :
          (0 : Gaussian.Basic.Canonical) - 0 - 0 * (z - w) = 0 := by
        apply Gaussian.Basic.ext <;>
          simp only [Gaussian.Basic.sub_re, Gaussian.Basic.sub_im, Gaussian.Basic.mul_re, Gaussian.Basic.mul_im,
            Gaussian.Basic.zero_re, Gaussian.Basic.zero_im] <;>
          ring1
      rw [zeroError, Gaussian.Norm.Basic.normSq_zero]
      change (0 : Fraction.Rational) ≤ 0 * Data.Gaussian.Norm.Basic.normSq (z - w) ^ 2
      have product : (0 : Fraction.Rational) * Data.Gaussian.Norm.Basic.normSq (z - w) ^ 2 = 0 := by ring1
      rw [product])
  have derivativeEvaluation :
      (p.coeffs.foldl (Dense.Derivative.evalDerivativeStep w)
        (0, 0)).2 = (Dense.Gaussian.GCD.derivative p).eval w := by
    exact (Dense.Derivative.eval_derivative p w).symm
  rw [derivativeEvaluation] at specification
  simpa only [Dense.Basic.DensePolynomial.eval, Dense.Basic.DensePolynomial.evalCoeffs, denseEvalTaylorRemainderBound,
    denseHornerTaylorNormBounds] using specification.2.2.2.2.2.2

/-- The positive enlarged Taylor coefficient bounds the squared first-order error throughout the box.

Both displayed points are contained in the same box. The enlarged coefficient
bounds the computed coefficient, and the displacement fourth power is nonnegative. -/
public theorem normSq_dense_taylor_remainder_le_denseTaylorRemainderBound
    (p : Basic.CanonicalCoefficients.CoefficientPolynomial) {B : Geometry.Rational.Box} {z w :
      Gaussian.Basic.Canonical}
    (zInside : B.Contains z) (wInside : B.Contains w) :
    Data.Gaussian.Norm.Basic.normSq (p.eval z - p.eval w -
        (Dense.Gaussian.GCD.derivative p).eval w * (z - w)) ≤
      denseTaylorRemainderBound p B * Data.Gaussian.Norm.Basic.normSq (z - w) ^ 2 := by
  exact (normSq_dense_taylor_remainder_le p zInside wInside).trans
    (Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (Order.Basic.le_max_right _ _)
      (Order.Arithmetic.pow_nonneg_direct
        (Gaussian.Norm.Basic.normSq_nonneg (z - w)) 2))

end Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Taylor
