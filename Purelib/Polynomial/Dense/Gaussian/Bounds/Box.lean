module

import Purelib.Data.Gaussian.Basic
public import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Bounds.Horner
import Purelib.Polynomial.Dense.Basic
public import Purelib.Polynomial.Dense.Evaluation
public import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Horner

import Purelib.Tactic.Ring
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

/-!
# Polynomial quadrance bounds on rational boxes

The original Gaussian coefficient list and box squared-radius bound feed
one retained Horner fold. Its value and slope components bound evaluation
quadrance and squared differences; maximum floors give positive majorants.
-/

open Purelib
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry
open Purelib.Geometry.Rational
open Purelib.Polynomial

namespace Purelib.Polynomial.Dense.Gaussian.Bounds.Box

open Purelib.Data.Gaussian

/-- Fold the displayed Gaussian coefficient table into value and slope bounds for the rational box.

The initial bounds are zero and every step uses the same exact squared-radius bound of the original box. -/
@[expose] public def denseHornerNormBounds (p : Basic.CanonicalCoefficients.CoefficientPolynomial) (B : Box) :
    Bounds.Horner :=
  p.coeffs.foldl (Dense.Gaussian.Bounds.Horner.step B.normSqBound) ⟨0, 0⟩

/-- The squared-value upper bound read from the polynomial's box Horner fold.

The original coefficient-list fold retains the computed value and slope
bounds together. This projection reads the value component without
replacing its coefficient list, box radius or fold operation. -/
@[expose] public def denseEvalNormBound (p : Basic.CanonicalCoefficients.CoefficientPolynomial) (B : Box) :
  Fraction.Rational :=
  (Dense.Gaussian.Bounds.Box.denseHornerNormBounds p B).value

/-- The squared-difference multiplier read from the polynomial's box Horner fold.

The original coefficient-list fold retains the computed value and slope
bounds together. This projection reads the slope component using the
same coefficient list, box radius and fold operation. -/
@[expose] public def denseEvalNormLipschitzBound (p : Basic.CanonicalCoefficients.CoefficientPolynomial) (B : Box) :
    Fraction.Rational :=
  (Dense.Gaussian.Bounds.Box.denseHornerNormBounds p B).slope

/-- Positive finite majorant for the squared value norm.

The original folded value bound is compared with the scalar floor one.
The same rational maximum keeps that computed bound and ensures a
positive value majorant. -/
@[expose] public def denseEvalNormMajorant (p : Basic.CanonicalCoefficients.CoefficientPolynomial) (B : Box) :
  Fraction.Rational :=
  max 1 (Dense.Gaussian.Bounds.Box.denseEvalNormBound p B)

/-- The box value majorant is positive because its floor is one.

The original rational maximum bounds its scalar floor one from above.
The strictly positive floor therefore makes this same majorant positive. -/
public theorem denseEvalNormMajorant_pos (p : Basic.CanonicalCoefficients.CoefficientPolynomial) (B : Box) :
    0 < Dense.Gaussian.Bounds.Box.denseEvalNormMajorant p B :=
  (by decide : (0 : Fraction.Rational) < 1).trans_le (Fraction.Order.Basic.le_max_left _ _)

/-- Both value and slope components of the box Horner fold are nonnegative.

The same finite Horner fold starts with zero value and slope bounds and
uses the nonnegative squared-radius bound of the original box. Its
retained invariants make both final components nonnegative. -/
public theorem denseHornerNormBounds_nonneg (p : Basic.CanonicalCoefficients.CoefficientPolynomial) (B : Box) :
    0 ≤ Dense.Gaussian.Bounds.Box.denseEvalNormBound p B ∧
      0 ≤ Dense.Gaussian.Bounds.Box.denseEvalNormLipschitzBound p B := by
  have specification := Purelib.Polynomial.Dense.Gaussian.Bounds.Horner.evalNormBoundsCoeffs_spec p.coeffs
    (radiusSq := B.normSqBound) (x := 0) (y := 0)
    B.normSqBound_nonneg
    (by rw [Gaussian.Norm.Basic.normSq_zero]; exact B.normSqBound_nonneg)
    (by rw [Gaussian.Norm.Basic.normSq_zero]; exact B.normSqBound_nonneg)
    0 0 ⟨0, 0⟩ (by decide) (by decide)
    (by rw [Gaussian.Norm.Basic.normSq_zero]) (by rw [Gaussian.Norm.Basic.normSq_zero])
    (by
      change (0 : Fraction.Rational) ≤ 0 * Data.Gaussian.Norm.Basic.normSq ((0 : Gaussian.Basic.Canonical) - 0)
      have hproduct : (0 : Fraction.Rational) * Data.Gaussian.Norm.Basic.normSq ((0 : Gaussian.Basic.Canonical) - 0)
        = 0 := by
        ring1
      rw [hproduct])
  exact ⟨specification.1, specification.2.1⟩

/-- The box Horner slope bound with a positive unit floor.

The original folded slope bound is compared with the scalar floor one.
The retained rational maximum gives the same polynomial and box a
strictly positive squared-difference multiplier. -/
@[expose] public def denseLipschitzBound (p : Basic.CanonicalCoefficients.CoefficientPolynomial) (B : Box) :
  Fraction.Rational :=
  max 1 (Dense.Gaussian.Bounds.Box.denseEvalNormLipschitzBound p B)

/-- The box Lipschitz multiplier is positive because its floor is one.

The original maximum is at least its scalar floor one. That positive
floor makes the retained polynomial and box Lipschitz multiplier positive. -/
public theorem denseLipschitzBound_pos (p : Basic.CanonicalCoefficients.CoefficientPolynomial) (B : Box) :
    0 < Dense.Gaussian.Bounds.Box.denseLipschitzBound p B :=
  (by decide : (0 : Fraction.Rational) < 1).trans_le (Fraction.Order.Basic.le_max_left _ _)

/-- Evaluation at any point in the rational box has quadrance bounded by the computed Horner value bound.

The retained containment witness places the evaluation point within
the original box radius. Folding the same coefficients from the zero
accumulator carries its squared-norm bound to the final value component. -/
public theorem normSq_eval_le_denseEvalNormBound
    (p : Basic.CanonicalCoefficients.CoefficientPolynomial) {B : Box} {z : Gaussian.Basic.Canonical}
    (inside : B.Contains z) :
    Data.Gaussian.Norm.Basic.normSq (p.eval z) ≤ Dense.Gaussian.Bounds.Box.denseEvalNormBound p B := by
  have specification := Purelib.Polynomial.Dense.Gaussian.Bounds.Horner.evalNormBoundsCoeffs_spec p.coeffs
    (radiusSq := B.normSqBound) (x := z) (y := z)
    B.normSqBound_nonneg (B.normSq_le_normSqBound inside)
    (B.normSq_le_normSqBound inside)
    0 0 ⟨0, 0⟩ (by decide) (by decide)
    (by rw [Gaussian.Norm.Basic.normSq_zero]) (by rw [Gaussian.Norm.Basic.normSq_zero])
    (by
      change (0 : Fraction.Rational) ≤ 0 * Data.Gaussian.Norm.Basic.normSq (z - z)
      have hproduct : (0 : Fraction.Rational) * Data.Gaussian.Norm.Basic.normSq (z - z) = 0 := by ring1
      rw [hproduct])
  simpa only [Dense.Basic.DensePolynomial.eval, Dense.Basic.DensePolynomial.evalCoeffs,
    Dense.Gaussian.Bounds.Box.denseEvalNormBound, Dense.Gaussian.Bounds.Box.denseHornerNormBounds]
    using specification.2.2.1

/-- Evaluation at any point in the rational box has quadrance bounded by the positive value majorant.

The original box containment witness bounds the evaluation quadrance
by the folded value bound. The retained maximum majorant also bounds
that same value component. -/
public theorem normSq_eval_le_denseEvalNormMajorant
    (p : Basic.CanonicalCoefficients.CoefficientPolynomial) {B : Box} {z : Gaussian.Basic.Canonical}
    (inside : B.Contains z) :
    Data.Gaussian.Norm.Basic.normSq (p.eval z) ≤ Dense.Gaussian.Bounds.Box.denseEvalNormMajorant p B :=
  (Dense.Gaussian.Bounds.Box.normSq_eval_le_denseEvalNormBound p inside).trans (Fraction.Order.Basic.le_max_right _ _)

/-- Two points in the same box have polynomial squared-distance bounded by the computed slope times their
squared-distance.

Both original evaluation points satisfy the same box containment bounds.
The retained Horner invariants control their squared difference by the
original folded slope bound times their input squared difference. -/
public theorem normSq_eval_sub_eval_le
    (p : Basic.CanonicalCoefficients.CoefficientPolynomial) {B : Box} {z w : Gaussian.Basic.Canonical}
    (zInside : B.Contains z) (wInside : B.Contains w) :
    Data.Gaussian.Norm.Basic.normSq (p.eval z - p.eval w) ≤
      Dense.Gaussian.Bounds.Box.denseEvalNormLipschitzBound p B * Data.Gaussian.Norm.Basic.normSq (z - w) := by
  have specification := Purelib.Polynomial.Dense.Gaussian.Bounds.Horner.evalNormBoundsCoeffs_spec p.coeffs
    (radiusSq := B.normSqBound) (x := z) (y := w)
    B.normSqBound_nonneg (B.normSq_le_normSqBound zInside)
    (B.normSq_le_normSqBound wInside)
    0 0 ⟨0, 0⟩ (by decide) (by decide)
    (by rw [Gaussian.Norm.Basic.normSq_zero]) (by rw [Gaussian.Norm.Basic.normSq_zero])
    (by
      change (0 : Fraction.Rational) ≤ 0 * Data.Gaussian.Norm.Basic.normSq (z - w)
      have hproduct : (0 : Fraction.Rational) * Data.Gaussian.Norm.Basic.normSq (z - w) = 0 := by ring1
      rw [hproduct])
  simpa only [Dense.Basic.DensePolynomial.eval, Dense.Basic.DensePolynomial.evalCoeffs,
    Dense.Gaussian.Bounds.Box.denseEvalNormLipschitzBound,
    Dense.Gaussian.Bounds.Box.denseHornerNormBounds] using specification.2.2.2.2

/-- The positive box Lipschitz multiplier bounds polynomial squared-distance for any two contained points.

The original folded slope bound controls the two evaluations in the
same box. Its retained maximum with one dominates that slope bound,
and their input squared difference is nonnegative. -/
public theorem normSq_eval_sub_eval_le_denseLipschitzBound
    (p : Basic.CanonicalCoefficients.CoefficientPolynomial) {B : Box} {z w : Gaussian.Basic.Canonical}
    (zInside : B.Contains z) (wInside : B.Contains w) :
    Data.Gaussian.Norm.Basic.normSq (p.eval z - p.eval w) ≤
      Dense.Gaussian.Bounds.Box.denseLipschitzBound p B * Data.Gaussian.Norm.Basic.normSq (z - w) := by
  exact (Dense.Gaussian.Bounds.Box.normSq_eval_sub_eval_le p zInside wInside).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (Fraction.Order.Basic.le_max_right _ _) (Gaussian.Norm.Basic.normSq_nonneg (z - w)))

/-- The computed box value bound dominates twice the quadrance of the polynomial's constant evaluation.

The original coefficient-list fold starts from zero and uses the retained
nonnegative box radius. Its value invariant controls twice the final
zero-input evaluation quadrance, without a containment condition on zero. -/
public theorem twice_normSq_eval_zero_le_denseEvalNormBound
    (p : Basic.CanonicalCoefficients.CoefficientPolynomial) (B : Box) :
    2 * Data.Gaussian.Norm.Basic.normSq (p.eval 0) ≤ Dense.Gaussian.Bounds.Box.denseEvalNormBound p B := by
  have bound := Purelib.Polynomial.Dense.Gaussian.Bounds.Horner.twice_normSq_foldl_zero_le_hornerValue B.normSqBound
    B.normSqBound_nonneg p.coeffs 0 ⟨0, 0⟩ (by decide) (by
      rw [Gaussian.Norm.Basic.normSq_zero]
      decide)
  simpa only [Dense.Basic.DensePolynomial.eval, Dense.Basic.DensePolynomial.evalCoeffs,
    Dense.Gaussian.Bounds.Box.denseEvalNormBound, Dense.Gaussian.Bounds.Box.denseHornerNormBounds]
    using bound

/-- The positive box value majorant dominates twice the quadrance of the constant evaluation.

The original box value bound controls twice the zero-input evaluation
quadrance. Its retained maximum majorant dominates that same folded
value component. -/
public theorem twice_normSq_eval_zero_le_denseEvalNormMajorant
    (p : Basic.CanonicalCoefficients.CoefficientPolynomial) (B : Box) :
    2 * Data.Gaussian.Norm.Basic.normSq (p.eval 0) ≤ Dense.Gaussian.Bounds.Box.denseEvalNormMajorant p B :=
  (Dense.Gaussian.Bounds.Box.twice_normSq_eval_zero_le_denseEvalNormBound p B).trans
    (Fraction.Order.Basic.le_max_right _ _)

/-- Coefficient-computable multiplier for the polynomial residual of any
nonzero rational sample returned from a winding-one box.

The original polynomial and ambient box determine the same retained
positive Lipschitz bound. Multiplication by four gives the displayed
residual multiplier without replacing that computed observation. -/
@[expose] public def residualConstant (p : Basic.CanonicalCoefficients.CoefficientPolynomial) (ambient : Box) :
  Fraction.Rational :=
  4 * Dense.Gaussian.Bounds.Box.denseLipschitzBound p ambient

/-- The fourfold box Lipschitz residual multiplier is nonnegative.

The original box Lipschitz multiplier is positive. Its product with
the nonnegative scalar four therefore has a nonnegative floor. -/
public theorem residualConstant_nonneg (p : Basic.CanonicalCoefficients.CoefficientPolynomial) (ambient : Box) :
    0 ≤ Dense.Gaussian.Bounds.Box.residualConstant p ambient :=
  Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
    (Dense.Gaussian.Bounds.Box.denseLipschitzBound_pos p ambient).le

end Purelib.Polynomial.Dense.Gaussian.Bounds.Box
