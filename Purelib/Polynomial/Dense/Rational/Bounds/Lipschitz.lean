module

import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Interval.Basic
import Purelib.Polynomial.Bounds.Horner
import Purelib.Polynomial.Dense.Basic
public import Purelib.Polynomial.Dense.Evaluation
public import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Rational.Bounds.Horner.Pair

import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
public import Purelib.Data.Rat.Interval.Bounds

/-!
# Retained rational Horner square bounds

The original finite coefficient folds retain their interval radii and
accumulator data. Value bounds and paired value/difference bounds
certify those same finite evaluations and their scalar readbacks.
-/

namespace Purelib.Polynomial.Dense.Rational.Bounds.Lipschitz

open Purelib
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Rational
open Purelib.Polynomial.Dense.Rational.Bounds

/-- Compute squared-value and squared-difference bounds by a finite coefficient fold.

The original coefficient list is folded from the retained zero pair.
Each paired Horner step consumes the same interval square bound and
updates its original value and slope components. -/
@[expose] public def denseHornerSqBounds (p : Basic.CoordinatePolynomial) (interval : Data.Rat.Interval.Bounds) :
    Bounds.Horner :=
  p.coeffs.foldl (Horner.Pair.step interval.squareBound) ⟨0, 0⟩

/-- Read the squared-value component of the computed finite Horner bounds.

The readback projects the value component from the original paired
coefficient fold over the retained interval; no second fold or bound
is computed by this projection. -/
@[expose] public def denseEvalSqBound (p : Basic.CoordinatePolynomial) (interval : Data.Rat.Interval.Bounds) :
  Fraction.Rational :=
  (denseHornerSqBounds p interval).value

/-- Read the slope component bounding squared value differences by squared point differences.

The readback projects the slope component from the original paired
coefficient fold over the retained interval. Its product with a squared
point difference bounds the original squared evaluation difference. -/
@[expose] public def denseEvalSqLipschitzBound
    (p : Basic.CoordinatePolynomial) (interval : Data.Rat.Interval.Bounds) : Fraction.Rational :=
  (denseHornerSqBounds p interval).slope

/-- Refining the interval cannot increase either computed Horner bound.

The supplied interval refines the retained root interval. Its original
square bound cannot increase, so the same coefficient fold from zero
bounds both retained value and slope components. -/
public theorem denseHornerSqBounds_le_of_refines (p : Basic.CoordinatePolynomial)
    {interval root : Data.Rat.Interval.Bounds} (refines : interval.Refines root) :
    denseEvalSqBound p interval ≤ denseEvalSqBound p root ∧
      denseEvalSqLipschitzBound p interval ≤
        denseEvalSqLipschitzBound p root := by
  exact Horner.Pair.hornerSqBoundsCoeffs_monotone p.coeffs
    interval.squareBound_nonneg root.squareBound_nonneg
    (le_refl 0) (le_refl 0) (le_refl 0) (le_refl 0)
    (interval.squareBound_le_of_refines refines) (le_refl 0) (le_refl 0)

/-- Refining the interval cannot increase its computed squared-value bound.

The supplied interval refines the retained root interval. The value
projection of the same original paired coefficient fold preserves
the resulting bound order. -/
public theorem denseEvalSqBound_le_of_refines (p : Basic.CoordinatePolynomial)
    {interval root : Data.Rat.Interval.Bounds} (refines : interval.Refines root) :
    denseEvalSqBound p interval ≤ denseEvalSqBound p root :=
  (denseHornerSqBounds_le_of_refines p refines).1

/-- Refining the interval cannot increase its computed squared-difference slope bound.

The supplied interval refines the retained root interval. The slope
projection of the same original paired coefficient fold preserves
the resulting bound order. -/
public theorem denseEvalSqLipschitzBound_le_of_refines (p : Basic.CoordinatePolynomial)
    {interval root : Data.Rat.Interval.Bounds} (refines : interval.Refines root) :
    denseEvalSqLipschitzBound p interval ≤
      denseEvalSqLipschitzBound p root :=
  (denseHornerSqBounds_le_of_refines p refines).2

/-- Both computed Horner bound components are nonnegative.

The paired fold starts from zero value and slope bounds. Each original
coefficient step preserves nonnegativity under the interval's retained
nonnegative square bound. -/
public theorem denseHornerSqBounds_nonneg (p : Basic.CoordinatePolynomial) (interval : Data.Rat.Interval.Bounds) :
    0 ≤ denseEvalSqBound p interval ∧
      0 ≤ denseEvalSqLipschitzBound p interval := by
  have specification := Horner.Pair.evalSqBoundsCoeffs_spec p.coeffs
    (radiusSq := interval.squareBound) (x := 0) (y := 0)
    interval.squareBound_nonneg interval.squareBound_nonneg
    interval.squareBound_nonneg 0 0 ⟨0, 0⟩
    (le_refl 0) (le_refl 0) (le_refl 0) (le_refl 0) (by
      change (0 : Fraction.Rational) ≤ 0 * 0 ^ 2
      rw [zero_mul])
  exact ⟨specification.1, specification.2.1⟩

/-- Bound the squared difference of two polynomial values on the same interval.

Both supplied points belong to the same retained interval. The original
coefficient fold bounds their squared evaluation difference by its
computed slope component times their original squared point difference. -/
public theorem eval_sub_sq_le
    (p : Basic.CoordinatePolynomial) (interval : Data.Rat.Interval.Bounds) {x y : Fraction.Rational}
    (xInside : interval.Contains x) (yInside : interval.Contains y) :
    (p.eval x - p.eval y) ^ 2 ≤
      denseEvalSqLipschitzBound p interval * (x - y) ^ 2 := by
  have specification := Horner.Pair.evalSqBoundsCoeffs_spec p.coeffs
    (radiusSq := interval.squareBound) (x := x) (y := y)
    interval.squareBound_nonneg (interval.sq_le_squareBound xInside)
    (interval.sq_le_squareBound yInside) 0 0 ⟨0, 0⟩
    (le_refl 0) (le_refl 0) (le_refl 0) (le_refl 0) (by
      change (0 : Fraction.Rational) ≤ 0 * (x - y) ^ 2
      rw [zero_mul])
  simpa only [Dense.Basic.DensePolynomial.eval, Dense.Basic.DensePolynomial.evalCoeffs, denseEvalSqLipschitzBound,
    denseHornerSqBounds] using specification.2.2.2.2

end Purelib.Polynomial.Dense.Rational.Bounds.Lipschitz
