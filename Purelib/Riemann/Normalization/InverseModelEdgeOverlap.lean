module
public import Purelib.Riemann.Normalization.InverseModelOverlap
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
public import Purelib.Polynomial.Dense.Rational.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
public import Purelib.Data.Rat.Interval.Basic
import Purelib.Geometry.Rational.Affine
import Purelib.Polynomial.Dense.Arithmetic
public import Purelib.Polynomial.Dense.Gaussian.Path.Components
import Purelib.Polynomial.Dense.Multiplication
import Purelib.Polynomial.Dense.Rational.Sign.Interval.Uniform

import Purelib.Riemann.Normalization.InverseModelOverlapCocycle
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

@[expose] public section

/-!
# One computed sheet transition along a whole shared edge

The real dot product of two inverse-root models has a uniform squared gap
from zero.  Its finite polynomial restriction therefore has one sign along
every shared affine segment.  One cached endpoint comparison determines the
transition at all rational parameters, including newly introduced cuts.
-/

namespace Purelib.Riemann.Normalization.InverseModelEdgeOverlap

open Purelib.Riemann.Normalization.InverseModelOverlap
  (SignAlignment OverlapSample inverse_value_ne_zero normalized_value_lower)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian Polynomial Box half correction
  residualStep correction_residual residualStep_contracts Model)

open Purelib.Data.Gaussian.Basic.Canonical

/-- The rational coordinate dot product of two Gaussian values. -/
def overlapDot (left right : Gaussian) : Coordinate := left.re * right.re + left.im * right.im

namespace SignAlignment

variable {reference candidate parameter : Gaussian} {leftError rightError : Coordinate}

open Purelib.Data.Gaussian
open Purelib.Data.Rat
/-- A nearest-sign alignment with both inverse-root residual bounds at most one sixteenth controls the reference squared
norm by sixteen times the aligned dot product. -/
theorem norm_le_dot (alignment : SignAlignment reference candidate)
    (leftResidual : normSq (1 - parameter * reference ^ 2) ≤ leftError)
    (rightResidual : normSq (1 - parameter * candidate ^ 2) ≤ rightError)
    (leftSmall : leftError ≤ 1 / 16) (rightSmall : rightError ≤ 1 / 16) :
    normSq reference ≤ 16 * overlapDot reference alignment.value := by
  have allowance : 24 * (leftError + rightError) ≤ (3 : Coordinate) :=
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add leftSmall rightSmall)
      (by decide)).trans_eq (by decide +kernel : (24 : Coordinate) * (1 / 16 + 1 / 16) = 3)
  have distance : normSq (reference - alignment.value) * 4 ≤ 3 * normSq reference := by
    calc
      _ ≤ (6 * (leftError + rightError) * normSq reference) * 4 :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          (alignment.distance_le leftResidual rightResidual leftSmall) (by decide)
      _ = (24 * (leftError + rightError)) * normSq reference := by ring1
      _ ≤ _ := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct allowance (Basic.Canonical.normSq_nonneg _)
  calc
    _ = normSq reference * 4 - 3 * normSq reference := by ring1
    _ ≤ normSq (reference + alignment.value) * 4 - normSq (reference - alignment.value) * 4 :=
      Fraction.Order.Arithmetic.sub_le_sub_direct
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct alignment.sum_norm_lower (by decide)) distance
    _ = _ := by simp only [normSq, Basic.add_re, Basic.add_im, Basic.sub_re, Basic.sub_im, overlapDot]; ring1

/-- The aligned dot product is strictly positive when both inverse-root residual bounds are at most one sixteenth. -/
theorem dot_positive (alignment : SignAlignment reference candidate)
    (leftResidual : normSq (1 - parameter * reference ^ 2) ≤ leftError)
    (rightResidual : normSq (1 - parameter * candidate ^ 2) ≤ rightError)
    (leftSmall : leftError ≤ 1 / 16) (rightSmall : rightError ≤ 1 / 16) :
    0 < overlapDot reference alignment.value := by
  have referencePositive := Norm.Basic.normSq_pos (inverse_value_ne_zero (leftResidual.trans leftSmall))
  rw [Norm.Basic.normSq_eq_canonical] at referencePositive
  have positive := referencePositive.trans_le
    (SignAlignment.norm_le_dot alignment leftResidual rightResidual leftSmall rightSmall)
  by_cases dotPositive : 0 < overlapDot reference alignment.value
  · exact dotPositive
  · have nonpositive := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (le_of_not_gt dotPositive) (by decide : (0 : Coordinate) ≤ 16)
    rw [Fraction.Field.mul_zero_direct] at nonpositive
    exact (not_lt_of_ge nonpositive positive).elim

/-- The retained nearest-sign flip is the negative-dot-product decision.

Both inverse-root residual bounds are at most one sixteenth at the same
parameter. Positivity of the aligned dot product determines the original
Boolean branch without changing its retained candidate. -/
theorem flip_eq_dot_sign (alignment : SignAlignment reference candidate)
    (leftResidual : normSq (1 - parameter * reference ^ 2) ≤ leftError)
    (rightResidual : normSq (1 - parameter * candidate ^ 2) ≤ rightError)
    (leftSmall : leftError ≤ 1 / 16) (rightSmall : rightError ≤ 1 / 16) :
    alignment.flip = !(decide (0 ≤ overlapDot reference candidate)) := by
  have positive := SignAlignment.dot_positive alignment leftResidual rightResidual leftSmall rightSmall
  rw [alignment.value_eq] at positive
  rcases alignment with ⟨flip, value, valueEq, nearest⟩
  cases flip with
  | false =>
      change 0 < overlapDot reference candidate at positive
      rw [decide_eq_true positive.le]
      exact Eq.refl _
  | true =>
      change 0 < overlapDot reference (-candidate) at positive
      have negIdentity : overlapDot reference (-candidate) = -overlapDot reference candidate := by
        simp only [overlapDot, Basic.neg_re, Basic.neg_im]
        ring1
      rw [negIdentity] at positive
      have translated := Fraction.Order.Arithmetic.add_lt_add_right_direct positive (overlapDot reference candidate)
      have negative : overlapDot reference candidate < 0 := by
        calc
          _ = 0 + overlapDot reference candidate := by ring1
          _ < -overlapDot reference candidate + overlapDot reference candidate := translated
          _ = 0 := by ring1
      rw [decide_eq_false (not_le_of_gt negative)]
      exact Eq.refl _

/-- Bound the squared coordinate dot product below by the reciprocal of 768 times a positive parameter-norm majorant.

Both inverse-root residual bounds are at most one sixteenth; squaring removes the retained sign choice while the
normalized reference bound supplies the quantitative gap. -/
theorem dot_squared_lower (alignment : SignAlignment reference candidate)
    (leftResidual : normSq (1 - parameter * reference ^ 2) ≤ leftError)
    (rightResidual : normSq (1 - parameter * candidate ^ 2) ≤ rightError)
    (leftSmall : leftError ≤ 1 / 16) (rightSmall : rightError ≤ 1 / 16)
    {majorant : Coordinate} (majorantPositive : 0 < majorant) (upper : normSq parameter ≤ majorant) :
    1 / (768 * majorant) ≤ overlapDot reference candidate ^ 2 := by
  have squared := Fraction.Order.Arithmetic.pow_le_pow_direct (Basic.Canonical.normSq_nonneg reference)
    (SignAlignment.norm_le_dot alignment leftResidual rightResidual leftSmall rightSmall) 2
  have signSquare : overlapDot reference alignment.value ^ 2 = overlapDot reference candidate ^ 2 := by
    rw [alignment.value_eq]
    cases alignment.flip
    · rfl
    · change overlapDot reference (-candidate) ^ 2 = overlapDot reference candidate ^ 2
      simp only [overlapDot, Basic.neg_re, Basic.neg_im]
      ring1
  have squareBound : normSq reference ^ 2 ≤ 256 * overlapDot reference candidate ^ 2 := by
    calc
      _ ≤ (16 * overlapDot reference alignment.value) ^ 2 := squared
      _ = 256 * overlapDot reference alignment.value ^ 2 := by ring1
      _ = _ := by rw [signSquare]
  apply (Fraction.Order.Field.div_le_iff_pos
    (Fraction.Order.Arithmetic.mul_pos_direct (by decide +kernel : (0 : Coordinate) < 768) majorantPositive)).2
  calc
    _ = 3 * (1 / 3 : Coordinate) := by decide
    _ ≤ 3 * (normSq parameter * normSq reference ^ 2) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (normalized_value_lower (leftResidual.trans leftSmall)) (by decide)
    _ ≤ 3 * (majorant * (256 * overlapDot reference candidate ^ 2)) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Fraction.Order.Arithmetic.mul_le_mul_direct upper squareBound
          (Fraction.Order.Arithmetic.sq_nonneg_direct _) majorantPositive.le) (by decide)
    _ = _ := by ring1

end SignAlignment

open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
/-- Form the rational dot-product polynomial of two Gaussian polynomials along the given affine line.

Its coefficients combine the real path restrictions and imaginary path restrictions separately, retaining the original
origin and direction. -/
def overlapPolynomial (left right : Polynomial) (origin direction : Gaussian) :
  Dense.Rational.Basic.CoordinatePolynomial
  :=
  Path.Components.pathReal left origin direction * Path.Components.pathReal right origin direction +
    Path.Components.pathImag left origin direction * Path.Components.pathImag right origin direction

open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
/-- The overlap polynomial evaluates to the coordinate dot product on its affine line.

The real and imaginary path restrictions use the same retained origin,
direction and rational parameter in both original polynomials. -/
theorem eval_overlapPolynomial (left right : Polynomial) (origin direction : Gaussian) (parameter : Coordinate) :
    (overlapPolynomial left right origin direction).eval parameter =
      overlapDot (left.eval (Affine.line origin direction parameter))
        (right.eval (Affine.line origin direction parameter)) := by
  dsimp only [overlapPolynomial, overlapDot]
  rewrite [Dense.Basic.DensePolynomial.eval_add, Dense.Basic.DensePolynomial.eval_mul,
    Dense.Basic.DensePolynomial.eval_mul, Path.Components.eval_pathReal,
    Path.Components.eval_pathReal, Path.Components.eval_pathImag, Path.Components.eval_pathImag]
  exact Eq.refl _

namespace Model

variable {polynomial : Polynomial} {leftBox rightBox : Purelib.Riemann.Normalization.InverseRootPolynomial.Box}

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
/-- Canonical overlap samples at two parameters of a common model edge choose the same sign.

The whole rational interval lies in both original model boxes. A positive squared-dot lower bound and the constructive
polynomial sign theorem preserve the sign between the two parameters. -/
theorem edge_flip_eq {polynomial : Polynomial} {leftBox rightBox : Purelib.Geometry.Rational.Box} (left : Model
  polynomial leftBox) (right :
  Model polynomial rightBox)
    (origin direction : Gaussian) (interval : Data.Rat.Interval.Bounds)
    (leftInside : ∀ parameter, interval.Contains parameter → leftBox.Contains (Affine.line origin direction parameter))
    (rightInside : ∀ parameter, interval.Contains parameter → rightBox.Contains (Affine.line origin direction
      parameter))
    {first last : Coordinate} (firstInside : interval.Contains first) (lastInside : interval.Contains last) :
    (OverlapSample.build left right (Affine.line origin direction first)).alignment.flip =
      (OverlapSample.build left right (Affine.line origin direction last)).alignment.flip := by
  have leftResidual (parameter : Coordinate) (inside : interval.Contains parameter) :
      normSq (1 - polynomial.eval (Affine.line origin direction parameter) *
        (left.value.eval (Affine.line origin direction parameter)) ^ 2) ≤ left.bound := by
    rw [← left.residual_eq]
    exact left.residualBound _ (leftInside parameter inside)
  have rightResidual (parameter : Coordinate) (inside : interval.Contains parameter) :
      normSq (1 - polynomial.eval (Affine.line origin direction parameter) *
        (right.value.eval (Affine.line origin direction parameter)) ^ 2) ≤ right.bound := by
    rw [← right.residual_eq]
    exact right.residualBound _ (rightInside parameter inside)
  let majorant := Bounds.Box.denseEvalNormMajorant polynomial leftBox
  have majorantPositive : 0 < majorant := Bounds.Box.denseEvalNormMajorant_pos polynomial leftBox
  have gapPositive : (0 : Coordinate) < 1 / (768 * majorant) :=
    Fraction.Order.Field.div_pos_direct (by decide)
      (Fraction.Order.Arithmetic.mul_pos_direct (by decide +kernel) majorantPositive)
  have gap (parameter : Coordinate) (inside : interval.Contains parameter) :
      1 / (768 * majorant) ≤ (overlapPolynomial left.value right.value origin direction).eval parameter ^ 2 := by
    rw [eval_overlapPolynomial]
    exact SignAlignment.dot_squared_lower (SignAlignment.build _ _) (leftResidual parameter inside) (rightResidual
      parameter inside)
      left.bound_small right.bound_small majorantPositive
      (by
          simpa only [Norm.Basic.normSq_eq_canonical]
            using Bounds.Box.normSq_eval_le_denseEvalNormMajorant polynomial (leftInside parameter inside))
  have signs := Dense.Rational.Sign.Interval.Uniform.sign_eq_of_squared_lower
    (overlapPolynomial left.value right.value origin direction) interval gapPositive gap firstInside lastInside
  rw [eval_overlapPolynomial, eval_overlapPolynomial] at signs
  dsimp only [OverlapSample.build]
  rw [SignAlignment.flip_eq_dot_sign (SignAlignment.build _ _) (leftResidual first firstInside) (rightResidual first
    firstInside) left.bound_small right.bound_small,
    SignAlignment.flip_eq_dot_sign (SignAlignment.build _ _) (leftResidual last lastInside) (rightResidual last
      lastInside) left.bound_small right.bound_small,
    signs]

end Model

end Purelib.Riemann.Normalization.InverseModelEdgeOverlap
