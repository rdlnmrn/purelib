module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Nat.Order
public import Purelib.Data.Gaussian.Field
public import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Bounds.Square

import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Polynomial.Bounds.Horner
import Purelib.Polynomial.Dense.Basic
public import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring
import Purelib.Algebra.Ring.Normalization
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic

open Purelib.Data.Rat.Fraction.Order

/-!
# Gaussian Horner bounds

The original finite coefficient-list fold propagates squared-value and
squared-difference bounds. Its shared radius and initial accumulator
certificates control both final evaluations and their difference.
-/

open scoped Purelib.Data.Nat

open Purelib.Data
open Purelib.Data.Rat
open Purelib.Data.Rat.Bounds
open Purelib.Algebra.Ring
open Purelib.Polynomial

namespace Purelib.Polynomial.Dense.Gaussian.Bounds.Horner

open Purelib.Data.Gaussian

/-- The exact rational scalar type used for squared-norm Horner bounds. -/
public abbrev Coordinate := Fraction.Rational

/-- Advance the squared-value and squared-difference bounds by one Gaussian Horner coefficient.

The value bound uses the input squared-radius bound and coefficient quadrance; the slope bound also retains the
preceding value bound. -/
@[expose] public def step (radiusSq : Fraction.Rational)
    (bounds : Bounds.Horner) (coefficient : Basic.Canonical) : Bounds.Horner where
  value := 2 * (bounds.value * radiusSq + Norm.Basic.normSq coefficient)
  slope := 2 * (bounds.slope * radiusSq + bounds.value)

end Purelib.Polynomial.Dense.Gaussian.Bounds.Horner

section

open Purelib.Data.Gaussian

namespace Purelib.Polynomial.Dense.Gaussian.Bounds.Horner
/-- The finite Horner fold preserves nonnegative value and slope bounds and bounds both evaluations and their squared
difference.

The two inputs share a nonnegative squared-radius bound; the initial accumulators and their difference satisfy the
supplied bound invariants. -/
public theorem evalNormBoundsCoeffs_spec
    (coeffs : List Basic.Canonical) {radiusSq : Fraction.Rational} {x y : Basic.Canonical}
    (hradius : 0 ≤ radiusSq)
    (hx : Norm.Basic.normSq x ≤ radiusSq) (hy : Norm.Basic.normSq y ≤ radiusSq)
    (accX accY : Basic.Canonical) (bounds : Bounds.Horner)
    (hvalue : 0 ≤ bounds.value) (hslope : 0 ≤ bounds.slope)
    (haccX : Norm.Basic.normSq accX ≤ bounds.value)
    (haccY : Norm.Basic.normSq accY ≤ bounds.value)
    (hdiff : Norm.Basic.normSq (accX - accY) ≤
      bounds.slope * Norm.Basic.normSq (x - y)) :
    let finalX := coeffs.foldl
      (fun acc coefficient => acc * x + coefficient) accX
    let finalY := coeffs.foldl
      (fun acc coefficient => acc * y + coefficient) accY
    let finalBounds := coeffs.foldl
      (step radiusSq) bounds
    0 ≤ finalBounds.value ∧ 0 ≤ finalBounds.slope ∧
      Norm.Basic.normSq finalX ≤ finalBounds.value ∧
      Norm.Basic.normSq finalY ≤ finalBounds.value ∧
      Norm.Basic.normSq (finalX - finalY) ≤
        finalBounds.slope * Norm.Basic.normSq (x - y) := by
  induction coeffs generalizing accX accY bounds with
  | nil => exact ⟨hvalue, hslope, haccX, haccY, hdiff⟩
  | cons coefficient coeffs ih =>
      simp only [List.foldl_cons]
      apply ih
      · apply Square.twice_nonneg
        exact add_nonneg
          (Arithmetic.mul_nonneg_direct hvalue hradius)
          (Norm.Basic.normSq_nonneg coefficient)
      · apply Square.twice_nonneg
        exact add_nonneg
          (Arithmetic.mul_nonneg_direct hslope hradius)
          hvalue
      · have hmul : Norm.Basic.normSq accX * Norm.Basic.normSq x ≤
            bounds.value * radiusSq :=
          Arithmetic.mul_le_mul_direct haccX hx
            (Norm.Basic.normSq_nonneg x) hvalue
        calc
          Norm.Basic.normSq (accX * x + coefficient) ≤
              2 * (Norm.Basic.normSq (accX * x) + Norm.Basic.normSq coefficient) :=
            Norm.Bounds.normSq_add_le_two _ _
          _ = 2 * (Norm.Basic.normSq accX * Norm.Basic.normSq x +
            Norm.Basic.normSq coefficient) := by
            rw [Norm.Basic.normSq_mul]
          _ ≤ 2 * (bounds.value * radiusSq + Norm.Basic.normSq coefficient) :=
            Square.twice_le_twice (add_le_add hmul (le_refl _))
      · have hmul : Norm.Basic.normSq accY * Norm.Basic.normSq y ≤
            bounds.value * radiusSq :=
          Arithmetic.mul_le_mul_direct haccY hy
            (Norm.Basic.normSq_nonneg y) hvalue
        calc
          Norm.Basic.normSq (accY * y + coefficient) ≤
              2 * (Norm.Basic.normSq (accY * y) + Norm.Basic.normSq coefficient) :=
            Norm.Bounds.normSq_add_le_two _ _
          _ = 2 * (Norm.Basic.normSq accY * Norm.Basic.normSq y +
            Norm.Basic.normSq coefficient) := by
            rw [Norm.Basic.normSq_mul]
          _ ≤ 2 * (bounds.value * radiusSq + Norm.Basic.normSq coefficient) :=
            Square.twice_le_twice (add_le_add hmul (le_refl _))
      · have hidentity :
            (accX * x + coefficient) - (accY * y + coefficient) =
              (accX - accY) * x + accY * (x - y) := by
          apply Basic.ext <;>
            simp only [Basic.sub_re, Basic.sub_im, Basic.add_re, Basic.add_im,
              Basic.mul_re, Basic.mul_im] <;>
            ring1
        rw [hidentity]
        have hfirst : Norm.Basic.normSq (accX - accY) * Norm.Basic.normSq x ≤
            (bounds.slope * Norm.Basic.normSq (x - y)) * radiusSq :=
          Arithmetic.mul_le_mul_direct hdiff hx
            (Norm.Basic.normSq_nonneg x)
            (Arithmetic.mul_nonneg_direct hslope
              (Norm.Basic.normSq_nonneg (x - y)))
        have hsecond : Norm.Basic.normSq accY * Norm.Basic.normSq (x - y) ≤
            bounds.value * Norm.Basic.normSq (x - y) :=
          Arithmetic.mul_le_mul_of_nonneg_right_direct
            haccY (Norm.Basic.normSq_nonneg (x - y))
        calc
          Norm.Basic.normSq ((accX - accY) * x + accY * (x - y)) ≤
              2 * (Norm.Basic.normSq ((accX - accY) * x) +
                Norm.Basic.normSq (accY * (x - y))) := Norm.Bounds.normSq_add_le_two _ _
          _ = 2 * (Norm.Basic.normSq (accX - accY) * Norm.Basic.normSq x +
                Norm.Basic.normSq accY * Norm.Basic.normSq (x - y)) := by
            rw [Norm.Basic.normSq_mul, Norm.Basic.normSq_mul]
          _ ≤ 2 * ((bounds.slope * Norm.Basic.normSq (x - y)) * radiusSq +
                bounds.value * Norm.Basic.normSq (x - y)) :=
            Square.twice_le_twice (add_le_add hfirst hsecond)
          _ = 2 * (bounds.slope * radiusSq + bounds.value) *
                Norm.Basic.normSq (x - y) := by ring1
/-- The finite Horner value bound dominates twice the quadrance of evaluation at zero.

The radius and initial value ceiling are nonnegative, and the initial ceiling
bounds twice the accumulator quadrance. Folding the same coefficient list
preserves the bound for the final zero-input evaluation and retained ceiling. -/
public theorem twice_normSq_foldl_zero_le_hornerValue
    (radiusSq : Fraction.Rational) (radiusNonnegative : 0 ≤ radiusSq) :
    ∀ (coefficients : List Basic.Canonical) (accumulator : Basic.Canonical)
      (bounds : Bounds.Horner),
      0 ≤ bounds.value →
      2 * Norm.Basic.normSq accumulator ≤ bounds.value →
      2 * Norm.Basic.normSq
          (coefficients.foldl
            (fun value coefficient => value * 0 + coefficient) accumulator) ≤
        (coefficients.foldl (step radiusSq) bounds).value := by
  intro coefficients
  induction coefficients with
  | nil =>
      intro accumulator bounds _ bound
      exact bound
  | cons coefficient coefficients inductionHypothesis =>
      intro accumulator bounds boundsNonnegative _
      simp only [List.foldl_cons]
      apply inductionHypothesis
      · unfold step
        exact Arithmetic.mul_nonneg_direct (by decide)
          (add_nonneg
            (Arithmetic.mul_nonneg_direct boundsNonnegative
              radiusNonnegative)
            (Norm.Basic.normSq_nonneg coefficient))
      · simp only [mul_zero, zero_add]
        unfold step
        apply Arithmetic.mul_le_mul_of_nonneg_left_direct
        · exact le_add_of_nonneg_left
            (Arithmetic.mul_nonneg_direct boundsNonnegative
              radiusNonnegative)
        · decide
end Purelib.Polynomial.Dense.Gaussian.Bounds.Horner

end

section

open Purelib.Data.Gaussian

namespace Purelib.Polynomial.Dense.Gaussian.Bounds.Horner
/-- Increasing a nonnegative radius and initial bounds cannot decrease the folded Horner bounds.

The two folds retain the same coefficient list. The supplied weak radius,
value and slope comparisons propagate through every step, preserving weak
comparison of both final bounds. -/
public theorem fold_bounds_mono (coefficients : List Basic.Canonical)
    {small large : Fraction.Rational} (smallNonnegative : 0 ≤ small)
    (radiusBound : small ≤ large) (left right : Bounds.Horner)
    (valueNonnegative : 0 ≤ left.value) (slopeNonnegative : 0 ≤ left.slope)
    (valueBound : left.value ≤ right.value) (slopeBound : left.slope ≤ right.slope) :
    (coefficients.foldl (step small) left).value ≤
        (coefficients.foldl (step large) right).value ∧
      (coefficients.foldl (step small) left).slope ≤
        (coefficients.foldl (step large) right).slope := by
  induction coefficients generalizing left right with
  | nil => exact ⟨valueBound, slopeBound⟩
  | cons coefficient coefficients ih =>
      simp only [List.foldl_cons]
      apply ih
      · exact Arithmetic.mul_nonneg_direct (by decide)
          (add_nonneg (Arithmetic.mul_nonneg_direct
            valueNonnegative smallNonnegative) (Norm.Basic.normSq_nonneg coefficient))
      · exact Arithmetic.mul_nonneg_direct (by decide)
          (add_nonneg (Arithmetic.mul_nonneg_direct
            slopeNonnegative smallNonnegative) valueNonnegative)
      · exact Arithmetic.mul_le_mul_of_nonneg_left_direct
          (add_le_add (Arithmetic.mul_le_mul_direct valueBound radiusBound
            smallNonnegative (valueNonnegative.trans valueBound)) le_rfl) (by decide)
      · exact Arithmetic.mul_le_mul_of_nonneg_left_direct
          (add_le_add (Arithmetic.mul_le_mul_direct slopeBound radiusBound
            smallNonnegative (slopeNonnegative.trans slopeBound)) valueBound) (by decide)
end Purelib.Polynomial.Dense.Gaussian.Bounds.Horner

end

public section

namespace Purelib.Polynomial.Dense.Gaussian.Bounds.Horner

open Purelib.Data.Gaussian
open Purelib.Data.Rat

/-- Fold the original coefficient table into value and slope bounds at a supplied squared disk radius. -/
def onDisk (polynomial : Dense.Basic.DensePolynomial Gaussian.Basic.Canonical) (radiusSq : Fraction.Rational) :
    Bounds.Horner := polynomial.coeffs.foldl (step radiusSq) ⟨0, 0⟩

/-- Both components of the original disk Horner fold are nonnegative at a nonnegative radius. -/
theorem onDisk_nonnegative (polynomial : Dense.Basic.DensePolynomial Gaussian.Basic.Canonical)
    (radiusSq : Fraction.Rational) (nonnegative : 0 ≤ radiusSq) :
    0 ≤ (onDisk polynomial radiusSq).value ∧ 0 ≤ (onDisk polynomial radiusSq).slope := by
  have specification := evalNormBoundsCoeffs_spec polynomial.coeffs nonnegative
    (x := 0) (y := 0)
    (Norm.Basic.normSq_zero ▸ nonnegative) (Norm.Basic.normSq_zero ▸ nonnegative)
    0 0 ⟨0, 0⟩ (by decide) (by decide)
    (Norm.Basic.normSq_zero ▸ (by decide : (0 : Fraction.Rational) ≤ 0))
    (Norm.Basic.normSq_zero ▸ (by decide : (0 : Fraction.Rational) ≤ 0))
    (by
      change Norm.Basic.normSq ((0 : Gaussian.Basic.Canonical) - 0) ≤ 0 * Norm.Basic.normSq (0 - 0)
      rewrite [Normalization.sub_zero, Norm.Basic.normSq_zero, Fraction.zero_mul]
      exact le_rfl)
  exact ⟨specification.1, specification.2.1⟩

/-- The same disk Horner value bounds the original polynomial reading at every point in that disk. -/
theorem normSq_eval_le_onDisk (polynomial : Dense.Basic.DensePolynomial Gaussian.Basic.Canonical)
    (radiusSq : Fraction.Rational) (nonnegative : 0 ≤ radiusSq) (point : Gaussian.Basic.Canonical)
    (inside : Norm.Basic.normSq point ≤ radiusSq) :
    Norm.Basic.normSq (polynomial.eval point) ≤ (onDisk polynomial radiusSq).value := by
  have specification := evalNormBoundsCoeffs_spec polynomial.coeffs nonnegative inside inside
    0 0 ⟨0, 0⟩ (by decide) (by decide)
    (Norm.Basic.normSq_zero ▸ (by decide : (0 : Fraction.Rational) ≤ 0))
    (Norm.Basic.normSq_zero ▸ (by decide : (0 : Fraction.Rational) ≤ 0))
    (by
      change Norm.Basic.normSq ((0 : Gaussian.Basic.Canonical) - 0) ≤ 0 * Norm.Basic.normSq (point - point)
      rewrite [Normalization.sub_zero, Norm.Basic.normSq_zero, Fraction.zero_mul]
      exact le_rfl)
  exact specification.2.2.1

end Purelib.Polynomial.Dense.Gaussian.Bounds.Horner

end
