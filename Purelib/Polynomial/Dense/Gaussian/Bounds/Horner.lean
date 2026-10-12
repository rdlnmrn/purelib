module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Field
public import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Bounds.Square

import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Polynomial.Bounds.Horner
import Purelib.Polynomial.Dense.Basic
import Purelib.Tactic.Ring
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic

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
open Purelib.Polynomial

namespace Purelib.Polynomial.Dense.Gaussian.Bounds.Horner

open Purelib.Data.Gaussian

/-- The exact rational scalar type used for squared-norm Horner bounds. -/
public abbrev Coordinate := Fraction.Rational

/-- Advance the squared-value and squared-difference bounds by one Gaussian Horner coefficient.

The value bound uses the input squared-radius bound and coefficient quadrance; the slope bound also retains the
preceding value bound. -/
@[expose] public def step (radiusSq : Fraction.Rational)
    (bounds : Bounds.Horner) (coefficient : Gaussian.Basic.Canonical) : Bounds.Horner where
  value := 2 * (bounds.value * radiusSq + Gaussian.Norm.Basic.normSq coefficient)
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
    (coeffs : List Gaussian.Basic.Canonical) {radiusSq : Fraction.Rational} {x y : Gaussian.Basic.Canonical}
    (hradius : 0 ≤ radiusSq)
    (hx : Gaussian.Norm.Basic.normSq x ≤ radiusSq) (hy : Gaussian.Norm.Basic.normSq y ≤ radiusSq)
    (accX accY : Gaussian.Basic.Canonical) (bounds : Bounds.Horner)
    (hvalue : 0 ≤ bounds.value) (hslope : 0 ≤ bounds.slope)
    (haccX : Gaussian.Norm.Basic.normSq accX ≤ bounds.value)
    (haccY : Gaussian.Norm.Basic.normSq accY ≤ bounds.value)
    (hdiff : Gaussian.Norm.Basic.normSq (accX - accY) ≤
      bounds.slope * Gaussian.Norm.Basic.normSq (x - y)) :
    let finalX := coeffs.foldl
      (fun acc coefficient => acc * x + coefficient) accX
    let finalY := coeffs.foldl
      (fun acc coefficient => acc * y + coefficient) accY
    let finalBounds := coeffs.foldl
      (Dense.Gaussian.Bounds.Horner.step radiusSq) bounds
    0 ≤ finalBounds.value ∧ 0 ≤ finalBounds.slope ∧
      Gaussian.Norm.Basic.normSq finalX ≤ finalBounds.value ∧
      Gaussian.Norm.Basic.normSq finalY ≤ finalBounds.value ∧
      Gaussian.Norm.Basic.normSq (finalX - finalY) ≤
        finalBounds.slope * Gaussian.Norm.Basic.normSq (x - y) := by
  induction coeffs generalizing accX accY bounds with
  | nil => exact ⟨hvalue, hslope, haccX, haccY, hdiff⟩
  | cons coefficient coeffs ih =>
      simp only [List.foldl_cons]
      apply ih
      · apply Square.twice_nonneg
        exact add_nonneg
          (Fraction.Order.Arithmetic.mul_nonneg_direct hvalue hradius)
          (Gaussian.Norm.Basic.normSq_nonneg coefficient)
      · apply Square.twice_nonneg
        exact add_nonneg
          (Fraction.Order.Arithmetic.mul_nonneg_direct hslope hradius)
          hvalue
      · have hmul : Gaussian.Norm.Basic.normSq accX * Gaussian.Norm.Basic.normSq x ≤
            bounds.value * radiusSq :=
          Fraction.Order.Arithmetic.mul_le_mul_direct haccX hx
            (Gaussian.Norm.Basic.normSq_nonneg x) hvalue
        calc
          Gaussian.Norm.Basic.normSq (accX * x + coefficient) ≤
              2 * (Gaussian.Norm.Basic.normSq (accX * x) + Gaussian.Norm.Basic.normSq coefficient) :=
            Gaussian.Norm.Bounds.normSq_add_le_two _ _
          _ = 2 * (Gaussian.Norm.Basic.normSq accX * Gaussian.Norm.Basic.normSq x +
            Gaussian.Norm.Basic.normSq coefficient) := by
            rw [Gaussian.Norm.Basic.normSq_mul]
          _ ≤ 2 * (bounds.value * radiusSq + Gaussian.Norm.Basic.normSq coefficient) :=
            Square.twice_le_twice (add_le_add hmul (le_refl _))
      · have hmul : Gaussian.Norm.Basic.normSq accY * Gaussian.Norm.Basic.normSq y ≤
            bounds.value * radiusSq :=
          Fraction.Order.Arithmetic.mul_le_mul_direct haccY hy
            (Gaussian.Norm.Basic.normSq_nonneg y) hvalue
        calc
          Gaussian.Norm.Basic.normSq (accY * y + coefficient) ≤
              2 * (Gaussian.Norm.Basic.normSq (accY * y) + Gaussian.Norm.Basic.normSq coefficient) :=
            Gaussian.Norm.Bounds.normSq_add_le_two _ _
          _ = 2 * (Gaussian.Norm.Basic.normSq accY * Gaussian.Norm.Basic.normSq y +
            Gaussian.Norm.Basic.normSq coefficient) := by
            rw [Gaussian.Norm.Basic.normSq_mul]
          _ ≤ 2 * (bounds.value * radiusSq + Gaussian.Norm.Basic.normSq coefficient) :=
            Square.twice_le_twice (add_le_add hmul (le_refl _))
      · have hidentity :
            (accX * x + coefficient) - (accY * y + coefficient) =
              (accX - accY) * x + accY * (x - y) := by
          apply Gaussian.Basic.ext <;>
            simp only [Gaussian.Basic.sub_re, Gaussian.Basic.sub_im, Gaussian.Basic.add_re, Gaussian.Basic.add_im,
              Gaussian.Basic.mul_re, Gaussian.Basic.mul_im] <;>
            ring1
        rw [hidentity]
        have hfirst : Gaussian.Norm.Basic.normSq (accX - accY) * Gaussian.Norm.Basic.normSq x ≤
            (bounds.slope * Gaussian.Norm.Basic.normSq (x - y)) * radiusSq :=
          Fraction.Order.Arithmetic.mul_le_mul_direct hdiff hx
            (Gaussian.Norm.Basic.normSq_nonneg x)
            (Fraction.Order.Arithmetic.mul_nonneg_direct hslope
              (Gaussian.Norm.Basic.normSq_nonneg (x - y)))
        have hsecond : Gaussian.Norm.Basic.normSq accY * Gaussian.Norm.Basic.normSq (x - y) ≤
            bounds.value * Gaussian.Norm.Basic.normSq (x - y) :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
            haccY (Gaussian.Norm.Basic.normSq_nonneg (x - y))
        calc
          Gaussian.Norm.Basic.normSq ((accX - accY) * x + accY * (x - y)) ≤
              2 * (Gaussian.Norm.Basic.normSq ((accX - accY) * x) +
                Gaussian.Norm.Basic.normSq (accY * (x - y))) := Gaussian.Norm.Bounds.normSq_add_le_two _ _
          _ = 2 * (Gaussian.Norm.Basic.normSq (accX - accY) * Gaussian.Norm.Basic.normSq x +
                Gaussian.Norm.Basic.normSq accY * Gaussian.Norm.Basic.normSq (x - y)) := by
            rw [Gaussian.Norm.Basic.normSq_mul, Gaussian.Norm.Basic.normSq_mul]
          _ ≤ 2 * ((bounds.slope * Gaussian.Norm.Basic.normSq (x - y)) * radiusSq +
                bounds.value * Gaussian.Norm.Basic.normSq (x - y)) :=
            Square.twice_le_twice (add_le_add hfirst hsecond)
          _ = 2 * (bounds.slope * radiusSq + bounds.value) *
                Gaussian.Norm.Basic.normSq (x - y) := by ring1
/-- The finite Horner value bound dominates twice the quadrance of evaluation at zero.

The radius and initial value ceiling are nonnegative, and the initial ceiling
bounds twice the accumulator quadrance. Folding the same coefficient list
preserves the bound for the final zero-input evaluation and retained ceiling. -/
public theorem twice_normSq_foldl_zero_le_hornerValue
    (radiusSq : Fraction.Rational) (radiusNonnegative : 0 ≤ radiusSq) :
    ∀ (coefficients : List Gaussian.Basic.Canonical) (accumulator : Gaussian.Basic.Canonical)
      (bounds : Bounds.Horner),
      0 ≤ bounds.value →
      2 * Gaussian.Norm.Basic.normSq accumulator ≤ bounds.value →
      2 * Gaussian.Norm.Basic.normSq
          (coefficients.foldl
            (fun value coefficient => value * 0 + coefficient) accumulator) ≤
        (coefficients.foldl (Dense.Gaussian.Bounds.Horner.step radiusSq) bounds).value := by
  intro coefficients
  induction coefficients with
  | nil =>
      intro accumulator bounds _ bound
      exact bound
  | cons coefficient coefficients inductionHypothesis =>
      intro accumulator bounds boundsNonnegative _
      simp only [List.foldl_cons]
      apply inductionHypothesis
      · unfold Dense.Gaussian.Bounds.Horner.step
        exact Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
          (add_nonneg
            (Fraction.Order.Arithmetic.mul_nonneg_direct boundsNonnegative
              radiusNonnegative)
            (Gaussian.Norm.Basic.normSq_nonneg coefficient))
      · simp only [mul_zero, zero_add]
        unfold Dense.Gaussian.Bounds.Horner.step
        apply Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        · exact le_add_of_nonneg_left
            (Fraction.Order.Arithmetic.mul_nonneg_direct boundsNonnegative
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
public theorem fold_bounds_mono (coefficients : List Gaussian.Basic.Canonical)
    {small large : Fraction.Rational} (smallNonnegative : 0 ≤ small)
    (radiusBound : small ≤ large) (left right : Bounds.Horner)
    (valueNonnegative : 0 ≤ left.value) (slopeNonnegative : 0 ≤ left.slope)
    (valueBound : left.value ≤ right.value) (slopeBound : left.slope ≤ right.slope) :
    (coefficients.foldl (Dense.Gaussian.Bounds.Horner.step small) left).value ≤
        (coefficients.foldl (Dense.Gaussian.Bounds.Horner.step large) right).value ∧
      (coefficients.foldl (Dense.Gaussian.Bounds.Horner.step small) left).slope ≤
        (coefficients.foldl (Dense.Gaussian.Bounds.Horner.step large) right).slope := by
  induction coefficients generalizing left right with
  | nil => exact ⟨valueBound, slopeBound⟩
  | cons coefficient coefficients ih =>
      simp only [List.foldl_cons]
      apply ih
      · exact Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
          (add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct
            valueNonnegative smallNonnegative) (Gaussian.Norm.Basic.normSq_nonneg coefficient))
      · exact Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
          (add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct
            slopeNonnegative smallNonnegative) valueNonnegative)
      · exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (add_le_add (Fraction.Order.Arithmetic.mul_le_mul_direct valueBound radiusBound
            smallNonnegative (valueNonnegative.trans valueBound)) le_rfl) (by decide)
      · exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (add_le_add (Fraction.Order.Arithmetic.mul_le_mul_direct slopeBound radiusBound
            smallNonnegative (slopeNonnegative.trans slopeBound)) valueBound) (by decide)
end Purelib.Polynomial.Dense.Gaussian.Bounds.Horner

end
