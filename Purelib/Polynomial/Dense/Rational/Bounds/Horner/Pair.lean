module

import Purelib.Data.Rat.Bounds.Square

import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Polynomial.Bounds.Horner
import Purelib.Polynomial.Dense.Basic
import Purelib.Tactic.Ring
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Algebra.Semiring.Normalization

/-!
# Retained rational Horner square bounds

The original finite coefficient folds retain their interval radii and
accumulator data. Value bounds and paired value/difference bounds
certify those same finite evaluations and their scalar readbacks.
-/

namespace Purelib.Polynomial.Dense.Rational.Bounds.Horner.Pair

open Purelib
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction
open Purelib.Data.Rat.Bounds.Square (twice_le_twice twice_nonneg add_sq_le_two)
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Rational
open Purelib.Algebra.Semiring

/-- The constructive rational carrier for squared Horner value and difference bounds. -/
public abbrev Coordinate := Fraction.Rational

/-- Advance simultaneous squared-value and squared-difference bounds by one Horner coefficient.

The original paired step updates the value component with the coefficient
square and the slope component with the previous value bound. Both
components use the same retained squared radius. -/
@[expose] public def step (radiusSq : Coordinate)
    (bounds : Bounds.Horner) (coefficient : Coordinate) : Bounds.Horner where
  value := 2 * (bounds.value * radiusSq + coefficient ^ 2)
  slope := 2 * (bounds.slope * radiusSq + bounds.value)

/-- Propagate simultaneous squared-value and squared-difference bounds through a finite Horner fold.

Both supplied point squares lie below the retained nonnegative radius.
The original accumulators and their difference satisfy the given value
and slope bounds, which propagate through the same coefficient fold. -/
public theorem evalSqBoundsCoeffs_spec
    (coefficients : List Fraction.Rational) {radiusSq x y : Fraction.Rational}
    (radiusNonnegative : 0 ≤ radiusSq)
    (xBound : x ^ 2 ≤ radiusSq) (yBound : y ^ 2 ≤ radiusSq)
    (accumulatorX accumulatorY : Fraction.Rational) (bounds : Bounds.Horner)
    (valueNonnegative : 0 ≤ bounds.value)
    (slopeNonnegative : 0 ≤ bounds.slope)
    (accumulatorXBound : accumulatorX ^ 2 ≤ bounds.value)
    (accumulatorYBound : accumulatorY ^ 2 ≤ bounds.value)
    (differenceBound : (accumulatorX - accumulatorY) ^ 2 ≤
      bounds.slope * (x - y) ^ 2) :
    let finalX := coefficients.foldl
      (fun value coefficient => value * x + coefficient) accumulatorX
    let finalY := coefficients.foldl
      (fun value coefficient => value * y + coefficient) accumulatorY
    let finalBounds := coefficients.foldl
      (step radiusSq) bounds
    0 ≤ finalBounds.value ∧ 0 ≤ finalBounds.slope ∧
      finalX ^ 2 ≤ finalBounds.value ∧
      finalY ^ 2 ≤ finalBounds.value ∧
      (finalX - finalY) ^ 2 ≤ finalBounds.slope * (x - y) ^ 2 := by
  induction coefficients generalizing accumulatorX accumulatorY bounds with
  | nil => exact ⟨valueNonnegative, slopeNonnegative,
      accumulatorXBound, accumulatorYBound, differenceBound⟩
  | cons coefficient coefficients inductionHypothesis =>
      simp only [List.foldl_cons]
      apply inductionHypothesis
      · apply twice_nonneg
        exact add_nonneg
          (Order.Arithmetic.mul_nonneg_direct
            valueNonnegative radiusNonnegative)
          (Order.Arithmetic.sq_nonneg_direct coefficient)
      · apply twice_nonneg
        exact add_nonneg
          (Order.Arithmetic.mul_nonneg_direct
            slopeNonnegative radiusNonnegative)
          valueNonnegative
      · have productBound : (accumulatorX * x) ^ 2 ≤
            bounds.value * radiusSq := by
          rw [Normalization.product_pow accumulatorX x 2]
          exact Order.Arithmetic.mul_le_mul_direct
            accumulatorXBound xBound
            (Order.Arithmetic.sq_nonneg_direct x)
            valueNonnegative
        exact (add_sq_le_two (accumulatorX * x) coefficient).trans
          (twice_le_twice
            (add_le_add productBound (le_refl (coefficient ^ 2))))
      · have productBound : (accumulatorY * y) ^ 2 ≤
            bounds.value * radiusSq := by
          rw [Normalization.product_pow accumulatorY y 2]
          exact Order.Arithmetic.mul_le_mul_direct
            accumulatorYBound yBound
            (Order.Arithmetic.sq_nonneg_direct y)
            valueNonnegative
        exact (add_sq_le_two (accumulatorY * y) coefficient).trans
          (twice_le_twice
            (add_le_add productBound (le_refl (coefficient ^ 2))))
      · have identity :
            (accumulatorX * x + coefficient) -
                (accumulatorY * y + coefficient) =
              (accumulatorX - accumulatorY) * x +
                accumulatorY * (x - y) := by ring1
        rw [identity]
        have firstBound :
            (accumulatorX - accumulatorY) ^ 2 * x ^ 2 ≤
              (bounds.slope * (x - y) ^ 2) * radiusSq :=
          Order.Arithmetic.mul_le_mul_direct differenceBound xBound
            (Order.Arithmetic.sq_nonneg_direct x)
            (Order.Arithmetic.mul_nonneg_direct slopeNonnegative
              (Order.Arithmetic.sq_nonneg_direct (x - y)))
        have secondBound : accumulatorY ^ 2 * (x - y) ^ 2 ≤
            bounds.value * (x - y) ^ 2 :=
          Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
            accumulatorYBound
            (Order.Arithmetic.sq_nonneg_direct (x - y))
        calc
          ((accumulatorX - accumulatorY) * x +
              accumulatorY * (x - y)) ^ 2 ≤
              2 * (((accumulatorX - accumulatorY) * x) ^ 2 +
                (accumulatorY * (x - y)) ^ 2) := add_sq_le_two _ _
          _ = 2 * ((accumulatorX - accumulatorY) ^ 2 * x ^ 2 +
                accumulatorY ^ 2 * (x - y) ^ 2) := by
            rw [Normalization.product_pow (accumulatorX - accumulatorY) x 2,
              Normalization.product_pow accumulatorY (x - y) 2]
          _ ≤ 2 * ((bounds.slope * (x - y) ^ 2) * radiusSq +
                bounds.value * (x - y) ^ 2) :=
            twice_le_twice (add_le_add firstBound secondBound)
          _ = 2 * (bounds.slope * radiusSq + bounds.value) *
                (x - y) ^ 2 := by ring1

/-- Enlarging the nonnegative radius, value bound and slope bound enlarges both final Horner bounds.

The original coefficient list is fixed while nonnegative radii, value
bounds and slope bounds are enlarged. Induction retains both original
paired accumulator updates at each coefficient. -/
public theorem hornerSqBoundsCoeffs_monotone
    (coefficients : List Fraction.Rational) {smallRadius largeRadius : Fraction.Rational}
    {smallBounds largeBounds : Bounds.Horner}
    (smallRadiusNonnegative : 0 ≤ smallRadius)
    (largeRadiusNonnegative : 0 ≤ largeRadius)
    (smallValueNonnegative : 0 ≤ smallBounds.value)
    (smallSlopeNonnegative : 0 ≤ smallBounds.slope)
    (largeValueNonnegative : 0 ≤ largeBounds.value)
    (largeSlopeNonnegative : 0 ≤ largeBounds.slope)
    (radiusLe : smallRadius ≤ largeRadius)
    (valueLe : smallBounds.value ≤ largeBounds.value)
    (slopeLe : smallBounds.slope ≤ largeBounds.slope) :
    let smallFinal := coefficients.foldl
      (step smallRadius) smallBounds
    let largeFinal := coefficients.foldl
      (step largeRadius) largeBounds
    smallFinal.value ≤ largeFinal.value ∧
      smallFinal.slope ≤ largeFinal.slope := by
  induction coefficients generalizing smallBounds largeBounds with
  | nil => exact ⟨valueLe, slopeLe⟩
  | cons coefficient coefficients inductionHypothesis =>
      simp only [List.foldl_cons]
      have valueProductLe : smallBounds.value * smallRadius ≤
          largeBounds.value * largeRadius :=
        Order.Arithmetic.mul_le_mul_direct valueLe radiusLe
          smallRadiusNonnegative largeValueNonnegative
      have slopeProductLe : smallBounds.slope * smallRadius ≤
          largeBounds.slope * largeRadius :=
        Order.Arithmetic.mul_le_mul_direct slopeLe radiusLe
          smallRadiusNonnegative largeSlopeNonnegative
      have nextValueLe :
          (step smallRadius smallBounds coefficient).value ≤
            (step largeRadius largeBounds coefficient).value :=
        twice_le_twice (add_le_add valueProductLe (le_refl _))
      have nextSlopeLe :
          (step smallRadius smallBounds coefficient).slope ≤
            (step largeRadius largeBounds coefficient).slope :=
        twice_le_twice (add_le_add slopeProductLe valueLe)
      apply inductionHypothesis
      · apply twice_nonneg
        exact add_nonneg
          (Order.Arithmetic.mul_nonneg_direct
            smallValueNonnegative smallRadiusNonnegative)
          (Order.Arithmetic.sq_nonneg_direct coefficient)
      · apply twice_nonneg
        exact add_nonneg
          (Order.Arithmetic.mul_nonneg_direct
            smallSlopeNonnegative smallRadiusNonnegative)
          smallValueNonnegative
      · apply twice_nonneg
        exact add_nonneg
          (Order.Arithmetic.mul_nonneg_direct
            largeValueNonnegative largeRadiusNonnegative)
          (Order.Arithmetic.sq_nonneg_direct coefficient)
      · apply twice_nonneg
        exact add_nonneg
          (Order.Arithmetic.mul_nonneg_direct
            largeSlopeNonnegative largeRadiusNonnegative)
          largeValueNonnegative
      · exact nextValueLe
      · exact nextSlopeLe

end Purelib.Polynomial.Dense.Rational.Bounds.Horner.Pair
