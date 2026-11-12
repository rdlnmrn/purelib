module
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Legendre.Paths
public import Purelib.Curves.Legendre.Polynomial
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Clearance.Box.Dominance.Basic
import Purelib.Polynomial.Dense.Gaussian.Linear.Translated
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Boundary
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring

open Purelib.Data.Rat.Fraction.Order

open Purelib.Data.Gaussian.Norm

open Purelib

open Purelib.Curves.Legendre

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Polynomial.Clearance.Box

open Purelib.Polynomial.Dense.Gaussian.Linear.Translated

section
@[expose] public section

/-!
# One explicit rational Legendre crossing segment

This module certifies a single positive projected crossing of the moving
Legendre root over the fixed root at zero.  The parameter moves horizontally
from `1/4 + 2i` to `-1/4 + 2i`.  Broad chamber-owner boxes retain the
same three roots across the coefficient overlap, while much smaller sample
owners certify the change in left-to-right projection order.
-/

namespace Purelib.Curves.Legendre.Rouche

/-- The sharp Rouché estimate for changing only the moving Legendre factor. Unlike a generic dense coefficient majorant,
it retains the two common fixed factors and therefore sees the exact root-displacement condition. -/
def factorMoveDominanceAt (source target : Data.Gaussian.Basic.Canonical) {box :
  Rational.Box}
    (zeroClearance : Boundary.Basic.BoundaryClearance
      (translatedCoordinate 0) box)
    (movingClearance : Boundary.Basic.BoundaryClearance
      (translatedCoordinate source) box)
    (oneClearance : Boundary.Basic.BoundaryClearance
      (translatedCoordinate 1) box)
    (displacementSmall :
      Basic.normSq
          (source - target) < movingClearance.bound) :
    Dominance.Basic.BoundaryNormDominance
      (Paths.polynomial source) (Polynomial.perturbationAt source target) box where
  margin := zeroClearance.bound * oneClearance.bound *
    (movingClearance.bound -
      Basic.normSq
        (source - target))
  positive := by
    apply Arithmetic.mul_pos_direct
    · exact Arithmetic.mul_pos_direct
        zeroClearance.positive oneClearance.positive
    · exact Arithmetic.sub_pos_direct displacementSmall
  lower := by
    intro point boundary
    have zeroLower := zeroClearance.lower point boundary
    have movingLower := movingClearance.lower point boundary
    have oneLower := oneClearance.lower point boundary
    rw [← Basic.normSq_eq_canonical] at zeroLower movingLower oneLower
    have commonLower : zeroClearance.bound * oneClearance.bound ≤
        Basic.normSq
            ((translatedCoordinate 0).eval point) *
          Basic.normSq
            ((translatedCoordinate 1).eval point) := by
      exact (Arithmetic.mul_le_mul_of_nonneg_right_direct
        zeroLower oneClearance.positive.le).trans
          (Arithmetic.mul_le_mul_of_nonneg_left_direct
            oneLower
            (Basic.normSq_nonneg
              ((translatedCoordinate 0).eval point)))
    have gapLower : movingClearance.bound -
          Basic.normSq
            (source - target) ≤
        Basic.normSq
            ((translatedCoordinate source).eval
              point) -
          Basic.normSq
            (source - target) :=
      Arithmetic.sub_le_sub_right_direct movingLower _
    have gapNonnegative : 0 ≤ movingClearance.bound -
        Basic.normSq
          (source - target) :=
      (Arithmetic.sub_pos_direct displacementSmall).le
    have commonNonnegative : 0 ≤
        Basic.normSq
            ((translatedCoordinate 0).eval point) *
          Basic.normSq
            ((translatedCoordinate 1).eval point) :=
      Arithmetic.mul_nonneg_direct
        (Basic.normSq_nonneg _)
        (Basic.normSq_nonneg _)
    have scaled :=
      (Arithmetic.mul_le_mul_of_nonneg_right_direct
        commonLower gapNonnegative).trans
        (Arithmetic.mul_le_mul_of_nonneg_left_direct
          gapLower commonNonnegative)
    rw [← Basic.normSq_eq_canonical ((Paths.polynomial source).eval point),
      ← Basic.normSq_eq_canonical ((Polynomial.perturbationAt source target).eval point)]
    rw [Polynomial.polynomial_eval_factorsAt source,
      Polynomial.perturbationAt_eval source target,
      Basic.normSq_mul,
      Basic.normSq_mul,
      Basic.normSq_mul,
      Basic.normSq_mul]
    calc
      zeroClearance.bound * oneClearance.bound *
          (movingClearance.bound -
            Basic.normSq
              (source - target)) ≤
        (Basic.normSq
            ((translatedCoordinate 0).eval point) *
          Basic.normSq
            ((translatedCoordinate 1).eval point)) *
          (Basic.normSq
              ((translatedCoordinate
                source).eval point) -
            Basic.normSq
              (source - target)) := scaled
      _ =
          Basic.normSq
                ((translatedCoordinate 0).eval point) *
              Basic.normSq
                ((translatedCoordinate
                  source).eval point) *
              Basic.normSq
                ((translatedCoordinate 1).eval point) -
            Basic.normSq
                ((translatedCoordinate 0).eval point) *
              Basic.normSq
                ((translatedCoordinate 1).eval point) *
              Basic.normSq
                (source - target) := by ring1
end Purelib.Curves.Legendre.Rouche

end
