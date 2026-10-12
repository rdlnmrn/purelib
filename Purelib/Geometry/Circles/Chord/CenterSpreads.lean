module
import Purelib.Geometry.Plane.Line.Affine
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Line.Quadrance
import Purelib.Geometry.Plane.Line.Relations
public import Purelib.Geometry.Plane.Line.Spread
import Purelib.Geometry.Plane.Line.Spread.Orthogonality
public import Purelib.Geometry.Plane.Point.Affine
import Purelib.Geometry.Plane.Point.Affine.Quadrance
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Point.Quadrance
import Purelib.Geometry.Triangles.Isosceles.Median
import Purelib.Geometry.Triangles.Right.Trigonometry

import Purelib.Algebra.Field.ExplicitField
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Nontrivial.Defs
import Purelib.Tactic.Ring

open Purelib.Algebra.Field (ExplicitField)
open Purelib.Geometry.Plane (Line)

open Purelib

open Purelib.Geometry

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Line.Basic

open Purelib.Geometry.Plane.Line.Spread

open Purelib.Geometry.Plane.Point

open Purelib.Geometry.Plane.Point.Affine

section
@[expose] public section

/-!
# Divine Proportions, remaining Chapter 12 exercises

This module completes the reader exercises: the finite chord argument from
Exercise 12.1, the null-side circumcenter argument from Exercise 12.4, and the
remaining exact polynomial and spread calculations.
-/

namespace Purelib.Geometry.Circles.Chord.CenterSpreads

open Purelib.Algebra

variable {K : Type*} [ExplicitField K]

/-- The finite one-chord argument used twice in Exercise 12.1. The midpoint line from an equal-quadrance center is
perpendicular to the chord. The right-triangle Spread ratio and the cleared Extended-spread identity identify the two
center spreads with the spread at the opposite vertex; Complementary spreads then gives the spread at the chord
endpoint. -/
theorem exercise_12_1
    [Nontrivial K] [DecidableEq K]
    (opposite left right center : Geometry.Plane.Point K)
    (rightLeftDistinct : right ≠ left)
    (oppositeLeftDistinct : opposite ≠ left)
    (oppositeRightDistinct : opposite ≠ right)
    (centerRightDistinct : center ≠ right)
    (centerLeftDistinct : center ≠ left)
    (centerMidpointDistinct : center ≠ Affine.midpoint right left)
    (rightMidpointDistinct : right ≠ Affine.midpoint right left)
    (oppositeLeftNonNull :
      ¬ (Incidence.lineThrough opposite left oppositeLeftDistinct).IsNull)
    (oppositeRightNonNull :
      ¬ (Incidence.lineThrough opposite right oppositeRightDistinct).IsNull)
    (chordNonNull :
      ¬ (Incidence.lineThrough right left rightLeftDistinct).IsNull)
    (centerRightNonNull :
      ¬ (Incidence.lineThrough center right centerRightDistinct).IsNull)
    (centerLeftNonNull :
      ¬ (Incidence.lineThrough center left centerLeftDistinct).IsNull)
    (centerMidpointNonNull :
      ¬ (Incidence.lineThrough center (Affine.midpoint right left)
        centerMidpointDistinct).IsNull)
    (twoNonzero : (2 : K) ≠ 0)
    (equalRadii : Quadrance.quadrance center right = Quadrance.quadrance center left)
    (medianPerpendicularChord :
      (Incidence.lineThrough center (Affine.midpoint right left)
        centerMidpointDistinct).Perpendicular
          (Incidence.lineThrough right left rightLeftDistinct))
    (sourceSpread : K)
    (sourceSpreadValue :
      Spread.spread (Incidence.lineThrough opposite left oppositeLeftDistinct)
          (Incidence.lineThrough opposite right oppositeRightDistinct)
          oppositeLeftNonNull oppositeRightNonNull = sourceSpread)
    (extendedChord :
      sourceSpread * (4 * Quadrance.quadrance center right) = Quadrance.quadrance left right) :
    let rightCenterNonNull :
        ¬ (Incidence.lineThrough right center centerRightDistinct.symm).IsNull := by
      intro reversedNull
      apply centerRightNonNull
      apply (Quadrance.null_line_iff_quadrance_zero center right
        centerRightDistinct).2
      calc
        Quadrance.quadrance center right = Quadrance.quadrance right center :=
          Quadrance.quadrance_symm center right
        _ = 0 := (Quadrance.null_line_iff_quadrance_zero right center
          centerRightDistinct.symm).1 reversedNull
    Spread.spread (Incidence.lineThrough opposite left oppositeLeftDistinct)
          (Incidence.lineThrough opposite right oppositeRightDistinct)
          oppositeLeftNonNull oppositeRightNonNull = sourceSpread ∧
      Spread.spread (Incidence.lineThrough right center centerRightDistinct.symm)
          (Incidence.lineThrough right left rightLeftDistinct)
          rightCenterNonNull chordNonNull = 1 - sourceSpread ∧
      Spread.spread (Incidence.lineThrough center right centerRightDistinct)
          (Incidence.lineThrough center (Affine.midpoint right left) centerMidpointDistinct)
          centerRightNonNull centerMidpointNonNull = sourceSpread ∧
      Spread.spread (Incidence.lineThrough center left centerLeftDistinct)
          (Incidence.lineThrough center (Affine.midpoint right left) centerMidpointDistinct)
          centerLeftNonNull centerMidpointNonNull = sourceSpread := by
  dsimp only
  let chord := Incidence.lineThrough right left rightLeftDistinct
  let median := Incidence.lineThrough center (Affine.midpoint right left)
    centerMidpointDistinct
  let centerRight := Incidence.lineThrough center right centerRightDistinct
  let centerLeft := Incidence.lineThrough center left centerLeftDistinct
  let rightCenter := Incidence.lineThrough right center centerRightDistinct.symm
  let rightMidpoint := Incidence.lineThrough right (Affine.midpoint right left)
    rightMidpointDistinct
  have rightMidpointParallelChord : rightMidpoint.Parallel chord := by
    apply Incidence.lineThrough_parallel_of_contains chord right (Affine.midpoint right left)
      rightMidpointDistinct
    · exact Incidence.lineThrough_contains_first right left rightLeftDistinct
    · exact Affine.midpoint_on_line right left rightLeftDistinct twoNonzero
  have medianPerpendicularRightMidpoint :
      median.Perpendicular rightMidpoint := by
    apply Line.perpendicular_symm
    exact Relations.perpendicular_of_parallel_left chord rightMidpoint median
      (Line.parallel_symm rightMidpointParallelChord)
      (Line.perpendicular_symm medianPerpendicularChord)
  have centerSpreadRatio :
      Spread.spread centerRight median centerRightNonNull centerMidpointNonNull =
        Quadrance.quadrance right (Affine.midpoint right left) /
          Quadrance.quadrance center right := by
    exact Triangles.Right.Trigonometry.spread_ratio center right (Affine.midpoint right left)
      centerRightDistinct centerMidpointDistinct rightMidpointDistinct
      centerRightNonNull centerMidpointNonNull twoNonzero
      medianPerpendicularRightMidpoint
  have midpointQuadrance :
      Quadrance.quadrance right (Affine.midpoint right left) = Quadrance.quadrance left right / 4 := by
    calc
      Quadrance.quadrance right (Affine.midpoint right left) =
          Quadrance.quadrance (Affine.midpoint right left) right :=
        Quadrance.quadrance_symm right (Affine.midpoint right left)
      _ = Quadrance.quadrance right left / 4 :=
        Quadrance.midpoint_quadrance right left twoNonzero
      _ = Quadrance.quadrance left right / 4 := by
        rw [Quadrance.quadrance_symm right left]
  have fourNonzero : (4 : K) ≠ 0 := by
    have squareNonzero :=
      ExplicitField.mul_ne_zero twoNonzero twoNonzero
    simpa only [show (4 : K) = 2 * 2 by ring1] using squareNonzero
  have quarterChord :
      Quadrance.quadrance left right / 4 =
        sourceSpread * Quadrance.quadrance center right := by
    have productsEqual :
        (Quadrance.quadrance left right / 4) * 4 =
          (sourceSpread * Quadrance.quadrance center right) * 4 := by
      calc
        (Quadrance.quadrance left right / 4) * 4 = Quadrance.quadrance left right :=
          ExplicitField.div_mul_cancel _ fourNonzero
        _ = sourceSpread * (4 * Quadrance.quadrance center right) :=
          extendedChord.symm
        _ = (sourceSpread * Quadrance.quadrance center right) * 4 := by ring1
    have fourCancel : (4 : K) * (4 : K)⁻¹ = 1 :=
      ExplicitField.mul_inv_cancel 4 fourNonzero
    calc
      Quadrance.quadrance left right / 4 =
          ((Quadrance.quadrance left right / 4) * 4) * (4 : K)⁻¹ := by
        simp only [ExplicitField.div_eq_mul_inv]
        rw [mul_assoc, fourCancel, mul_one]
      _ = ((sourceSpread * Quadrance.quadrance center right) * 4) *
          (4 : K)⁻¹ := by rw [productsEqual]
      _ = sourceSpread * Quadrance.quadrance center right := by
        rw [mul_assoc, fourCancel, mul_one]
  have centerRadiusNonzero : Quadrance.quadrance center right ≠ 0 := by
    intro radiusZero
    apply centerRightNonNull
    exact (Quadrance.null_line_iff_quadrance_zero center right
      centerRightDistinct).2 radiusZero
  have centerSpreadTimesRadius :
      Spread.spread centerRight median centerRightNonNull centerMidpointNonNull *
          Quadrance.quadrance center right =
        sourceSpread * Quadrance.quadrance center right := by
    calc
      Spread.spread centerRight median centerRightNonNull centerMidpointNonNull *
            Quadrance.quadrance center right =
          (Quadrance.quadrance right (Affine.midpoint right left) /
              Quadrance.quadrance center right) * Quadrance.quadrance center right := by
        rw [centerSpreadRatio]
      _ = Quadrance.quadrance right (Affine.midpoint right left) :=
        ExplicitField.div_mul_cancel _ centerRadiusNonzero
      _ = Quadrance.quadrance left right / 4 := midpointQuadrance
      _ = sourceSpread * Quadrance.quadrance center right := quarterChord
  have radiusCancel :
      Quadrance.quadrance center right * (Quadrance.quadrance center right)⁻¹ = 1 :=
    ExplicitField.mul_inv_cancel _ centerRadiusNonzero
  have centerSpreadValue :
      Spread.spread centerRight median centerRightNonNull centerMidpointNonNull =
        sourceSpread := by
    calc
      Spread.spread centerRight median centerRightNonNull centerMidpointNonNull =
          (Spread.spread centerRight median centerRightNonNull
              centerMidpointNonNull * Quadrance.quadrance center right) *
            (Quadrance.quadrance center right)⁻¹ := by
        rw [mul_assoc, radiusCancel, mul_one]
      _ = (sourceSpread * Quadrance.quadrance center right) *
          (Quadrance.quadrance center right)⁻¹ := by
        rw [centerSpreadTimesRadius]
      _ = sourceSpread := by rw [mul_assoc, radiusCancel, mul_one]
  have centerSpreadEquality :=
    Triangles.Isosceles.Median.isosceles_midpoint_equal_spreads right left center
      centerRightDistinct centerLeftDistinct centerMidpointDistinct
      centerRightNonNull centerLeftNonNull centerMidpointNonNull
      twoNonzero equalRadii
  have centerLeftSpreadValue :
      Spread.spread centerLeft median centerLeftNonNull centerMidpointNonNull =
        sourceSpread := centerSpreadEquality.symm.trans centerSpreadValue
  have rightCenterNonNull : ¬ rightCenter.IsNull := by
    intro reversedNull
    apply centerRightNonNull
    apply (Quadrance.null_line_iff_quadrance_zero center right
      centerRightDistinct).2
    calc
      Quadrance.quadrance center right = Quadrance.quadrance right center :=
        Quadrance.quadrance_symm center right
      _ = 0 := (Quadrance.null_line_iff_quadrance_zero right center
        centerRightDistinct.symm).1 reversedNull
  have centerRightParallelReverse : centerRight.Parallel rightCenter := by
    unfold centerRight rightCenter Geometry.Plane.Line.Parallel Incidence.lineThrough
    ring1
  have centerSpreadReverse :
      Spread.spread centerRight median centerRightNonNull centerMidpointNonNull =
        Spread.spread rightCenter median rightCenterNonNull centerMidpointNonNull := by
    exact Spread.spread_eq_of_parallel_pairs centerRight median rightCenter median
      centerRightNonNull centerMidpointNonNull rightCenterNonNull
      centerMidpointNonNull centerRightParallelReverse
      (Line.parallel_refl median)
  have medianReverseSpreadValue :
      Spread.spread median rightCenter centerMidpointNonNull rightCenterNonNull =
        sourceSpread := by
    calc
      Spread.spread median rightCenter centerMidpointNonNull rightCenterNonNull =
          Spread.spread rightCenter median rightCenterNonNull
            centerMidpointNonNull :=
        Spread.spread_symm median rightCenter centerMidpointNonNull
          rightCenterNonNull
      _ = Spread.spread centerRight median centerRightNonNull
          centerMidpointNonNull := centerSpreadReverse.symm
      _ = sourceSpread := centerSpreadValue
  have complementary := Orthogonality.complementary_spreads median chord rightCenter
    centerMidpointNonNull chordNonNull rightCenterNonNull
    medianPerpendicularChord
  have rightComplement :
      Spread.spread rightCenter chord rightCenterNonNull chordNonNull =
        1 - sourceSpread := by
    calc
      Spread.spread rightCenter chord rightCenterNonNull chordNonNull =
          Spread.spread chord rightCenter chordNonNull rightCenterNonNull :=
        Spread.spread_symm rightCenter chord rightCenterNonNull chordNonNull
      _ = (Spread.spread chord rightCenter chordNonNull rightCenterNonNull +
            Spread.spread median rightCenter centerMidpointNonNull
              rightCenterNonNull) -
          Spread.spread median rightCenter centerMidpointNonNull
            rightCenterNonNull := by ring1
      _ = 1 - Spread.spread median rightCenter centerMidpointNonNull
          rightCenterNonNull := by rw [complementary]
      _ = 1 - sourceSpread := by rw [medianReverseSpreadValue]
  exact ⟨sourceSpreadValue, rightComplement, centerSpreadValue,
    centerLeftSpreadValue⟩
end Purelib.Geometry.Circles.Chord.CenterSpreads

end
