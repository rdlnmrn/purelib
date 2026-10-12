module
public import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Projective.Chordal.Affine
public import Purelib.Geometry.Projective.Chordal.Basic
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Geometry.Rational.Box.Interior

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

open Purelib

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Geometry.Projective

open Purelib.Geometry.Projective.Chordal

open Purelib.Geometry.Projective.Line

open Purelib.Geometry.Rational.Box

section
@[expose] public section

/-!
# Projective clearance from a strict rational box interior

A displayed rational point strictly inside a rational box has a positive
squared-chordal distance from every affine point outside that box.  The gap
below is deliberately conservative but entirely rational and executable.
It remains positive even when the outside point runs towards projective
infinity, which is exactly what an ordinary affine distance estimate misses.

This is a pointwise finite separation theorem.  It introduces no root,
limit, compactness argument, or completed point.
-/

namespace Purelib.Geometry.Projective.Chordal.Box.Interior

/-! ## Uniform separation of a finite box from projective infinity -/

/-- Positive squared-chordal gap from projective infinity to every affine point of a displayed finite rational box. -/
def infinityBoxGap (box : Rational.Box) :
  Fraction.Rational :=
  1 / (1 + box.normSqBound)

/-- The computed squared-chordal gap between a finite box and the projective infinity coordinate is positive. -/
theorem infinityBoxGap_pos (box : Rational.Box)
  : 0 < infinityBoxGap box :=
  Fraction.Order.Field.div_pos_direct (by decide)
    (add_pos_of_pos_of_nonneg (by decide) box.normSqBound_nonneg)

/-- Every affine point in the box is at least the computed rational gap from `ω`; no compactification or limiting point
is introduced. -/
theorem infinityBoxGap_le_affine
    {box : Rational.Box} {point : Data.Gaussian.Basic.Canonical} (inside : box.Contains point) :
    infinityBoxGap box ≤
      Chordal.Basic.chordalSq
        (Proj.affine point) Proj.omega := by
  rw [Affine.chordalSq_omega]
  exact Fraction.Order.Field.div_le_div_of_nonneg_left_direct
    (by decide)
    (add_pos_of_pos_of_nonneg (by decide)
      (Data.Gaussian.Norm.Basic.normSq_nonneg point))
    (add_le_add le_rfl (box.normSq_le_normSqBound inside))

/-- Conservative projective gap from a strict interior rational point to the complete affine complement of its box. -/
def strictChordalGap (box : Rational.Box) (point
  : Data.Gaussian.Basic.Canonical) : Fraction.Rational :=
  let gapSq := Interior.strictCoordinateGap box point ^ 2
  gapSq /
    ((1 + Data.Gaussian.Norm.Basic.normSq point) *
      (1 + 2 * Data.Gaussian.Norm.Basic.normSq point + 2 * gapSq))

/-- A point strictly inside the box has a positive computed squared-chordal clearance. -/
theorem strictChordalGap_pos
    {box : Rational.Box} {point : Data.Gaussian.Basic.Canonical} (strict : box.StrictContains point) :
    0 < strictChordalGap box point := by
  let gap := Interior.strictCoordinateGap box point
  have gapPositive : 0 < gap := Interior.strictCoordinateGap_pos strict
  have gapSqPositive : 0 < gap ^ 2 :=
    Fraction.Order.Arithmetic.pow_pos_direct gapPositive 2
  have firstPositive : 0 < 1 + Data.Gaussian.Norm.Basic.normSq point :=
    add_pos_of_pos_of_nonneg (by decide) (Data.Gaussian.Norm.Basic.normSq_nonneg point)
  have secondPositive : 0 <
      1 + 2 * Data.Gaussian.Norm.Basic.normSq point + 2 * gap ^ 2 :=
    add_pos_of_pos_of_nonneg
      (add_pos_of_pos_of_nonneg (by decide)
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
          (Data.Gaussian.Norm.Basic.normSq_nonneg point)))
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        (Fraction.Order.Arithmetic.sq_nonneg_direct gap))
  exact Fraction.Order.Field.div_pos_direct gapSqPositive
    (Fraction.Order.Arithmetic.mul_pos_direct firstPositive secondPositive)

/-- The computed rational projective gap is below the squared-chordal distance from the strict point to every displayed
affine point outside the box. -/
theorem strictChordalGap_le_affine_of_outside
    {box : Rational.Box} {point other : Data.Gaussian.Basic.Canonical}
    (strict : box.StrictContains point) (outside : ¬box.Contains other) :
    strictChordalGap box point ≤
      Chordal.Basic.chordalSq
        (Proj.affine point) (Proj.affine other) := by
  let gap := Interior.strictCoordinateGap box point
  let gapSq := gap ^ 2
  let distance := Data.Gaussian.Norm.Basic.normSq (point - other)
  let pointNorm := Data.Gaussian.Norm.Basic.normSq point
  let otherNorm := Data.Gaussian.Norm.Basic.normSq other
  let common := 1 + pointNorm
  let targetPart := 1 + 2 * pointNorm + 2 * gapSq
  let actualPart := 1 + otherNorm
  have gapSqLe : gapSq ≤ distance := by
    simpa only [gapSq, gap, distance] using
      Interior.strictCoordinateGap_sq_le_normSq_sub_of_outside strict outside
  have gapSqNonnegative : 0 ≤ gapSq := by
    exact Fraction.Order.Arithmetic.sq_nonneg_direct gap
  have distanceNonnegative : 0 ≤ distance := Data.Gaussian.Norm.Basic.normSq_nonneg _
  have pointNormNonnegative : 0 ≤ pointNorm := Data.Gaussian.Norm.Basic.normSq_nonneg _
  have otherNormNonnegative : 0 ≤ otherNorm := Data.Gaussian.Norm.Basic.normSq_nonneg _
  have commonPositive : 0 < common :=
    add_pos_of_pos_of_nonneg (by decide) pointNormNonnegative
  have targetPartPositive : 0 < targetPart := by
    dsimp only [targetPart]
    exact add_pos_of_pos_of_nonneg
      (add_pos_of_pos_of_nonneg (by decide)
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
          pointNormNonnegative))
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        gapSqNonnegative)
  have actualPartPositive : 0 < actualPart :=
    add_pos_of_pos_of_nonneg (by decide) otherNormNonnegative
  have otherNormUpper : otherNorm ≤ 2 * (pointNorm + distance) := by
    have raw := Data.Gaussian.Norm.Bounds.normSq_sub_le_two point (point - other)
    have identity : point - (point - other) = other := by
      apply Data.Gaussian.Basic.ext <;>
        simp only [Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im, -eq_self, -iff_self] <;> ring1
    rw [identity] at raw
    simpa only [otherNorm, pointNorm, distance] using raw
  have actualPartUpper : actualPart ≤
      1 + 2 * pointNorm + 2 * distance := by
    dsimp only [actualPart]
    calc
      1 + otherNorm ≤ 1 + 2 * (pointNorm + distance) := by
        calc
          1 + otherNorm = otherNorm + 1 := by ring1
          _ ≤ 2 * (pointNorm + distance) + 1 :=
            Fraction.Order.Arithmetic.add_le_add_right_direct
              otherNormUpper 1
          _ = 1 + 2 * (pointNorm + distance) := by ring1
      _ = 1 + 2 * pointNorm + 2 * distance := by ring1
  have cross : gapSq * actualPart ≤ distance * targetPart := by
    calc
      gapSq * actualPart ≤
          gapSq * (1 + 2 * pointNorm + 2 * distance) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          actualPartUpper gapSqNonnegative
      _ = gapSq * (1 + 2 * pointNorm) + 2 * gapSq * distance := by
        ring1
      _ ≤ distance * (1 + 2 * pointNorm) + 2 * distance * gapSq :=
        add_le_add
          (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
            gapSqLe
            (add_nonneg (by decide)
              (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
                pointNormNonnegative)))
          (le_of_eq (by ring1))
      _ = distance * targetPart := by
        dsimp only [targetPart]
        ring1
  have targetDenominatorPositive : 0 < common * targetPart :=
    Fraction.Order.Arithmetic.mul_pos_direct commonPositive targetPartPositive
  have actualDenominatorPositive : 0 < common * actualPart :=
    Fraction.Order.Arithmetic.mul_pos_direct commonPositive actualPartPositive
  have crossWithCommon : gapSq * (common * actualPart) ≤
      distance * (common * targetPart) := by
    calc
      gapSq * (common * actualPart) = common * (gapSq * actualPart) := by
        ring1
      _ ≤ common * (distance * targetPart) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct cross
          commonPositive.le
      _ = distance * (common * targetPart) := by ring1
  rw [Affine.chordalSq_affine]
  change gapSq / (common * targetPart) ≤
    distance / (common * actualPart)
  exact Fraction.Order.Field.div_le_div_of_cross targetDenominatorPositive
    actualDenominatorPositive crossWithCommon

/-! ## A point-independent gap from a uniform interior strip -/

/-- Squared-chordal gap shared by every in-box point carrying the displayed positive coordinate margin. The box norm
majorant removes the point from the numerical value of the bound. -/
def interiorStripChordalGap (box : Rational.Box)
  (radius : Fraction.Rational) : Fraction.Rational :=
  let radiusSq := radius ^ 2
  radiusSq /
    ((1 + box.normSqBound) *
      (1 + 2 * box.normSqBound + 2 * radiusSq))

/-- A positive strip radius gives a positive uniform squared-chordal gap for the box. -/
theorem interiorStripChordalGap_pos
    (box : Rational.Box) {radius : Fraction.Rational} (positive : 0 < radius) :
    0 < interiorStripChordalGap box radius := by
  have radiusSqPositive : 0 < radius ^ 2 :=
    Fraction.Order.Arithmetic.pow_pos_direct positive 2
  have firstPositive : 0 < 1 + box.normSqBound :=
    add_pos_of_pos_of_nonneg (by decide) box.normSqBound_nonneg
  have secondPositive : 0 <
      1 + 2 * box.normSqBound + 2 * radius ^ 2 :=
    add_pos_of_pos_of_nonneg
      (add_pos_of_pos_of_nonneg (by decide)
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
          box.normSqBound_nonneg))
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        (Fraction.Order.Arithmetic.sq_nonneg_direct radius))
  exact Fraction.Order.Field.div_pos_direct radiusSqPositive
    (Fraction.Order.Arithmetic.mul_pos_direct firstPositive secondPositive)

/-- A uniform positive coordinate strip gives a point-independent projective gap from all of its points to the whole
affine complement of the box. -/
theorem interiorStripChordalGap_le_affine_of_outside
    {box : Rational.Box} {point other : Data.Gaussian.Basic.Canonical} {radius : Fraction.Rational}
    (positive : 0 < radius)
    (contains : box.Contains point)
    (left : box.xLower + radius < point.re)
    (right : point.re + radius < box.xUpper)
    (bottom : box.yLower + radius < point.im)
    (top : point.im + radius < box.yUpper)
    (outside : ¬box.Contains other) :
    interiorStripChordalGap box radius ≤
      Chordal.Basic.chordalSq
        (Proj.affine point) (Proj.affine other) := by
  let radiusSq := radius ^ 2
  let distance := Data.Gaussian.Norm.Basic.normSq (point - other)
  let pointNorm := Data.Gaussian.Norm.Basic.normSq point
  let otherNorm := Data.Gaussian.Norm.Basic.normSq other
  let bound := box.normSqBound
  let targetCommon := 1 + bound
  let targetPart := 1 + 2 * bound + 2 * radiusSq
  let actualCommon := 1 + pointNorm
  let actualPart := 1 + otherNorm
  have radiusSqLe : radiusSq ≤ distance := by
    simpa only [radiusSq, distance] using
      Interior.interiorStripRadius_sq_le_normSq_sub_of_outside positive left
        right bottom top outside
  have radiusSqNonnegative : 0 ≤ radiusSq :=
    Fraction.Order.Arithmetic.sq_nonneg_direct radius
  have distanceNonnegative : 0 ≤ distance := Data.Gaussian.Norm.Basic.normSq_nonneg _
  have pointNormNonnegative : 0 ≤ pointNorm := Data.Gaussian.Norm.Basic.normSq_nonneg _
  have otherNormNonnegative : 0 ≤ otherNorm := Data.Gaussian.Norm.Basic.normSq_nonneg _
  have boundNonnegative : 0 ≤ bound := box.normSqBound_nonneg
  have pointNormLe : pointNorm ≤ bound := by
    simpa only [pointNorm, bound] using box.normSq_le_normSqBound contains
  have actualCommonLe : actualCommon ≤ targetCommon := by
    dsimp only [actualCommon, targetCommon]
    calc
      1 + pointNorm = pointNorm + 1 := by ring1
      _ ≤ bound + 1 :=
        Fraction.Order.Arithmetic.add_le_add_right_direct pointNormLe 1
      _ = 1 + bound := by ring1
  have targetCommonPositive : 0 < targetCommon :=
    add_pos_of_pos_of_nonneg (by decide) boundNonnegative
  have targetPartPositive : 0 < targetPart := by
    dsimp only [targetPart]
    exact add_pos_of_pos_of_nonneg
      (add_pos_of_pos_of_nonneg (by decide)
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
          boundNonnegative))
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        radiusSqNonnegative)
  have actualCommonPositive : 0 < actualCommon :=
    add_pos_of_pos_of_nonneg (by decide) pointNormNonnegative
  have actualPartPositive : 0 < actualPart :=
    add_pos_of_pos_of_nonneg (by decide) otherNormNonnegative
  have otherNormUpper : otherNorm ≤ 2 * (pointNorm + distance) := by
    have raw := Data.Gaussian.Norm.Bounds.normSq_sub_le_two point (point - other)
    have identity : point - (point - other) = other := by
      apply Data.Gaussian.Basic.ext <;>
        simp only [Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im, -eq_self, -iff_self] <;> ring1
    rw [identity] at raw
    simpa only [otherNorm, pointNorm, distance] using raw
  have actualPartUpper : actualPart ≤
      1 + 2 * bound + 2 * distance := by
    dsimp only [actualPart]
    calc
      1 + otherNorm ≤ 1 + 2 * (pointNorm + distance) := by
        calc
          1 + otherNorm = otherNorm + 1 := by ring1
          _ ≤ 2 * (pointNorm + distance) + 1 :=
            Fraction.Order.Arithmetic.add_le_add_right_direct otherNormUpper 1
          _ = 1 + 2 * (pointNorm + distance) := by ring1
      _ ≤ 1 + 2 * bound + 2 * distance := by
        have scaled :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            pointNormLe (show (0 : Fraction.Rational) ≤ 2 by decide)
        calc
          1 + 2 * (pointNorm + distance) =
              2 * pointNorm + (1 + 2 * distance) := by ring1
          _ ≤ 2 * bound + (1 + 2 * distance) :=
            Fraction.Order.Arithmetic.add_le_add_right_direct scaled
              (1 + 2 * distance)
          _ = 1 + 2 * bound + 2 * distance := by ring1
      _ = 1 + 2 * bound + 2 * distance := by ring1
  have cross :
      radiusSq * (actualCommon * actualPart) ≤
        distance * (targetCommon * targetPart) := by
    calc
      radiusSq * (actualCommon * actualPart) ≤
          radiusSq *
            (targetCommon * (1 + 2 * bound + 2 * distance)) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Fraction.Order.Arithmetic.mul_le_mul_direct actualCommonLe
            actualPartUpper actualPartPositive.le targetCommonPositive.le)
          radiusSqNonnegative
      _ = targetCommon *
          (radiusSq * (1 + 2 * bound) + 2 * radiusSq * distance) := by
        ring1
      _ ≤ targetCommon *
          (distance * (1 + 2 * bound) + 2 * distance * radiusSq) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (add_le_add
            (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
              radiusSqLe
              (add_nonneg (by decide)
                (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
                  boundNonnegative)))
            (le_of_eq (by ring1)))
          targetCommonPositive.le
      _ = distance * (targetCommon * targetPart) := by
        dsimp only [targetPart]
        ring1
  have targetDenominatorPositive : 0 < targetCommon * targetPart :=
    Fraction.Order.Arithmetic.mul_pos_direct targetCommonPositive
      targetPartPositive
  have actualDenominatorPositive : 0 < actualCommon * actualPart :=
    Fraction.Order.Arithmetic.mul_pos_direct actualCommonPositive
      actualPartPositive
  rw [Affine.chordalSq_affine]
  change radiusSq / (targetCommon * targetPart) ≤
    distance / (actualCommon * actualPart)
  exact Fraction.Order.Field.div_le_div_of_cross targetDenominatorPositive
    actualDenominatorPositive cross
end Purelib.Geometry.Projective.Chordal.Box.Interior

end
