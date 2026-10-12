module
public import Purelib.Geometry.Plane.Medians
import Purelib.Algebra.Field.Ratio
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Point.Affine
import Purelib.Geometry.Plane.Point.Basic
public import Purelib.Geometry.Plane.Point.Quadrance
import Purelib.Geometry.Triangles.Median.Quadrance
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra.Field

open Purelib.Geometry

open Purelib.Geometry.Plane.Point

section
@[expose] public section

/-!
# Divine Proportions, Chapter 10 further exercises

This module contains the equilateral centroid calculations, the unit-
quadrance existence criterion, and the corrected right-altitude formulas.
-/

namespace Purelib.Geometry.Triangles.Equilateral.Centroid

variable {K : Type*} [ExplicitField K]

/-- An equilateral triangle's vertex-to-centroid, centroid-to-midpoint and median quadrances are respectively one third,
one twelfth and three quarters of the common side quadrance.

Two and three are nonzero, allowing all displayed denominator cancellations. -/
theorem quadrance_ratios
    (first second third : Geometry.Plane.Point K) (q : K)
    (twoNonzero : (2 : K) ≠ 0) (threeNonzero : (3 : K) ≠ 0)
    (firstQuadrance : Quadrance.quadrance second third = q)
    (secondQuadrance : Quadrance.quadrance first third = q)
    (thirdQuadrance : Quadrance.quadrance first second = q) :
    Quadrance.quadrance third (Geometry.centroidPoint first second third) = q / 3 ∧
      Quadrance.quadrance (Geometry.centroidPoint first second third)
          (Affine.midpoint first second) = q / 12 ∧
      Quadrance.quadrance third (Affine.midpoint first second) = 3 * q / 4 := by
  have fourNonzero : (4 : K) ≠ 0 := by
    have squareNonzero :=
      ExplicitField.mul_ne_zero twoNonzero twoNonzero
    simpa only [show (4 : K) = 2 * 2 by ring1] using squareNonzero
  have nineNonzero : (9 : K) ≠ 0 := by
    have squareNonzero :=
      ExplicitField.mul_ne_zero threeNonzero threeNonzero
    simpa only [show (9 : K) = 3 * 3 by ring1] using squareNonzero
  have twelveNonzero : (12 : K) ≠ 0 := by
    simpa only [show (12 : K) = 4 * 3 by ring1] using
      ExplicitField.mul_ne_zero fourNonzero threeNonzero
  let medianQuadrance := Quadrance.quadrance third (Affine.midpoint first second)
  have medianCleared : medianQuadrance * 4 = 3 * q := by
    have cleared := Triangles.Median.Quadrance.median_quadrance_cleared first second third twoNonzero
    change Quadrance.quadrance (Affine.midpoint first second) third * 4 =
      2 * Quadrance.quadrance first third + 2 * Quadrance.quadrance second third -
        Quadrance.quadrance first second at cleared
    calc
      medianQuadrance * 4 =
          Quadrance.quadrance (Affine.midpoint first second) third * 4 := by
        unfold medianQuadrance
        rw [Quadrance.quadrance_symm third (Affine.midpoint first second)]
      _ = 2 * Quadrance.quadrance first third + 2 * Quadrance.quadrance second third -
          Quadrance.quadrance first second := cleared
      _ = 3 * q := by
        rw [firstQuadrance, secondQuadrance, thirdQuadrance]
        ring1
  have medianValue : medianQuadrance = 3 * q / 4 := by
    apply ExplicitField.eq_of_mul_eq_mul_right fourNonzero
    calc
      medianQuadrance * 4 = 3 * q := medianCleared
      _ = (3 * q / 4) * 4 :=
        (ExplicitField.div_mul_cancel (3 * q) fourNonzero).symm
  have centroidRatios := Triangles.Median.Quadrance.centroid_quadrance_ratios third first second twoNonzero
    threeNonzero
  rw [Geometry.centroidPoint_cyclic_right first second third] at centroidRatios
  have vertexCentroid :
      Quadrance.quadrance third (Geometry.centroidPoint first second third) = q / 3 := by
    calc
      Quadrance.quadrance third (Geometry.centroidPoint first second third) =
          4 * medianQuadrance / 9 := centroidRatios.1
      _ = q / 3 := by
        apply Ratio.ratio_eq_of_cross_product nineNonzero threeNonzero
        calc
          (4 * medianQuadrance) * 3 =
              3 * (medianQuadrance * 4) := by ring1
          _ = 3 * (3 * q) := by rw [medianCleared]
          _ = q * 9 := by ring1
  have centroidMidpoint :
      Quadrance.quadrance (Geometry.centroidPoint first second third)
          (Affine.midpoint first second) = q / 12 := by
    calc
      Quadrance.quadrance (Geometry.centroidPoint first second third)
          (Affine.midpoint first second) = medianQuadrance / 9 :=
        centroidRatios.2.1
      _ = q / 12 := by
        apply Ratio.ratio_eq_of_cross_product nineNonzero twelveNonzero
        calc
          medianQuadrance * 12 =
              (medianQuadrance * 4) * 3 := by ring1
          _ = (3 * q) * 3 := by rw [medianCleared]
          _ = q * 9 := by ring1
  exact ⟨vertexCentroid, centroidMidpoint, medianValue⟩
end Purelib.Geometry.Triangles.Equilateral.Centroid

end
