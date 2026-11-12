module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Scale
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Dimensions
import Purelib.Geometry.Rational.Box.Gaussian.Corners
import Purelib.Geometry.Rational.Box.Square.Centered
import Purelib.Integration.Energy.AffineTriangle

import Purelib.Geometry.Rectangle.Partition.PreparedBoxTriangulation
import Purelib.Topology.Mesh.CoordinateTriangulation
public import Purelib.Integration.Path.Dyadic.RadialTriangles
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Tactic.Ring
import Purelib.Data.List.Membership

open Purelib.Data.Rat.Fraction.Order

public section

/-!
# Finite radial fans of retained root-coordinate edges

These fans interpolate the actual sampled t coordinates. The containing
box is proved from their square-error norm bounds; no reciprocal-disk
membership is asserted for an approximate root or its square.
-/

namespace Purelib.Riemann.RootContinuation.RootRadialGeometry

open Purelib.Data.List

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rational (Box)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Gaussian.Scale (scale normSq_scale)
open Purelib.Integration.Energy.AffineTriangle (crossEnergy coordinateTriangleArea)
open Purelib.Geometry.Rational.Box.Gaussian.Corners (lowerLeft lowerRight upperRight upperLeft)
open Purelib.Geometry.Rectangle.Partition.PreparedBoxTriangulation (lowerTriangle upperTriangle boxTriangles)
open Purelib.Topology.Mesh.CoordinateTriangulation (CoordinateTriangle)
open Purelib.Integration.Path.Dyadic.RadialTriangles (unitBox)

open Purelib.Geometry in
/-- The Gaussian rational box centered at zero with half-width four. -/
@[expose] def domain : Box := Box.Square.Centered.BoxTransport.centeredBox 0 4 (by decide)

section
open Purelib.Data
/-- Interpolate linearly between the two retained Gaussian edge endpoints. -/
@[expose] def chord (first last : Gaussian.Basic.Canonical) (parameter : Rational) : Gaussian :=
  scale (1 - parameter) first + scale parameter last

/-- Scale the interpolated edge point by the parameter's real radial coordinate. -/
@[expose] def point (first last parameter : Gaussian.Basic.Canonical) : Gaussian :=
  scale parameter.re (chord first last parameter.im)

/-- Changing the chord parameter gives its difference times the endpoint displacement. -/
theorem chord_difference (first last : Gaussian.Basic.Canonical) (left right : Rational) :
    chord first last left - chord first last right = scale (left - right) (last - first) := by
  apply Gaussian.Basic.ext <;> simp only [chord, Gaussian.Basic.add_re, Gaussian.Basic.add_im, Gaussian.Basic.sub_re,
    Gaussian.Basic.sub_im,
    Gaussian.Scale.scale_re, Gaussian.Scale.scale_im] <;> ring1

/-- The square of a rational parameter between zero and one is at most one. -/
private theorem unit_square {parameter : Rational} (unit : 0 ≤ parameter ∧ parameter ≤ 1) : parameter ^ 2 ≤
  1 :=
  (Arithmetic.pow_le_pow_direct unit.1 unit.2 2).trans_eq (by decide)

/-- A chord between endpoints of quadrance at most two has quadrance at most eight. -/
theorem chord_norm {first last : Gaussian.Basic.Canonical} (firstBound : normSq first ≤ 2) (lastBound : normSq last ≤ 2)
    {parameter : Rational} (unit : 0 ≤ parameter ∧ parameter ≤ 1) : normSq (chord first last parameter) ≤ 8
      := by
  have complement : 0 ≤ 1 - parameter ∧ 1 - parameter ≤ 1 :=
    ⟨Arithmetic.sub_nonneg_direct unit.2,
      (Arithmetic.sub_le_sub_direct le_rfl unit.1).trans_eq (by ring1)⟩
  have scaled {value : Gaussian.Basic.Canonical} (bound : normSq value ≤ 2) {factor : Rational}
      (square : factor ^ 2 ≤ 1) : normSq (scale factor value) ≤ 2 := by
    rw [← Gaussian.Norm.Basic.normSq_eq_canonical, normSq_scale, Gaussian.Norm.Basic.normSq_eq_canonical]
    exact (Arithmetic.mul_le_mul_direct square bound (normSq_nonneg _) (by
      decide)).trans_eq (by ring1)
  have triangleBound := Gaussian.Norm.Bounds.normSq_add_le_two
    (scale (1 - parameter) first)
    (scale parameter last)
  simp only [Gaussian.Norm.Basic.normSq_eq_canonical] at triangleBound
  exact triangleBound.trans ((Arithmetic.mul_le_mul_of_nonneg_left_direct
    (add_le_add (scaled firstBound (unit_square complement)) (scaled lastBound (unit_square unit))) (by
      decide)).trans_eq (by decide))

end

open Purelib.Integration in
open Purelib.Data in
open Purelib.Geometry in
/-- The radial image of a unit-box parameter lies in the retained containing box.

Both sampled edge endpoints have quadrance at most two; the conclusion uses their finite norm bounds alone. -/
theorem point_inside {first last : Gaussian.Basic.Canonical} (firstBound : normSq first ≤ 2) (lastBound : normSq last ≤
  2)
    {parameter : Gaussian.Basic.Canonical} (unit : Path.Dyadic.RadialTriangles.unitBox.Contains parameter) :
      domain.Contains (point first last parameter) := by
  apply Box.Square.Centered.centeredBox_contains_of_normSq_sub_le (by decide : (0 : Rational) ≤ 4)
  rw [Gaussian.Basic.sub_zero, Gaussian.Norm.Basic.normSq_eq_canonical]
  have estimate : normSq (point first last parameter) ≤ 8 := by
    rw [point, ← Gaussian.Norm.Basic.normSq_eq_canonical, normSq_scale,
      Gaussian.Norm.Basic.normSq_eq_canonical]
    exact (Arithmetic.mul_le_mul_direct (unit_square ⟨unit.1, unit.2.1⟩)
      (chord_norm firstBound lastBound unit.2.2) (normSq_nonneg _) (by decide)).trans_eq (by
        ring1)
  exact estimate.trans (by decide : (8 : Rational) ≤ 4 ^ 2)

open Purelib.Integration in
open Purelib.Data in
/-- Radial interpolation multiplies squared parameter distance by at most sixteen.

The two parameters lie in the unit box and both retained edge endpoints have quadrance at most two. -/
theorem point_distance {first last : Gaussian.Basic.Canonical} (firstBound : normSq first ≤ 2) (lastBound : normSq last
  ≤ 2)
    (left right : Gaussian.Basic.Canonical) (leftUnit : Path.Dyadic.RadialTriangles.unitBox.Contains left)
    (rightUnit : Path.Dyadic.RadialTriangles.unitBox.Contains right) :
    normSq (point first last left - point first last right) ≤ 16 * normSq (left - right) := by
  have edgeBound := Gaussian.Norm.Bounds.normSq_sub_le_two last first
  simp only [Gaussian.Norm.Basic.normSq_eq_canonical] at edgeBound
  have edge : normSq (last - first) ≤ 8 := edgeBound.trans
    ((Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add lastBound firstBound) (by
      decide)).trans_eq (by decide))
  have horizontal : normSq (scale (left.re - right.re) (chord first last left.im)) ≤ (left.re - right.re)
    ^ 2 * 8 := by
    rw [← Gaussian.Norm.Basic.normSq_eq_canonical, normSq_scale, Gaussian.Norm.Basic.normSq_eq_canonical]
    exact Arithmetic.mul_le_mul_of_nonneg_left_direct (chord_norm firstBound lastBound leftUnit.2.2)
      (Arithmetic.sq_nonneg_direct _)
  have vertical : normSq (scale right.re (chord first last left.im - chord first last right.im)) ≤
    (left.im - right.im) ^ 2 * 8 := by
    rw [← Gaussian.Norm.Basic.normSq_eq_canonical, normSq_scale, Gaussian.Norm.Basic.normSq_eq_canonical]
    have movement : normSq (chord first last left.im - chord first last right.im) ≤ (left.im - right.im) ^ 2 * 8 := by
      rw [chord_difference, ← Gaussian.Norm.Basic.normSq_eq_canonical, normSq_scale,
        Gaussian.Norm.Basic.normSq_eq_canonical]
      exact Arithmetic.mul_le_mul_of_nonneg_left_direct edge
        (Arithmetic.sq_nonneg_direct _)
    exact (Arithmetic.mul_le_mul_direct (unit_square ⟨rightUnit.1, rightUnit.2.1⟩)
      movement (normSq_nonneg _) (by decide)).trans_eq (by ring1)
  have difference : point first last left - point first last right =
      scale (left.re - right.re) (chord first last left.im) +
      scale right.re (chord first last left.im - chord first last right.im) := by
    apply Gaussian.Basic.ext <;> simp only [point, Gaussian.Basic.add_re, Gaussian.Basic.add_im, Gaussian.Basic.sub_re,
      Gaussian.Basic.sub_im,
      Gaussian.Scale.scale_re, Gaussian.Scale.scale_im] <;> ring1
  rw [difference]
  have triangleBound := Gaussian.Norm.Bounds.normSq_add_le_two
    (scale (left.re - right.re) (chord first last left.im))
    (scale right.re (chord first last left.im - chord first last right.im))
  simp only [Gaussian.Norm.Basic.normSq_eq_canonical] at triangleBound
  exact triangleBound.trans ((Arithmetic.mul_le_mul_of_nonneg_left_direct
    (add_le_add horizontal vertical) (by decide)).trans_eq (by
        simp only [normSq, Gaussian.Basic.sub_re, Gaussian.Basic.sub_im];
        ring1))

open Purelib.Topology in
open Purelib.Data in
/-- Map a coordinate triangle's three retained parameters into the radial fan. -/
@[expose] def triangle (first last : Gaussian.Basic.Canonical) (parameters :
  CoordinateTriangle) : CoordinateTriangle :=
  ⟨point first last parameters.first, point first last parameters.second, point first last parameters.third⟩

open Purelib.Integration
open Purelib.Data
open Purelib.Geometry
/-- The lower mapped box triangle has the exact upper-radius weighted cross-energy area. -/
theorem lower_area (first last : Gaussian.Basic.Canonical) (box : Box) :
    Rectangle.Partition.PreparedBoxTriangulation.coordinateArea (triangle first last
      (lowerTriangle box)) =
      box.xUpper * box.widthX * box.widthY * crossEnergy first last := by
  unfold Rectangle.Partition.PreparedBoxTriangulation.coordinateArea triangle
    lowerTriangle point chord coordinateTriangleArea
    crossEnergy
    lowerLeft lowerRight
      upperRight Gaussian.Components.Basic.point Box.widthX
      Box.widthY
  simp only [Gaussian.Scale.scale_re, Gaussian.Scale.scale_im, Gaussian.Basic.add_re, Gaussian.Basic.add_im,
    Gaussian.Basic.conj, Gaussian.Basic.mul_im, Rat.Fraction.Field.div_eq_mul_inv_direct]
  ring1

/-- The upper mapped box triangle has the exact lower-radius weighted cross-energy area. -/
theorem upper_area (first last : Gaussian.Basic.Canonical) (box : Box) :
    Rectangle.Partition.PreparedBoxTriangulation.coordinateArea (triangle first last
      (upperTriangle box)) =
      box.xLower * box.widthX * box.widthY * crossEnergy first last := by
  unfold Rectangle.Partition.PreparedBoxTriangulation.coordinateArea triangle
    upperTriangle point chord coordinateTriangleArea
    crossEnergy
    lowerLeft upperRight
      upperLeft Gaussian.Components.Basic.point Box.widthX
      Box.widthY
  simp only [Gaussian.Scale.scale_re, Gaussian.Scale.scale_im, Gaussian.Basic.add_re, Gaussian.Basic.add_im,
    Gaussian.Basic.conj, Gaussian.Basic.mul_im, Rat.Fraction.Field.div_eq_mul_inv_direct]
  ring1

/-- Every radial fan triangle has nonnegative area for an oriented endpoint pair.

Each retained parameter box refines the unit box, so its radial coordinates and widths are nonnegative; the endpoint
cross energy is also nonnegative. -/
theorem triangles_nonnegative (first last : Gaussian.Basic.Canonical) (oriented : 0 ≤ crossEnergy
  first last)
    (boxes : List Box) (within : ∀ box ∈ boxes, box.Refines
      unitBox) :
    ∀ parameters ∈ boxTriangles boxes, 0 ≤
      Rectangle.Partition.PreparedBoxTriangulation.coordinateArea (triangle first last parameters) := by
  induction boxes with
  | nil => intro parameters member; exact (List.not_mem_nil member).elim
  | cons box boxes ih =>
      intro parameters member
      have radial : 0 ≤ box.xLower := (within box List.mem_cons_self).1
      have scaled {radius : Rational} (positive : 0 ≤ radius) :
          0 ≤ radius * box.widthX * box.widthY * crossEnergy first last :=
        Arithmetic.mul_nonneg_direct (Arithmetic.mul_nonneg_direct
          (Arithmetic.mul_nonneg_direct positive box.widthX_nonneg) box.widthY_nonneg) oriented
      rcases Membership.mem_cons.mp member with rfl | member
      · rw [lower_area]; exact scaled (radial.trans box.x_valid)
      · rcases Membership.mem_cons.mp member with rfl | member
        · rw [upper_area]; exact scaled radial
        · exact ih (fun other member => within other (List.mem_cons_of_mem box member)) parameters member

end Purelib.Riemann.RootContinuation.RootRadialGeometry
