module
import Purelib.Data.List.Membership
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Scale
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Affine
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Boundary
import Purelib.Geometry.Rational.Box.Dimensions
import Purelib.Geometry.Rational.Box.Gaussian.Corners
import Purelib.Geometry.Rational.Box.Segment
import Purelib.Integration.Energy.AffineTriangle
public import Purelib.Polynomial.Dense.Gaussian.Reciprocal.Bounds

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedExteriorReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Geometry.Rectangle.Partition.PreparedBoxTriangulation
public import Purelib.Riemann.Paths.PreparedBoundarySegments
import Purelib.Topology.Mesh.CoordinateTriangulation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Orientation
public import Purelib.Integration.Path.Dyadic.RadialTriangles
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Tactic.Ring

open Purelib.Data.Rat.Fraction.Order

open Purelib

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Data.Gaussian

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Geometry.Rational

open Purelib.Geometry.Rational.Box

open Purelib.Geometry.Rational.Box.Gaussian

open Purelib.Geometry.Rectangle.Partition

open Purelib.Integration.Energy

open Purelib.Integration.Path.Dyadic

open Purelib.Polynomial.Dense.Gaussian

open Purelib.Riemann.Paths

open Purelib.Riemann.Topology

open Purelib.Topology.Mesh

public section

/-!
# Radial caps on actual inverted boundary sides

The outer parameter edge is the inverse of the original affine source
edge. It is not the chord between the inverse endpoints. All estimates are
finite rational calculations on the fixed ambient boundary.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches.Cuts (Ambient)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Gaussian.Scale (scale normSq_scale)
open Purelib.Integration.Energy.AffineTriangle (coordinateTriangleArea)
open Purelib.Geometry.Rational.Box.Gaussian.Corners (lowerLeft lowerRight upperRight upperLeft)
open Purelib.Geometry.Rectangle.Partition.PreparedBoxTriangulation (lowerTriangle upperTriangle boxTriangles)
open Purelib.Topology.Mesh.CoordinateTriangulation (CoordinateTriangle)
open Purelib.Riemann.Paths.PreparedBoundarySegments (SameSide)
open Purelib.Integration.Path.Dyadic.RadialTriangles (unitBox)

/-- The affine source point on the original oriented boundary side. -/
@[expose] def source (first last : Basic.Canonical) (parameter : Rational) : Gaussian :=
  first + scale parameter (last - first)

/-- The radial scaling of the inverse of the actual affine source point.

The imaginary parameter selects the source point before inversion; the real parameter scales its inverse toward zero. -/
@[expose] def point (first last parameter : Basic.Canonical) : Gaussian :=
  scale parameter.re (source first last
    parameter.im)⁻¹

/-- The source parameterization is the affine line from the first endpoint with the original side displacement. -/
theorem source_eq_line (first last : Basic.Canonical) (parameter : Rational) :
    source first last parameter = Affine.line first
      (last - first) parameter := by
  apply Basic.ext
  · simp only [-eq_self, -iff_self, source, Affine.line,
      Basic.add_re, Basic.mul_re, Scale.scale_re,
      Cast.ofCoordinate_re, Cast.ofCoordinate_im]; ring1
  · simp only [-eq_self, -iff_self, source, Affine.line,
      Basic.add_im, Basic.mul_im, Scale.scale_im,
      Cast.ofCoordinate_re, Cast.ofCoordinate_im]; ring1

/-- At radial parameter one, the cap point is exactly the inverse of the original source point. -/
theorem outer (first last : Basic.Canonical) (parameter : Rational) :
    point first last ⟨1, parameter⟩ =
      (source first last parameter)⁻¹ := by
  change scale 1 (source first last parameter)⁻¹ =
    _
  apply Basic.ext <;> simp only [-eq_self, -iff_self, Scale.scale_re, Scale.scale_im,
    Fraction.Field.one_mul] <;> rfl

/-- Interpolation between two points on the same box side remains on the box boundary for a unit parameter. -/
theorem source_boundary {box : Box} {first last : Basic.Canonical}
    (firstInside : box.Contains first) (lastInside : box.Contains last)
    (side : SameSide box first last) {parameter : Rational}
    (unit : 0 ≤ parameter ∧ parameter ≤ 1) : Boundary.OnBoxBoundary box
      (source first last parameter) := by
  have within := contains_line firstInside lastInside unit
  rw [← source_eq_line] at within
  refine ⟨within, ?_⟩
  have re_eq {value : Rational} (firstEq : first.re = value) (lastEq : last.re = value) :
      (source first last parameter).re = value := by
    simp only [-eq_self, -iff_self, source,
      Basic.add_re, Basic.sub_re, Scale.scale_re, firstEq, lastEq]
    ring1
  have im_eq {value : Rational} (firstEq : first.im = value) (lastEq : last.im = value) :
      (source first last parameter).im = value := by
    simp only [-eq_self, -iff_self, source,
      Basic.add_im, Basic.sub_im, Scale.scale_im, firstEq, lastEq]
    ring1
  rcases side with side | side | side | side
  · exact Or.inl (re_eq side.1 side.2)
  · exact Or.inr (Or.inl (re_eq side.1 side.2))
  · exact Or.inr (Or.inr (Or.inl (im_eq side.1 side.2)))
  · exact Or.inr (Or.inr (Or.inr (im_eq side.1 side.2)))

/-- The difference of two nonzero Gaussian inverses factors through their original displacement and both inverses. -/
private theorem inverse_difference {first last : Basic.Canonical} (firstNonzero : first ≠ 0) (lastNonzero
  : last ≠ 0) :
    first⁻¹ - last⁻¹ = (last - first) * first⁻¹ * last⁻¹ := by
  have firstCancel : first⁻¹ * first = 1 := by
    rw [Field.inv_eq]; exact Field.inv_mul first
      firstNonzero
  have lastCancel : last⁻¹ * last = 1 := by
    rw [Field.inv_eq]; exact Field.inv_mul last
      lastNonzero
  apply Field.mul_right_cancel_of_ne (Field.mul_ne_zero_direct firstNonzero lastNonzero)
  calc
    _ = (first⁻¹ * first) * last - (last⁻¹ * last) * first := by ring1
    _ = last - first := by rw [firstCancel, lastCancel]; ring1
    _ = (last - first) * (first⁻¹ * first) * (last⁻¹ * last) := by rw [firstCancel, lastCancel]; ring1
    _ = _ := by ring1

/-- The source displacement is the original side displacement scaled by the difference of parameters. -/
theorem source_difference (first last : Basic.Canonical) (left right : Rational) :
    source first last left -
      source first last right = scale (left -
      right) (last - first) := by
  apply Basic.ext
  · simp only [-eq_self, -iff_self, source,
      Basic.add_re, Basic.sub_re, Scale.scale_re]; ring1
  · simp only [-eq_self, -iff_self, source,
      Basic.add_im, Basic.sub_im, Scale.scale_im]; ring1

variable {genus : Nat} {curve : HyperellipticCurve genus} {first last :
  Basic.Canonical}

/-- The squared distance between inverse source points is at most eight times the squared parameter difference on the
ambient boundary. -/
theorem inverse_distance (firstInside : (Ambient curve).Contains first) (lastInside : (Ambient curve).Contains
  last)
    (side : SameSide (Ambient curve) first last) {left right : Rational}
    (leftUnit : 0 ≤ left ∧ left ≤ 1) (rightUnit : 0 ≤ right ∧ right ≤ 1) :
    Norm.Basic.normSq ((source
      first last left)⁻¹ - (source first last right)⁻¹)
      ≤ 8 * (left - right) ^ 2 := by
  have leftBoundary := source_boundary firstInside
    lastInside side leftUnit
  have rightBoundary := source_boundary firstInside
    lastInside side rightUnit
  have firstBoundary := source_boundary firstInside
    lastInside side (show (0 : Rational) ≤ 0 ∧ 0 ≤ 1 by decide)
  have lastBoundary := source_boundary firstInside
    lastInside side (show (0 : Rational) ≤ 1 ∧ 1 ≤ 1 by decide)
  have atZero : source first last 0 = first := by apply
    Basic.ext <;> simp only [-eq_self, -iff_self,
    source, Basic.add_re,
    Basic.add_im, Basic.sub_re, Basic.sub_im, Scale.scale_re, Scale.scale_im]
    <;> ring1
  have atOne : source first last 1 = last := by apply
    Basic.ext <;> simp only [-eq_self, -iff_self,
    source, Basic.add_re,
    Basic.add_im, Basic.sub_re, Basic.sub_im, Scale.scale_re, Scale.scale_im]
    <;> ring1
  rw [atZero] at firstBoundary
  rw [atOne] at lastBoundary
  have edgeBound : Norm.Basic.normSq (last - first) ≤ 8 * ReciprocalExteriorCollar.radius curve ^
    2 :=
    (Norm.Bounds.normSq_sub_le_two last first).trans
      ((Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Arithmetic.add_le_add_direct (ReciprocalExteriorCollar.boundary_norm_bounds curve lastBoundary).2
        (ReciprocalExteriorCollar.boundary_norm_bounds curve firstBoundary).2) (by decide)).trans_eq (by ring1))
  have leftDisk := ReciprocalExteriorCollar.inverse_inDisk curve leftBoundary
  have rightDisk := ReciprocalExteriorCollar.inverse_inDisk curve rightBoundary
  have leftWeighted : ReciprocalExteriorCollar.radius curve ^ 2 * Norm.Basic.normSq
    (source first last left)⁻¹ ≤ 1 := leftDisk
  have rightBound := Reciprocal.Bounds.disk_unit_bound rightDisk
  have product := Arithmetic.mul_le_mul_direct leftWeighted rightBound
    (Norm.Basic.normSq_nonneg _) (by decide)
  rw [Fraction.Field.one_mul] at product
  rw [inverse_difference
    (PreparedExteriorReciprocal.boundary_nonzero leftBoundary)
    (PreparedExteriorReciprocal.boundary_nonzero rightBoundary), Norm.Basic.normSq_mul,
      Norm.Basic.normSq_mul,
      source_difference, normSq_scale]
  have edgeScaled := Arithmetic.mul_le_mul_of_nonneg_left_direct edgeBound
    (Arithmetic.sq_nonneg_direct (right - left))
  have full := Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Arithmetic.mul_le_mul_of_nonneg_right_direct edgeScaled (Norm.Basic.normSq_nonneg
      (source first last left)⁻¹))
      (Norm.Basic.normSq_nonneg (source
        first last right)⁻¹)
  calc
    _ ≤ ((right - left) ^ 2 * (8 * ReciprocalExteriorCollar.radius curve ^ 2)) *
        Norm.Basic.normSq (source
          first last left)⁻¹ * Norm.Basic.normSq
          (source first last right)⁻¹ := full
    _ = (8 * (left - right) ^ 2) *
        ((ReciprocalExteriorCollar.radius curve ^ 2 * Norm.Basic.normSq
          (source first last left)⁻¹) *
          Norm.Basic.normSq
          (source first last right)⁻¹) := by ring1
    _ ≤ (8 * (left - right) ^ 2) * 1 := Arithmetic.mul_le_mul_of_nonneg_left_direct product
      (Arithmetic.mul_nonneg_direct (by decide) (Arithmetic.sq_nonneg_direct _))
    _ = _ := by ring1

/-- Every unit-square parameter maps into the retained reciprocal disk. -/
theorem point_inside (firstInside : (Ambient curve).Contains first) (lastInside : (Ambient curve).Contains
  last)
    (side : SameSide (Ambient curve) first last) {parameter :
      Basic.Canonical}
    (unit : RadialTriangles.unitBox.Contains parameter) :
    Reciprocal.Bounds.InDisk curve.polynomial (point
      first last parameter) := by
  have inside := ReciprocalExteriorCollar.inverse_inDisk curve
    (source_boundary firstInside lastInside side
    unit.2.2)
  have square : parameter.re ^ 2 ≤ 1 := (Arithmetic.pow_le_pow_direct unit.1 unit.2.1 2).trans_eq (by
    decide)
  have scaled := Arithmetic.mul_le_mul_of_nonneg_right_direct square
    (Norm.Basic.normSq_nonneg (source
    first last parameter.im)⁻¹)
  rw [Fraction.Field.one_mul] at scaled
  change ReciprocalExteriorCollar.radius curve ^ 2 * Norm.Basic.normSq
    (point first last parameter) ≤ 1
  rw [point, normSq_scale]
  exact (Arithmetic.mul_le_mul_of_nonneg_left_direct scaled (Arithmetic.sq_nonneg_direct
    _)).trans inside

/-- The radial inverse-side parameterization has squared-distance bound thirty-two on the unit square. -/
theorem point_distance (firstInside : (Ambient curve).Contains first) (lastInside : (Ambient curve).Contains
  last)
    (side : SameSide (Ambient curve) first last) (left right :
      Basic.Canonical)
    (leftUnit : RadialTriangles.unitBox.Contains left) (rightUnit : RadialTriangles.unitBox.Contains right) :
    Norm.Basic.normSq (point
      first last left - point first last right) ≤ 32 *
      Norm.Basic.normSq (left - right) := by
  have leftInverse := Reciprocal.Bounds.disk_unit_bound
    (ReciprocalExteriorCollar.inverse_inDisk curve
      (source_boundary firstInside lastInside side
      leftUnit.2.2))
  have rightSquare : right.re ^ 2 ≤ 1 :=
    (Arithmetic.pow_le_pow_direct rightUnit.1 rightUnit.2.1 2).trans_eq (by decide)
  have movement := inverse_distance firstInside
    lastInside side leftUnit.2.2 rightUnit.2.2
  have movementLarge : Norm.Basic.normSq
    ((source first last left.im)⁻¹ -
    (source first last right.im)⁻¹) ≤
      (left.im - right.im) ^ 2 * 16 := by
    exact movement.trans ((Arithmetic.mul_le_mul_of_nonneg_right_direct
      (by decide : (8 : Rational) ≤ 16) (Arithmetic.sq_nonneg_direct _)).trans_eq (by ring1))
  have horizontal : Norm.Basic.normSq (scale (left.re - right.re)
    (source first last left.im)⁻¹) ≤
      (left.re - right.re) ^ 2 * 16 := by
    rw [normSq_scale]
    exact Arithmetic.mul_le_mul_of_nonneg_left_direct
      (leftInverse.trans (by decide : (1 : Rational) ≤ 16)) (Arithmetic.sq_nonneg_direct _)
  have vertical : Norm.Basic.normSq (scale right.re
    ((source first last left.im)⁻¹ -
    (source first last right.im)⁻¹)) ≤
      (left.im - right.im) ^ 2 * 16 := by
    rw [normSq_scale]
    exact (Arithmetic.mul_le_mul_direct rightSquare movementLarge (Norm.Basic.normSq_nonneg
      _) (by decide)).trans_eq
      (Fraction.Field.one_mul _)
  have difference : point first last left -
    point first last right =
      scale (left.re - right.re) (source first
        last left.im)⁻¹ +
        scale right.re ((source first last
          left.im)⁻¹ - (source first last right.im)⁻¹)
          := by
    apply Basic.ext
    · simp only [-eq_self, -iff_self, point,
        Scale.scale_re, Basic.add_re, Basic.sub_re]; ring1
    · simp only [-eq_self, -iff_self, point,
        Scale.scale_im, Basic.add_im, Basic.sub_im]; ring1
  rw [difference]
  exact (Norm.Bounds.normSq_add_le_two _ _).trans
    ((Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Arithmetic.add_le_add_direct horizontal vertical) (by decide)).trans_eq
      (by simp only [-eq_self, -iff_self, Norm.Basic.normSq, Basic.sub_re,
        Basic.sub_im]; ring1))

/-- Map all three retained parameter vertices through the radial inverse-side parameterization. -/
@[expose] def triangle (first last : Basic.Canonical) (parameters :
  CoordinateTriangle) : CoordinateTriangle :=
  ⟨point first last parameters.first, point first last
    parameters.second, point first last
    parameters.third⟩

/-- The lower parameter triangle has the exact upper-radius weighted reciprocal arc area. -/
theorem lower_area (first last : Basic.Canonical) (box : Box) :
    PreparedBoxTriangulation.coordinateArea (triangle
      first last (lowerTriangle box)) =
      box.xUpper * box.widthX * coordinateTriangleArea 0
        (source first last box.yLower)⁻¹
          (source first last box.yUpper)⁻¹ := by
  unfold PreparedBoxTriangulation.coordinateArea
    triangle lowerTriangle
    point coordinateTriangleArea
    lowerLeft lowerRight upperRight Components.Basic.point widthX
  simp only [-eq_self, -iff_self, Scale.scale_re, Scale.scale_im, Basic.zero_re,
    Basic.zero_im, Fraction.Field.div_eq_mul_inv_direct]
  ring1

/-- The upper parameter triangle has the exact lower-radius weighted reciprocal arc area. -/
theorem upper_area (first last : Basic.Canonical) (box : Box) :
    PreparedBoxTriangulation.coordinateArea (triangle
      first last (upperTriangle box)) =
      box.xLower * box.widthX * coordinateTriangleArea 0
        (source first last box.yLower)⁻¹
          (source first last box.yUpper)⁻¹ := by
  unfold PreparedBoxTriangulation.coordinateArea
    triangle upperTriangle
    point coordinateTriangleArea
    lowerLeft upperRight upperLeft Components.Basic.point widthX
  simp only [-eq_self, -iff_self, Scale.scale_re, Scale.scale_im, Basic.zero_re,
    Basic.zero_im, Fraction.Field.div_eq_mul_inv_direct]
  ring1

/-- An ordered reciprocal source arc has nonnegative origin area when the original side has the opposite orientation. -/
theorem arc_area_nonnegative (first last : Basic.Canonical) (oriented : 0 ≤
  coordinateTriangleArea 0 last first)
    {left right : Rational} (ordered : left ≤ right) :
    0 ≤ coordinateTriangleArea 0 (source
      first last left)⁻¹ (source first last right)⁻¹ :=
      by
  have area : coordinateTriangleArea 0
    (source first last right)
    (source first last left) =
      (right - left) * coordinateTriangleArea 0 last first := by
    simp only [-eq_self, -iff_self, coordinateTriangleArea,
      source, Basic.add_re,
      Basic.add_im, Basic.sub_re, Basic.sub_im,
      Scale.scale_re, Scale.scale_im, Basic.zero_re, Basic.zero_im,
        Fraction.Field.div_eq_mul_inv_direct]
    ring1
  rw [PreparedEnergySurface.reciprocal_origin_area, area]
  exact Field.div_nonneg_direct
    (Arithmetic.mul_nonneg_direct (Arithmetic.sub_nonneg_direct ordered) oriented)
    (Arithmetic.mul_nonneg_direct (Norm.Basic.normSq_nonneg _)
      (Norm.Basic.normSq_nonneg _))

/-- Every retained parameter-box triangle has nonnegative radial image area under the original side orientation and
unit-box containment. -/
theorem triangles_nonnegative (first last : Basic.Canonical) (oriented : 0 ≤
  coordinateTriangleArea 0 last first)
    (boxes : List Box) (within : ∀ box ∈ boxes, box.Refines unitBox) :
    ∀ parameters ∈ boxTriangles boxes, 0 ≤ PreparedBoxTriangulation.coordinateArea
      (triangle first last parameters) := by
  induction boxes with
  | nil => intro parameters member; exact (List.not_mem_nil member).elim
  | cons box boxes ih =>
      intro parameters member
      have radial : 0 ≤ box.xLower := (within box List.mem_cons_self).1
      have arc := arc_area_nonnegative first last
        oriented box.y_valid
      rcases Purelib.Data.List.Membership.mem_cons.mp member with rfl | member
      · rw [lower_area]
        exact Arithmetic.mul_nonneg_direct
          (Arithmetic.mul_nonneg_direct (radial.trans box.x_valid) box.widthX_nonneg) arc
      · rcases Purelib.Data.List.Membership.mem_cons.mp member with rfl | member
        · rw [upper_area]
          exact Arithmetic.mul_nonneg_direct
            (Arithmetic.mul_nonneg_direct radial box.widthX_nonneg) arc
        · exact ih (fun other member => within other (List.mem_cons_of_mem box member)) parameters member

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry
