module
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Gaussian.Corners
import Purelib.Integration.Energy.Polygon

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Topology.Mesh.CoordinateTriangulation
import Purelib.Topology.Polygon.Stokes
public import Purelib.Geometry.Rectangle.Partition.PreparedBoxTriangulation
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Topology.PreparedSurfaceCoercivity
import Purelib.Riemann.Topology.PreparedSurfacePartitions
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

public section

/-!
# The geometric outer boundary of a refined observation rectangle

For arbitrary shared coordinate primitive values, the computed triangulation
boundary sum is exactly the sum on the four dyadically subdivided exterior
sides.  All rectangle-internal and diagonal contributions cancel by finite
algebra.  This is a local geometric identification, not yet an identification
with the global A/B period programs.
-/

namespace Purelib.Geometry.Rectangle.Partition.PreparedBoxBoundary

open Purelib

open Purelib.Algebra

open Purelib.Data.Gaussian

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Geometry.Rational.Box.Gaussian

open Purelib.Geometry.Rectangle.Partition

open Purelib.Integration.Energy

open Purelib.Topology.Mesh

open Purelib.Topology.Polygon

/-- The rational coordinate type of the rectangle boundary. -/
private abbrev Coordinate := Fraction.Rational
/-- Gaussian rational boundary values. -/
private abbrev Gaussian := Basic.Canonical
/-- An axis-aligned rational box with ordered endpoints. -/
private abbrev Box := Rational.Box
open Purelib.LinearAlgebra
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Geometry.Rational.Box.Gaussian.Corners (lowerLeft lowerRight upperLeft upperRight)
open Purelib.Integration.Energy.Polygon (energyPrimitivePoint)
open Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions (midpoint halfLower halfUpper cells child)
open Purelib.Geometry.Rectangle.Partition.PreparedBoxTriangulation (boxTriangles lowerTriangle upperTriangle
  TriangulatedPartition)
open Purelib.Topology.Mesh.CoordinateTriangulation (CoordinateTriangle)

/-- Left-to-right trapezoidal boundary contribution on a dyadic horizontal side. Only the displayed finite vertex values
are consumed. -/
@[expose] def horizontalBoundary (primitive : Canonical ->
  PrimitivePoint) :
    Nat -> Fraction.Rational -> Fraction.Rational ->
      Fraction.Rational -> Canonical
  | 0, lower, upper, height => Stokes.edgeArea (primitive ⟨lower, height⟩) (primitive ⟨upper,
    height⟩)
  | depth + 1, lower, upper, height =>
      PreparedBoxBoundary.horizontalBoundary primitive depth lower
        (midpoint lower upper) height +
        PreparedBoxBoundary.horizontalBoundary primitive depth
          (midpoint lower upper) upper height

/-- Bottom-to-top contribution on a dyadic vertical side. -/
@[expose] def verticalBoundary (primitive : Canonical ->
  PrimitivePoint) :
    Nat -> Fraction.Rational -> Fraction.Rational ->
      Fraction.Rational -> Canonical
  | 0, lower, upper, horizontal => Stokes.edgeArea (primitive ⟨horizontal, lower⟩) (primitive
    ⟨horizontal, upper⟩)
  | depth + 1, lower, upper, horizontal =>
      PreparedBoxBoundary.verticalBoundary primitive depth lower
        (midpoint lower upper) horizontal +
        PreparedBoxBoundary.verticalBoundary primitive depth
          (midpoint lower upper) upper horizontal

/-- Counterclockwise exterior boundary: bottom and right forwards, top and left backwards. Negative signs record the
latter two orientations. -/
@[expose] def rectangleBoundary (primitive : Canonical -> PrimitivePoint) (depth : Nat) (box
  : Rational.Box) : Canonical :=
  horizontalBoundary primitive depth box.xLower box.xUpper box.yLower +
    verticalBoundary primitive depth box.yLower box.yUpper box.xUpper -
    horizontalBoundary primitive depth box.xLower box.xUpper box.yUpper
      -
    verticalBoundary primitive depth box.yLower box.yUpper box.xLower

/-- The four children have precisely the subdivided exterior boundary; their four shared internal half-sides occur with
opposite signs.

The four retained child rectangles share the original midpoint coordinates.
Their internal half-side contributions cancel with opposite orientations;
the remaining contributions form the parent exterior at the next depth. -/
theorem rectangleBoundary_children (primitive : Canonical -> PrimitivePoint) (depth : Nat)
  (box : Rational.Box) :
    rectangleBoundary primitive depth (child box
      false false) +
      rectangleBoundary primitive depth (child
        box true false) +
      rectangleBoundary primitive depth (child
        box false true) +
      rectangleBoundary primitive depth (child
        box true true) =
        rectangleBoundary primitive (depth + 1) box := by
  dsimp only [rectangleBoundary, child,
    halfLower, halfUpper,
    horizontalBoundary, verticalBoundary]
  repeat rw [if_neg (by decide : (false : Bool) ≠ true)]
  repeat rw [if_pos (rfl : (true : Bool) = true)]
  ring1

/-- Sum the unsubdivided oriented boundary contributions of a finite box list. -/
@[expose] def sumBoxBoundaries (primitive : Canonical ->
  PrimitivePoint) : List Rational.Box ->
  Canonical
  | [] => 0
  | box :: rest => rectangleBoundary primitive 0 box +
    PreparedBoxBoundary.sumBoxBoundaries primitive rest

/-- Boundary summation is additive over concatenated box lists.

Structural recursion preserves the left list's ordered boundary readings.
The supplied right list remains the same tail in both sums. -/
theorem sumBoxBoundaries_append (primitive : Canonical -> PrimitivePoint) (left right : List
  Rational.Box) :
    sumBoxBoundaries primitive (left ++ right) =
      sumBoxBoundaries primitive left +
        sumBoxBoundaries primitive right := by
  induction left with
  | nil => exact (zero_add _).symm
  | cons box rest inductionHypothesis =>
      change rectangleBoundary primitive 0 box + sumBoxBoundaries primitive (rest ++ right) =
        (rectangleBoundary primitive 0 box + sumBoxBoundaries primitive rest) +
          sumBoxBoundaries primitive right
      rw [inductionHypothesis, add_assoc]

/-- Exact cancellation across every level of the actual finite quadtree.

Each depth retains the four-child traversal of the original box.
Additivity combines their boundary sums, and the shared interior sides cancel
while the exterior is subdivided to the same retained depth. -/
theorem sumBoxBoundaries_cells (primitive : Canonical -> PrimitivePoint) (depth : Nat) (box :
  Rational.Box) :
    sumBoxBoundaries primitive (cells depth box)
      = rectangleBoundary primitive depth box := by
  induction depth generalizing box with
  | zero => exact add_zero _
  | succ depth inductionHypothesis =>
      rw [cells, sumBoxBoundaries_append, sumBoxBoundaries_append,
        sumBoxBoundaries_append, inductionHypothesis, inductionHypothesis,
        inductionHypothesis, inductionHypothesis]
      exact rectangleBoundary_children primitive depth box

/-- The primitive wedge area of the three coordinate vertices of a triangle. -/
@[expose] def coordinateWedge (primitive : Canonical -> PrimitivePoint) (triangle :
  CoordinateTriangle) : Canonical :=
  Stokes.triangleWedgeArea (primitive triangle.first) (primitive triangle.second) (primitive triangle.third)

/-- The two face diagonals cancel, leaving the actual four sides. -/
theorem coordinateWedge_box (primitive : Canonical -> PrimitivePoint) (box :
  Rational.Box) :
    coordinateWedge primitive (lowerTriangle box) +
      coordinateWedge primitive (upperTriangle box) =
      rectangleBoundary primitive 0 box := by
  unfold coordinateWedge
  rw [<- Stokes.triangleBoundaryArea_eq_wedgeArea, <- Stokes.triangleBoundaryArea_eq_wedgeArea]
  change Stokes.edgeArea (primitive (lowerLeft box)) (primitive (lowerRight box)) +
      Stokes.edgeArea (primitive (lowerRight box)) (primitive (upperRight box)) +
      Stokes.edgeArea (primitive (upperRight box)) (primitive (lowerLeft box)) +
      (Stokes.edgeArea (primitive (lowerLeft box)) (primitive (upperRight box)) +
        Stokes.edgeArea (primitive (upperRight box)) (primitive (upperLeft box)) +
        Stokes.edgeArea (primitive (upperLeft box)) (primitive (lowerLeft box))) = _
  rw [Stokes.edgeArea_reverse (primitive (upperRight box)) (primitive (lowerLeft box)),
    Stokes.edgeArea_reverse (primitive (upperLeft box)) (primitive (upperRight box)),
    Stokes.edgeArea_reverse (primitive (lowerLeft box)) (primitive (upperLeft box))]
  unfold rectangleBoundary horizontalBoundary
    verticalBoundary lowerLeft lowerRight upperLeft upperRight
    Components.Basic.point
  ring1

/-- Sum primitive wedge areas over a finite coordinate triangle list. -/
@[expose] def sumCoordinateWedges (primitive : Canonical ->
  PrimitivePoint) : List
  CoordinateTriangle -> Canonical
  | [] => 0
  | triangle :: rest => coordinateWedge primitive triangle +
    PreparedBoxBoundary.sumCoordinateWedges primitive rest

/-- The structural wedge sum equals the sum over finite triangle indices. -/
theorem sumCoordinateWedges_eq_sumFin (primitive : Canonical -> PrimitivePoint) (triangles :
  List CoordinateTriangle) :
    sumCoordinateWedges primitive triangles =
      FiniteSum.Fin.sumFin (fun index : Fin triangles.length =>
        coordinateWedge primitive triangles[index.val]) := by
  induction triangles with
  | nil => rfl
  | cons triangle rest inductionHypothesis =>
      rw [FiniteSum.Fin.sumFin_succ]
      change coordinateWedge primitive triangle +
        sumCoordinateWedges primitive rest =
        coordinateWedge primitive triangle +
          FiniteSum.Fin.sumFin (fun index : Fin rest.length =>
            coordinateWedge primitive rest[index.val])
      rw [inductionHypothesis]

/-- The two triangles in each box sum to its four-sided oriented boundary contribution. -/
theorem sumCoordinateWedges_boxTriangles (primitive : Canonical -> PrimitivePoint) (boxes :
  List Rational.Box) :
    sumCoordinateWedges primitive
      (boxTriangles boxes) = sumBoxBoundaries
      primitive boxes := by
  induction boxes with
  | nil => rfl
  | cons box rest inductionHypothesis =>
      simp only [boxTriangles,
        sumCoordinateWedges, inductionHypothesis,
        sumBoxBoundaries]
      rw [<- add_assoc, coordinateWedge_box]

namespace TriangulatedPartition

/-- Exact geometric identification of the computed boundary *sum* with the four refined outer sides, for every shared
coordinate primitive assignment. This does not assert equality of the boundary lists or a global period word. -/
theorem boundaryArea_eq_rectangleBoundary {depth : Nat} (surface : TriangulatedPartition depth)
    (primitive : Canonical -> PrimitivePoint) :
    Stokes.edgeListArea (fun vertex => primitive (surface.mesh.coordinate vertex)) surface.mesh.triangulation.boundary =
      rectangleBoundary primitive depth surface.partition.parent := by
  rw [<- surface.mesh.wedgeSum_eq_boundaryArea]
  calc
    _ = FiniteSum.Fin.sumFin (fun index : Fin (boxTriangles surface.partition.leaves).length =>
        coordinateWedge primitive
          (boxTriangles surface.partition.leaves)[index.val]) := by
      apply FiniteSum.Fin.sumFin_congr
      intro index
      have coordinates := surface.mesh.face_coordinates index
      unfold coordinateWedge
      dsimp only
      rw [coordinates.1, coordinates.2.1, coordinates.2.2]
    _ = sumCoordinateWedges primitive
      (boxTriangles surface.partition.leaves) :=
      (sumCoordinateWedges_eq_sumFin _ _).symm
    _ = sumBoxBoundaries primitive surface.partition.leaves :=
      sumCoordinateWedges_boxTriangles _ _
    _ = rectangleBoundary primitive depth surface.partition.parent :=
      by
      rw [surface.partition.leaves_eq, sumBoxBoundaries_cells]

/-- The cached error-controlled energy sample uses that same geometric exterior boundary; no separate
boundary-identification witness is needed. -/
theorem affineSample_boundaryArea {depth : Nat} (surface : TriangulatedPartition depth)
    (primitive : Canonical -> Canonical)
    (coefficient : Fin (boxTriangles surface.partition.leaves).length ->
      Canonical)
    (radius : Fraction.Rational) (positive : 0 < radius) :
    (surface.affineSample (fun vertex => primitive (surface.mesh.coordinate vertex))
      coefficient radius positive).boundaryArea =
        rectangleBoundary (fun point => energyPrimitivePoint
          (primitive point)) depth surface.partition.parent :=
  boundaryArea_eq_rectangleBoundary surface
    (fun point => energyPrimitivePoint (primitive point))

/-- The computed affine energy, after paying all computed local errors, is bounded by the energy on the actual
subdivided outer sides. Establishing smallness of those errors for prepared integrals remains the analytic step. -/
theorem affineSample_energy_le_rectangleBoundary {depth : Nat} (surface : TriangulatedPartition
  depth)
    (primitive : Canonical -> Canonical)
    (coefficient : Fin (boxTriangles surface.partition.leaves).length ->
      Canonical)
    (radius : Fraction.Rational) (positive : 0 < radius) :
    let sample := surface.affineSample (fun vertex => primitive (surface.mesh.coordinate vertex))
      coefficient radius positive
    sample.affineEnergy - sample.errorBudget <=
      (rectangleBoundary (fun point => energyPrimitivePoint
        (primitive point)) depth surface.partition.parent).im / 4 := by
  have bounded := (surface.affineSample (fun vertex => primitive (surface.mesh.coordinate vertex))
    coefficient radius positive).affineEnergy_sub_errorBudget_le_boundaryEnergy
  rw [affineSample_boundaryArea
    surface primitive coefficient radius positive] at bounded
  exact bounded

end TriangulatedPartition

end Purelib.Geometry.Rectangle.Partition.PreparedBoxBoundary
