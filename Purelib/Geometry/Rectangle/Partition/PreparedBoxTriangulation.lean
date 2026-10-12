module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rational.Box.Content
import Purelib.Geometry.Rational.Box.Dimensions
public import Purelib.Geometry.Rational.Box.Gaussian.Corners
import Purelib.Integration.Energy.AffineTriangle

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
public import Purelib.Riemann.Topology.PreparedSurfacePartitions
import Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedObservationMesh
public import Purelib.Riemann.Topology.PreparedSurfaceCoercivity
public import Purelib.Topology.Mesh.CoordinateTriangulation
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Topology.Polygon.Stokes
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

open Purelib

open Purelib.Algebra

open Purelib.Data.Gaussian

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Geometry.Rational.Box

open Purelib.Geometry.Rational.Box.Gaussian

open Purelib.Geometry.Rectangle.Partition

open Purelib.Integration.Energy

open Purelib.Riemann.Topology

open Purelib.Riemann.Topology.PreparedSurfaceCoercivity

open Purelib.Topology.Mesh

open Purelib.Topology.Mesh.CoordinateTriangulation
open _root_.Purelib.Topology.Mesh renaming CoordinateTriangulation -> CoordinateTriangulation

public section

/-!
# Shared-edge triangulations of the actual observation refinements

Split each cached rectangle into two counterclockwise triangles, index equal
corner coordinates consistently, and cancel internal edges by a proved finite
algorithm.  The resulting incidence-certified triangulation retains exactly
the box partition's area and has positively oriented faces.

The uncancelled boundary is computed, not identified here with an A/B period
word.  Sheet-consistent primitive construction and that global identification
remain separate obligations.
-/

namespace Purelib.Geometry.Rectangle.Partition.PreparedBoxTriangulation

/-- Rational coordinates of the rectangle triangulation. -/
private abbrev Coordinate := Fraction.Rational
/-- Gaussian rational vertices of the triangulation. -/
private abbrev Gaussian := Data.Gaussian.Basic.Canonical
open _root_.Purelib.Topology.Mesh (CoordinateTriangulation)
open _root_.Purelib.Topology.Mesh.CoordinateTriangulation (CoordinateTriangle)
open Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions (Box Coordinate sumCells cells_refine cells_diagonalSq
  cells_proper)
open Purelib.Riemann.Topology.PreparedSurfacePartitions (BoxPartition)
open Purelib.Integration.Energy.AffineTriangle (coordinateTriangleArea)
open Purelib.Geometry.Rational.Box.Gaussian.Corners (lowerLeft lowerRight upperRight upperLeft)

open Purelib.LinearAlgebra
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

/-- The counterclockwise triangle below the lower-left to upper-right diagonal. -/
@[expose] def lowerTriangle (box : PreparedBoxPartitions.Box) : CoordinateTriangle :=
  ⟨lowerLeft box, Corners.lowerRight box, Corners.upperRight box⟩

/-- The counterclockwise triangle above the lower-left to upper-right diagonal. -/
@[expose] def upperTriangle (box : PreparedBoxPartitions.Box) : CoordinateTriangle :=
  ⟨lowerLeft box, Corners.upperRight box, Corners.upperLeft box⟩

/-- The oriented coordinate area of a triangle. -/
@[expose] def coordinateArea (triangle : CoordinateTriangulation.CoordinateTriangle) : Fraction.Rational :=
  AffineTriangle.coordinateTriangleArea triangle.first triangle.second triangle.third

/-- The lower triangle has half the rectangle area.

The original three rectangle corners define the lower counterclockwise triangle. Direct coordinate expansion identifies
its oriented area with half the same retained box content. -/
theorem lowerTriangle_area (box : PreparedBoxPartitions.Box) : coordinateArea
  (lowerTriangle box) =
    Content.boxContent box / 2 := by
  dsimp only [coordinateArea, lowerTriangle,
    AffineTriangle.coordinateTriangleArea, Corners.lowerLeft, Corners.lowerRight, Corners.upperRight,
    Content.boxContent, Rational.Box.widthX, Rational.Box.widthY,
      Components.Basic.point]
  apply congrArg (fun value : Fraction.Rational => value / 2)
  ring1

/-- The upper triangle has half the rectangle area.

The original three rectangle corners define the upper counterclockwise triangle. Direct coordinate expansion identifies
its oriented area with half the same retained box content. -/
theorem upperTriangle_area (box : PreparedBoxPartitions.Box) : coordinateArea
  (upperTriangle box) =
    Content.boxContent box / 2 := by
  dsimp only [coordinateArea, upperTriangle,
    AffineTriangle.coordinateTriangleArea, Corners.lowerLeft, Corners.upperRight, Corners.upperLeft,
    Content.boxContent, Rational.Box.widthX, Rational.Box.widthY,
      Components.Basic.point]
  apply congrArg (fun value : Fraction.Rational => value / 2)
  ring1

/-- Two positively oriented faces per actual rectangle leaf. -/
@[expose] def boxTriangles : List Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions.Box -> List
  Purelib.Topology.Mesh.CoordinateTriangulation.CoordinateTriangle
  | [] => []
  | box :: rest => lowerTriangle box ::
    upperTriangle box ::
    boxTriangles rest

/-- The triangle list has two faces for each input box. -/
theorem boxTriangles_length (boxes : List PreparedBoxPartitions.Box) :
  (boxTriangles boxes).length = 2 * boxes.length := by
  induction boxes with
  | nil => rfl
  | cons box rest inductionHypothesis =>
      simp only [boxTriangles, List.length_cons,
        inductionHypothesis]
      omega

open Purelib.Data.List in
/-- Proper input boxes give strictly positive oriented triangle areas.

Each original proper rectangle has positive content. Both retained corner triangles have half that content, and
structural membership identifies the exact triangle or passes the occurrence to the unchanged tail. -/
theorem boxTriangles_positive (boxes : List PreparedBoxPartitions.Box) (proper : forall box, box ∈ boxes -> box.Proper)
    {triangle : CoordinateTriangulation.CoordinateTriangle} (member : triangle ∈
      boxTriangles boxes) : 0 <
      coordinateArea triangle := by
  induction boxes with
  | nil => exact (List.not_mem_nil member).elim
  | cons box rest inductionHypothesis =>
      rcases Membership.mem_cons.mp member with equal | member
      · rw [equal, lowerTriangle_area]
        exact Fraction.Order.Field.div_pos_direct
          (Content.boxContent_pos_of_proper (proper box List.mem_cons_self)) (by decide)
      · rcases Membership.mem_cons.mp member with equal | member
        · rw [equal, upperTriangle_area]
          exact Fraction.Order.Field.div_pos_direct
            (Content.boxContent_pos_of_proper (proper box List.mem_cons_self)) (by decide)
        · exact inductionHypothesis (fun box member => proper box (List.mem_cons_of_mem _ member)) member

/-- Sum oriented areas along a finite triangle list. -/
@[expose] def sumTriangleAreas : List Purelib.Topology.Mesh.CoordinateTriangulation.CoordinateTriangle ->
  Purelib.Data.Rat.Fraction.Rational
  | [] => 0
  | triangle :: rest => coordinateArea triangle +
    sumTriangleAreas rest

/-- The structural triangle-area sum equals its finite-index sum. -/
theorem sumTriangleAreas_eq_sumFin (triangles : List CoordinateTriangulation.CoordinateTriangle) :
    sumTriangleAreas triangles = FiniteSum.Fin.sumFin (fun index :
      Fin triangles.length => coordinateArea triangles[index.val])
      := by
  induction triangles with
  | nil => rfl
  | cons triangle rest inductionHypothesis =>
      rw [FiniteSum.Fin.sumFin_succ]
      change coordinateArea triangle +
        sumTriangleAreas rest =
        coordinateArea triangle +
        FiniteSum.Fin.sumFin (fun index : Fin rest.length =>
          coordinateArea rest[index.val])
      rw [inductionHypothesis]

/-- Splitting boxes into two triangles preserves their total area. -/
theorem boxTriangles_areaSum (boxes : List PreparedBoxPartitions.Box) :
    sumTriangleAreas
      (boxTriangles boxes) = PreparedBoxPartitions.sumCells
      Content.boxContent boxes := by
  induction boxes with
  | nil => rfl
  | cons box rest inductionHypothesis =>
      rw [boxTriangles,
        sumTriangleAreas,
        sumTriangleAreas, inductionHypothesis,
        lowerTriangle_area,
          upperTriangle_area, PreparedBoxPartitions.sumCells]
      calc
        _ = (Content.boxContent box / 2) * 2 + PreparedBoxPartitions.sumCells Content.boxContent rest := by ring1
        _ = _ := by rw [Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)]

open Purelib.Data.List in
/-- Each triangle's three vertices lie in one actual input leaf box.

Structural membership identifies the original lower or upper triangle of a displayed box, or retains the exact
occurrence in the tail. The retained corner inequalities certify containment in that same input leaf. -/
private theorem triangle_in_leaf (boxes : List PreparedBoxPartitions.Box) {triangle :
  CoordinateTriangulation.CoordinateTriangle}
    (member : triangle ∈ boxTriangles boxes) :
    ∃ box ∈ boxes, box.Contains triangle.first ∧ box.Contains triangle.second ∧ box.Contains triangle.third := by
  induction boxes with
  | nil => cases member
  | cons box boxes ih =>
      rcases Membership.mem_cons.mp member with equal | member
      · subst triangle
        exact ⟨box, List.mem_cons_self ..,
          ⟨le_rfl, box.x_valid, le_rfl, box.y_valid⟩,
          ⟨box.x_valid, le_rfl, le_rfl, box.y_valid⟩,
          ⟨box.x_valid, le_rfl, box.y_valid, le_rfl⟩⟩
      · rcases Membership.mem_cons.mp member with equal | member
        · subst triangle
          exact ⟨box, List.mem_cons_self ..,
            ⟨le_rfl, box.x_valid, le_rfl, box.y_valid⟩,
            ⟨box.x_valid, le_rfl, box.y_valid, le_rfl⟩,
            ⟨le_rfl, box.x_valid, box.y_valid, le_rfl⟩⟩
        · obtain ⟨leaf, inLeaves, first, second, third⟩ := ih member
          exact ⟨leaf, List.mem_cons_of_mem _ inLeaves, first, second, third⟩

set_option genInjectivity false in
/-- Cache a coordinate-realized, incidence-certified triangulation of a specific geometric partition. The existing
partition is reused unchanged.

The original partition remains the source of every retained leaf triangle. The coordinate triangulation indexes exactly
that ordered list and retains its geometric and incidence certificates without substituting a new partition. -/
structure TriangulatedPartition (depth : Nat) where
  /-- The original cached box partition at the specified depth. -/ partition : PreparedSurfacePartitions.BoxPartition
    depth
  /-- A shared-index triangulation of exactly the triangles of the retained leaves. -/ mesh :
    Topology.Mesh.CoordinateTriangulation (boxTriangles
    partition.leaves)

constructive_injectivity TriangulatedPartition

namespace TriangulatedPartition

variable {depth : Nat}

/-- Construct and cache the coordinate-realized triangulation of an existing box partition. -/
@[expose] def build (partition : PreparedSurfacePartitions.BoxPartition depth) :
  TriangulatedPartition depth :=
  ⟨partition, CoordinateTriangulation.build (boxTriangles
    partition.leaves)⟩

/-- A depth-n partition has two times four to the n retained triangle faces. -/
theorem faceCount_eq (surface : TriangulatedPartition depth) :
    (boxTriangles surface.partition.leaves).length = 2 * 4 ^ depth
      := by
  rw [boxTriangles_length, surface.partition.length_eq]

/-- Every retained face lies in the parent box, and its two displacements from the first vertex obey the cached leaf
diagonal bound. -/
theorem face_geometry {depth : Nat} (mesh : TriangulatedPartition
  depth)
    (face : Fin (boxTriangles mesh.partition.leaves).length) :
    mesh.partition.parent.Contains (mesh.mesh.coordinate (mesh.mesh.triangulation.faces face).first) ∧
    mesh.partition.parent.Contains (mesh.mesh.coordinate (mesh.mesh.triangulation.faces face).second) ∧
    mesh.partition.parent.Contains (mesh.mesh.coordinate (mesh.mesh.triangulation.faces face).third) ∧
    Data.Gaussian.Norm.Basic.normSq (mesh.mesh.coordinate (mesh.mesh.triangulation.faces face).second -
      mesh.mesh.coordinate (mesh.mesh.triangulation.faces face).first) ≤ mesh.partition.leafDiagonalSq ∧
    Data.Gaussian.Norm.Basic.normSq (mesh.mesh.coordinate (mesh.mesh.triangulation.faces face).third -
      mesh.mesh.coordinate (mesh.mesh.triangulation.faces face).first) ≤ mesh.partition.leafDiagonalSq := by
  have coordinates := mesh.mesh.face_coordinates face
  rw [coordinates.1, coordinates.2.1, coordinates.2.2]
  obtain ⟨leaf, member, first, second, third⟩ := triangle_in_leaf
    mesh.partition.leaves (List.getElem_mem _)
  have refines : leaf.Refines mesh.partition.parent := by
    apply PreparedBoxPartitions.cells_refine depth mesh.partition.parent
    rw [← mesh.partition.leaves_eq]
    exact member
  have diameterEq : leaf.diagonalSq = mesh.partition.leafDiagonalSq := by
    rw [mesh.partition.leafDiagonalSq_eq]
    apply PreparedBoxPartitions.cells_diagonalSq depth mesh.partition.parent
    rw [← mesh.partition.leaves_eq]
    exact member
  exact ⟨refines.contains first, refines.contains second, refines.contains third,
    (Rational.Box.normSq_sub_le_diagonalSq second first).trans_eq diameterEq,
    (Rational.Box.normSq_sub_le_diagonalSq third first).trans_eq diameterEq⟩

/-- The indexed face area equals the coordinate triangle area in the retained list. -/
theorem faceArea_eq (surface : TriangulatedPartition depth)
    (index : Fin (boxTriangles surface.partition.leaves).length) :
    AffineTriangle.coordinateTriangleArea
        (surface.mesh.coordinate (surface.mesh.triangulation.faces index).first)
        (surface.mesh.coordinate (surface.mesh.triangulation.faces index).second)
        (surface.mesh.coordinate (surface.mesh.triangulation.faces index).third) =
      coordinateArea
        (boxTriangles surface.partition.leaves)[index.val] := by
  have coordinates := surface.mesh.face_coordinates index
  rw [coordinates.1, coordinates.2.1, coordinates.2.2]
  rfl

/-- Every face has strictly positive geometric orientation, not just a positive total which could hide folded or
negatively oriented triangles. -/
theorem faceArea_positive (surface : TriangulatedPartition depth)
    (proper : surface.partition.parent.Proper)
    (index : Fin (boxTriangles surface.partition.leaves).length) :
    0 < AffineTriangle.coordinateTriangleArea
        (surface.mesh.coordinate (surface.mesh.triangulation.faces index).first)
        (surface.mesh.coordinate (surface.mesh.triangulation.faces index).second)
        (surface.mesh.coordinate (surface.mesh.triangulation.faces index).third) := by
  rw [surface.faceArea_eq]
  apply boxTriangles_positive surface.partition.leaves ?_
    (List.getElem_mem _)
  intro box member
  apply PreparedBoxPartitions.cells_proper depth proper
  rw [<- surface.partition.leaves_eq]
  exact member

/-- Shared indexing and internal-edge cancellation preserve the exact area of the original observation rectangle at
every finite refinement. -/
theorem areaSum_eq (surface : TriangulatedPartition depth) :
    FiniteSum.Fin.sumFin (fun index => AffineTriangle.coordinateTriangleArea
        (surface.mesh.coordinate (surface.mesh.triangulation.faces index).first)
        (surface.mesh.coordinate (surface.mesh.triangulation.faces index).second)
        (surface.mesh.coordinate (surface.mesh.triangulation.faces index).third)) = surface.partition.area := by
  calc
    _ = FiniteSum.Fin.sumFin (fun index : Fin (boxTriangles
      surface.partition.leaves).length =>
        coordinateArea
          (boxTriangles surface.partition.leaves)[index.val]) :=
      FiniteSum.Fin.sumFin_congr surface.faceArea_eq
    _ = sumTriangleAreas
      (boxTriangles surface.partition.leaves) :=
      (sumTriangleAreas_eq_sumFin _).symm
    _ = PreparedBoxPartitions.sumCells Content.boxContent surface.partition.leaves :=
      boxTriangles_areaSum _
    _ = _ := surface.partition.totalArea_eq

/-- All geometric and incidence inputs to the error-controlled Stokes layer are now constructed. Primitive samples and
differential coefficients are separate finite analytic inputs; their local budgets are computed automatically. -/
@[expose] def affineSample (surface : TriangulatedPartition depth)
    (primitive : Fin surface.mesh.vertices.length -> Data.Gaussian.Basic.Canonical)
    (coefficient : Fin (boxTriangles
      surface.partition.leaves).length -> Data.Gaussian.Basic.Canonical)
    (radius : Fraction.Rational) (positive : 0 < radius) :
    PreparedSurfaceCoercivity.AffineSurfaceSample surface.mesh.vertices.length
      (boxTriangles surface.partition.leaves).length :=
  AffineSurfaceSample.ofVertices
    surface.mesh.triangulation surface.mesh.coordinate primitive coefficient radius positive

end TriangulatedPartition

end Purelib.Geometry.Rectangle.Partition.PreparedBoxTriangulation
