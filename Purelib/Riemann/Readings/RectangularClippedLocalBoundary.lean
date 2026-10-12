module
import Purelib.Data.List.Map
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Topology.Polygon.Stokes

import Purelib.Geometry.Rectangle.Partition.PreparedBoxTriangulation
import Purelib.Geometry.Rectangle.Partition.RectangularMeshRefinement
public import Purelib.Riemann.Meshes.RectangularObservationMesh
public import Purelib.Geometry.Rectangle.Partition.PreparedBoxBoundary
import Purelib.Topology.Mesh.CoordinateTriangulation
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Data.Gaussian.Basic

open Purelib.Riemann

public section

/-!
# Owner-indexed boundaries on a clipped observation mesh

The retained owner of every clipped box supplies its original primitive values
throughout its ordered triangle descendants and finite boundary readback.
-/
section

open Purelib.Data.List
open Purelib.Riemann.Normalization.InverseRootPolynomial (Box Gaussian)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Riemann.Integration.RectangularOwnedTriangulation (ModelTriangle OwnedTriangulation)
open Purelib.Riemann.Meshes.RectangularObservationMesh (ObservationPieces ObservationMesh)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts)
open Purelib.Geometry.Rectangle.Partition.RectangularMeshRefinement.ModelTriangle (fromBoxes lowerBox upperBox)
open Purelib.Geometry.Rectangle.Partition.PreparedBoxBoundary (coordinateWedge sumCoordinateWedges rectangleBoundary)

variable {columns rows : Nat} {geometry : Geometry columns rows}

namespace Purelib.Riemann.Readings.RectangularClippedLocalBoundary

open Purelib.Geometry.Rectangle.Partition in
/-- Sum coordinate wedges using each original model triangle's own rectangular owner.

The ordered triangle list retains its exact column and row indices, so local primitive values are read from that
original model cell. -/
@[expose] def localWedges (values : Fin (columns + 1) → Fin (rows + 1) → Gaussian → PrimitivePoint) :
    List (ModelTriangle geometry) → Gaussian
  | [] => 0
  | triangle :: rest => PreparedBoxBoundary.coordinateWedge (values triangle.column triangle.row) triangle.triangle +
    localWedges values rest

/-- The owner-indexed local wedge sum preserves concatenation of the original triangle lists.

The head wedge remains fixed while scalar addition transports the tail
concatenation equation; no triangle owners or ordering change. -/
theorem localWedges_append (values : Fin (columns + 1) → Fin (rows + 1) → Gaussian → PrimitivePoint)
    (first last : List (ModelTriangle geometry)) :
    localWedges values (first ++ last) = localWedges values first + localWedges values last := by
  induction first with
  | nil => exact (zero_add (localWedges values last)).symm
  | cons triangle rest ih =>
      change coordinateWedge (values triangle.column triangle.row) triangle.triangle + localWedges values (rest ++ last)
        =
        (coordinateWedge (values triangle.column triangle.row) triangle.triangle + localWedges values rest) +
          localWedges values last
      rewrite [ih, add_assoc]
      exact Eq.refl _

open Purelib.Geometry.Rectangle.Partition in
/-- Local wedges of the original cell's refined boxes equal their coordinate-wedge sum.

Each original box contributes its two retained owner-indexed triangles.
Structural induction compares the same two head wedges and remaining boxes. -/
theorem localWedges_fromBoxes
    (values : Fin (columns + 1) → Fin (rows + 1) → Gaussian → PrimitivePoint)
    (column : Fin (columns + 1)) (row : Fin (rows + 1)) (boxes : List Box)
    (refines : ∀ box, box ∈ boxes → box.Refines (geometry.box column row)) :
    localWedges values (RectangularMeshRefinement.ModelTriangle.fromBoxes geometry column row boxes refines) =
      PreparedBoxBoundary.sumCoordinateWedges (values column row) (PreparedBoxTriangulation.boxTriangles boxes) := by
  induction boxes with
  | nil => rfl
  | cons box rest ih =>
      change _ + (_ + localWedges values (RectangularMeshRefinement.ModelTriangle.fromBoxes geometry column row rest _))
        = _
      rewrite [ih]
      exact Eq.refl _

open Purelib.Algebra in
open Purelib.Geometry.Rectangle.Partition in
/-- The recursive local wedge sum equals the finite sum at the original bounded triangle indices.

The finite sum visits the original bounded triangle positions. Its length
transport uses the exact map-length certificate and retains those same indices. -/
theorem localWedges_eq_sumFin
    (values : Fin (columns + 1) → Fin (rows + 1) → Gaussian → PrimitivePoint)
    (triangles : List (ModelTriangle geometry)) :
    localWedges values triangles = FiniteSum.Fin.sumFin
      (fun index : Fin (triangles.map ModelTriangle.triangle).length =>
        let source := triangles[index.val]'(by exact (Map.length_map ModelTriangle.triangle triangles) ▸ index.isLt)
        PreparedBoxBoundary.coordinateWedge (values source.column source.row) source.triangle) := by
  induction triangles with
  | nil => rfl
  | cons triangle rest ih =>
      simp only [List.map_cons, List.length_cons]
      rw [FiniteSum.Fin.sumFin_succ]
      change PreparedBoxBoundary.coordinateWedge (values triangle.column triangle.row) triangle.triangle + localWedges
        values rest =
        PreparedBoxBoundary.coordinateWedge (values triangle.column triangle.row) triangle.triangle + _
      rw [ih]
      rfl

end Purelib.Riemann.Readings.RectangularClippedLocalBoundary

namespace Purelib.Riemann.Readings.RectangularClippedLocalBoundary.OwnedTriangulation

open Purelib.Algebra in
open Purelib.Topology.Polygon in
/-- The original owned triangulation reads local wedges through its exact mesh coordinates and face sources.

The retained face-source and coordinate equations identify the same original
triangle at each bounded position before comparing its three primitive values. -/
theorem localWedges_eq_indexed {triangles : List (ModelTriangle geometry)}
    (surface : OwnedTriangulation triangles)
    (values : Fin (columns + 1) → Fin (rows + 1) → Gaussian → PrimitivePoint) :
    localWedges values triangles = FiniteSum.Fin.sumFin
      (fun face : Fin (triangles.map ModelTriangle.triangle).length =>
        let triangle := surface.mesh.triangulation.faces face
        let source := surface.faceSource face
        Stokes.triangleWedgeArea
          (values source.column source.row (surface.mesh.coordinate triangle.first))
          (values source.column source.row (surface.mesh.coordinate triangle.second))
          (values source.column source.row (surface.mesh.coordinate triangle.third))) := by
  rw [localWedges_eq_sumFin]
  apply FiniteSum.Fin.sumFin_congr
  intro face
  have coordinates := surface.mesh.face_coordinates face
  dsimp only
  rewrite [coordinates.1, coordinates.2.1, coordinates.2.2,
    Map.getElem_map ModelTriangle.triangle triangles face.val
      ((Map.length_map ModelTriangle.triangle triangles) ▸ face.isLt) face.isLt]
  exact Eq.refl _

end Purelib.Riemann.Readings.RectangularClippedLocalBoundary.OwnedTriangulation

section

open Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationPieces

open Purelib.Geometry.Rectangle.Partition

namespace Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationPieces

/-- Sum each original observation box's boundary using its retained model-cell owner. -/
@[expose] def localBoundary (values : Fin
  (columns + 1) → Fin (rows + 1) → Gaussian → PrimitivePoint)
    (depth : Nat) : {boxes : List Box} → ObservationPieces geometry boxes → Gaussian
  | _, .nil => 0
  | box :: _, .cons column row _ tail =>
      PreparedBoxBoundary.rectangleBoundary (values column row) depth box + tail.localBoundary values depth

/-- The original observation triangles' local wedge sum equals the retained sum of box boundaries.

The exact observation-piece owners and subdivision depth identify each refined box boundary and its original primitive
values. -/
theorem localWedges_eq_boundary {boxes : List
  Box} (pieces : ObservationPieces geometry boxes)
    (values : Fin (columns + 1) → Fin (rows + 1) → Gaussian → PrimitivePoint) (depth : Nat) :
    Readings.RectangularClippedLocalBoundary.localWedges values (pieces.triangles depth) =
      pieces.localBoundary values depth := by
  induction pieces with
  | nil => rfl
  | cons column row refines tail ih =>
      rw [triangles, Readings.RectangularClippedLocalBoundary.localWedges_append,
        Readings.RectangularClippedLocalBoundary.localWedges_fromBoxes,
        PreparedBoxBoundary.sumCoordinateWedges_boxTriangles,
        PreparedBoxBoundary.sumBoxBoundaries_cells, ih]
      rfl

end Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationPieces

end

section

open Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationMesh

variable {cuts : GridCuts geometry} {box : Box}

namespace Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationMesh

/-- The original observation triangles' local wedge sum equals the retained sum of box boundaries.

The exact observation-piece owners and subdivision depth identify each refined box boundary and its original primitive
values. -/
theorem localWedges_eq_boundary (mesh :
  ObservationMesh cuts box)
    (values : Fin (columns + 1) → Fin (rows + 1) → Gaussian → PrimitivePoint) :
    Readings.RectangularClippedLocalBoundary.localWedges values mesh.triangles =
      mesh.pieces.localBoundary values mesh.depth := by
  rw [mesh.triangles_eq]
  exact mesh.pieces.localWedges_eq_boundary values mesh.depth

end Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationMesh

end
end

end
