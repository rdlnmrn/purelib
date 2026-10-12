module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Membership
import Purelib.Data.List.Append
import Purelib.Data.Nat.Multiplication
import Purelib.Data.Gaussian.Basic
import Purelib.Data.List.Map
import Purelib.Geometry.Rational.Box.Content

import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxTriangulation
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Topology.Mesh.CoordinateTriangulation
public import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
public import Purelib.Geometry.Rectangle.Partition.RectangularMeshRefinement
import Init.Prelude
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Tactic.Ring

public section

/-!
# Coarse-model meshes containing a prescribed finite point bank

Every selected coarse rectangle is partitioned at the same requested
coordinate bank. The resulting triangles retain their original model owners;
no inverse-root or primitive polynomial is acquired or refined. The indexed
mesh therefore contains every requested point lying in a selected rectangle,
with no caller-supplied vertex index or successful lookup certificate.
-/

namespace Purelib.Geometry.Rectangle.Partition.RectangularCommonMesh

open Purelib

open Purelib.Data.List

open Purelib.Geometry.Rational.Box

open Purelib.Geometry.Rectangle.Partition

open Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts

open Purelib.Geometry.Rectangle.Partition.RectangularMeshRefinement

open Purelib.Riemann.Integration

open Purelib.Riemann.Integration.RectangularOwnedTriangulation

open Purelib.Riemann.Normalization

open Purelib.Topology.Mesh

namespace CoordinateTriangulation

open Purelib.Data.Gaussian.Basic (Canonical)
open _root_.Purelib.Topology.Mesh (CoordinateTriangulation)
open _root_.Purelib.Topology.Mesh.CoordinateTriangulation (CoordinateTriangle triangleVertices)

/-- A point in the triangle vertex list is a corner of an actual listed triangle.

Structural membership identifies one of the three original head corners or a corner in the unchanged triangle tail. The
retained triangle occurrence and its ordered corner alternatives refer to that exact original list. -/
private theorem vertex_occurrence {triangles : List CoordinateTriangulation.CoordinateTriangle} {point :
  Data.Gaussian.Basic.Canonical}
    (member : point ∈ CoordinateTriangulation.triangleVertices triangles) :
    ∃ triangle ∈ triangles, point = triangle.first ∨ point = triangle.second ∨ point = triangle.third := by
  induction triangles with
  | nil => cases member
  | cons first rest ih =>
      rcases Membership.mem_cons.mp member with firstEq | member
      · exact ⟨first, List.mem_cons_self, Or.inl firstEq⟩
      · rcases Membership.mem_cons.mp member with secondEq | member
        · exact ⟨first, List.mem_cons_self, Or.inr (Or.inl secondEq)⟩
        · rcases Membership.mem_cons.mp member with thirdEq | member
          · exact ⟨first, List.mem_cons_self, Or.inr (Or.inr thirdEq)⟩
          · obtain ⟨triangle, inRest, corner⟩ := ih member
            exact ⟨triangle, List.mem_cons_of_mem _ inRest, corner⟩

/-- Coordinate realization ensures that every geometric triangle corner is present even in an independently generated,
deduplicated vertex bank. -/
theorem contains_triangle_vertex {triangles : List CoordinateTriangulation.CoordinateTriangle} (mesh :
  Topology.Mesh.CoordinateTriangulation triangles)
    {point : Data.Gaussian.Basic.Canonical} (member : point ∈ CoordinateTriangulation.triangleVertices triangles) :
      point ∈ mesh.vertices := by
  obtain ⟨triangle, triangleMember, corner⟩ :=
    vertex_occurrence member
  obtain ⟨index, bound, equal⟩ := List.mem_iff_getElem.mp triangleMember
  have coordinates := mesh.face_coordinates ⟨index, bound⟩
  rw [equal] at coordinates
  rcases corner with rfl | rfl | rfl
  · rw [← coordinates.1]; exact List.getElem_mem _
  · rw [← coordinates.2.1]; exact List.getElem_mem _
  · rw [← coordinates.2.2]; exact List.getElem_mem _

end CoordinateTriangulation

namespace RectangularInverseModels

open Purelib.Riemann.Normalization.InverseRootPolynomial (Box Gaussian Coordinate)
open _root_.Purelib.Topology.Mesh (CoordinateTriangulation)
open _root_.Purelib.Topology.Mesh.CoordinateTriangulation (triangleVertices CoordinateTriangle VertexLookup
  lookupVertex)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Riemann.Integration.RectangularOwnedTriangulation (ModelTriangle OwnedTriangulation)
open Purelib.Riemann.Branches
open Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions (sumCells)
open Purelib.Geometry.Rectangle.Partition.PreparedBoxTriangulation (boxTriangles sumTriangleAreas)

variable {columns rows : Nat} {geometry : Purelib.Riemann.Normalization.RectangularInverseModels.Geometry columns rows}
  {points : List Purelib.Data.Gaussian.Basic.Canonical}

set_option genInjectivity false in
/-- All new geometry for one cell is retained separately from its fixed coarse inverse model. Generated triangulations
use the same readback law.

The coordinate-cut partition remains indexed by the original coarse-cell pair and requested points. Its retained
triangle list carries the exact two-triangle readback with the same containment witnesses. -/
structure CutCell (geometry : RectangularInverseModels.Geometry columns rows) (column : Fin (columns + 1)) (row : Fin
  (rows + 1))
    (points : List Data.Gaussian.Basic.Canonical) where
  /-- The coordinate-cut partition of the original coarse cell. -/ partition : CutPartition
    (geometry.box column row) points
  /-- The cached triangles retaining that coarse model owner. -/ triangles : List
    (RectangularOwnedTriangulation.ModelTriangle geometry)
  /-- The cache is the owned two-triangle construction on the partition boxes. -/ triangles_eq : triangles =
    ModelTriangle.fromBoxes geometry column row partition.boxes
    (fun _ member => partition.refines member)

constructive_injectivity CutCell

namespace CutCell

variable {column : Fin (columns + 1)} {row : Fin (rows + 1)}

/-- Build the coordinate-cut partition and owned triangles of one coarse cell. -/
@[expose] def build (geometry : RectangularInverseModels.Geometry columns rows) (column : Fin (columns + 1)) (row : Fin
  (rows + 1)) (points : List Data.Gaussian.Basic.Canonical) :
    CutCell geometry column row points :=
  let partition := CutPartition.build (geometry.box column row) (geometry.box_proper column row) points
  ⟨partition, ModelTriangle.fromBoxes geometry column row partition.boxes (fun _ member => partition.refines member),
    rfl⟩

/-- Forgetting coarse owners gives exactly the retained partition's coordinate triangles. -/
theorem coordinates (cell : CutCell geometry
  column row points) :
    cell.triangles.map ModelTriangle.triangle = PreparedBoxTriangulation.boxTriangles cell.partition.boxes := by
  rw [cell.triangles_eq]
  exact ModelTriangle.fromBoxes_coordinates ..

/-- The retained triangle count is twice the rectangle count. -/
theorem length_eq (cell : CutCell geometry
  column row points) : cell.triangles.length = 2 * cell.partition.count := by
  have equal := congrArg List.length cell.coordinates
  simpa only [Map.length_map, PreparedBoxTriangulation.boxTriangles_length, cell.partition.count_eq] using equal

/-- The retained triangle areas sum to the original coarse cell area. -/
theorem area_eq (cell : CutCell geometry
  column row points) :
    PreparedBoxTriangulation.sumTriangleAreas (cell.triangles.map ModelTriangle.triangle) = Content.boxContent
      (geometry.box column row) := by
  rw [cell.coordinates, PreparedBoxTriangulation.boxTriangles_areaSum]
  exact cell.partition.area_eq

/-- Every retained owned triangle has positive oriented coordinate area. -/
theorem positive (cell : CutCell geometry
  column row points) {triangle : RectangularOwnedTriangulation.ModelTriangle geometry}
    (member : triangle ∈ cell.triangles) : 0 < PreparedBoxTriangulation.coordinateArea triangle.triangle := by
  have inCoordinates : triangle.triangle ∈ cell.triangles.map ModelTriangle.triangle :=
    Map.mem_map.mpr ⟨triangle, member, rfl⟩
  rw [cell.coordinates] at inCoordinates
  exact PreparedBoxTriangulation.boxTriangles_positive _ (fun _ member => cell.partition.proper member) inCoordinates

/-- Every requested point in a selected coarse cell appears in the retained mesh geometry. -/
theorem point_mem (cell : CutCell geometry
  column row points) (point : Data.Gaussian.Basic.Canonical) (member : point ∈ points)
    (inside : (geometry.box column row).Contains point) : point ∈ CoordinateTriangulation.triangleVertices
      (cell.triangles.map ModelTriangle.triangle) := by
  rw [cell.coordinates]
  exact cell.partition.point_mem_vertices point member inside

end CutCell

set_option genInjectivity false in
/-- The spine preserves the selected coarse-cell order, including a possibly empty or disconnected selection. All
computations are cached.

Each head retains the original column, row and cut-cell cache. The dependent tail preserves the same selected-cell order
and repeated occurrences without equality tests on model owners. -/
inductive CutCells (geometry : RectangularInverseModels.Geometry columns rows) (points : List
  Data.Gaussian.Basic.Canonical) :
    List (Fin (columns + 1) × Fin (rows + 1)) → Type
  /-- The empty selected-cell cache. -/ | nil :
    CutCells geometry points []
  /-- Retain one cut cell followed by the cache for the remaining selection. -/ | cons {column : Fin (columns + 1)} {row
    : Fin (rows + 1)} {rest : List (Fin (columns + 1) × Fin (rows + 1))}
      (cell : CutCell geometry column row
        points) (tail : CutCells
        geometry points rest) :
      CutCells geometry points
        ((column, row) :: rest)

constructive_injectivity CutCells

namespace CutCells

/-- Build a cached cut cell for each selected coarse index pair, preserving order. -/
@[expose] def build (geometry : Purelib.Riemann.Normalization.RectangularInverseModels.Geometry columns rows) (points :
  List Purelib.Data.Gaussian.Basic.Canonical) :
    (selection : List (Fin (columns + 1) × Fin (rows + 1))) →
      CutCells geometry points
      selection
  | [] => .nil
  | (column, row) :: rest => .cons (.build geometry column row points)
    (build geometry points
    rest)

/-- Concatenate the cached owned triangle lists in selected-cell order. -/
@[expose] def triangles : {selection : List (Fin (columns + 1) × Fin (rows + 1))} →
  CutCells geometry points selection → List
  (RectangularOwnedTriangulation.ModelTriangle geometry)
  | _, .nil => []
  | _, .cons cell tail => cell.triangles ++ tail.triangles

/-- Sum the cached rectangle counts along the selected-cell spine. -/
@[expose] def rectangleCount : {selection : List (Fin (columns + 1) × Fin (rows + 1))} →
  CutCells geometry points selection → Nat
  | _, .nil => 0
  | _, .cons cell tail => cell.partition.count + tail.rectangleCount

variable {selection : List (Fin (columns + 1) × Fin (rows + 1))}

open Purelib.Geometry.Rectangle.Partition.RectangularCommonMesh.RectangularInverseModels.CutCells in
/-- The selected triangle list has twice the cached rectangle count.

Each retained cut cell contributes twice its original rectangle count. Structural concatenation adds those exact cached
list lengths without changing selected-cell order. -/
theorem length_eq (cells : CutCells geometry
  points selection) : cells.triangles.length = 2 * cells.rectangleCount := by
  induction cells with
  | nil => rfl
  | cons cell tail ih =>
      change (cell.triangles ++ tail.triangles).length = 2 * (cell.partition.count + tail.rectangleCount)
      rw [Append.length_append, cell.length_eq, ih, Nat.mul_add]

/-- The total rectangle count is bounded by selection length times the per-cell quadratic bound.

Each original cut-cell cache satisfies the same per-cell point bound. Natural scalar addition and distributivity compose
those retained bounds along the exact selection spine. -/
theorem count_le (cells : CutCells geometry
  points selection) :
    cells.rectangleCount ≤ selection.length * ((points.length + 1) * (points.length + 1)) := by
  induction cells with
  | nil => exact Nat.zero_le _
  | cons cell tail ih =>
      have bounded := Nat.add_le_add cell.partition.count_le ih
      simpa only [rectangleCount,
        List.length_cons, Data.Nat.Multiplication.right_distrib, Nat.one_mul, Nat.add_comm] using bounded

/-- Triangle-area summation is additive over concatenation. -/
private theorem areas_append (first last : List CoordinateTriangulation.CoordinateTriangle) :
    PreparedBoxTriangulation.sumTriangleAreas (first ++ last) = PreparedBoxTriangulation.sumTriangleAreas first +
      PreparedBoxTriangulation.sumTriangleAreas last := by
  induction first with
  | nil =>
    change PreparedBoxTriangulation.sumTriangleAreas last = 0 + PreparedBoxTriangulation.sumTriangleAreas last; ring1
  | cons first rest ih => simp only [List.cons_append, PreparedBoxTriangulation.sumTriangleAreas, ih]; ring1

open Purelib.Geometry.Rectangle.Partition.RectangularCommonMesh.RectangularInverseModels.CutCells in
/-- Exact area for the whole selected bank, counting the selection exactly as supplied. This makes no disjointness claim
for a repeated coarse cell.

Each retained cell contributes its exact original coarse-box content. Structural concatenation adds the same cached
triangle areas, including every repeated selected coarse-cell occurrence. -/
theorem area_eq (cells : CutCells geometry
  points selection) :
    PreparedBoxTriangulation.sumTriangleAreas (cells.triangles.map ModelTriangle.triangle) =
      PreparedBoxPartitions.sumCells Content.boxContent (selection.map fun cell => geometry.box cell.1 cell.2) := by
  induction cells with
  | nil => rfl
  | cons cell tail ih =>
      change PreparedBoxTriangulation.sumTriangleAreas ((cell.triangles ++ tail.triangles).map ModelTriangle.triangle) =
        Content.boxContent (geometry.box _ _) + PreparedBoxPartitions.sumCells Content.boxContent _
      rw [Map.map_append, areas_append, cell.area_eq, ih]

/-- The vertex occurrences of concatenated triangle lists concatenate in order.

The three original corners of every head triangle precede the same retained tail vertices. Constructor congruence
transports the tail equality while preserving all ordered occurrences. -/
private theorem vertices_append (first last : List CoordinateTriangulation.CoordinateTriangle) :
    CoordinateTriangulation.triangleVertices (first ++ last) = CoordinateTriangulation.triangleVertices first ++
      CoordinateTriangulation.triangleVertices last := by
  induction first with
  | nil => rfl
  | cons first rest ih =>
      exact congrArg (List.cons first.first)
        (congrArg (List.cons first.second) (congrArg (List.cons first.third) ih))

open Purelib.Geometry.Rectangle.Partition.RectangularCommonMesh.RectangularInverseModels.CutCells in
/-- Every requested point in a selected coarse cell appears in the retained mesh geometry.

The retained selected-cell occurrence identifies its original cut-cell cache. Its point witness enters the same
coordinate-triangle concatenation, preserving original coarse indices and selection multiplicity. -/
theorem point_mem (cells : CutCells geometry
  points selection) (point : Data.Gaussian.Basic.Canonical) (member : point ∈ points)
    (column : Fin (columns + 1)) (row : Fin (rows + 1)) (selected : (column, row) ∈ selection)
    (inside : (geometry.box column row).Contains point) : point ∈ CoordinateTriangulation.triangleVertices
      (cells.triangles.map ModelTriangle.triangle) := by
  induction cells with
  | nil => cases selected
  | cons cell tail ih =>
      rw [triangles, Map.map_append, vertices_append]
      rcases Membership.mem_cons.mp selected with equal | selected
      · cases equal
        exact List.mem_append_left _ (cell.point_mem point member inside)
      · exact List.mem_append_right _ (ih selected)

/-- Every retained owned triangle has positive oriented coordinate area.

Structural append membership selects the exact retained cut cell or an unchanged tail occurrence. Its original
coordinate-area certificate applies to that same owned triangle. -/
theorem positive (cells : CutCells geometry
  points selection) {triangle : RectangularOwnedTriangulation.ModelTriangle geometry}
    (member : triangle ∈ cells.triangles) : 0 < PreparedBoxTriangulation.coordinateArea triangle.triangle := by
  induction cells with
  | nil => cases member
  | cons cell tail ih =>
      rcases Membership.mem_append.mp member with member | member
      · exact cell.positive member
      · exact ih member

end CutCells

set_option genInjectivity false in
/-- The indexed mesh and its full cut geometry are retained independently of the primitive values that will later be
evaluated on it.

The cut-cell spine, combined owned triangles and shared-index surface are cached once. Their defining equations keep the
original selection, requested points and coarse geometry as the construction indices. -/
structure CommonMesh (geometry : RectangularInverseModels.Geometry columns rows) (selection : List (Fin (columns + 1) ×
  Fin (rows + 1))) (points : List Data.Gaussian.Basic.Canonical) where
  /-- The cached cut cells for the exact coarse-cell selection. -/ cells :
    CutCells geometry points selection
  /-- The cached combined owned triangle list. -/ triangles : List (RectangularOwnedTriangulation.ModelTriangle
    geometry)
  /-- The triangle cache is exactly the retained cut-cell triangle list. -/ triangles_eq : triangles = cells.triangles
  /-- The shared-index triangulation of those same owned triangles. -/ surface :
    RectangularOwnedTriangulation.OwnedTriangulation triangles
  /-- The cached total face count. -/ triangleCount : Nat
  /-- The cached face count equals the retained triangle-list length. -/ triangleCount_eq : triangleCount =
    triangles.length

constructive_injectivity CommonMesh

namespace CommonMesh

variable {selection : List (Fin (columns + 1) × Fin (rows + 1))}

/-- Build one shared-index mesh from the retained cut-cell geometry.

Cache the selected cells, their exact combined triangles and count; the coarse model bank and point request remain the
original inputs. -/
@[expose] def build (geometry : RectangularInverseModels.Geometry columns rows) (selection : List (Fin (columns + 1) ×
  Fin (rows + 1))) (points : List Data.Gaussian.Basic.Canonical) :
    CommonMesh geometry selection points :=
  let cells := Geometry.Rectangle.Partition.RectangularCommonMesh.RectangularInverseModels.CutCells.build geometry
    points selection
  let triangles := cells.triangles
  ⟨cells, triangles, rfl, OwnedTriangulation.build triangles, 2 * cells.rectangleCount, cells.length_eq.symm⟩

/-- The face count is bounded by twice selection length times the per-cell quadratic bound. -/
theorem count_le (mesh : CommonMesh geometry
  selection points) :
    mesh.triangleCount ≤ 2 * (selection.length * ((points.length + 1) * (points.length + 1))) := by
  rw [mesh.triangleCount_eq, mesh.triangles_eq, mesh.cells.length_eq]
  exact Nat.mul_le_mul_left 2 mesh.cells.count_le

/-- The common mesh preserves the sum of the selected coarse-cell areas, including selection multiplicity. -/
theorem area_eq (mesh : CommonMesh geometry
  selection points) :
    PreparedBoxTriangulation.sumTriangleAreas (mesh.triangles.map ModelTriangle.triangle) =
      PreparedBoxPartitions.sumCells Content.boxContent (selection.map fun cell => geometry.box cell.1 cell.2) := by
  rw [mesh.triangles_eq]
  exact mesh.cells.area_eq

/-- Every retained owned triangle has positive oriented coordinate area. -/
theorem positive (mesh : CommonMesh geometry
  selection points) {triangle : RectangularOwnedTriangulation.ModelTriangle geometry}
    (member : triangle ∈ mesh.triangles) : 0 < PreparedBoxTriangulation.coordinateArea triangle.triangle := by
  rw [mesh.triangles_eq] at member
  exact mesh.cells.positive member

/-- Every requested point in a selected coarse cell appears in the retained mesh geometry. -/
theorem point_mem (mesh : CommonMesh
  geometry selection points) (point : Data.Gaussian.Basic.Canonical) (member : point ∈ points)
    (column : Fin (columns + 1)) (row : Fin (rows + 1)) (selected : (column, row) ∈ selection)
    (inside : (geometry.box column row).Contains point) : point ∈ mesh.surface.mesh.vertices := by
  apply Geometry.Rectangle.Partition.RectangularCommonMesh.CoordinateTriangulation.contains_triangle_vertex
    mesh.surface.mesh
  rw [mesh.triangles_eq]
  exact mesh.cells.point_mem point member column row selected inside

/-- Guaranteed exact lookup for every requested point in a selected cell. The result is an index and its coordinate
equation, not an optional index. -/
@[expose] def lookup (mesh : CommonMesh
  geometry selection points) (point : Data.Gaussian.Basic.Canonical) (member : point ∈ points)
    (column : Fin (columns + 1)) (row : Fin (rows + 1)) (selected : (column, row) ∈ selection)
    (inside : (geometry.box column row).Contains point) : CoordinateTriangulation.VertexLookup
      mesh.surface.mesh.vertices point :=
  CoordinateTriangulation.lookupVertex point mesh.surface.mesh.vertices (mesh.point_mem point member column row selected
    inside)

end CommonMesh

end RectangularInverseModels

end Purelib.Geometry.Rectangle.Partition.RectangularCommonMesh
