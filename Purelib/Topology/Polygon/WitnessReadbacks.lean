module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.List.Flatten

import Purelib.Topology.Polygon.Stokes
public import Purelib.Topology.Surface.Sewing.VertexSewing
public import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Tactic.Ring

open Purelib

public section

/-! Finite scalar readbacks of displayed edge maps, signed face boundaries
and original incidence witnesses. No endpoint closure or cycle is assumed. -/

namespace Purelib.Topology.Polygon.WitnessReadbacks

open Purelib.Topology.Polygon.Stokes (OrientedEdge OrientedTriangle PrimitivePoint EdgeReordering Triangulation
  edgeListArea edgeArea edgeArea_reverse edgeListArea_append edgeListArea_reordering pairedEdgeOccurrences
  pairedEdgeOccurrences_area_zero triangleEdgeOccurrences triangleWedgeSum)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Geometry.Grid.CellBoundary (sumValues)

/-- Relabeling edge endpoints commutes with reading their oriented area sum. -/
theorem mapped_area {source target : Nat} (labels : Fin source → Fin target)
    (primitive : Fin target → PrimitivePoint) (edges : List (OrientedEdge source)) :
    edgeListArea (fun vertex => primitive (labels vertex)) edges = edgeListArea primitive (edges.map
      (Topology.Surface.Sewing.VertexSewing.OrientedEdge.map labels)) := by
  induction edges with
  | nil => rfl
  | cons edge tail ih => exact congrArg (_ + ·) ih

/-- Reversing each edge occurrence negates the complete edge-area sum. -/
theorem reverse_area {count : Nat} (primitive : Fin count → PrimitivePoint) (edges : List (OrientedEdge count)) :
    edgeListArea primitive (edges.map OrientedEdge.reverse) = -edgeListArea primitive edges := by
  induction edges with
  | nil => exact (neg_zero : -(0 : Data.Gaussian.Basic.Canonical) = 0).symm
  | cons edge tail ih =>
      change edgeArea (primitive edge.finish) (primitive edge.start) + _ = -(edgeArea _ _ + _)
      rw [edgeArea_reverse, ih]
      ring1

/-- The flattened triangle boundary area equals the sum of its face boundary areas.

Flattening preserves each original face boundary in order, and the area readback adds the same signed edge occurrences.
-/
theorem triangles_area {count : Nat} (primitive : Fin count → PrimitivePoint) (triangles : List (OrientedTriangle
  count)) :
    edgeListArea primitive (triangles.flatMap OrientedTriangle.boundary) =
      Polynomial.Geometry.Grid.CellBoundary.sumValues (fun triangle => edgeListArea primitive triangle.boundary)
        triangles := by
  induction triangles with
  | nil => rfl
  | cons triangle tail ih => rw [Data.List.Flatten.flatMap_cons, edgeListArea_append, ih]; rfl

/-- Projecting triangle corners preserves the summed area of their projected boundaries.

The original vertex relabeling acts on the same ordered face boundaries; the sum retains every face and occurrence. -/
theorem projected_triangles {source target : Nat} (labels : Fin source → Fin target)
    (primitive : Fin target → PrimitivePoint) (triangles : List (OrientedTriangle source)) :
    edgeListArea (fun vertex => primitive (labels vertex)) (triangles.flatMap OrientedTriangle.boundary) =
      Polynomial.Geometry.Grid.CellBoundary.sumValues (fun triangle => edgeListArea primitive
        (Topology.Surface.Sewing.VertexSewing.OrientedTriangle.map labels triangle).boundary) triangles := by
  induction triangles with
  | nil => rfl
  | cons triangle tail ih =>
      rw [Data.List.Flatten.flatMap_cons, edgeListArea_append, Polynomial.Geometry.Grid.CellBoundary.sumValues, ih,
        mapped_area, Topology.Surface.Sewing.VertexSewing.OrientedTriangle.boundary_map]

/-- Vertex labels act on the supplied occurrence witness, preserving its signs. -/
theorem mapped_incidence_area {source target : Nat} (labels : Fin source → Fin target)
    (primitive : Fin target → PrimitivePoint) {left right : List (OrientedEdge source)}
    (incidence : EdgeReordering left right) :
    edgeListArea primitive (left.map (Topology.Surface.Sewing.VertexSewing.OrientedEdge.map labels)) =
      edgeListArea primitive (right.map (Topology.Surface.Sewing.VertexSewing.OrientedEdge.map labels)) :=
  edgeListArea_reordering primitive (Topology.Surface.Sewing.VertexSewing.EdgeReordering.map labels incidence)

namespace Triangulation

/-- The faces and boundary are read from the original triangulation's incidence. -/
theorem incidence_readback {vertexCount faceCount : Nat}
    (triangulation : Triangulation vertexCount faceCount)
    (primitive : Fin vertexCount → PrimitivePoint) :
    edgeListArea primitive (triangleEdgeOccurrences triangulation.faces) =
      edgeListArea primitive (triangulation.boundary ++ pairedEdgeOccurrences triangulation.internalEdges) :=
  edgeListArea_reordering primitive triangulation.incidence

/-- This certificate is the original finite incidence witness after relabeling. -/
theorem mapped_incidence_readback {vertexCount faceCount target : Nat}
    (triangulation : Triangulation vertexCount faceCount) (labels : Fin vertexCount → Fin target) :
    EdgeReordering
      ((triangleEdgeOccurrences triangulation.faces).map (Topology.Surface.Sewing.VertexSewing.OrientedEdge.map labels))
      ((triangulation.boundary ++ pairedEdgeOccurrences triangulation.internalEdges).map
        (Topology.Surface.Sewing.VertexSewing.OrientedEdge.map labels)) :=
  Topology.Surface.Sewing.VertexSewing.EdgeReordering.map labels triangulation.incidence

/-- Displayed internal occurrences still cancel after relabeling. -/
theorem mapped_internal_readback {vertexCount faceCount target : Nat}
    (triangulation : Triangulation vertexCount faceCount) (labels : Fin vertexCount → Fin target)
    (primitive : Fin target → PrimitivePoint) :
    edgeListArea primitive ((pairedEdgeOccurrences triangulation.internalEdges).map
      (Topology.Surface.Sewing.VertexSewing.OrientedEdge.map labels)) = 0 := by
  rw [← mapped_area]
  exact pairedEdgeOccurrences_area_zero _ triangulation.internalEdges

/-- Finite Stokes reads the mapped boundary of these same retained faces. -/
theorem mapped_boundary_readback {vertexCount faceCount target : Nat}
    (triangulation : Triangulation vertexCount faceCount) (labels : Fin vertexCount → Fin target)
    (primitive : Fin target → PrimitivePoint) :
    triangleWedgeSum (fun vertex => primitive (labels vertex)) triangulation.faces =
      edgeListArea primitive (triangulation.boundary.map
        (Topology.Surface.Sewing.VertexSewing.OrientedEdge.map labels)) :=
  (Topology.Polygon.Stokes.Triangulation.wedgeSum_eq_boundaryArea triangulation
    (fun vertex => primitive (labels vertex))).trans (mapped_area labels primitive triangulation.boundary)

end Triangulation

end Purelib.Topology.Polygon.WitnessReadbacks
