module
import Purelib.Riemann.Paths.RectangularJoinedTraceReadings

import Purelib.Integration.Path.JoinedTraceIndices
import Purelib.LinearAlgebra.Grid.Offsets
public import Purelib.Riemann.Paths.RectangularTraceIncrementBlocks

@[expose] public section

/-! Scalar readback from certified whole-side caches to their original
pieces and owner junctions. All certificates refer to the retained indices. -/
namespace Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh
open Purelib.Riemann.Normalization.InverseRootPolynomial (Box Gaussian Coordinate Polynomial)
open Purelib.Riemann.Paths.RectangularDyadicPairedTrace (dyadicCount)
open Purelib.Integration.Path.JoinedTrace (VertexTrace)
open Purelib.Integration.Path.JoinedTraceIndices (Embedding)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry Bank)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts)
open Purelib.Riemann.Meshes.RectangularObservationMesh (ObservationMesh)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives)
open Purelib.Riemann.Integration.RectangularPrimitiveGluing (PrimitiveAnchors)
open Purelib.Riemann.Readings.RectangularPointReadings (PointReadings)
open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh (MatchedHorizontalSide
  MatchedVerticalSide)

variable {lc lr rc rr columns rows : Nat} {lg : Geometry lc lr} {rg : Geometry rc rr}
  {leftCuts : GridCuts lg} {rightCuts : GridCuts rg} {leftBox rightBox : Box}
  {left : ObservationMesh leftCuts leftBox} {right : ObservationMesh rightCuts rightBox}
  {polynomial numerator : Polynomial} {geometry : Geometry columns rows}
  {models : Bank polynomial geometry} {primitives : Primitives models numerator}
  {anchors : PrimitiveAnchors primitives} {offsets : LinearAlgebra.Grid.Offsets anchors.edges}
  {depth : Nat}

namespace MatchedHorizontalSide.Trace
variable {leftRow : Fin left.partition.y.intervals.length} {rightRow : Fin right.partition.y.intervals.length}
  {height : Coordinate} {side : MatchedHorizontalSide left right leftRow rightRow height}

open Purelib.Riemann in
open Purelib.Riemann.Paths.RectangularTraceIncrementBlocks.MatchedHorizontalSide in
/-- Read a retained horizontal side piece from its exact whole-side cache.

The certified embedding preserves the original coarse column and dyadic vertex indices, while the supplied pointwise
readback identifies the same retained values. -/
theorem pieceReadings_spec (trace : side.Trace depth) (column : Fin (left.boundaryColumns + 1))
    (original : PointReadings anchors offsets (fun vertex => trace.point (trace.vertices.indexed vertex)))
    (values : side.Vertex depth → Gaussian)
    (readback : ∀ vertex, original.values vertex = values (trace.vertices.indexed vertex))
    (vertex : Fin (dyadicCount depth + 1)) :
    (Trace.pieceReadings trace column original).values vertex = values (Fin.cast left.boundaryColumns_eq column, vertex)
      :=
  Paths.RectangularJoinedTraceReadings.readingsOfIndexed_spec (Trace.pieceEmbedding trace column) original values
    readback vertex

open Purelib.Integration in
open Purelib.Riemann in
open Purelib.Riemann.Paths.RectangularTraceIncrementBlocks.MatchedHorizontalSide in
/-- Read a retained owner junction from its exact whole-side cache.

The two indexed endpoints are the last vertex of the preceding horizontal piece and the first vertex of the next piece,
preserving both original owners. -/
theorem junctionReadings_spec (trace : side.Trace depth) (column : Fin left.boundaryColumns)
    (original : PointReadings anchors offsets (fun vertex => trace.point (trace.vertices.indexed vertex)))
    (values : side.Vertex depth → Gaussian)
    (readback : ∀ vertex, original.values vertex = values (trace.vertices.indexed vertex)) (vertex : Fin 2) :
    (Trace.junctionReadings trace column original).values vertex = values
      (if vertex.val = 0 then (side.pieceVertices depth column.castSucc).last else (side.pieceVertices depth
        column.succ).first) :=
  Paths.RectangularJoinedTraceReadings.readingsOfIndexed_spec (Path.JoinedTraceIndices.junctionEmbedding
    (Trace.pieceEmbedding trace column.castSucc) (Trace.pieceEmbedding trace column.succ))
    original values readback vertex

end MatchedHorizontalSide.Trace
namespace MatchedVerticalSide.Trace
variable {leftColumn : Fin left.partition.x.intervals.length} {rightColumn : Fin right.partition.x.intervals.length}
  {horizontal : Coordinate} {side : MatchedVerticalSide left right leftColumn rightColumn horizontal}

open Purelib.Riemann in
open Purelib.Riemann.Paths.RectangularTraceIncrementBlocks.MatchedVerticalSide in
/-- Read a retained vertical side piece from its exact whole-side cache.

The certified embedding preserves the original coarse row and dyadic vertex indices, while the supplied pointwise
readback identifies the same retained values. -/
theorem pieceReadings_spec (trace : side.Trace depth) (row : Fin (left.boundaryRows + 1))
    (original : PointReadings anchors offsets (fun vertex => trace.point (trace.vertices.indexed vertex)))
    (values : side.Vertex depth → Gaussian)
    (readback : ∀ vertex, original.values vertex = values (trace.vertices.indexed vertex))
    (vertex : Fin (dyadicCount depth + 1)) :
    (Trace.pieceReadings trace row original).values vertex = values (Fin.cast left.boundaryRows_eq row, vertex) :=
  Paths.RectangularJoinedTraceReadings.readingsOfIndexed_spec (Trace.pieceEmbedding trace row) original values readback
    vertex

open Purelib.Integration in
open Purelib.Riemann in
open Purelib.Riemann.Paths.RectangularTraceIncrementBlocks.MatchedVerticalSide in
/-- Read a retained owner junction from its exact whole-side cache.

The two indexed endpoints are the last vertex of the preceding vertical piece and the first vertex of the next piece,
preserving both original owners. -/
theorem junctionReadings_spec (trace : side.Trace depth) (row : Fin left.boundaryRows)
    (original : PointReadings anchors offsets (fun vertex => trace.point (trace.vertices.indexed vertex)))
    (values : side.Vertex depth → Gaussian)
    (readback : ∀ vertex, original.values vertex = values (trace.vertices.indexed vertex)) (vertex : Fin 2) :
    (Trace.junctionReadings trace row original).values vertex = values
      (if vertex.val = 0 then (side.pieceVertices depth row.castSucc).last else (side.pieceVertices depth
        row.succ).first) :=
  Paths.RectangularJoinedTraceReadings.readingsOfIndexed_spec (Path.JoinedTraceIndices.junctionEmbedding
    (Trace.pieceEmbedding trace row.castSucc) (Trace.pieceEmbedding trace row.succ))
    original values readback vertex

end MatchedVerticalSide.Trace
end Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh
