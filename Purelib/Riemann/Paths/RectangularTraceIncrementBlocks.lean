module
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Data.Gaussian.Basic

import Purelib.Integration.Path.CenteredPathIncrements
import Purelib.Integration.Path.JoinedTrace
import Purelib.LinearAlgebra.Grid.Offsets
public import Purelib.Riemann.Paths.RectangularMatchedSideTrace
public import Purelib.Riemann.Paths.RectangularMatchedVerticalSideTrace
import Purelib.Integration.Path.JoinedTraceIncrements
public import Purelib.Riemann.Paths.RectangularJoinedTraceReadings
public import Purelib.Integration.Polynomial.Rectangle.JoinedSampleBlocks
public import Purelib.Integration.Polynomial.Rectangle.SampleReadback
import Purelib.Integration.Path.JoinedTraceIndices
import Purelib.Integration.Path.PairedIncrementArea

@[expose] public section

namespace Purelib.Riemann.Paths.RectangularTraceIncrementBlocks

/-! Extract every matched-side segment and owner junction from the supplied
centered sample. This preserves cached numerical readings and their order. -/
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Box Coordinate)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Integration.Path.JoinedTrace (VertexTrace)
open Purelib.Integration.Path.JoinedTraceIndices (Embedding concatenateEntry junctionEmbedding)
open Purelib.Riemann.Integration.RectangularPairedPointBanks (Trace)
open Purelib.Riemann.Paths.RectangularPairedSegments (PairedSegmentPiece)
open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh (MatchedHorizontalSide
  MatchedVerticalSide)
open Purelib.Riemann.Normalization.RectangularInverseModels (Bank)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives)
open Purelib.Riemann.Integration.RectangularPrimitiveGluing (PrimitiveAnchors)
open Purelib.Riemann.Readings.RectangularPointReadings (PointReadings)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts)
open Purelib.Riemann.Meshes.RectangularObservationMesh (ObservationMesh)
open Purelib.Riemann.Periods.CenteredBilinearPath (Sample)
open Purelib.Riemann.Paths.RectangularDyadicPairedTrace (dyadicCount)
variable {leftColumns leftRows rightColumns rightRows : Nat}
  {leftGeometry : Geometry leftColumns leftRows} {rightGeometry : Geometry rightColumns rightRows}
  {leftCuts : GridCuts leftGeometry} {rightCuts : GridCuts rightGeometry} {leftBox rightBox : Box}
  {left : ObservationMesh leftCuts leftBox} {right : ObservationMesh rightCuts rightBox}

namespace MatchedHorizontalSide.Trace

variable {leftRow : Fin left.partition.y.intervals.length} {rightRow : Fin right.partition.y.intervals.length}
  {height : Coordinate} {side : MatchedHorizontalSide left right leftRow rightRow height} {depth : Nat}

open Purelib.Integration in
/-- Embed one horizontal segment's retained vertices in the original joined side trace. -/
def pieceEmbedding (trace : side.Trace depth) (column : Fin (left.boundaryColumns + 1)) :
  Path.JoinedTraceIndices.Embedding (side.pieceVertices depth column) trace.vertices :=
  (Path.JoinedTraceIndices.concatenateEntry (side.pieceVertices depth) column).castWhole trace.vertices_eq.symm

open Purelib.Riemann in
open Purelib.LinearAlgebra in
/-- Restrict the original point-reading cache to one horizontal segment.

The exact vertex embedding preserves the original owner and value observations at every segment index. -/
def pieceReadings (trace : side.Trace depth) (column : Fin (left.boundaryColumns + 1))
    {polynomial numerator : Normalization.InverseRootPolynomial.Polynomial}
    {columns rows : Nat} {geometry : Geometry columns rows}
    {models : Bank polynomial geometry} {primitives : Primitives models numerator}
    {anchors : PrimitiveAnchors primitives} {offsets : LinearAlgebra.Grid.Offsets anchors.edges}
    (original : PointReadings anchors offsets (fun vertex => trace.point (trace.vertices.indexed vertex))) :
    PointReadings anchors offsets (fun vertex =>
      (trace.segments.get (Fin.cast left.boundaryColumns_eq column)).points vertex) :=
  Paths.RectangularJoinedTraceReadings.readingsOfIndexed
    (count := dyadicCount depth)
    (vertices := fun vertex => (Fin.cast left.boundaryColumns_eq column, vertex))
    (Paths.RectangularTraceIncrementBlocks.MatchedHorizontalSide.Trace.pieceEmbedding trace column) original

open Purelib.Riemann in
open Purelib.Integration in
open Purelib.LinearAlgebra in
/-- Restrict the original cache to the two owner occurrences at a horizontal junction. -/
def junctionReadings (trace : side.Trace depth) (column : Fin left.boundaryColumns)
    {polynomial numerator : Normalization.InverseRootPolynomial.Polynomial}
    {columns rows : Nat} {geometry : Geometry columns rows}
    {models : Bank polynomial geometry} {primitives : Primitives models numerator}
    {anchors : PrimitiveAnchors primitives} {offsets : LinearAlgebra.Grid.Offsets anchors.edges}
    (original : PointReadings anchors offsets (fun vertex => trace.point (trace.vertices.indexed vertex))) :
    PointReadings anchors offsets (fun vertex : Fin 2 => trace.point
      (if vertex.val = 0 then (side.pieceVertices depth column.castSucc).last else (side.pieceVertices depth
        column.succ).first)) :=
  Paths.RectangularJoinedTraceReadings.readingsOfIndexed
    (count := 1)
    (vertices := fun vertex : Fin 2 =>
      if vertex.val = 0 then (side.pieceVertices depth column.castSucc).last
      else (side.pieceVertices depth column.succ).first)
    (Path.JoinedTraceIndices.junctionEmbedding
      (Paths.RectangularTraceIncrementBlocks.MatchedHorizontalSide.Trace.pieceEmbedding trace column.castSucc)
      (Paths.RectangularTraceIncrementBlocks.MatchedHorizontalSide.Trace.pieceEmbedding trace column.succ)) original

open Purelib.Integration in
/-- Both owner occurrences at a horizontal junction have the exact preceding piece's last physical point. -/
theorem junction_point (trace : side.Trace depth) (column : Fin left.boundaryColumns) (vertex : Fin 2) :
    trace.point (if vertex.val = 0 then (side.pieceVertices depth column.castSucc).last
      else (side.pieceVertices depth column.succ).first) =
        (side.pieces (Fin.cast left.boundaryColumns_eq column.castSucc)).last := by
  by_cases zero : vertex.val = 0
  · rw [if_pos zero, MatchedHorizontalSide.pieceVertices, Path.JoinedTrace.VertexTrace.ofIndexed_last]
    exact (trace.segments.get _).last_point
  · rw [if_neg zero]
    have adjacent := side.consecutive column.val (Fin.cast left.boundaryColumns_eq column.succ).isLt
    exact ((trace.segments.get (Fin.cast left.boundaryColumns_eq column.succ)).first_point).trans adjacent.symm

section
open Purelib.Integration
open Purelib.Data
/-- The exact piece-and-junction increment partition of the retained horizontal side sample. -/
def IncrementPartition (trace : side.Trace depth)
    (values : Fin (leftColumns + 1) → Fin (leftRows + 1) → Gaussian.Basic.Canonical → PrimitivePoint)
    (sample : Sample (fun vertex => trace.leftValue values (trace.vertices.indexed vertex))) :=
  Path.JoinedTraceIncrements.VertexTrace.IncrementPartition (trace.leftValue values) (side.pieceVertices depth 0)
    (List.ofFn (fun index : Fin left.boundaryColumns => side.pieceVertices depth index.succ)) sample

/-- Partition the retained horizontal side sample using its original ordered segment traces. -/
def incrementPartition (trace : side.Trace depth)
    (values : Fin (leftColumns + 1) → Fin (leftRows + 1) → Gaussian.Basic.Canonical → PrimitivePoint)
    (sample : Sample (fun vertex => trace.leftValue values (trace.vertices.indexed vertex))) :
    IncrementPartition trace values sample :=
  Path.JoinedTraceIncrements.VertexTrace.IncrementPartition.build (trace.leftValue values) (side.pieceVertices depth 0)
    (List.ofFn (fun index : Fin left.boundaryColumns => side.pieceVertices depth index.succ)) sample trace.vertices_eq

end

open Purelib.Data in
/-- A sample on every actual horizontal segment vertex trace. -/
def PieceSamples (trace : side.Trace depth)
    (values : Fin (leftColumns + 1) → Fin (leftRows + 1) → Gaussian.Basic.Canonical → PrimitivePoint) :=
  (column : Fin (left.boundaryColumns + 1)) →
    Sample (fun vertex => trace.leftValue values ((side.pieceVertices depth column).indexed vertex))

open Purelib.Integration in
open Purelib.Data in
/-- A two-vertex sample on every adjacent horizontal owner junction. -/
def JunctionSamples (trace : side.Trace depth)
    (values : Fin (leftColumns + 1) → Fin (leftRows + 1) → Gaussian.Basic.Canonical → PrimitivePoint) :=
  (column : Fin left.boundaryColumns) → Sample (Polynomial.Rectangle.JoinedSampleBlocks.JunctionValues (trace.leftValue
    values)
    (side.pieceVertices depth column.castSucc) (side.pieceVertices depth column.succ))

section
open Purelib.Riemann
open Purelib.Integration
open Purelib.Data
/-- Reindex the existing horizontal segment samples into their exact retained vertex traces. -/
def pieceSamplesOfSegments (trace : side.Trace depth)
    (values : Fin (leftColumns + 1) → Fin (leftRows + 1) → Gaussian.Basic.Canonical → PrimitivePoint)
    (samples : (column : Fin (left.boundaryColumns + 1)) → Sample (fun vertex =>
      trace.leftValue values (Fin.cast left.boundaryColumns_eq column, vertex))) :
        Paths.RectangularTraceIncrementBlocks.MatchedHorizontalSide.Trace.PieceSamples trace values :=
  fun column => Polynomial.Rectangle.SampleReadback.VertexTrace.ofIndexedSample (fun vertex => (Fin.cast
    left.boundaryColumns_eq column, vertex))
    (trace.leftValue values) (samples column)

/-- The ordered horizontal piece and owner-junction increment blocks from the supplied caches. -/
def sampledBlocks (trace : side.Trace depth)
    (values : Fin (leftColumns + 1) → Fin (leftRows + 1) → Gaussian.Basic.Canonical → PrimitivePoint)
    (pieces : Paths.RectangularTraceIncrementBlocks.MatchedHorizontalSide.Trace.PieceSamples trace values) (junctions :
      Paths.RectangularTraceIncrementBlocks.MatchedHorizontalSide.Trace.JunctionSamples trace values) : List (List
      PrimitivePoint) :=
  Polynomial.Rectangle.JoinedSampleBlocks.sampledBlocks (trace.leftValue values) (side.pieceVertices depth) pieces
    junctions

/-- The supplied horizontal sample blocks equal the original sample's retained increment partition. -/
theorem sampledBlocks_eq (trace : side.Trace depth)
    (values : Fin (leftColumns + 1) → Fin (leftRows + 1) → Gaussian.Basic.Canonical → PrimitivePoint)
    (pieces : Paths.RectangularTraceIncrementBlocks.MatchedHorizontalSide.Trace.PieceSamples trace values) (junctions :
      Paths.RectangularTraceIncrementBlocks.MatchedHorizontalSide.Trace.JunctionSamples trace values)
    (sample : Sample (fun vertex => trace.leftValue values (trace.vertices.indexed vertex))) :
    Paths.RectangularTraceIncrementBlocks.MatchedHorizontalSide.Trace.sampledBlocks trace values pieces junctions =
      (Paths.RectangularTraceIncrementBlocks.MatchedHorizontalSide.Trace.incrementPartition trace values sample).blocks
      :=
  Polynomial.Rectangle.JoinedSampleBlocks.sampledBlocks_partition (trace.leftValue values) (side.pieceVertices depth)
    pieces junctions
    (Paths.RectangularTraceIncrementBlocks.MatchedHorizontalSide.Trace.incrementPartition trace values sample)

/-- The flattened horizontal piece and junction blocks have exactly the retained sample's centered area. -/
theorem sampledBlocks_area (trace : side.Trace depth)
    (values : Fin (leftColumns + 1) → Fin (leftRows + 1) → Gaussian.Basic.Canonical → PrimitivePoint)
    (pieces : Paths.RectangularTraceIncrementBlocks.MatchedHorizontalSide.Trace.PieceSamples trace values) (junctions :
      Paths.RectangularTraceIncrementBlocks.MatchedHorizontalSide.Trace.JunctionSamples trace values)
    (sample : Sample (fun vertex => trace.leftValue values (trace.vertices.indexed vertex))) :
    Path.PairedIncrementArea.area (Paths.RectangularTraceIncrementBlocks.MatchedHorizontalSide.Trace.sampledBlocks trace
      values pieces junctions).flatten = sample.centeredArea := by
  rw [Paths.RectangularTraceIncrementBlocks.MatchedHorizontalSide.Trace.sampledBlocks_eq trace values pieces junctions
    sample, (Paths.RectangularTraceIncrementBlocks.MatchedHorizontalSide.Trace.incrementPartition trace values
    sample).flatten_eq]
  exact Path.CenteredPathIncrements.Sample.increments_area sample

end

end MatchedHorizontalSide.Trace

namespace MatchedVerticalSide.Trace

open Purelib.Integration.Path.JoinedTraceIndices (Embedding)

variable {leftColumn : Fin left.partition.x.intervals.length} {rightColumn : Fin right.partition.x.intervals.length}
  {horizontal : Coordinate} {side : MatchedVerticalSide left right leftColumn rightColumn horizontal} {depth : Nat}

open Purelib.Integration in
/-- Embed one vertical segment's retained vertices in the original joined side trace. -/
def pieceEmbedding (trace : side.Trace depth) (row : Fin (left.boundaryRows + 1)) :
  Path.JoinedTraceIndices.Embedding (side.pieceVertices depth row) trace.vertices :=
  (Path.JoinedTraceIndices.concatenateEntry (side.pieceVertices depth) row).castWhole trace.vertices_eq.symm

open Purelib.Riemann in
open Purelib.LinearAlgebra in
/-- Restrict the original point-reading cache to one vertical segment.

The exact vertex embedding preserves the original owner and value observations at every segment index. -/
def pieceReadings (trace : side.Trace depth) (row : Fin (left.boundaryRows + 1))
    {polynomial numerator : Normalization.InverseRootPolynomial.Polynomial}
    {columns rows : Nat} {geometry : Geometry columns rows}
    {models : Bank polynomial geometry} {primitives : Primitives models numerator}
    {anchors : PrimitiveAnchors primitives} {offsets : LinearAlgebra.Grid.Offsets anchors.edges}
    (original : PointReadings anchors offsets (fun vertex => trace.point (trace.vertices.indexed vertex))) :
    PointReadings anchors offsets (fun vertex =>
      (trace.segments.get (Fin.cast left.boundaryRows_eq row)).points vertex) :=
  Paths.RectangularJoinedTraceReadings.readingsOfIndexed
    (count := dyadicCount depth)
    (vertices := fun vertex => (Fin.cast left.boundaryRows_eq row, vertex))
    (Paths.RectangularTraceIncrementBlocks.MatchedVerticalSide.Trace.pieceEmbedding trace row) original

open Purelib.Riemann in
open Purelib.Integration in
open Purelib.LinearAlgebra in
/-- Restrict the original cache to the two owner occurrences at a vertical junction. -/
def junctionReadings (trace : side.Trace depth) (row : Fin left.boundaryRows)
    {polynomial numerator : Normalization.InverseRootPolynomial.Polynomial}
    {columns rows : Nat} {geometry : Geometry columns rows}
    {models : Bank polynomial geometry} {primitives : Primitives models numerator}
    {anchors : PrimitiveAnchors primitives} {offsets : LinearAlgebra.Grid.Offsets anchors.edges}
    (original : PointReadings anchors offsets (fun vertex => trace.point (trace.vertices.indexed vertex))) :
    PointReadings anchors offsets (fun vertex : Fin 2 => trace.point
      (if vertex.val = 0 then (side.pieceVertices depth row.castSucc).last else (side.pieceVertices depth
        row.succ).first)) :=
  Paths.RectangularJoinedTraceReadings.readingsOfIndexed
    (count := 1)
    (vertices := fun vertex : Fin 2 =>
      if vertex.val = 0 then (side.pieceVertices depth row.castSucc).last
      else (side.pieceVertices depth row.succ).first)
    (Path.JoinedTraceIndices.junctionEmbedding
      (Paths.RectangularTraceIncrementBlocks.MatchedVerticalSide.Trace.pieceEmbedding trace row.castSucc)
      (Paths.RectangularTraceIncrementBlocks.MatchedVerticalSide.Trace.pieceEmbedding trace row.succ)) original

open Purelib.Integration in
/-- Both owner occurrences at a vertical junction have the exact preceding piece's last physical point. -/
theorem junction_point (trace : side.Trace depth) (row : Fin left.boundaryRows) (vertex : Fin 2) :
    trace.point (if vertex.val = 0 then (side.pieceVertices depth row.castSucc).last
      else (side.pieceVertices depth row.succ).first) =
        (side.pieces (Fin.cast left.boundaryRows_eq row.castSucc)).last := by
  by_cases zero : vertex.val = 0
  · rw [if_pos zero, MatchedVerticalSide.pieceVertices, Path.JoinedTrace.VertexTrace.ofIndexed_last]
    exact (trace.segments.get _).last_point
  · rw [if_neg zero]
    have adjacent := side.consecutive row.val (Fin.cast left.boundaryRows_eq row.succ).isLt
    exact ((trace.segments.get (Fin.cast left.boundaryRows_eq row.succ)).first_point).trans adjacent.symm

section
open Purelib.Integration
open Purelib.Data
/-- The exact piece-and-junction increment partition of the retained vertical side sample. -/
def IncrementPartition (trace : side.Trace depth)
    (values : Fin (leftColumns + 1) → Fin (leftRows + 1) → Gaussian.Basic.Canonical → PrimitivePoint)
    (sample : Sample (fun vertex => trace.leftValue values (trace.vertices.indexed vertex))) :=
  Path.JoinedTraceIncrements.VertexTrace.IncrementPartition (trace.leftValue values) (side.pieceVertices depth 0)
    (List.ofFn (fun index : Fin left.boundaryRows => side.pieceVertices depth index.succ)) sample

/-- Partition the retained vertical side sample using its original ordered segment traces. -/
def incrementPartition (trace : side.Trace depth)
    (values : Fin (leftColumns + 1) → Fin (leftRows + 1) → Gaussian.Basic.Canonical → PrimitivePoint)
    (sample : Sample (fun vertex => trace.leftValue values (trace.vertices.indexed vertex))) :
    IncrementPartition trace values sample :=
  Path.JoinedTraceIncrements.VertexTrace.IncrementPartition.build (trace.leftValue values) (side.pieceVertices depth 0)
    (List.ofFn (fun index : Fin left.boundaryRows => side.pieceVertices depth index.succ)) sample trace.vertices_eq

end

open Purelib.Data in
/-- A sample on every actual vertical segment vertex trace. -/
def PieceSamples (trace : side.Trace depth)
    (values : Fin (leftColumns + 1) → Fin (leftRows + 1) → Gaussian.Basic.Canonical → PrimitivePoint) :=
  (row : Fin (left.boundaryRows + 1)) →
    Sample (fun vertex => trace.leftValue values ((side.pieceVertices depth row).indexed vertex))

open Purelib.Integration in
open Purelib.Data in
/-- A two-vertex sample on every adjacent vertical owner junction. -/
def JunctionSamples (trace : side.Trace depth)
    (values : Fin (leftColumns + 1) → Fin (leftRows + 1) → Gaussian.Basic.Canonical → PrimitivePoint) :=
  (row : Fin left.boundaryRows) → Sample (Polynomial.Rectangle.JoinedSampleBlocks.JunctionValues (trace.leftValue
    values)
    (side.pieceVertices depth row.castSucc) (side.pieceVertices depth row.succ))

section
open Purelib.Riemann
open Purelib.Integration
open Purelib.Data
/-- Reindex the existing vertical segment samples into their exact retained vertex traces. -/
def pieceSamplesOfSegments (trace : side.Trace depth)
    (values : Fin (leftColumns + 1) → Fin (leftRows + 1) → Gaussian.Basic.Canonical → PrimitivePoint)
    (samples : (row : Fin (left.boundaryRows + 1)) → Sample (fun vertex =>
      trace.leftValue values (Fin.cast left.boundaryRows_eq row, vertex))) :
        Paths.RectangularTraceIncrementBlocks.MatchedVerticalSide.Trace.PieceSamples trace values :=
  fun row => Polynomial.Rectangle.SampleReadback.VertexTrace.ofIndexedSample (fun vertex => (Fin.cast
    left.boundaryRows_eq row, vertex))
    (trace.leftValue values) (samples row)

/-- The ordered vertical piece and owner-junction increment blocks from the supplied caches. -/
def sampledBlocks (trace : side.Trace depth)
    (values : Fin (leftColumns + 1) → Fin (leftRows + 1) → Gaussian.Basic.Canonical → PrimitivePoint)
    (pieces : Paths.RectangularTraceIncrementBlocks.MatchedVerticalSide.Trace.PieceSamples trace values) (junctions :
      Paths.RectangularTraceIncrementBlocks.MatchedVerticalSide.Trace.JunctionSamples trace values) : List (List
      PrimitivePoint) :=
  Polynomial.Rectangle.JoinedSampleBlocks.sampledBlocks (trace.leftValue values) (side.pieceVertices depth) pieces
    junctions

/-- The supplied vertical sample blocks equal the original sample's retained increment partition. -/
theorem sampledBlocks_eq (trace : side.Trace depth)
    (values : Fin (leftColumns + 1) → Fin (leftRows + 1) → Gaussian.Basic.Canonical → PrimitivePoint)
    (pieces : Paths.RectangularTraceIncrementBlocks.MatchedVerticalSide.Trace.PieceSamples trace values) (junctions :
      Paths.RectangularTraceIncrementBlocks.MatchedVerticalSide.Trace.JunctionSamples trace values)
    (sample : Sample (fun vertex => trace.leftValue values (trace.vertices.indexed vertex))) :
    Paths.RectangularTraceIncrementBlocks.MatchedVerticalSide.Trace.sampledBlocks trace values pieces junctions =
      (Paths.RectangularTraceIncrementBlocks.MatchedVerticalSide.Trace.incrementPartition trace values sample).blocks :=
  Polynomial.Rectangle.JoinedSampleBlocks.sampledBlocks_partition (trace.leftValue values) (side.pieceVertices depth)
    pieces junctions
    (Paths.RectangularTraceIncrementBlocks.MatchedVerticalSide.Trace.incrementPartition trace values sample)

/-- The flattened vertical piece and junction blocks have exactly the retained sample's centered area. -/
theorem sampledBlocks_area (trace : side.Trace depth)
    (values : Fin (leftColumns + 1) → Fin (leftRows + 1) → Gaussian.Basic.Canonical → PrimitivePoint)
    (pieces : Paths.RectangularTraceIncrementBlocks.MatchedVerticalSide.Trace.PieceSamples trace values) (junctions :
      Paths.RectangularTraceIncrementBlocks.MatchedVerticalSide.Trace.JunctionSamples trace values)
    (sample : Sample (fun vertex => trace.leftValue values (trace.vertices.indexed vertex))) :
    Path.PairedIncrementArea.area (Paths.RectangularTraceIncrementBlocks.MatchedVerticalSide.Trace.sampledBlocks trace
      values pieces junctions).flatten = sample.centeredArea := by
  rw [Paths.RectangularTraceIncrementBlocks.MatchedVerticalSide.Trace.sampledBlocks_eq trace values pieces junctions
    sample, (Paths.RectangularTraceIncrementBlocks.MatchedVerticalSide.Trace.incrementPartition trace values
    sample).flatten_eq]
  exact Path.CenteredPathIncrements.Sample.increments_area sample

end

end MatchedVerticalSide.Trace

end Purelib.Riemann.Paths.RectangularTraceIncrementBlocks
