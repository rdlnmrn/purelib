module

import Purelib.Integration.Path.Dyadic.DyadicTrace
import Purelib.Integration.Path.JoinedTrace
import Purelib.Riemann.Integration.RectangularMatchedPerimeter
public import Purelib.Riemann.Paths.RectangularMatchedVerticalSideTrace
public import Purelib.Riemann.Paths.RectangularMatchedSideTrace
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Data.Gaussian.Basic
import Purelib.Riemann.Paths.RectangularDyadicPairedTrace
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Topology.Polygon.Stokes
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Readings.RectangularMatchedObservationSides
import Purelib.Riemann.Paths.RectangularPairedSegments
import Purelib.Data.Vector.Basic
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Tactic.Ring

@[expose] public section

/-! Exact retained endpoints of whole matched traces. -/
namespace Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh

open Purelib.Riemann.Normalization.InverseRootPolynomial (Box Gaussian Coordinate)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint edgeArea)
open Purelib.Integration.Path.JoinedTrace (VertexTrace)
open Purelib.Riemann.Periods.CenteredBilinearPath (Sample)
open Purelib.Riemann.Paths.RectangularDyadicPairedTrace (dyadicCount)
open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh (MatchedHorizontalSide
  MatchedVerticalSide)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts)
open Purelib.Riemann.Meshes.RectangularObservationMesh (ObservationMesh)

variable {leftColumns leftRows rightColumns rightRows : Nat}
  {leftGeometry : Geometry leftColumns leftRows} {rightGeometry : Geometry rightColumns rightRows}
  {leftCuts : GridCuts leftGeometry} {rightCuts : GridCuts rightGeometry} {leftBox rightBox : Box}
  {left : ObservationMesh leftCuts leftBox} {right : ObservationMesh rightCuts rightBox}

namespace MatchedHorizontalSide.Trace

open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedHorizontalSide.Trace (leftValue
  rightValue)

variable {leftRow : Fin left.partition.y.intervals.length}
  {rightRow : Fin right.partition.y.intervals.length} {height : Coordinate}
  {side : MatchedHorizontalSide left right leftRow rightRow height} {depth : Nat}

open Purelib.Integration.Path in
open Purelib.Integration.Path.Dyadic in
/-- The joined matched-side trace ends at the original last interval and its final dyadic vertex. -/
theorem
  last_index
  (trace : side.Trace depth) :
    trace.vertices.indexed (Fin.last trace.vertices.rest.length) =
      (Fin.cast left.boundaryColumns_eq (Fin.last left.boundaryColumns), Fin.last (dyadicCount depth)) := by
  rw [JoinedTrace.VertexTrace.indexed, DyadicTrace.indexed_last]
  change trace.vertices.last = _
  rw [trace.vertices_eq, JoinedTrace.VertexTrace.concatenate_last]
  exact JoinedTrace.VertexTrace.ofIndexed_last _

/-- The joined matched-side trace ends at the original last paired piece's endpoint. -/
theorem
  last_point
  (trace : side.Trace depth) :
    trace.point (trace.vertices.indexed (Fin.last trace.vertices.rest.length)) =
      (side.pieces (Fin.cast left.boundaryColumns_eq (Fin.last left.boundaryColumns))).last := by
  rw [trace.last_index]
  exact (trace.segments.get _).last_point

open Purelib.Topology.Polygon
/-- The retained sample endpoint term equals the chord between the original first and last left-owner values.

The supplied pointwise readback identifies the exact joined trace, preserving both extreme piece indices and their
original model-cell owners. -/
theorem
  left_endpoint
  (trace : side.Trace depth)
    (values : Fin (leftColumns + 1) → Fin (leftRows + 1) → Gaussian → PrimitivePoint)
    {readings : Fin (trace.vertices.rest.length + 1) → PrimitivePoint}
    (sample : Sample readings)
    (readback : ∀ vertex, readings vertex = trace.leftValue values (trace.vertices.indexed vertex)) :
    sample.endpoint =
      edgeArea
        (values (side.pieces (Fin.cast left.boundaryColumns_eq 0)).leftColumn
          (side.pieces (Fin.cast left.boundaryColumns_eq 0)).leftRow
          (side.pieces (Fin.cast left.boundaryColumns_eq 0)).first)
        (values (side.pieces (Fin.cast left.boundaryColumns_eq (Fin.last left.boundaryColumns))).leftColumn
          (side.pieces (Fin.cast left.boundaryColumns_eq (Fin.last left.boundaryColumns))).leftRow
          (side.pieces (Fin.cast left.boundaryColumns_eq (Fin.last left.boundaryColumns))).last) := by
  rw [sample.endpoint_eq, readback, readback]
  have firstValue : trace.leftValue values (trace.vertices.indexed 0) =
      values (side.pieces (Fin.cast left.boundaryColumns_eq 0)).leftColumn
        (side.pieces (Fin.cast left.boundaryColumns_eq 0)).leftRow
        (side.pieces (Fin.cast left.boundaryColumns_eq 0)).first := by
    unfold leftValue
    rw [trace.first_point, trace.first_index]
  have lastValue : trace.leftValue values (trace.vertices.indexed (Fin.last trace.vertices.rest.length)) =
      values (side.pieces (Fin.cast left.boundaryColumns_eq (Fin.last left.boundaryColumns))).leftColumn
        (side.pieces (Fin.cast left.boundaryColumns_eq (Fin.last left.boundaryColumns))).leftRow
        (side.pieces (Fin.cast left.boundaryColumns_eq (Fin.last left.boundaryColumns))).last := by
    unfold leftValue
    rw [trace.last_point, trace.last_index]
  rw [firstValue, lastValue]
  simp only [edgeArea, Stokes.PrimitivePoint.sub]
  ring1

/-- The retained sample endpoint term equals the chord between the original first and last right-owner values.

The supplied pointwise readback identifies the exact joined trace, preserving both extreme piece indices and their
original model-cell owners. -/
theorem
  right_endpoint
  (trace : side.Trace depth)
    (values : Fin (rightColumns + 1) → Fin (rightRows + 1) → Gaussian → PrimitivePoint)
    {readings : Fin (trace.vertices.rest.length + 1) → PrimitivePoint}
    (sample : Sample readings)
    (readback : ∀ vertex, readings vertex = trace.rightValue values (trace.vertices.indexed vertex)) :
    sample.endpoint =
      edgeArea
        (values (side.pieces (Fin.cast left.boundaryColumns_eq 0)).rightColumn
          (side.pieces (Fin.cast left.boundaryColumns_eq 0)).rightRow
          (side.pieces (Fin.cast left.boundaryColumns_eq 0)).first)
        (values (side.pieces (Fin.cast left.boundaryColumns_eq (Fin.last left.boundaryColumns))).rightColumn
          (side.pieces (Fin.cast left.boundaryColumns_eq (Fin.last left.boundaryColumns))).rightRow
          (side.pieces (Fin.cast left.boundaryColumns_eq (Fin.last left.boundaryColumns))).last) := by
  rw [sample.endpoint_eq, readback, readback]
  have firstValue : trace.rightValue values (trace.vertices.indexed 0) =
      values (side.pieces (Fin.cast left.boundaryColumns_eq 0)).rightColumn
        (side.pieces (Fin.cast left.boundaryColumns_eq 0)).rightRow
        (side.pieces (Fin.cast left.boundaryColumns_eq 0)).first := by
    unfold rightValue
    rw [trace.first_point, trace.first_index]
  have lastValue : trace.rightValue values (trace.vertices.indexed (Fin.last trace.vertices.rest.length)) =
      values (side.pieces (Fin.cast left.boundaryColumns_eq (Fin.last left.boundaryColumns))).rightColumn
        (side.pieces (Fin.cast left.boundaryColumns_eq (Fin.last left.boundaryColumns))).rightRow
        (side.pieces (Fin.cast left.boundaryColumns_eq (Fin.last left.boundaryColumns))).last := by
    unfold rightValue
    rw [trace.last_point, trace.last_index]
  rw [firstValue, lastValue]
  simp only [edgeArea, Stokes.PrimitivePoint.sub]
  ring1

end MatchedHorizontalSide.Trace

namespace MatchedVerticalSide.Trace

open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedVerticalSide.Trace (leftValue
  rightValue)

variable {leftColumn : Fin left.partition.x.intervals.length}
  {rightColumn : Fin right.partition.x.intervals.length} {horizontal : Coordinate}
  {side : MatchedVerticalSide left right leftColumn rightColumn horizontal} {depth : Nat}

open Purelib.Integration.Path in
open Purelib.Integration.Path.Dyadic in
/-- The joined matched-side trace ends at the original last interval and its final dyadic vertex. -/
theorem
  last_index
  (trace : side.Trace depth) :
    trace.vertices.indexed (Fin.last trace.vertices.rest.length) =
      (Fin.cast left.boundaryRows_eq (Fin.last left.boundaryRows), Fin.last (dyadicCount depth)) := by
  rw [JoinedTrace.VertexTrace.indexed, DyadicTrace.indexed_last]
  change trace.vertices.last = _
  rw [trace.vertices_eq, JoinedTrace.VertexTrace.concatenate_last]
  exact JoinedTrace.VertexTrace.ofIndexed_last _

/-- The joined matched-side trace ends at the original last paired piece's endpoint. -/
theorem
  last_point
  (trace : side.Trace depth) :
    trace.point (trace.vertices.indexed (Fin.last trace.vertices.rest.length)) =
      (side.pieces (Fin.cast left.boundaryRows_eq (Fin.last left.boundaryRows))).last := by
  rw [trace.last_index]
  exact (trace.segments.get _).last_point

open Purelib.Topology.Polygon
/-- The retained sample endpoint term equals the chord between the original first and last left-owner values.

The supplied pointwise readback identifies the exact joined trace, preserving both extreme piece indices and their
original model-cell owners. -/
theorem
  left_endpoint
  (trace : side.Trace depth)
    (values : Fin (leftColumns + 1) → Fin (leftRows + 1) → Gaussian → PrimitivePoint)
    {readings : Fin (trace.vertices.rest.length + 1) → PrimitivePoint}
    (sample : Sample readings)
    (readback : ∀ vertex, readings vertex = trace.leftValue values (trace.vertices.indexed vertex)) :
    sample.endpoint =
      edgeArea
        (values (side.pieces (Fin.cast left.boundaryRows_eq 0)).leftColumn
          (side.pieces (Fin.cast left.boundaryRows_eq 0)).leftRow
          (side.pieces (Fin.cast left.boundaryRows_eq 0)).first)
        (values (side.pieces (Fin.cast left.boundaryRows_eq (Fin.last left.boundaryRows))).leftColumn
          (side.pieces (Fin.cast left.boundaryRows_eq (Fin.last left.boundaryRows))).leftRow
          (side.pieces (Fin.cast left.boundaryRows_eq (Fin.last left.boundaryRows))).last) := by
  rw [sample.endpoint_eq, readback, readback]
  have firstValue : trace.leftValue values (trace.vertices.indexed 0) =
      values (side.pieces (Fin.cast left.boundaryRows_eq 0)).leftColumn
        (side.pieces (Fin.cast left.boundaryRows_eq 0)).leftRow
        (side.pieces (Fin.cast left.boundaryRows_eq 0)).first := by
    unfold leftValue
    rw [trace.first_point, trace.first_index]
  have lastValue : trace.leftValue values (trace.vertices.indexed (Fin.last trace.vertices.rest.length)) =
      values (side.pieces (Fin.cast left.boundaryRows_eq (Fin.last left.boundaryRows))).leftColumn
        (side.pieces (Fin.cast left.boundaryRows_eq (Fin.last left.boundaryRows))).leftRow
        (side.pieces (Fin.cast left.boundaryRows_eq (Fin.last left.boundaryRows))).last := by
    unfold leftValue
    rw [trace.last_point, trace.last_index]
  rw [firstValue, lastValue]
  simp only [edgeArea, Stokes.PrimitivePoint.sub]
  ring1

/-- The retained sample endpoint term equals the chord between the original first and last right-owner values.

The supplied pointwise readback identifies the exact joined trace, preserving both extreme piece indices and their
original model-cell owners. -/
theorem
  right_endpoint
  (trace : side.Trace depth)
    (values : Fin (rightColumns + 1) → Fin (rightRows + 1) → Gaussian → PrimitivePoint)
    {readings : Fin (trace.vertices.rest.length + 1) → PrimitivePoint}
    (sample : Sample readings)
    (readback : ∀ vertex, readings vertex = trace.rightValue values (trace.vertices.indexed vertex)) :
    sample.endpoint =
      edgeArea
        (values (side.pieces (Fin.cast left.boundaryRows_eq 0)).rightColumn
          (side.pieces (Fin.cast left.boundaryRows_eq 0)).rightRow
          (side.pieces (Fin.cast left.boundaryRows_eq 0)).first)
        (values (side.pieces (Fin.cast left.boundaryRows_eq (Fin.last left.boundaryRows))).rightColumn
          (side.pieces (Fin.cast left.boundaryRows_eq (Fin.last left.boundaryRows))).rightRow
          (side.pieces (Fin.cast left.boundaryRows_eq (Fin.last left.boundaryRows))).last) := by
  rw [sample.endpoint_eq, readback, readback]
  have firstValue : trace.rightValue values (trace.vertices.indexed 0) =
      values (side.pieces (Fin.cast left.boundaryRows_eq 0)).rightColumn
        (side.pieces (Fin.cast left.boundaryRows_eq 0)).rightRow
        (side.pieces (Fin.cast left.boundaryRows_eq 0)).first := by
    unfold rightValue
    rw [trace.first_point, trace.first_index]
  have lastValue : trace.rightValue values (trace.vertices.indexed (Fin.last trace.vertices.rest.length)) =
      values (side.pieces (Fin.cast left.boundaryRows_eq (Fin.last left.boundaryRows))).rightColumn
        (side.pieces (Fin.cast left.boundaryRows_eq (Fin.last left.boundaryRows))).rightRow
        (side.pieces (Fin.cast left.boundaryRows_eq (Fin.last left.boundaryRows))).last := by
    unfold rightValue
    rw [trace.last_point, trace.last_index]
  rw [firstValue, lastValue]
  simp only [edgeArea, Stokes.PrimitivePoint.sub]
  ring1

end MatchedVerticalSide.Trace

end Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh
