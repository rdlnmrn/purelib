module

import Purelib.Riemann.Integration.RectangularMatchedSideEndpoints
public import Purelib.Riemann.Paths.RectangularMatchedVerticalSideTrace
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Riemann.Readings.RectangularObservationAssembly
public import Purelib.Riemann.Paths.RectangularMatchedSideTrace
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Integration.Path.JoinedTrace
import Purelib.Riemann.Readings.RectangularMatchedObservationSides
import Purelib.Riemann.Paths.RectangularPairedSegments
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Data.Vector.Basic
import Purelib.Topology.Polygon.Stokes
import Purelib.Riemann.Paths.RectangularSegmentSplitting

@[expose] public section

/-! Canonical endpoint determinants of matched sides, independent of trace subdivision. -/
namespace Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh

open Purelib.Riemann.Normalization.InverseRootPolynomial (Box Gaussian Coordinate)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint edgeArea)
open Purelib.Integration.Path.JoinedTrace (VertexTrace)
open Purelib.Riemann.Periods.CenteredBilinearPath (Sample)
open Purelib.Riemann.Paths.RectangularDyadicPairedTrace (dyadicCount)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts)
open Purelib.Riemann.Meshes.RectangularObservationMesh (ObservationMesh)
open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh (MatchedHorizontalSide
  MatchedVerticalSide)

variable {leftColumns leftRows rightColumns rightRows : Nat}
  {leftGeometry : Geometry leftColumns leftRows} {rightGeometry : Geometry rightColumns rightRows}
  {leftCuts : GridCuts leftGeometry} {rightCuts : GridCuts rightGeometry} {leftBox rightBox : Box}
  {left : ObservationMesh leftCuts leftBox} {right : ObservationMesh rightCuts rightBox}

namespace MatchedHorizontalSide
variable {leftRow : Fin left.partition.y.intervals.length}
  {rightRow : Fin right.partition.y.intervals.length} {height : Coordinate}
  {side : MatchedHorizontalSide left right leftRow rightRow height} {depth : Nat}

/-- The chord area between the matched side's exact first and last left-owner primitive values. -/
def leftChord
  (side : MatchedHorizontalSide left right leftRow rightRow height)
    (values : Fin (leftColumns + 1) → Fin (leftRows + 1) → Gaussian → PrimitivePoint) : Gaussian :=
  edgeArea
    (values (side.pieces (Fin.cast left.boundaryColumns_eq 0)).leftColumn
      (side.pieces (Fin.cast left.boundaryColumns_eq 0)).leftRow
      (side.pieces (Fin.cast left.boundaryColumns_eq 0)).first)
    (values (side.pieces (Fin.cast left.boundaryColumns_eq (Fin.last left.boundaryColumns))).leftColumn
      (side.pieces (Fin.cast left.boundaryColumns_eq (Fin.last left.boundaryColumns))).leftRow
      (side.pieces (Fin.cast left.boundaryColumns_eq (Fin.last left.boundaryColumns))).last)

/-- The retained sample's endpoint term equals the original matched side's left chord. -/
theorem
  Trace.left_endpoint_eq_chord
  (trace : side.Trace depth)
    (values : Fin (leftColumns + 1) → Fin (leftRows + 1) → Gaussian → PrimitivePoint)
    {readings : Fin (trace.vertices.rest.length + 1) → PrimitivePoint}
    (sample : Sample readings)
    (readback : ∀ vertex, readings vertex = trace.leftValue values (trace.vertices.indexed vertex)) :
    sample.endpoint = side.leftChord values :=
  trace.left_endpoint values sample readback

/-- The chord area between the matched side's exact first and last right-owner primitive values. -/
def rightChord
  (side : MatchedHorizontalSide left right leftRow rightRow height)
    (values : Fin (rightColumns + 1) → Fin (rightRows + 1) → Gaussian → PrimitivePoint) : Gaussian :=
  edgeArea
    (values (side.pieces (Fin.cast left.boundaryColumns_eq 0)).rightColumn
      (side.pieces (Fin.cast left.boundaryColumns_eq 0)).rightRow
      (side.pieces (Fin.cast left.boundaryColumns_eq 0)).first)
    (values (side.pieces (Fin.cast left.boundaryColumns_eq (Fin.last left.boundaryColumns))).rightColumn
      (side.pieces (Fin.cast left.boundaryColumns_eq (Fin.last left.boundaryColumns))).rightRow
      (side.pieces (Fin.cast left.boundaryColumns_eq (Fin.last left.boundaryColumns))).last)

/-- The retained sample's endpoint term equals the original matched side's right chord. -/
theorem
  Trace.right_endpoint_eq_chord
  (trace : side.Trace depth)
    (values : Fin (rightColumns + 1) → Fin (rightRows + 1) → Gaussian → PrimitivePoint)
    {readings : Fin (trace.vertices.rest.length + 1) → PrimitivePoint}
    (sample : Sample readings)
    (readback : ∀ vertex, readings vertex = trace.rightValue values (trace.vertices.indexed vertex)) :
    sample.endpoint = side.rightChord values :=
  trace.right_endpoint values sample readback

end MatchedHorizontalSide

namespace MatchedVerticalSide
variable {leftColumn : Fin left.partition.x.intervals.length}
  {rightColumn : Fin right.partition.x.intervals.length} {horizontal : Coordinate}
  {side : MatchedVerticalSide left right leftColumn rightColumn horizontal} {depth : Nat}

/-- The chord area between the matched side's exact first and last left-owner primitive values. -/
def leftChord
  (side : MatchedVerticalSide left right leftColumn rightColumn horizontal)
    (values : Fin (leftColumns + 1) → Fin (leftRows + 1) → Gaussian → PrimitivePoint) : Gaussian :=
  edgeArea
    (values (side.pieces (Fin.cast left.boundaryRows_eq 0)).leftColumn
      (side.pieces (Fin.cast left.boundaryRows_eq 0)).leftRow
      (side.pieces (Fin.cast left.boundaryRows_eq 0)).first)
    (values (side.pieces (Fin.cast left.boundaryRows_eq (Fin.last left.boundaryRows))).leftColumn
      (side.pieces (Fin.cast left.boundaryRows_eq (Fin.last left.boundaryRows))).leftRow
      (side.pieces (Fin.cast left.boundaryRows_eq (Fin.last left.boundaryRows))).last)

/-- The retained sample's endpoint term equals the original matched side's left chord. -/
theorem
  Trace.left_endpoint_eq_chord
  (trace : side.Trace depth)
    (values : Fin (leftColumns + 1) → Fin (leftRows + 1) → Gaussian → PrimitivePoint)
    {readings : Fin (trace.vertices.rest.length + 1) → PrimitivePoint}
    (sample : Sample readings)
    (readback : ∀ vertex, readings vertex = trace.leftValue values (trace.vertices.indexed vertex)) :
    sample.endpoint = side.leftChord values :=
  trace.left_endpoint values sample readback

/-- The chord area between the matched side's exact first and last right-owner primitive values. -/
def rightChord
  (side : MatchedVerticalSide left right leftColumn rightColumn horizontal)
    (values : Fin (rightColumns + 1) → Fin (rightRows + 1) → Gaussian → PrimitivePoint) : Gaussian :=
  edgeArea
    (values (side.pieces (Fin.cast left.boundaryRows_eq 0)).rightColumn
      (side.pieces (Fin.cast left.boundaryRows_eq 0)).rightRow
      (side.pieces (Fin.cast left.boundaryRows_eq 0)).first)
    (values (side.pieces (Fin.cast left.boundaryRows_eq (Fin.last left.boundaryRows))).rightColumn
      (side.pieces (Fin.cast left.boundaryRows_eq (Fin.last left.boundaryRows))).rightRow
      (side.pieces (Fin.cast left.boundaryRows_eq (Fin.last left.boundaryRows))).last)

/-- The retained sample's endpoint term equals the original matched side's right chord. -/
theorem
  Trace.right_endpoint_eq_chord
  (trace : side.Trace depth)
    (values : Fin (rightColumns + 1) → Fin (rightRows + 1) → Gaussian → PrimitivePoint)
    {readings : Fin (trace.vertices.rest.length + 1) → PrimitivePoint}
    (sample : Sample readings)
    (readback : ∀ vertex, readings vertex = trace.rightValue values (trace.vertices.indexed vertex)) :
    sample.endpoint = side.rightChord values :=
  trace.right_endpoint values sample readback

end MatchedVerticalSide

end Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh
