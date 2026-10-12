module

import Purelib.Riemann.Integration.RectangularMatchedSideEndpoints
public import Purelib.Integration.Path.EndpointJump
import Purelib.Riemann.Readings.RectangularMatchedObservationSides
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Riemann.Paths.RectangularMatchedSideTrace
public import Purelib.Riemann.Paths.RectangularMatchedVerticalSideTrace

@[expose] public section

/-! Primitive jumps use the actual whole-side endpoints and retained owners. -/
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

/-- The horizontal whole-side primitive jump using the retained first and last owners.

The oriented area pairs the initial left/right discrepancy with the actual left-side total displacement. -/
def jump (side
  : MatchedHorizontalSide left right leftRow rightRow height)
    (leftValues : Fin (leftColumns + 1) → Fin (leftRows + 1) → Gaussian → PrimitivePoint)
    (rightValues : Fin (rightColumns + 1) → Fin (rightRows + 1) → Gaussian → PrimitivePoint) : Gaussian :=
  edgeArea
    ((leftValues (side.pieces (Fin.cast left.boundaryColumns_eq 0)).leftColumn
      (side.pieces (Fin.cast left.boundaryColumns_eq 0)).leftRow
      (side.pieces (Fin.cast left.boundaryColumns_eq 0)).first).sub (rightValues (side.pieces (Fin.cast
        left.boundaryColumns_eq 0)).rightColumn
      (side.pieces (Fin.cast left.boundaryColumns_eq 0)).rightRow
      (side.pieces (Fin.cast left.boundaryColumns_eq 0)).first))
    ((leftValues (side.pieces (Fin.cast left.boundaryColumns_eq (Fin.last left.boundaryColumns))).leftColumn
      (side.pieces (Fin.cast left.boundaryColumns_eq (Fin.last left.boundaryColumns))).leftRow
      (side.pieces (Fin.cast left.boundaryColumns_eq (Fin.last left.boundaryColumns))).last).sub (leftValues
        (side.pieces (Fin.cast left.boundaryColumns_eq 0)).leftColumn
      (side.pieces (Fin.cast left.boundaryColumns_eq 0)).leftRow
      (side.pieces (Fin.cast left.boundaryColumns_eq 0)).first))

open Purelib.Riemann in
/-- The sampled horizontal endpoint jump equals the retained whole-side jump.

Both sample readbacks identify the original whole-side endpoints and model owners. -/
theorem
  Trace.endpointJump_eq
  (trace : side.Trace depth)
    (leftValues : Fin (leftColumns + 1) → Fin (leftRows + 1) → Gaussian → PrimitivePoint)
    (rightValues : Fin (rightColumns + 1) → Fin (rightRows + 1) → Gaussian → PrimitivePoint)
    {leftReadings rightReadings : Fin (trace.vertices.rest.length + 1) → PrimitivePoint}
    (leftSample : Sample leftReadings) (rightSample : Sample rightReadings)
    (leftReadback : ∀ vertex, leftReadings vertex = trace.leftValue leftValues (trace.vertices.indexed vertex))
    (rightReadback : ∀ vertex, rightReadings vertex = trace.rightValue rightValues (trace.vertices.indexed vertex)) :
    leftSample.endpointJump rightSample = side.jump leftValues rightValues := by
  rw [Sample.endpointJump, leftSample.centered_eq, leftReadback, leftReadback, rightReadback]
  unfold Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedHorizontalSide.Trace.leftValue
    Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedHorizontalSide.Trace.rightValue
  rw [trace.first_point, trace.last_point, trace.first_index, trace.last_index]
  rfl

end MatchedHorizontalSide

namespace MatchedVerticalSide
variable {leftColumn : Fin left.partition.x.intervals.length}
  {rightColumn : Fin right.partition.x.intervals.length} {horizontal : Coordinate}
  {side : MatchedVerticalSide left right leftColumn rightColumn horizontal} {depth : Nat}

/-- The vertical whole-side primitive jump using the retained first and last owners.

The oriented area pairs the initial left/right discrepancy with the actual left-side total displacement. -/
def jump (side :
  MatchedVerticalSide left right leftColumn rightColumn horizontal)
    (leftValues : Fin (leftColumns + 1) → Fin (leftRows + 1) → Gaussian → PrimitivePoint)
    (rightValues : Fin (rightColumns + 1) → Fin (rightRows + 1) → Gaussian → PrimitivePoint) : Gaussian :=
  edgeArea
    ((leftValues (side.pieces (Fin.cast left.boundaryRows_eq 0)).leftColumn
      (side.pieces (Fin.cast left.boundaryRows_eq 0)).leftRow
      (side.pieces (Fin.cast left.boundaryRows_eq 0)).first).sub (rightValues (side.pieces (Fin.cast
        left.boundaryRows_eq 0)).rightColumn
      (side.pieces (Fin.cast left.boundaryRows_eq 0)).rightRow
      (side.pieces (Fin.cast left.boundaryRows_eq 0)).first))
    ((leftValues (side.pieces (Fin.cast left.boundaryRows_eq (Fin.last left.boundaryRows))).leftColumn
      (side.pieces (Fin.cast left.boundaryRows_eq (Fin.last left.boundaryRows))).leftRow
      (side.pieces (Fin.cast left.boundaryRows_eq (Fin.last left.boundaryRows))).last).sub (leftValues (side.pieces
        (Fin.cast left.boundaryRows_eq 0)).leftColumn
      (side.pieces (Fin.cast left.boundaryRows_eq 0)).leftRow
      (side.pieces (Fin.cast left.boundaryRows_eq 0)).first))

open Purelib.Riemann in
/-- The sampled vertical endpoint jump equals the retained whole-side jump.

Both sample readbacks identify the original whole-side endpoints and model owners. -/
theorem
  Trace.endpointJump_eq
  (trace : side.Trace depth)
    (leftValues : Fin (leftColumns + 1) → Fin (leftRows + 1) → Gaussian → PrimitivePoint)
    (rightValues : Fin (rightColumns + 1) → Fin (rightRows + 1) → Gaussian → PrimitivePoint)
    {leftReadings rightReadings : Fin (trace.vertices.rest.length + 1) → PrimitivePoint}
    (leftSample : Sample leftReadings) (rightSample : Sample rightReadings)
    (leftReadback : ∀ vertex, leftReadings vertex = trace.leftValue leftValues (trace.vertices.indexed vertex))
    (rightReadback : ∀ vertex, rightReadings vertex = trace.rightValue rightValues (trace.vertices.indexed vertex)) :
    leftSample.endpointJump rightSample = side.jump leftValues rightValues := by
  rw [Sample.endpointJump, leftSample.centered_eq, leftReadback, leftReadback, rightReadback]
  unfold Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedVerticalSide.Trace.leftValue
    Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedVerticalSide.Trace.rightValue
  rw [trace.first_point, trace.last_point, trace.first_index, trace.last_index]
  rfl

end MatchedVerticalSide

end Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh
