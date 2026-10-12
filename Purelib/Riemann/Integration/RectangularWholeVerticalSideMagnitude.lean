module
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Readings.RectangularMatchedObservationSides

import Purelib.LinearAlgebra.Grid.Offsets
import Purelib.Topology.Grid.Signs
public import Purelib.Riemann.Paths.RectangularMatchedVerticalSideTrace
import Purelib.Riemann.Integration.RectangularPrimitiveOverlap
import Purelib.Riemann.Integration.RectangularPrimitiveMagnitude
import Purelib.Integration.Path.SuccessiveMagnitude
import Purelib.Tactic.Ring
public import Purelib.Riemann.Readings.RectangularSeamBounds

section

open Purelib.Riemann.Normalization.InverseRootPolynomial

public section

/-! Whole-side displacement pays each retained coarse segment and owner gap. -/
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry Bank Transitions)
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (RegionClearance PrimitiveOverlapBounds)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives)
open Purelib.Riemann.Integration.RectangularPrimitiveGluing (PrimitiveAnchors)
open Purelib.Riemann.Integration.RectangularPrimitiveAccuracy (GridPrimitiveAccuracy)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts)
open Purelib.Riemann.Meshes.RectangularObservationMesh (ObservationMesh)

variable {polynomial numerator : Polynomial} {ambient : Box} {clearance : RegionClearance polynomial ambient}
  {bounds : PrimitiveOverlapBounds clearance numerator} {columns rows : Nat} {target : Coordinate}
  {geometry : Geometry columns rows} {bank : Bank polynomial geometry}
  {leftColumns leftRows : Nat} {leftGeometry : Geometry leftColumns leftRows}
  {leftCuts : GridCuts leftGeometry} {rightCuts : GridCuts geometry} {leftBox rightBox : Box}
  {left : ObservationMesh leftCuts leftBox} {right : ObservationMesh rightCuts rightBox}
  {leftColumn : Fin left.partition.x.intervals.length} {rightColumn : Fin right.partition.x.intervals.length}
  {horizontal : Coordinate} {side :
    Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedVerticalSide left right
    leftColumn rightColumn horizontal} {depth : Nat}

open Purelib.Riemann.Readings.RectangularSeamBounds (boundarySlope)

namespace Purelib.Riemann.Integration.RectangularWholeVerticalSideMagnitude

/-- Cancel the intermediate Gaussian value in two successive differences. -/
private theorem cancel (a b c : Gaussian) : (a - b) + (b - c) = a - c := by ring1

end Purelib.Riemann.Integration.RectangularWholeVerticalSideMagnitude

namespace Purelib.Riemann.Integration.RectangularPrimitiveAccuracy.GridPrimitiveAccuracy

open Purelib.Riemann.Integration.RectangularWholeVerticalSideMagnitude (cancel)

open Purelib.Riemann in
open Purelib.Integration in
open Purelib.Topology in
open Purelib.Data in
open Purelib.LinearAlgebra in
/-- Bound displacement along an actual matched vertical side from its first retained piece.

The original global error is at most one and every owner box refines the clearance box. Local slope bounds and gaps
between successive owners give the squared coarse row count, independently of fine trace depth. -/
theorem matched_vertical_side_magnitude (request : GridPrimitiveAccuracy bounds columns target)
    {transitions : Transitions (bank.refine request.index)} {gauge : Grid.Signs.Gauge transitions.flatGrid}
    {primitives : Primitives (Branches.RectangularSheetGauge.Transitions.oriented transitions gauge) numerator} (anchors
      : PrimitiveAnchors primitives)
    (offsets : LinearAlgebra.Grid.Offsets anchors.edges) (refines : ∀ column row, (geometry.box column row).Refines
      ambient)
    (small : request.globalBound ≤ 1) (trace : side.Trace depth) (vertex : side.Vertex depth) :
    let origin := side.pieces (Fin.cast left.boundaryRows_eq 0)
    Gaussian.Basic.Canonical.normSq (anchors.alignedValue offsets (side.pieces vertex.1).rightColumn (side.pieces
      vertex.1).rightRow (trace.point vertex) -
      anchors.alignedValue offsets origin.rightColumn origin.rightRow origin.first) ≤
      2 * (boundarySlope bounds + (left.boundaryRows : Coordinate) ^ 2 * (2 * (4 + boundarySlope bounds))) := by
  let startValue := fun column : Fin (left.boundaryRows + 1) =>
    let piece := side.pieces (Fin.cast left.boundaryRows_eq column)
    anchors.alignedValue offsets piece.rightColumn piece.rightRow piece.first
  have slopeNonnegative : 0 ≤ boundarySlope bounds :=
    Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct bounds.numeratorUpper_nonnegative
      bounds.inverseUpper_positive.le)) ambient.diagonalSq_nonneg
  have increment (column : Fin (columns + 1)) (row : Fin (rows + 1)) {first last : Gaussian}
      (firstInside : (geometry.box column row).Contains first) (lastInside : (geometry.box column row).Contains last) :
      Gaussian.Basic.Canonical.normSq (anchors.alignedValue offsets column row last - anchors.alignedValue offsets
        column row first) ≤ boundarySlope bounds := by
    rw [show anchors.alignedValue offsets column row last -
        anchors.alignedValue offsets column row first =
        primitives.value column row last - primitives.value column row first by
      dsimp only [PrimitiveAnchors.alignedValue]
      ring1]
    exact primitives.local_increment_bound bounds refines column row firstInside lastInside
  have steps (column : Fin left.boundaryRows) :
      Gaussian.Basic.Canonical.normSq (startValue column.succ - startValue column.castSucc) ≤ 2 * (4 + boundarySlope
        bounds) := by
    let before := side.pieces (Fin.cast left.boundaryRows_eq column.castSucc)
    let after := side.pieces (Fin.cast left.boundaryRows_eq column.succ)
    have joined : before.last = after.first :=
      side.consecutive column.val (by rw [← left.boundaryRows_eq]; exact column.succ.isLt)
    have gap := request.overlap_bound anchors offsets refines after.rightColumn before.rightColumn after.rightRow
      before.rightRow
      after.rightFirst (joined ▸ before.rightLast)
    have gapLe : Gaussian.Basic.Canonical.normSq (anchors.alignedValue offsets after.rightColumn after.rightRow
      after.first -
        anchors.alignedValue offsets before.rightColumn before.rightRow before.last) ≤ 4 := by
      rw [joined]
      exact gap.trans ((Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct small (show (0 : Coordinate) ≤ 4
        by decide)).trans_eq (by ring1))
    have localLe := increment before.rightColumn before.rightRow before.rightFirst before.rightLast
    have estimate := (Gaussian.Norm.Bounds.normSq_add_le_two
      (anchors.alignedValue offsets after.rightColumn after.rightRow after.first - anchors.alignedValue offsets
        before.rightColumn before.rightRow before.last)
      (anchors.alignedValue offsets before.rightColumn before.rightRow before.last - anchors.alignedValue offsets
        before.rightColumn before.rightRow before.first))
    simp only [Gaussian.Norm.Basic.normSq_eq_canonical] at estimate
    have estimate := estimate.trans
      (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add gapLe localLe) (by decide))
    rw [cancel] at estimate
    exact estimate
  let column := Fin.cast left.boundaryRows_eq.symm vertex.1
  have origins := Path.SuccessiveMagnitude.successive_magnitude startValue
    (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct
      (by decide : (0 : Rat.Fraction.Rational) ≤ 2)
      (add_nonneg (by decide : (0 : Rat.Fraction.Rational) ≤ 4) slopeNonnegative))
    (fun index => by
      have scalar := steps index
      simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using scalar) column
  simp only [Gaussian.Norm.Basic.normSq_eq_canonical] at origins
  have localLe := increment (side.pieces vertex.1).rightColumn (side.pieces vertex.1).rightRow
    (side.pieces vertex.1).rightFirst ((trace.segments.get vertex.1).right_contains vertex.2)
  have estimate := (Gaussian.Norm.Bounds.normSq_add_le_two
    (anchors.alignedValue offsets (side.pieces vertex.1).rightColumn (side.pieces vertex.1).rightRow (trace.point
      vertex) - startValue column)
    (startValue column - startValue 0))
  simp only [Gaussian.Norm.Basic.normSq_eq_canonical] at estimate
  have estimate := estimate.trans (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add localLe
    origins) (by decide))
  rw [cancel] at estimate
  exact estimate

end Purelib.Riemann.Integration.RectangularPrimitiveAccuracy.GridPrimitiveAccuracy

namespace Purelib.Riemann.Integration.RectangularWholeVerticalSideMagnitude

open Purelib.Riemann in
open Purelib.Topology in
open Purelib.Data in
open Purelib.LinearAlgebra in
/-- Bound the cached right-owner readings along the matched vertical trace.

Exact vertex and initial-point readback transports the whole-side estimate to the retained reading array, with the
original coarse row count and primitive accuracy request. -/
theorem matched_vertical_readings_magnitude (request : GridPrimitiveAccuracy bounds columns target)
    {transitions : Transitions (bank.refine request.index)} {gauge : Grid.Signs.Gauge transitions.flatGrid}
    {primitives : Primitives (Branches.RectangularSheetGauge.Transitions.oriented transitions gauge) numerator} (anchors
      : PrimitiveAnchors primitives)
    (offsets : LinearAlgebra.Grid.Offsets anchors.edges) (refines : ∀ column row, (geometry.box column row).Refines
      ambient)
    (small : request.globalBound ≤ 1) (trace : side.Trace depth) (vertex : Fin (trace.vertices.rest.length + 1)) :
    Gaussian.Basic.Canonical.normSq ((trace.rightReadings anchors offsets).values vertex - (trace.rightReadings anchors
      offsets).values 0) ≤
      2 * (boundarySlope bounds + (left.boundaryRows : Coordinate) ^ 2 * (2 * (4 + boundarySlope bounds))) := by
  rw [trace.rightReadings_value, trace.rightReadings_value, trace.first_point, trace.first_index]
  exact request.matched_vertical_side_magnitude anchors offsets refines small trace (trace.vertices.indexed vertex)

end Purelib.Riemann.Integration.RectangularWholeVerticalSideMagnitude

end
