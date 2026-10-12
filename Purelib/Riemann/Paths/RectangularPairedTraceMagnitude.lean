module
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Riemann.Readings.PrimitiveAreaBounds

import Purelib.LinearAlgebra.Grid.Offsets
public import Purelib.Riemann.Integration.RectangularPairedPointBanks
import Purelib.Riemann.Integration.RectangularPrimitiveMagnitude
public import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Tactic.Ring
public import Purelib.Riemann.Readings.RectangularSeamBounds

@[expose] public section

/-! The shared two-grid trace supplies its own reference magnitude through
the retained right-cell owner and the fixed ambient derivative ceiling. -/
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
namespace Purelib.Riemann.Paths.RectangularPairedTraceMagnitude

open Purelib.Riemann.Readings.RectangularSeamBounds (boundarySlope)

open Purelib.Riemann.Normalization.InverseRootPolynomial
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Riemann.Normalization.RectangularInverseModels (Bank)
open Purelib.Riemann.Paths.RectangularPairedSegments (PairedSegmentPiece)
open Purelib.Riemann.Integration.RectangularPairedPointBanks (Trace)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives)
open Purelib.Riemann.Integration.RectangularPrimitiveGluing (PrimitiveAnchors)
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (RegionClearance PrimitiveOverlapBounds)
open Purelib.Riemann.Periods.CenteredBilinearPath (Sample)

variable {leftColumns leftRows rightColumns rightRows : Nat}
  {leftGeometry : Geometry leftColumns leftRows} {rightGeometry : Geometry rightColumns rightRows}
  {piece : PairedSegmentPiece leftGeometry rightGeometry} {count : Nat}

open Purelib.Riemann in
open Purelib.Data in
open Purelib.LinearAlgebra in
/-- Bound a retained right-owner reading relative to the trace's initial reading.

All actual trace points lie in the same right model cell. The original ambient clearance and refinement certificate give
its uniform boundary-slope ceiling. -/
theorem right_increment_bound (trace : Trace piece count)
    {polynomial numerator : Polynomial} {ambient : Box} {clearance : RegionClearance polynomial ambient}
    {models : Bank polynomial rightGeometry} {primitives : Primitives models numerator}
    (anchors : PrimitiveAnchors primitives) (offsets : LinearAlgebra.Grid.Offsets anchors.edges)
    (bounds : PrimitiveOverlapBounds clearance numerator)
    (refines : ∀ column row, (rightGeometry.box column row).Refines ambient) (vertex : Fin (count + 1)) :
    Data.Gaussian.Norm.Basic.normSq ((trace.rightReadings anchors offsets).values vertex - (trace.rightReadings
      anchors offsets).values 0) ≤
      boundarySlope bounds := by
  rw [trace.rightReadings_value, trace.rightReadings_value]
  have equal : anchors.alignedValue offsets piece.rightColumn piece.rightRow (trace.points vertex) -
      anchors.alignedValue offsets piece.rightColumn piece.rightRow (trace.points 0) =
      primitives.value piece.rightColumn piece.rightRow (trace.points vertex) -
        primitives.value piece.rightColumn piece.rightRow (trace.points 0) := by
    simp only [PrimitiveAnchors.alignedValue]
    ring1
  rw [equal]
  have scalar := Integration.RectangularPrimitiveModels.Primitives.local_increment_bound
    primitives bounds refines piece.rightColumn piece.rightRow
    (trace.right_contains 0) (trace.right_contains vertex)
  simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using scalar

open Purelib.Data.Rat in
open Purelib.Riemann in
open Purelib.Topology in
open Purelib.Data in
open Purelib.LinearAlgebra in
/-- Bound both centered right-owner primitive readings on the retained paired trace.

The actual sample is centered at its original first reading; the maximum of the two original derivative ceilings bounds
both components at every retained vertex. -/
theorem paired_right_bound (trace : Trace piece count)
    {polynomial firstNumerator secondNumerator : Polynomial} {ambient : Box} {clearance : RegionClearance polynomial
      ambient}
    {firstModels secondModels : Bank polynomial rightGeometry}
    {firstPrimitives : Primitives firstModels firstNumerator} {secondPrimitives : Primitives secondModels
      secondNumerator}
    (firstAnchors : PrimitiveAnchors firstPrimitives) (firstOffsets : LinearAlgebra.Grid.Offsets firstAnchors.edges)
    (secondAnchors : PrimitiveAnchors secondPrimitives) (secondOffsets : LinearAlgebra.Grid.Offsets secondAnchors.edges)
    (firstBounds : PrimitiveOverlapBounds clearance firstNumerator) (secondBounds : PrimitiveOverlapBounds clearance
      secondNumerator)
    (refines : ∀ column row, (rightGeometry.box column row).Refines ambient)
    (sample : Sample (fun vertex =>
      ⟨(trace.rightReadings firstAnchors firstOffsets).values vertex,
        (trace.rightReadings secondAnchors secondOffsets).values vertex⟩)) (vertex : Fin (count + 1)) :
    Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded
      (sample.centered vertex) (max (boundarySlope firstBounds) (boundarySlope secondBounds)) := by
  rw [sample.centered_eq]
  constructor
  · have scalar := (right_increment_bound trace firstAnchors firstOffsets firstBounds refines vertex).trans
      (Fraction.Order.Basic.le_max_left (boundarySlope firstBounds) (boundarySlope secondBounds))
    simpa only [Gaussian.Norm.Basic.normSq_eq_canonical, Polygon.Stokes.PrimitivePoint.sub] using scalar
  · have scalar := (right_increment_bound trace secondAnchors secondOffsets secondBounds refines vertex).trans
      (Fraction.Order.Basic.le_max_right (boundarySlope firstBounds) (boundarySlope secondBounds))
    simpa only [Gaussian.Norm.Basic.normSq_eq_canonical, Polygon.Stokes.PrimitivePoint.sub] using scalar

end Purelib.Riemann.Paths.RectangularPairedTraceMagnitude
