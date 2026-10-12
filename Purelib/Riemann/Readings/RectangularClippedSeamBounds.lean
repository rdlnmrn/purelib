module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Periods.BilinearGridBoundary

import Purelib.Integration.Polynomial.Rectangle.Boundary.Assembly
import Purelib.LinearAlgebra.Grid.Offsets
import Purelib.Topology.Grid.Signs
import Purelib.Riemann.Integration.RectangularClippedSeamGeometry
import Purelib.Riemann.Readings.RectangularPairedSeamBounds
import Purelib.Riemann.Readings.RectangularClippedCornerBounds
import Purelib.Tactic.Ring
public import Purelib.Riemann.Readings.RectangularSeamBounds
public import Purelib.Riemann.Readings.RectangularObservationAssembly

open Purelib.Riemann.Normalization.InverseRootPolynomial

open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (RegionClearance PrimitiveOverlapBounds)

open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry Bank Transitions)

open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives)

open Purelib.Riemann.Integration.RectangularPrimitiveGluing (PrimitiveAnchors)

open Purelib.Riemann.Integration.RectangularPrimitiveAccuracy (GridPrimitiveAccuracy)

open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts)

open Purelib.Riemann.Meshes.RectangularObservationMesh (ObservationMesh)

open Purelib.Riemann.Readings.RectangularObservationAssembly.ObservationMesh (ClippedAssembly)

open Purelib.Riemann.Readings.RectangularSeamBounds (boundarySlope)

@[expose] public section

/-! Corrected seam bounds for the actual retained clipped assembly. -/
namespace Purelib.Riemann.Readings.RectangularObservationAssembly.ObservationMesh

open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {polynomial firstNumerator secondNumerator : Polynomial} {ambient : Box}
  {clearance : RegionClearance polynomial ambient}
  {firstBounds : PrimitiveOverlapBounds clearance firstNumerator}
  {secondBounds : PrimitiveOverlapBounds clearance secondNumerator}
  {columns rows : Nat} {firstTarget secondTarget : Coordinate}
  {geometry : Geometry columns rows} {bank : Bank polynomial geometry}
  (firstRequest : GridPrimitiveAccuracy firstBounds columns firstTarget)
  (secondRequest : GridPrimitiveAccuracy secondBounds columns secondTarget)
  {firstTransitions : Transitions (bank.refine firstRequest.index)}
  {secondTransitions : Transitions (bank.refine secondRequest.index)}
  {firstGauge : Purelib.Topology.Grid.Signs.Gauge firstTransitions.flatGrid}
  {secondGauge : Purelib.Topology.Grid.Signs.Gauge secondTransitions.flatGrid}
  {firstPrimitives : Primitives (Purelib.Riemann.Branches.RectangularSheetGauge.Transitions.oriented firstTransitions
    firstGauge) firstNumerator}
  {secondPrimitives : Primitives (Purelib.Riemann.Branches.RectangularSheetGauge.Transitions.oriented secondTransitions
    secondGauge) secondNumerator}
  (firstAnchors : PrimitiveAnchors firstPrimitives) (secondAnchors : PrimitiveAnchors secondPrimitives)
  (firstOffsets : LinearAlgebra.Grid.Offsets firstAnchors.edges)
  (secondOffsets : LinearAlgebra.Grid.Offsets secondAnchors.edges)
  (refines : ∀ column row, (geometry.box column row).Refines ambient)

namespace ClippedAssembly

include refines

variable {cuts : GridCuts geometry} {box : Box} {mesh : ObservationMesh cuts box}
  (assembly : ClippedAssembly mesh (fun column row point =>
    ⟨firstAnchors.alignedValue firstOffsets column row point, secondAnchors.alignedValue secondOffsets column row
      point⟩))

section
open Purelib.Data.Gaussian.Norm
open Purelib.Integration.Polynomial.Rectangle.Boundary
open Purelib.Riemann
open Purelib.Riemann.Readings.RectangularPairedSeamBounds
/-- Bound a retained horizontal adjacency seam with its original endpoint correction.

Both primitive requests provide the overlap and slope bounds on the assembly's actual dyadic trace. -/
theorem horizontal_bound
  (column : Fin mesh.boundaryColumns) (row : Fin (mesh.boundaryRows + 1)) :
    Data.Gaussian.Norm.Basic.normSq (Assembly.horizontalSeam (fun column row => assembly.sides column row) column row -
      Periods.BilinearGridBoundary.horizontalEndpoint assembly.corners column row) ≤
      8 * max (4 * firstRequest.globalBound) (4 * secondRequest.globalBound) *
        (4 * max (boundarySlope firstBounds) (boundarySlope secondBounds) +
          max (4 * boundarySlope firstBounds) (4 * boundarySlope secondBounds)) := by
  rw [assembly.horizontal_eq_dyadic]
  have scalar := (GridPrimitiveAccuracy.paired_segment_trace_bounds firstRequest firstAnchors firstOffsets refines
    (mesh.horizontalSeamPiece column row)).paired_dyadic_bound
    (GridPrimitiveAccuracy.paired_segment_trace_bounds secondRequest secondAnchors secondOffsets refines
      (mesh.horizontalSeamPiece column row)) mesh.depth
  simpa only [Basic.normSq_eq_canonical] using scalar

/-- Bound a retained vertical adjacency seam with its original endpoint correction.

Both primitive requests provide the overlap and slope bounds on the assembly's actual dyadic trace. -/
theorem vertical_bound
  (column : Fin (mesh.boundaryColumns + 1)) (row : Fin mesh.boundaryRows) :
    Data.Gaussian.Norm.Basic.normSq (Assembly.verticalSeam (fun column row => assembly.sides column row) column row -
      Periods.BilinearGridBoundary.verticalEndpoint assembly.corners column row) ≤
      8 * max (4 * firstRequest.globalBound) (4 * secondRequest.globalBound) *
        (4 * max (boundarySlope firstBounds) (boundarySlope secondBounds) +
          max (4 * boundarySlope firstBounds) (4 * boundarySlope secondBounds)) := by
  rw [assembly.vertical_eq_dyadic]
  have scalar := (GridPrimitiveAccuracy.paired_segment_trace_bounds firstRequest firstAnchors firstOffsets refines
    (mesh.verticalSeamPiece column row)).paired_dyadic_bound
    (GridPrimitiveAccuracy.paired_segment_trace_bounds secondRequest secondAnchors secondOffsets refines
      (mesh.verticalSeamPiece column row)) mesh.depth
  simpa only [Basic.normSq_eq_canonical] using scalar

end

open Purelib.Algebra in
open Purelib.Data.Gaussian.Norm in
open Purelib.Data.Gaussian.Norm.Sum in
open Purelib.Data.Rat.Fraction.Order in
open Purelib.Integration.Polynomial.Rectangle.Boundary in
open Purelib.Riemann in
/-- Pay all corrected seams using the assembly's retained horizontal and vertical seam counts.

The estimate uses both original global errors and boundary slopes and applies at the assembly's actual fine depth. -/
theorem seams_bound :
    let seam := 8 * max (4 * firstRequest.globalBound) (4 * secondRequest.globalBound) *
        (4 * max (boundarySlope firstBounds) (boundarySlope secondBounds) +
          max (4 * boundarySlope firstBounds) (4 * boundarySlope secondBounds))
    Data.Gaussian.Norm.Basic.normSq assembly.seams ≤
      2 * ((mesh.boundaryColumns : Coordinate) ^ 2 * ((mesh.boundaryRows + 1 : Nat) : Coordinate) ^ 2 +
        ((mesh.boundaryColumns + 1 : Nat) : Coordinate) ^ 2 * (mesh.boundaryRows : Coordinate) ^ 2) * seam := by
  dsimp only
  have horizontal := Indexed.normSq_sumFin_le
    (fun column => FiniteSum.Fin.sumFin (fun row =>
      Assembly.horizontalSeam (fun column row => assembly.sides column row) column row -
        Periods.BilinearGridBoundary.horizontalEndpoint assembly.corners column row))
    (((mesh.boundaryRows + 1 : Nat) : Coordinate) ^ 2 * (8 * max (4 * firstRequest.globalBound) (4 *
      secondRequest.globalBound) *
        (4 * max (boundarySlope firstBounds) (boundarySlope secondBounds) +
          max (4 * boundarySlope firstBounds) (4 * boundarySlope secondBounds))))
    (fun column => Indexed.normSq_sumFin_le _ _
      (assembly.horizontal_bound firstRequest secondRequest firstAnchors secondAnchors firstOffsets secondOffsets
        refines column))
  have vertical := Indexed.normSq_sumFin_le
    (fun column => FiniteSum.Fin.sumFin (fun row =>
      Assembly.verticalSeam (fun column row => assembly.sides column row) column row -
        Periods.BilinearGridBoundary.verticalEndpoint assembly.corners column row))
    ((mesh.boundaryRows : Coordinate) ^ 2 * (8 * max (4 * firstRequest.globalBound) (4 * secondRequest.globalBound) *
        (4 * max (boundarySlope firstBounds) (boundarySlope secondBounds) +
          max (4 * boundarySlope firstBounds) (4 * boundarySlope secondBounds))))
    (fun column => Indexed.normSq_sumFin_le _ _
      (assembly.vertical_bound firstRequest secondRequest firstAnchors secondAnchors firstOffsets secondOffsets refines
        column))
  rw [assembly.seams_eq, Periods.BilinearGridBoundary.correctedSeamSum]
  exact (Bounds.normSq_add_le_two _ _).trans
    ((Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add horizontal vertical)
      (by decide)).trans_eq (by ring1))

open Purelib.Data.Gaussian.Norm in
open Purelib.Data.Rat.Fraction.Order in
/-- Bound the local-to-exterior paired area discrepancy of the retained clipped assembly.

Its exact decomposition combines corrected seam sums and junction corner polygons, preserving the coarse count factors
and both original primitive requests. -/
theorem
  local_sub_exterior_bound
  :
    let seam := 8 * max (4 * firstRequest.globalBound) (4 * secondRequest.globalBound) *
        (4 * max (boundarySlope firstBounds) (boundarySlope secondBounds) +
          max (4 * boundarySlope firstBounds) (4 * boundarySlope secondBounds))
    Data.Gaussian.Norm.Basic.normSq (assembly.localTotal - assembly.exterior) ≤
      4 * ((mesh.boundaryColumns : Coordinate) ^ 2 * ((mesh.boundaryRows + 1 : Nat) : Coordinate) ^ 2 +
        ((mesh.boundaryColumns + 1 : Nat) : Coordinate) ^ 2 * (mesh.boundaryRows : Coordinate) ^ 2) * seam +
      512 * ((mesh.boundaryColumns : Coordinate) * (mesh.boundaryRows : Coordinate)) ^ 2 *
        (max firstRequest.globalBound secondRequest.globalBound) ^ 2 := by
  dsimp only
  rw [assembly.decomposition, show assembly.exterior + assembly.seams + assembly.cornerTotal - assembly.exterior =
    assembly.seams + assembly.cornerTotal by ring1]
  exact (Bounds.normSq_add_le_two _ _).trans
    ((Arithmetic.mul_le_mul_of_nonneg_left_direct
      (add_le_add (assembly.seams_bound firstRequest secondRequest firstAnchors secondAnchors firstOffsets secondOffsets
        refines)
        (assembly.cornerTotal_bound firstRequest secondRequest firstAnchors secondAnchors firstOffsets secondOffsets
          refines))
      (by decide)).trans_eq (by ring1))

end ClippedAssembly
end Purelib.Riemann.Readings.RectangularObservationAssembly.ObservationMesh
