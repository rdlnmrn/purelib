module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Riemann.Paths.RectangularConjugateSeamTrace
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Paths.RectangularSeamTraceBounds
import Purelib.Riemann.Periods.BilinearGridBoundary

import Purelib.Integration.Polynomial.Rectangle.Boundary.Assembly
import Purelib.LinearAlgebra.Grid.Offsets
import Purelib.Topology.Grid.Signs
import Purelib.Riemann.Integration.RectangularClippedConjugateCorners
import Purelib.Riemann.Integration.RectangularClippedSeamGeometry
import Purelib.Riemann.Readings.RectangularPairedSeamBounds
import Purelib.Tactic.Ring
public import Purelib.Riemann.Readings.RectangularSeamBounds
public import Purelib.Riemann.Readings.RectangularObservationAssembly

@[expose] public section

/-! Corrected energy seams retain their endpoint and corner terms. The
conjugate component obeys the same finite trace bounds at every depth. -/
namespace Purelib.Riemann.Integration.RectangularClippedConjugateSeams

open Purelib.Riemann.Readings.RectangularSeamBounds (boundarySlope)

open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (RegionClearance PrimitiveOverlapBounds)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry Bank Transitions)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives)
open Purelib.Riemann.Integration.RectangularPrimitiveGluing (PrimitiveAnchors)
open Purelib.Riemann.Integration.RectangularPrimitiveAccuracy (GridPrimitiveAccuracy)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts)
open Purelib.Riemann.Meshes.RectangularObservationMesh (ObservationMesh)
open Purelib.Riemann.Readings.RectangularObservationAssembly.ObservationMesh (ClippedAssembly)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open _root_.Purelib.Data.Gaussian.Basic (conj)

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

namespace ObservationMesh.ClippedAssembly

include refines

variable {cuts : GridCuts geometry} {box : Box} {mesh : ObservationMesh cuts box}
  (assembly : ClippedAssembly mesh (fun column row point =>
    ⟨conj (firstAnchors.alignedValue firstOffsets column row point), secondAnchors.alignedValue secondOffsets column row
      point⟩))

section
open Purelib.Riemann
open Purelib.Integration
open Purelib.Data
/-- Bound the actual corrected horizontal conjugate seam with its endpoint term retained.

The original two primitive requests supply overlap and increment bounds on the same retained seam segment at the
assembly's actual depth. -/
theorem conjugate_horizontal_bound (column : Fin mesh.boundaryColumns) (row : Fin (mesh.boundaryRows + 1)) :
    Data.Gaussian.Norm.Basic.normSq (Polynomial.Rectangle.Boundary.Assembly.horizontalSeam (fun column row =>
      assembly.sides column row) column row -
      Periods.BilinearGridBoundary.horizontalEndpoint assembly.corners column row) ≤
      8 * max (4 * firstRequest.globalBound) (4 * secondRequest.globalBound) *
        (4 * max (boundarySlope firstBounds) (boundarySlope secondBounds) +
          max (4 * boundarySlope firstBounds) (4 * boundarySlope secondBounds)) := by
  rw [assembly.horizontal_eq_dyadic]
  have scalar := Paths.RectangularSeamTraceBounds.SeamTraceBounds.paired_dyadic_bound
    (Paths.RectangularConjugateSeamTrace.SeamTraceBounds.conjugated
      (Readings.RectangularPairedSeamBounds.GridPrimitiveAccuracy.paired_segment_trace_bounds firstRequest firstAnchors
        firstOffsets refines
        (mesh.horizontalSeamPiece column row)))
    (Readings.RectangularPairedSeamBounds.GridPrimitiveAccuracy.paired_segment_trace_bounds secondRequest secondAnchors
      secondOffsets refines
      (mesh.horizontalSeamPiece column row)) mesh.depth
  dsimp only [Gaussian.Basic.Canonical.conj, Data.Gaussian.Basic.conj] at scalar ⊢
  simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using scalar

/-- Bound the actual corrected vertical conjugate seam with its endpoint term retained.

The original two primitive requests supply overlap and increment bounds on the same retained seam segment at the
assembly's actual depth. -/
theorem conjugate_vertical_bound (column : Fin (mesh.boundaryColumns + 1)) (row : Fin mesh.boundaryRows) :
    Data.Gaussian.Norm.Basic.normSq (Polynomial.Rectangle.Boundary.Assembly.verticalSeam (fun column row =>
      assembly.sides column row) column row -
      Periods.BilinearGridBoundary.verticalEndpoint assembly.corners column row) ≤
      8 * max (4 * firstRequest.globalBound) (4 * secondRequest.globalBound) *
        (4 * max (boundarySlope firstBounds) (boundarySlope secondBounds) +
          max (4 * boundarySlope firstBounds) (4 * boundarySlope secondBounds)) := by
  rw [assembly.vertical_eq_dyadic]
  have scalar := Paths.RectangularSeamTraceBounds.SeamTraceBounds.paired_dyadic_bound
    (Paths.RectangularConjugateSeamTrace.SeamTraceBounds.conjugated
      (Readings.RectangularPairedSeamBounds.GridPrimitiveAccuracy.paired_segment_trace_bounds firstRequest firstAnchors
        firstOffsets refines
        (mesh.verticalSeamPiece column row)))
    (Readings.RectangularPairedSeamBounds.GridPrimitiveAccuracy.paired_segment_trace_bounds secondRequest secondAnchors
      secondOffsets refines
      (mesh.verticalSeamPiece column row)) mesh.depth
  dsimp only [Gaussian.Basic.Canonical.conj, Data.Gaussian.Basic.conj] at scalar ⊢
  simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using scalar

end

open Purelib.Algebra in
open Purelib.Riemann in
open Purelib.Integration in
open Purelib.Data in
/-- Pay the complete corrected conjugate seam sum using the retained horizontal and vertical seam counts.

Both original global errors and boundary slopes remain explicit; the same estimate applies at every fine dyadic depth.
-/
theorem conjugate_seams_bound :
    let seam := 8 * max (4 * firstRequest.globalBound) (4 * secondRequest.globalBound) *
        (4 * max (boundarySlope firstBounds) (boundarySlope secondBounds) +
          max (4 * boundarySlope firstBounds) (4 * boundarySlope secondBounds))
    Data.Gaussian.Norm.Basic.normSq assembly.seams ≤
      2 * ((mesh.boundaryColumns : Coordinate) ^ 2 * ((mesh.boundaryRows + 1 : Nat) : Coordinate) ^ 2 +
        ((mesh.boundaryColumns + 1 : Nat) : Coordinate) ^ 2 * (mesh.boundaryRows : Coordinate) ^ 2) * seam := by
  dsimp only
  have horizontal := Gaussian.Norm.Sum.Indexed.normSq_sumFin_le
    (fun column => FiniteSum.Fin.sumFin (fun row =>
      Polynomial.Rectangle.Boundary.Assembly.horizontalSeam (fun column row => assembly.sides column row) column row -
        Periods.BilinearGridBoundary.horizontalEndpoint assembly.corners column row))
    (((mesh.boundaryRows + 1 : Nat) : Coordinate) ^ 2 * (8 * max (4 * firstRequest.globalBound) (4 *
      secondRequest.globalBound) *
        (4 * max (boundarySlope firstBounds) (boundarySlope secondBounds) +
          max (4 * boundarySlope firstBounds) (4 * boundarySlope secondBounds))))
    (fun column => Gaussian.Norm.Sum.Indexed.normSq_sumFin_le _ _
      (Integration.RectangularClippedConjugateSeams.ObservationMesh.ClippedAssembly.conjugate_horizontal_bound
        firstRequest secondRequest firstAnchors secondAnchors firstOffsets secondOffsets refines assembly column))
  have vertical := Gaussian.Norm.Sum.Indexed.normSq_sumFin_le
    (fun column => FiniteSum.Fin.sumFin (fun row =>
      Polynomial.Rectangle.Boundary.Assembly.verticalSeam (fun column row => assembly.sides column row) column row -
        Periods.BilinearGridBoundary.verticalEndpoint assembly.corners column row))
    ((mesh.boundaryRows : Coordinate) ^ 2 * (8 * max (4 * firstRequest.globalBound) (4 * secondRequest.globalBound) *
        (4 * max (boundarySlope firstBounds) (boundarySlope secondBounds) +
          max (4 * boundarySlope firstBounds) (4 * boundarySlope secondBounds))))
    (fun column => Gaussian.Norm.Sum.Indexed.normSq_sumFin_le _ _
      (Integration.RectangularClippedConjugateSeams.ObservationMesh.ClippedAssembly.conjugate_vertical_bound
        firstRequest secondRequest firstAnchors secondAnchors firstOffsets secondOffsets refines assembly column))
  rw [assembly.seams_eq, Periods.BilinearGridBoundary.correctedSeamSum]
  exact (Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
    ((Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add horizontal vertical)
      (by decide)).trans_eq (by ring1))

open Purelib.Riemann in
open Purelib.Data in
/-- Bound the complete local-to-exterior conjugate area discrepancy.

The retained assembly decomposition combines corrected seams and corner polygons with their exact coarse count factors
and original primitive-request bounds. -/
theorem conjugate_local_sub_exterior_bound :
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
  exact (Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
    ((Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (add_le_add (Integration.RectangularClippedConjugateSeams.ObservationMesh.ClippedAssembly.conjugate_seams_bound
        firstRequest secondRequest firstAnchors secondAnchors firstOffsets secondOffsets refines assembly)
        (Integration.RectangularClippedConjugateCorners.ObservationMesh.ClippedAssembly.conjugate_cornerTotal_bound
          firstRequest secondRequest firstAnchors secondAnchors firstOffsets secondOffsets refines assembly))
      (by decide)).trans_eq (by ring1))

end ObservationMesh.ClippedAssembly
end Purelib.Riemann.Integration.RectangularClippedConjugateSeams
