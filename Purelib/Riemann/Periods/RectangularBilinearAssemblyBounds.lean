module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Periods.RectangularBilinearCorners

import Purelib.LinearAlgebra.Grid.Offsets
import Purelib.Topology.Grid.Signs
import Purelib.Riemann.Paths.RectangularSeamTraceBounds
public import Purelib.Riemann.Periods.RectangularBilinearBoundaryAssembly
import Purelib.Tactic.Ring
public import Purelib.Riemann.Readings.RectangularSeamBounds

open Purelib.Riemann.Normalization.InverseRootPolynomial

@[expose] public section

section

open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (RegionClearance PrimitiveOverlapBounds)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry Bank Transitions)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives)
open Purelib.Riemann.Integration.RectangularPrimitiveGluing (PrimitiveAnchors)
open Purelib.Riemann.Integration.RectangularPrimitiveAccuracy (GridPrimitiveAccuracy)
open Purelib.Riemann.Readings.RectangularSeamBounds (boundarySlope)

with_weak_namespace _root_.Purelib.Riemann.Periods.RectangularBilinearAssemblyBounds
  open Purelib.Data in
  /-- The exact rational carrier of the retained bilinear assembly bounds. -/
  private abbrev Coordinate := Rat.Fraction.Rational

open Purelib

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

open Purelib.Riemann.Periods.RectangularBilinearBoundaryAssembly (BilinearBoundaryAssembly)
open Purelib.Riemann.Paths.RectangularSeamTraceBounds (SeamTraceBounds)

section

include refines

variable {depth : Nat}
  (assembly : BilinearBoundaryAssembly firstAnchors firstOffsets secondAnchors secondOffsets depth)

section
open Purelib.Data.Gaussian.Norm
open Purelib.Riemann.Paths.RectangularSeamTraceBounds

namespace Purelib.Riemann.Periods.RectangularBilinearAssemblyBounds.BilinearBoundaryAssembly

/-- Bound one horizontal bilinear seam correction by the two retained primitive requests. -/
theorem horizontal_bound (column : Fin columns) (row : Fin (rows + 1)) :
    Data.Gaussian.Norm.Basic.normSq (assembly.horizontalCorrections column row) ≤
      8 * max firstRequest.globalBound secondRequest.globalBound *
        (4 * max (boundarySlope firstBounds) (boundarySlope secondBounds) +
          max firstRequest.edgeBound secondRequest.edgeBound) := by
  rw [assembly.horizontalCorrection_eq_dyadic]
  have scalar := (GridPrimitiveAccuracy.horizontal_trace_bounds firstRequest firstAnchors firstOffsets refines column
    row).paired_dyadic_bound
    (GridPrimitiveAccuracy.horizontal_trace_bounds secondRequest secondAnchors secondOffsets refines column row) depth
  simpa only [Basic.normSq_eq_canonical] using scalar

/-- Bound one vertical bilinear seam correction by the two retained primitive requests. -/
theorem vertical_bound (column : Fin (columns + 1)) (row : Fin rows) :
    Data.Gaussian.Norm.Basic.normSq (assembly.verticalCorrections column row) ≤
      8 * max firstRequest.globalBound secondRequest.globalBound *
        (4 * max (boundarySlope firstBounds) (boundarySlope secondBounds) +
          max firstRequest.edgeBound secondRequest.edgeBound) := by
  rw [assembly.verticalCorrection_eq_dyadic]
  have scalar := (GridPrimitiveAccuracy.vertical_trace_bounds firstRequest firstAnchors firstOffsets refines column
    row).paired_dyadic_bound
    (GridPrimitiveAccuracy.vertical_trace_bounds secondRequest secondAnchors secondOffsets refines column row) depth
  simpa only [Basic.normSq_eq_canonical] using scalar

end Purelib.Riemann.Periods.RectangularBilinearAssemblyBounds.BilinearBoundaryAssembly

end

namespace Purelib.Riemann.Periods.RectangularBilinearAssemblyBounds.BilinearBoundaryAssembly

open Purelib.Data.Gaussian.Norm in
open Purelib.Riemann.Periods.RectangularBilinearCorners in
/-- Bound the total paired corner correction by the squared grid count and common global error. -/
theorem corner_bound :
    Data.Gaussian.Norm.Basic.normSq assembly.cornerTotal ≤
      64 * ((columns : Coordinate) * (rows : Coordinate)) ^ 2 *
        (max firstRequest.globalBound secondRequest.globalBound) ^ 2 := by
  rw [assembly.cornerTotal_eq, assembly.corners_eq]
  have scalar := (GridPrimitiveAccuracy.corner_differences firstRequest assembly.firstCorners
    refines).paired_total_bound
    (GridPrimitiveAccuracy.corner_differences secondRequest assembly.secondCorners refines)
  simpa only [Basic.normSq_eq_canonical] using scalar

end Purelib.Riemann.Periods.RectangularBilinearAssemblyBounds.BilinearBoundaryAssembly

namespace Purelib.Riemann.Periods.RectangularBilinearBoundaryAssembly.BilinearBoundaryAssembly

open Purelib.Algebra in
open Purelib.Data.Gaussian.Norm in
open Purelib.Data.Gaussian.Norm.Sum in
open Purelib.Data.Rat.Fraction.Order in
/-- Bound the complete difference between local bilinear area and the exterior reading.

The two retained primitive requests pay horizontal seams, vertical seams and corners with their actual rectangular grid
counts and common slope bounds. -/
theorem
  local_sub_exterior_bound :
    let seam := 8 * max firstRequest.globalBound secondRequest.globalBound *
      (4 * max (boundarySlope firstBounds) (boundarySlope secondBounds) +
        max firstRequest.edgeBound secondRequest.edgeBound)
    Data.Gaussian.Norm.Basic.normSq (assembly.localTotal - assembly.exterior) ≤
      4 * ((columns : Coordinate) ^ 2 * ((rows + 1 : Nat) : Coordinate) ^ 2 +
        ((columns + 1 : Nat) : Coordinate) ^ 2 * (rows : Coordinate) ^ 2) * seam +
      128 * ((columns : Coordinate) * (rows : Coordinate)) ^ 2 *
        (max firstRequest.globalBound secondRequest.globalBound) ^ 2 := by
  dsimp only
  have horizontal := Indexed.normSq_sumFin_le
    (fun column => FiniteSum.Fin.sumFin (fun row => assembly.horizontalCorrections column row))
    (((rows + 1 : Nat) : RectangularBilinearAssemblyBounds.Coordinate) ^ 2 *
      (8 * max firstRequest.globalBound secondRequest.globalBound *
        (4 * max (boundarySlope firstBounds) (boundarySlope secondBounds) +
          max firstRequest.edgeBound secondRequest.edgeBound)))
    (fun column => Indexed.normSq_sumFin_le _ _
      (RectangularBilinearAssemblyBounds.BilinearBoundaryAssembly.horizontal_bound
        firstRequest secondRequest firstAnchors secondAnchors firstOffsets secondOffsets refines
        assembly column))
  have vertical := Indexed.normSq_sumFin_le
    (fun column => FiniteSum.Fin.sumFin (fun row => assembly.verticalCorrections column row))
    ((rows : RectangularBilinearAssemblyBounds.Coordinate) ^ 2 *
      (8 * max firstRequest.globalBound secondRequest.globalBound *
        (4 * max (boundarySlope firstBounds) (boundarySlope secondBounds) +
          max firstRequest.edgeBound secondRequest.edgeBound)))
    (fun column => Indexed.normSq_sumFin_le _ _
      (RectangularBilinearAssemblyBounds.BilinearBoundaryAssembly.vertical_bound
        firstRequest secondRequest firstAnchors secondAnchors firstOffsets secondOffsets refines assembly column))
  have seam := Bounds.normSq_add_le_two
    (FiniteSum.Fin.sumFin (fun column => FiniteSum.Fin.sumFin (fun row => assembly.horizontalCorrections column row)))
    (FiniteSum.Fin.sumFin (fun column => FiniteSum.Fin.sumFin (fun row => assembly.verticalCorrections column row)))
  have seamBound := seam.trans (Arithmetic.mul_le_mul_of_nonneg_left_direct
    (add_le_add horizontal vertical) (by decide))
  rw [← assembly.seamTotal_eq_sum] at seamBound
  rw [assembly.decomposition]
  exact (Bounds.normSq_add_le_two _ _).trans
    ((Arithmetic.mul_le_mul_of_nonneg_left_direct
      (add_le_add seamBound (RectangularBilinearAssemblyBounds.BilinearBoundaryAssembly.corner_bound
        firstRequest secondRequest firstAnchors secondAnchors firstOffsets
        secondOffsets refines assembly))
      (by decide)).trans_eq (by ring1))

end Purelib.Riemann.Periods.RectangularBilinearBoundaryAssembly.BilinearBoundaryAssembly

end
end
