module
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Periods.BilinearGridBoundary
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps

import Purelib.LinearAlgebra.Grid.Offsets
import Purelib.Topology.Grid.Signs
import Purelib.Riemann.Integration.RectangularClippedCornerGeometry
import Purelib.Riemann.Integration.RectangularPrimitiveOverlap
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Riemann.Integration.RectangularPrimitiveModels
public import Purelib.Riemann.Integration.RectangularPrimitiveAccuracy
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Data.Vector.Basic
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

public section

/-! Actual clipped corner polygons are controlled by the retained primitive
overlap requests, including corners introduced by foreign model-grid cuts. -/
section

section

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
  (firstOffsets : Purelib.LinearAlgebra.Grid.Offsets firstAnchors.edges)
  (secondOffsets : Purelib.LinearAlgebra.Grid.Offsets secondAnchors.edges)
  (refines : ∀ column row, (geometry.box column row).Refines ambient)

namespace Purelib.Riemann.Readings.RectangularObservationAssembly.ObservationMesh.ClippedAssembly

include refines

variable {cuts : GridCuts geometry} {box : Box} {mesh : ObservationMesh cuts box}
  (assembly : ClippedAssembly mesh (fun column row point =>
    ⟨firstAnchors.alignedValue firstOffsets column row point, secondAnchors.alignedValue secondOffsets column row
      point⟩))

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Riemann.Integration in
open Purelib.Riemann.Periods in
open Purelib.Riemann.Readings in
open Purelib.Topology.Polygon in
/-- Bound an original clipped interior corner by the two retained primitive-request allowances.

The actual mesh junction owner and its containment identify both primitive comparisons; the resulting squared corner
norm is at most 256 times the squared maximum global bound. -/
theorem corner_bound (column : Fin mesh.boundaryColumns) (row : Fin mesh.boundaryRows) :
    Data.Gaussian.Norm.Basic.normSq (BilinearGridBoundary.interiorCorner assembly.corners column row) ≤
      256 * (max firstRequest.globalBound secondRequest.globalBound) ^ 2 := by
  let value := fun right above =>
    let owner := mesh.junctionOwner column row right above
    (⟨firstAnchors.alignedValue firstOffsets owner.column owner.row owner.point,
      secondAnchors.alignedValue secondOffsets owner.column owner.row owner.point⟩ : Stokes.PrimitivePoint)
  have contains (right above : Bool) :
      (geometry.box (mesh.junctionOwner column row right above).column
        (mesh.junctionOwner column row right above).row).Contains (mesh.junctionPoint column row) := by
    have inside := (mesh.junctionOwner column row right above).contains
    rw [mesh.junctionOwner_point] at inside
    exact inside
  have bounded (right above : Bool) :
      (PrimitiveAreaBounds.PrimitivePoint.Bounded (Stokes.PrimitivePoint.sub (value right above) (value false false)))
        (4 * max firstRequest.globalBound secondRequest.globalBound) := by
    let owner := mesh.junctionOwner column row right above
    let base := mesh.junctionOwner column row false false
    exact ⟨(RectangularPrimitiveAccuracy.GridPrimitiveAccuracy.overlap_bound firstRequest firstAnchors firstOffsets
      refines owner.column base.column owner.row base.row
        (contains right above) (contains false false)).trans
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Basic.le_max_left _ _) (by decide)),
      (RectangularPrimitiveAccuracy.GridPrimitiveAccuracy.overlap_bound secondRequest secondAnchors secondOffsets
        refines owner.column base.column owner.row base.row
        (contains right above) (contains false false)).trans
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Basic.le_max_right _ _) (by
          decide))⟩
  have corners := mesh.corner_junction (fun column row point =>
    ⟨firstAnchors.alignedValue firstOffsets column row point, secondAnchors.alignedValue secondOffsets column row
      point⟩) column row
  simp only [BilinearGridBoundary.interiorCorner, assembly.corners_eq]
  rw [corners.1, corners.2.1, corners.2.2.1, corners.2.2.2]
  exact (BilinearGridBoundary.cornerArea_bound (bounded false true) (bounded true true) (bounded true false)).trans_eq
    (by ring1)

open Purelib.Algebra in
open Purelib.Data.Gaussian in
open Purelib.Riemann.Periods in
/-- Bound the retained clipped corner total using its original finite grid dimensions.

The squared boundary-column/row count multiplies 256 times the squared maximum of the two original global request
bounds. -/
theorem cornerTotal_bound : Data.Gaussian.Norm.Basic.normSq assembly.cornerTotal ≤
    256 * ((mesh.boundaryColumns : Coordinate) * (mesh.boundaryRows : Coordinate)) ^ 2 *
      (max firstRequest.globalBound secondRequest.globalBound) ^ 2 := by
  rw [assembly.cornerTotal_eq]
  have estimate := Norm.Sum.Indexed.normSq_sumFin_le
    (fun column : Fin mesh.boundaryColumns => FiniteSum.Fin.sumFin
      (fun row : Fin mesh.boundaryRows => BilinearGridBoundary.interiorCorner assembly.corners column row))
    ((mesh.boundaryRows : Coordinate) ^ 2 * (256 * (max firstRequest.globalBound secondRequest.globalBound) ^ 2))
    (fun column => Norm.Sum.Indexed.normSq_sumFin_le _
      (256 * (max firstRequest.globalBound secondRequest.globalBound) ^ 2)
      (assembly.corner_bound firstRequest secondRequest firstAnchors secondAnchors firstOffsets secondOffsets refines
        column))
  exact estimate.trans_eq (by ring1)

end Purelib.Riemann.Readings.RectangularObservationAssembly.ObservationMesh.ClippedAssembly
end

end
