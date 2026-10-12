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
import Purelib.Riemann.Readings.RectangularClippedCornerBounds
import Purelib.Riemann.Paths.RectangularConjugateSeamTrace
import Purelib.Tactic.Ring
public import Purelib.Riemann.Integration.RectangularPrimitiveAccuracy
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Riemann.Meshes.RectangularObservationMesh
public import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Riemann.Integration.RectangularClippedCornerGeometry
import Purelib.Riemann.Integration.RectangularPrimitiveOverlap

public section

/-! Conjugate/value clipped corner polygons retain the same shrinking
overlap bound, including foreign cuts and all four retained model owners. -/
namespace Purelib.Riemann.Integration.RectangularClippedConjugateCorners

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

open Purelib.Riemann in
open Purelib.Topology in
open Purelib.Data in
/-- Bound one clipped conjugate/value junction polygon using its four retained model owners.

The squared area is at most 256 times the square of the larger primitive-overlap bound, including junctions introduced
by foreign cuts. -/
theorem conjugate_corner_bound (column : Fin mesh.boundaryColumns) (row : Fin mesh.boundaryRows) :
    Data.Gaussian.Norm.Basic.normSq (Periods.BilinearGridBoundary.interiorCorner assembly.corners column row) ≤
      256 * (max firstRequest.globalBound secondRequest.globalBound) ^ 2 := by
  let value := fun right above =>
    let owner := mesh.junctionOwner column row right above
    (⟨conj (firstAnchors.alignedValue firstOffsets owner.column owner.row owner.point),
      secondAnchors.alignedValue secondOffsets owner.column owner.row owner.point⟩ : Polygon.Stokes.PrimitivePoint)
  have contains (right above : Bool) :
      (geometry.box (mesh.junctionOwner column row right above).column
        (mesh.junctionOwner column row right above).row).Contains (mesh.junctionPoint column row) := by
    have inside := (mesh.junctionOwner column row right above).contains
    rw [mesh.junctionOwner_point] at inside
    exact inside
  have conjugateEq (value : Gaussian.Basic.Canonical) :
      Data.Gaussian.Basic.conj value = Gaussian.Basic.Canonical.conj value := rfl
  have bounded (right above : Bool) :
      Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded
        ((value right above).sub (value false false)) (4 * max firstRequest.globalBound secondRequest.globalBound) := by
    let owner := mesh.junctionOwner column row right above
    let base := mesh.junctionOwner column row false false
    exact ⟨by
      have estimate := (firstRequest.overlap_bound firstAnchors firstOffsets refines owner.column base.column owner.row
        base.row
        (contains right above) (contains false false)).trans
        (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Purelib.Data.Rat.Fraction.Order.Basic.le_max_left _ secondRequest.globalBound) (by decide))
      simpa only [-eq_self, -iff_self, value, Polygon.Stokes.PrimitivePoint.sub, conjugateEq,
        Gaussian.Basic.Canonical.normSq_conj_sub,
        mesh.junctionOwner_point] using estimate,
      (secondRequest.overlap_bound secondAnchors secondOffsets refines owner.column base.column owner.row base.row
        (contains right above) (contains false false)).trans
        (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Purelib.Data.Rat.Fraction.Order.Basic.le_max_right _ _) (by decide))⟩
  have corners := mesh.corner_junction (fun column row point =>
    ⟨conj (firstAnchors.alignedValue firstOffsets column row point), secondAnchors.alignedValue secondOffsets column row
      point⟩) column row
  simp only [-eq_self, -iff_self, Periods.BilinearGridBoundary.interiorCorner, assembly.corners_eq]
  rw [corners.1, corners.2.1, corners.2.2.1, corners.2.2.2]
  exact (Periods.BilinearGridBoundary.cornerArea_bound (bounded false true) (bounded true true) (bounded true
    false)).trans_eq (by ring1)

open Purelib.Algebra in
open Purelib.Riemann in
open Purelib.Data in
/-- Bound the sum of all retained clipped conjugate/value corner polygons.

The squared bound includes the square of the actual finite junction count and the same uniform primitive-overlap bound.
-/
theorem conjugate_cornerTotal_bound : Data.Gaussian.Norm.Basic.normSq assembly.cornerTotal ≤
    256 * ((mesh.boundaryColumns : Coordinate) * (mesh.boundaryRows : Coordinate)) ^ 2 *
      (max firstRequest.globalBound secondRequest.globalBound) ^ 2 := by
  rw [assembly.cornerTotal_eq]
  have estimate := Gaussian.Norm.Sum.Indexed.normSq_sumFin_le
    (fun column : Fin mesh.boundaryColumns => FiniteSum.Fin.sumFin
      (fun row : Fin mesh.boundaryRows => Periods.BilinearGridBoundary.interiorCorner assembly.corners column row))
    ((mesh.boundaryRows : Coordinate) ^ 2 * (256 * (max firstRequest.globalBound secondRequest.globalBound) ^ 2))
    (fun column => Gaussian.Norm.Sum.Indexed.normSq_sumFin_le _
      (256 * (max firstRequest.globalBound secondRequest.globalBound) ^ 2)
      (Integration.RectangularClippedConjugateCorners.ObservationMesh.ClippedAssembly.conjugate_corner_bound
        firstRequest secondRequest firstAnchors secondAnchors firstOffsets secondOffsets refines assembly column))
  exact estimate.trans_eq (by ring1)

end ObservationMesh.ClippedAssembly
end Purelib.Riemann.Integration.RectangularClippedConjugateCorners
