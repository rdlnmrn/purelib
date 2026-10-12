module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Topology.Polygon.Stokes

import Purelib.LinearAlgebra.Grid.Offsets
import Purelib.Topology.Grid.Signs
import Purelib.Riemann.Periods.RectangularSharedBilinearError
public import Purelib.Riemann.Readings.RectangularClippedLocalBoundary
public import Purelib.Riemann.Readings.RectangularSeamBounds
public import Purelib.Riemann.Integration.RectangularSharedPrimitives

@[expose] public section

/-! Shared paired mesh boundary compared with the actual clipped local sides. -/
namespace Purelib.Riemann.Readings.RectangularSharedClippedBoundary
open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (RegionClearance PrimitiveOverlapBounds)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry Bank Transitions)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives)
open Purelib.Riemann.Integration.RectangularPrimitiveGluing (PrimitiveAnchors)
open Purelib.Riemann.Integration.RectangularPrimitiveAccuracy (GridPrimitiveAccuracy)
open Purelib.Riemann.Integration.RectangularOwnedTriangulation (ModelTriangle)
open Purelib.Riemann.Integration.RectangularSharedPrimitives (SharedPrimitiveValues)
open Purelib.Riemann.Readings.RectangularSeamBounds (boundarySlope)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts)
open Purelib.Riemann.Meshes.RectangularObservationMesh (ObservationMesh)
open Purelib.Riemann.Periods.RectangularSharedBilinearError (shared_boundary_bilinear_error)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)

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

include refines

open Purelib.Data.Gaussian.Norm in
open Purelib.Riemann.Readings.RectangularClippedLocalBoundary in
open Purelib.Topology in
/-- Bound the shared paired mesh boundary against its actual clipped local side readings.

The original primitive requests, ambient containment and unit-sized common ownership error give the squared
triangle-count bound, with the retained clipped-boundary readback. -/
theorem shared_clipped_boundary_bilinear_error {cuts : GridCuts geometry} {box : Box}
    (mesh : ObservationMesh cuts box)
    (left : SharedPrimitiveValues firstAnchors firstOffsets mesh.surface)
    (right : SharedPrimitiveValues secondAnchors secondOffsets mesh.surface)
    (small : 16 * max firstRequest.globalBound secondRequest.globalBound ≤ 1) :
    Data.Gaussian.Norm.Basic.normSq (Polygon.Stokes.edgeListArea
        (fun vertex : Fin mesh.surface.mesh.vertices.length => ⟨left.values vertex, right.values vertex⟩)
        mesh.surface.mesh.triangulation.boundary -
      mesh.pieces.localBoundary
        (fun column row point => ⟨firstPrimitives.value column row point, secondPrimitives.value column row point⟩)
        mesh.depth) ≤
      ((mesh.triangles.map ModelTriangle.triangle).length : Coordinate) ^ 2 *
        (32 * (max (boundarySlope firstBounds) (boundarySlope secondBounds) + 1) *
          (16 * max firstRequest.globalBound secondRequest.globalBound)) := by
  have estimate := shared_boundary_bilinear_error firstRequest secondRequest firstAnchors secondAnchors
    firstOffsets secondOffsets refines left right small
  let values := fun column row point =>
    (⟨firstPrimitives.value column row point, secondPrimitives.value column row point⟩ : PrimitivePoint)
  have readback := OwnedTriangulation.localWedges_eq_indexed mesh.surface values
  rw [mesh.localWedges_eq_boundary] at readback
  rw [← readback] at estimate
  simpa only [Basic.normSq_eq_canonical] using estimate

end Purelib.Riemann.Readings.RectangularSharedClippedBoundary
