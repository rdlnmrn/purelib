module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Topology.Polygon.Stokes

import Purelib.LinearAlgebra.Grid.Offsets
import Purelib.Topology.Grid.Signs
public import Purelib.Riemann.Periods.ClippedBilinearBudget
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Vector.Basic
public import Purelib.Riemann.Integration.RectangularSharedPrimitives
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Topology.Mesh.CoordinateTriangulation
import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
public import Purelib.Riemann.Readings.RectangularClippedLocalBoundary
public import Purelib.Riemann.Readings.RectangularSeamBounds
import Purelib.Riemann.Integration.RectangularPrimitiveModels
import Purelib.Data.Rat.Fraction
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.Integration.RectangularPrimitiveAccuracy
import Mathlib.Order.Basic
import Purelib.Riemann.Readings.RectangularSharedClippedBoundary

@[expose] public section

/-! The actual clipped-boundary comparison with its finite count fully paid. -/
namespace Purelib.Riemann.Readings.RectangularRequestedClippedBoundary
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
open Purelib.Riemann.Periods (ClippedBilinearBudget)
open Purelib.Riemann.Readings.RectangularSharedClippedBoundary (shared_clipped_boundary_bilinear_error)
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

include refines

open Purelib.Data.Gaussian in
open Purelib.Topology.Polygon in
/-- The original shared clipped boundary meets its retained strict bilinear error target.

Both primitive requests must fit the same count-and-slope reading budget; the actual shared values, mesh boundary, local
pieces and dyadic depth remain fixed. -/
theorem requested_shared_clipped_boundary {cuts : GridCuts geometry} {box : Box}
    (mesh : ObservationMesh cuts box) {target : Coordinate}
    (budget : ClippedBilinearBudget (mesh.triangles.map ModelTriangle.triangle).length
      (max (boundarySlope firstBounds) (boundarySlope secondBounds)) target)
    (firstRequested : firstTarget ≤ budget.readingTarget) (secondRequested : secondTarget ≤ budget.readingTarget)
    (left : SharedPrimitiveValues firstAnchors firstOffsets mesh.surface)
    (right : SharedPrimitiveValues secondAnchors secondOffsets mesh.surface) :
    Data.Gaussian.Norm.Basic.normSq (Stokes.edgeListArea
        (fun vertex : Fin mesh.surface.mesh.vertices.length => ⟨left.values vertex, right.values vertex⟩)
        mesh.surface.mesh.triangulation.boundary -
      mesh.pieces.localBoundary
        (fun column row point => ⟨firstPrimitives.value column row point, secondPrimitives.value column row point⟩)
        mesh.depth) < target := by
  have leftLe := firstRequest.accurate.le.trans firstRequested
  have rightLe := secondRequest.accurate.le.trans secondRequested
  exact (shared_clipped_boundary_bilinear_error firstRequest secondRequest firstAnchors secondAnchors
    firstOffsets secondOffsets refines mesh left right (budget.small leftLe rightLe)).trans_lt
      (budget.paid leftLe rightLe)

end Purelib.Riemann.Readings.RectangularRequestedClippedBoundary
