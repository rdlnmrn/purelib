module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Topology.Surface.Cut.PrimitiveJumps

import Purelib.LinearAlgebra.Grid.Offsets
import Purelib.Topology.Grid.Signs
import Purelib.Riemann.Paths.RectangularTraceMagnitude
public import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Data.Vector.Basic
import Purelib.Topology.Polygon.Stokes
public import Purelib.Riemann.Integration.RectangularSharedPrimitives
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Integration.RectangularPrimitiveModels
import Purelib.Data.Gaussian.Basic
import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
public import Purelib.Riemann.Readings.RectangularSeamBounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Topology.Mesh.CoordinateTriangulation
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.Integration.RectangularPrimitiveAccuracy
import Purelib.Riemann.Normalization.RectangularInverseModels
import Mathlib.Order.Basic

open Purelib.Data.Rat

@[expose] public section

/-! Centered paired traces read the supplied shared mesh banks directly. -/
namespace Purelib.Riemann.Paths.RectangularCenteredTrace
open Purelib.Riemann.Normalization.InverseRootPolynomial (Polynomial Box)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (RegionClearance PrimitiveOverlapBounds)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry Bank Transitions)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives)
open Purelib.Riemann.Integration.RectangularPrimitiveGluing (PrimitiveAnchors)
open Purelib.Riemann.Integration.RectangularPrimitiveAccuracy (GridPrimitiveAccuracy)
open Purelib.Riemann.Integration.RectangularOwnedTriangulation (ModelTriangle OwnedTriangulation)
open Purelib.Riemann.Integration.RectangularSharedPrimitives (SharedPrimitiveValues)
open Purelib.Riemann.Readings.RectangularSeamBounds (boundarySlope)
open Purelib.Riemann.Periods.CenteredBilinearPath (Sample)
open Purelib.Riemann.Readings.PrimitiveAreaBounds.PrimitivePoint (Bounded)

variable {polynomial firstNumerator secondNumerator : Polynomial} {ambient : Box}
  {clearance : RegionClearance polynomial ambient}
  {firstBounds : PrimitiveOverlapBounds clearance firstNumerator}
  {secondBounds : PrimitiveOverlapBounds clearance secondNumerator}
  {columns rows : Nat} {firstTarget secondTarget : Purelib.Data.Rat.Fraction.Rational}
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

open Purelib.Riemann.Paths in
/-- Bound both coordinates of a centered paired primitive trace.

When both primitive requests have global bound at most one and the trace stays in one rectangle, the maximum of the two
boundary-slope bounds controls every centered vertex. -/
theorem paired_trace_magnitude {triangles : List (ModelTriangle geometry)}
    {surface : OwnedTriangulation triangles}
    (left : SharedPrimitiveValues firstAnchors firstOffsets surface)
    (right : SharedPrimitiveValues secondAnchors secondOffsets surface)
    (firstSmall : firstRequest.globalBound ≤ 1) (secondSmall : secondRequest.globalBound ≤ 1)
    {count : Nat} (trace : Fin (count + 1) → Fin surface.mesh.vertices.length)
    (sample : Sample (fun vertex => ⟨left.values (trace vertex), right.values (trace vertex)⟩))
    (column : Fin (columns + 1)) (row : Fin (rows + 1))
    (inside : ∀ vertex, (geometry.box column row).Contains (surface.mesh.coordinate (trace vertex)))
    (vertex : Fin (count + 1)) :
    Bounded (sample.centered vertex)
      (max (32 + 2 * boundarySlope firstBounds) (32 + 2 * boundarySlope secondBounds)) := by
  rw [sample.centered_eq]
  exact ⟨(RectangularTraceMagnitude.shared_centered_bound
    firstRequest left refines firstSmall column row (trace 0) (trace vertex)
      (inside 0) (inside vertex)).trans (Fraction.Order.Basic.le_max_left _ _),
    (RectangularTraceMagnitude.shared_centered_bound
      secondRequest right refines secondSmall column row (trace 0) (trace vertex)
      (inside 0) (inside vertex)).trans (Fraction.Order.Basic.le_max_right _ _)⟩

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Riemann.Periods in
open Purelib.Topology.Polygon in
/-- Bound the area change of two centered paired traces.

For a nonnegative perturbation at most one, separates the endpoint correction and bounds the squared area error by the
vertex-count square, retained slope magnitude and perturbation. -/
theorem paired_trace_comparison {triangles : List (ModelTriangle geometry)}
    {surface : OwnedTriangulation triangles}
    (left : SharedPrimitiveValues firstAnchors firstOffsets surface)
    (right : SharedPrimitiveValues secondAnchors secondOffsets surface)
    (firstSmall : firstRequest.globalBound ≤ 1) (secondSmall : secondRequest.globalBound ≤ 1)
    {count : Nat} (trace : Fin (count + 1) → Fin surface.mesh.vertices.length)
    (sample : Sample (fun vertex => ⟨left.values (trace vertex), right.values (trace vertex)⟩))
    (column : Fin (columns + 1)) (row : Fin (rows + 1))
    (inside : ∀ vertex, (geometry.box column row).Contains (surface.mesh.coordinate (trace vertex)))
    {changedValues : Fin (count + 1) → PrimitivePoint} (changed : Sample changedValues)
    {error : Fraction.Rational} (errorNonnegative : 0 ≤ error) (small : error ≤ 1)
    (accurate : ∀ vertex, Bounded
      (Stokes.PrimitivePoint.sub
        (changed.centered vertex) (sample.centered vertex)) error) :
    Data.Gaussian.Norm.Basic.normSq
      ((changed.originalArea - sample.originalArea) - (changed.endpoint - sample.endpoint)) ≤
      (count : Fraction.Rational) ^ 2 *
        (32 * (max (32 + 2 * boundarySlope firstBounds) (32 + 2 * boundarySlope secondBounds) + 1) * error) := by
  have bounded := paired_trace_magnitude firstRequest secondRequest firstAnchors secondAnchors
    firstOffsets secondOffsets refines left right firstSmall secondSmall trace sample column row inside
  have magnitudeNonnegative : 0 ≤ max (32 + 2 * boundarySlope firstBounds) (32 + 2 * boundarySlope secondBounds) :=
    (Basic.Canonical.normSq_nonneg _).trans (bounded 0).1
  exact CenteredBilinearPath.Sample.comparison changed sample
    magnitudeNonnegative errorNonnegative small bounded accurate

end Purelib.Riemann.Paths.RectangularCenteredTrace
