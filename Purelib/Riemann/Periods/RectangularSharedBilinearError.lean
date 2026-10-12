module
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
public import Purelib.Topology.Surface.Cut.PrimitiveJumps

import Purelib.LinearAlgebra.Grid.Offsets
import Purelib.Topology.Grid.Signs
import Purelib.Riemann.Integration.RectangularSharedPrimitives
import Purelib.Riemann.Integration.RectangularPrimitiveMagnitude
import Purelib.Topology.Surface.Boundary.HandleAreaBounds
public import Purelib.Riemann.Readings.RectangularPointReadings
public import Purelib.Riemann.Readings.RectangularSeamBounds

section

open Purelib.Riemann.Normalization.InverseRootPolynomial

public section

/-! Ownership errors for the actual two-function area of a shared triangle. -/
namespace Purelib.Riemann.Periods.RectangularSharedBilinearError

open Purelib.Data.Rat

open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (RegionClearance PrimitiveOverlapBounds)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry Bank Transitions)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives)
open Purelib.Riemann.Integration.RectangularPrimitiveGluing (PrimitiveAnchors)
open Purelib.Riemann.Integration.RectangularPrimitiveAccuracy (GridPrimitiveAccuracy)
open Purelib.Riemann.Readings.RectangularSeamBounds (boundarySlope)
open Purelib.Data in
/-- The exact rational carrier of the primitive error bounds. -/
private abbrev Coordinate := Rat.Fraction.Rational
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Topology.Polygon.Stokes (PrimitivePoint triangleWedgeArea)
open Purelib.Riemann.Integration.RectangularOwnedTriangulation (ModelTriangle OwnedTriangulation)
open Purelib.Riemann.Integration.RectangularSharedPrimitives (SharedPrimitiveValues)

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

open Purelib.Data.Gaussian in
open Purelib.Data.Gaussian.Norm in
open Purelib.Data.Rat.Fraction.Order in
open Purelib.Riemann.Integration.RectangularPrimitiveModels in
open Purelib.Riemann.Integration.RectangularSharedPrimitives in
open Purelib.Riemann.Readings.PrimitiveAreaBounds in
open Purelib.Topology in
open Purelib.Topology.Polygon.Stokes in
open Purelib.Topology.Surface.Boundary.HandleAreaBounds in
/-- Bound the ownership error in the actual paired area of a shared triangle.

The retained shared values are compared with that face's original primitive owners. Both model grids refine the same
clearance box, and sixteen times the larger global primitive error is at most one. -/
theorem shared_triangle_bilinear_error {triangles : List (ModelTriangle geometry)}
    {surface : OwnedTriangulation triangles}
    (left : SharedPrimitiveValues firstAnchors firstOffsets surface)
    (right : SharedPrimitiveValues secondAnchors secondOffsets surface)
    (face : Fin (triangles.map ModelTriangle.triangle).length)
    (small : 16 * max firstRequest.globalBound secondRequest.globalBound ≤ 1) :
    let triangle := surface.mesh.triangulation.faces face
    let source := surface.faceSource face
    let originalValues := fun vertex => (⟨firstPrimitives.value source.column source.row (surface.mesh.coordinate
      vertex),
      secondPrimitives.value source.column source.row (surface.mesh.coordinate vertex)⟩ : PrimitivePoint)
    normSq (triangleWedgeArea ⟨left.values triangle.first, right.values triangle.first⟩
        ⟨left.values triangle.second, right.values triangle.second⟩
        ⟨left.values triangle.third, right.values triangle.third⟩ -
      triangleWedgeArea (originalValues triangle.first) (originalValues triangle.second) (originalValues
        triangle.third)) ≤
      32 * (max (boundarySlope firstBounds) (boundarySlope secondBounds) + 1) *
        (16 * max firstRequest.globalBound secondRequest.globalBound) := by
  dsimp only
  let t := surface.mesh.triangulation.faces face
  let source := surface.faceSource face
  let original := fun vertex => (⟨firstPrimitives.value source.column source.row (surface.mesh.coordinate vertex),
    secondPrimitives.value source.column source.row (surface.mesh.coordinate vertex)⟩ : PrimitivePoint)
  let changed := fun vertex => (⟨left.values vertex, right.values vertex⟩ : PrimitivePoint)
  have inside := surface.face_inside face
  have firstNonnegative := firstRequest.edgeBound_nonnegative.trans firstRequest.edgeBound_le_globalBound
  have errorNonnegative : 0 ≤ 16 * max firstRequest.globalBound secondRequest.globalBound :=
    Arithmetic.mul_nonneg_direct (by decide) (firstNonnegative.trans (Fraction.Order.Basic.le_max_left _ _))
  have bound (vertex) (contained : (geometry.box source.column source.row).Contains (surface.mesh.coordinate vertex)) :
      PrimitivePoint.Bounded (PrimitivePoint.sub (original vertex) (original t.first)) (max (boundarySlope firstBounds)
        (boundarySlope secondBounds)) :=
    ⟨(Primitives.local_increment_bound firstPrimitives firstBounds refines _ _ inside.1 contained).trans
      (Fraction.Order.Basic.le_max_left _ _),
      (Primitives.local_increment_bound secondPrimitives secondBounds refines _ _ inside.1 contained).trans
        (Fraction.Order.Basic.le_max_right _ _)⟩
  have error (vertex) (contained : (geometry.box source.column source.row).Contains (surface.mesh.coordinate vertex)) :
      PrimitivePoint.Bounded
        (PrimitivePoint.sub (PrimitivePoint.sub (changed vertex) (changed t.first)) (PrimitivePoint.sub (original
          vertex) (original t.first)))
        (16 * max firstRequest.globalBound secondRequest.globalBound) :=
    ⟨(GridPrimitiveAccuracy.shared_local_increment_bound firstRequest left refines _ _ _ _ inside.1 contained).trans
      (Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Basic.le_max_left _ _) (by decide)),
      (GridPrimitiveAccuracy.shared_local_increment_bound secondRequest right refines _ _ _ _ inside.1 contained).trans
      (Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Basic.le_max_right _ _) (by decide))⟩
  have boundedFirst := bound t.second inside.2.1
  have boundedLast := bound t.third inside.2.2
  have scalar := PrimitivePoint.area_difference_bound
    (first := (PrimitivePoint.sub (original t.second) (original t.first)))
    (last := (PrimitivePoint.sub (original t.third) (original t.first)))
    (changedFirst := (PrimitivePoint.sub (changed t.second) (changed t.first)))
    (changedLast := (PrimitivePoint.sub (changed t.third) (changed t.first)))
    ((Basic.Canonical.normSq_nonneg _).trans boundedFirst.1) errorNonnegative small
    boundedFirst boundedLast (error t.second inside.2.1) (error t.third inside.2.2)
  simpa only [Basic.normSq_eq_canonical, Polygon.Stokes.triangleWedgeArea,
    Polygon.Stokes.edgeArea, PrimitivePoint.sub] using scalar

open Purelib.Algebra in
open Purelib.Data in
open Purelib.Data.Gaussian.Norm in
open Purelib.Data.Gaussian.Norm.Sum in
open Purelib.Topology in
/-- Bound the shared boundary area against the sum of the original local paired triangle areas.

Exact incidence transfers the shared-vertex wedge sum to the retained boundary. The triangle ownership estimate pays
every face with the squared actual face count and the same primitive-error smallness condition. -/
theorem shared_boundary_bilinear_error {triangles : List (ModelTriangle geometry)}
    {surface : OwnedTriangulation triangles}
    (left : SharedPrimitiveValues firstAnchors firstOffsets surface)
    (right : SharedPrimitiveValues secondAnchors secondOffsets surface)
    (small : 16 * max firstRequest.globalBound secondRequest.globalBound ≤ 1) :
    normSq (Polygon.Stokes.edgeListArea (fun vertex : Fin surface.mesh.vertices.length => ⟨left.values vertex,
      right.values vertex⟩)
        surface.mesh.triangulation.boundary -
      FiniteSum.Fin.sumFin (fun face : Fin (triangles.map ModelTriangle.triangle).length =>
        let triangle := surface.mesh.triangulation.faces face
        let source := surface.faceSource face
        let original := fun vertex : Fin surface.mesh.vertices.length => (⟨firstPrimitives.value source.column
          source.row (surface.mesh.coordinate vertex),
          secondPrimitives.value source.column source.row (surface.mesh.coordinate vertex)⟩ : PrimitivePoint)
        triangleWedgeArea (original triangle.first) (original triangle.second) (original triangle.third))) ≤
      ((triangles.map ModelTriangle.triangle).length : Rat.Fraction.Rational) ^ 2 *
        (32 * (max (boundarySlope firstBounds) (boundarySlope secondBounds) + 1) *
          (16 * max firstRequest.globalBound secondRequest.globalBound)) := by
  let actual := fun face : Fin (triangles.map ModelTriangle.triangle).length =>
    let triangle := surface.mesh.triangulation.faces face
    triangleWedgeArea ⟨left.values triangle.first, right.values triangle.first⟩
      ⟨left.values triangle.second, right.values triangle.second⟩
      ⟨left.values triangle.third, right.values triangle.third⟩
  let original := fun face : Fin (triangles.map ModelTriangle.triangle).length =>
    let triangle := surface.mesh.triangulation.faces face
    let source := surface.faceSource face
    let values := fun vertex : Fin surface.mesh.vertices.length => (⟨firstPrimitives.value source.column source.row
      (surface.mesh.coordinate vertex),
      secondPrimitives.value source.column source.row (surface.mesh.coordinate vertex)⟩ : PrimitivePoint)
    triangleWedgeArea (values triangle.first) (values triangle.second) (values triangle.third)
  have estimate := Indexed.normSq_sumFin_le
    (fun face : Fin (triangles.map ModelTriangle.triangle).length => actual face - original face)
    (32 * (max (boundarySlope firstBounds) (boundarySlope secondBounds) + 1) *
      (16 * max firstRequest.globalBound secondRequest.globalBound))
    (fun face => by
      have scalar := shared_triangle_bilinear_error firstRequest secondRequest firstAnchors secondAnchors
        firstOffsets secondOffsets refines left right face small
      simpa only [Basic.normSq_eq_canonical] using scalar)
  rw [FiniteSum.Fin.sumFin_sub] at estimate
  have actualEq : FiniteSum.Fin.sumFin actual =
      Polygon.Stokes.edgeListArea (fun vertex : Fin surface.mesh.vertices.length => ⟨left.values vertex, right.values
        vertex⟩)
        surface.mesh.triangulation.boundary :=
    surface.mesh.wedgeSum_eq_boundaryArea (fun vertex : Fin surface.mesh.vertices.length =>
      (⟨left.values vertex, right.values vertex⟩ : PrimitivePoint))
  rw [actualEq] at estimate
  simpa only [Basic.normSq_eq_canonical] using estimate

end Purelib.Riemann.Periods.RectangularSharedBilinearError

end
