module
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.RectangularPrimitiveMagnitude
public import Purelib.Riemann.Integration.RectangularSharedPrimitives
import Purelib.Topology.Polygon.Stokes
public import Purelib.Topology.Surface.Cut.PrimitiveJumps

import Purelib.LinearAlgebra.Grid.Offsets
import Purelib.Topology.Grid.Signs
import Purelib.Topology.Surface.Boundary.HandleAreaBounds
import Purelib.Riemann.Periods.RectangularSharedBilinearError
import Purelib.Tactic.Ring
public import Purelib.Riemann.Readings.RectangularSeamBounds

public section

/-!
# Ownership errors for conjugate/value area

The conjugate component retains the same increment norm bounds. This
compares energy pairs with the actual local primitives without treating the
conjugate of a holomorphic primitive as another holomorphic differential.
-/

namespace Purelib.Riemann.Integration.RectangularSharedConjugateError
open Purelib.Riemann.Normalization.InverseRootPolynomial (Polynomial Box)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Topology.Polygon.Stokes (PrimitivePoint triangleWedgeArea)
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (RegionClearance PrimitiveOverlapBounds)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry Bank Transitions)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives)
open Purelib.Riemann.Integration.RectangularPrimitiveGluing (PrimitiveAnchors)
open Purelib.Riemann.Integration.RectangularPrimitiveAccuracy (GridPrimitiveAccuracy)
open Purelib.Riemann.Integration.RectangularOwnedTriangulation (ModelTriangle OwnedTriangulation)
open Purelib.Riemann.Integration.RectangularSharedPrimitives (SharedPrimitiveValues)
open Purelib.Riemann.Readings.RectangularSeamBounds (boundarySlope)
open Purelib.Riemann.Readings.PrimitiveAreaBounds.PrimitivePoint (Bounded)
section
open Purelib.Data
/-- The exact rational carrier of the conjugate-area error bounds. -/
private abbrev Coordinate := Rat.Fraction.Rational
/-- The exact Gaussian rational carrier of the paired primitive values. -/
private abbrev Gaussian := Gaussian.Basic.Canonical

/-- Gaussian conjugation preserves the difference of two values. -/
private theorem conjugate_sub (first last : Gaussian.Basic.Canonical) : conj (first - last) = conj first - conj last :=
  by
  apply Gaussian.Basic.ext <;> simp only [-eq_self, -iff_self, conj, Gaussian.Basic.sub_re, Gaussian.Basic.sub_im] <;>
    ring1

end

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

open Purelib.Data in
open Purelib.Data.Gaussian in
open Purelib.Data.Gaussian.Norm in
open Purelib.Data.Rat.Fraction.Order in
open Purelib.Riemann.Integration.RectangularPrimitiveModels in
open Purelib.Riemann.Integration.RectangularSharedPrimitives in
open Purelib.Topology in
open Purelib.Topology.Polygon.Stokes in
open Purelib.Topology.Surface.Boundary.HandleAreaBounds in
/-- Bound conjugate/value triangle-area error between shared and original local primitives.

The same retained increment bounds control the conjugated first component. Ambient containment and the unit-sized common
error yield the stated slope-scaled norm bound. -/
theorem shared_triangle_conjugate_error {triangles : List (ModelTriangle geometry)}
    {surface : OwnedTriangulation triangles}
    (left : SharedPrimitiveValues firstAnchors firstOffsets surface)
    (right : SharedPrimitiveValues secondAnchors secondOffsets surface)
    (face : Fin (triangles.map ModelTriangle.triangle).length)
    (small : 16 * max firstRequest.globalBound secondRequest.globalBound ≤ 1) :
    let triangle := surface.mesh.triangulation.faces face
    let source := surface.faceSource face
    let originalValues := fun vertex => (⟨conj (firstPrimitives.value source.column source.row (surface.mesh.coordinate
      vertex)),
      secondPrimitives.value source.column source.row (surface.mesh.coordinate vertex)⟩ : PrimitivePoint)
    normSq (triangleWedgeArea ⟨conj (left.values triangle.first), right.values triangle.first⟩
        ⟨conj (left.values triangle.second), right.values triangle.second⟩
        ⟨conj (left.values triangle.third), right.values triangle.third⟩ -
      triangleWedgeArea (originalValues triangle.first) (originalValues triangle.second) (originalValues
        triangle.third)) ≤
      32 * (max (boundarySlope firstBounds) (boundarySlope secondBounds) + 1) *
        (16 * max firstRequest.globalBound secondRequest.globalBound) := by
  dsimp only
  let t := surface.mesh.triangulation.faces face
  let source := surface.faceSource face
  let original := fun vertex => (⟨conj (firstPrimitives.value source.column source.row (surface.mesh.coordinate
    vertex)),
    secondPrimitives.value source.column source.row (surface.mesh.coordinate vertex)⟩ : PrimitivePoint)
  let changed := fun vertex => (⟨conj (left.values vertex), right.values vertex⟩ : PrimitivePoint)
  have inside := surface.face_inside face
  have conjugateNorm (value : Gaussian.Basic.Canonical) :
      Basic.Canonical.normSq (Basic.Canonical.conj value) = Basic.Canonical.normSq value := by
    have conjugateEq : Basic.Canonical.conj value = Data.Gaussian.Basic.conj value := rfl
    rw [conjugateEq, ← Basic.normSq_eq_canonical, Basic.normSq_conj, Basic.normSq_eq_canonical]
  have firstNonnegative := firstRequest.edgeBound_nonnegative.trans firstRequest.edgeBound_le_globalBound
  have errorNonnegative : 0 ≤ 16 * max firstRequest.globalBound secondRequest.globalBound :=
    Arithmetic.mul_nonneg_direct (by decide) (firstNonnegative.trans (Purelib.Data.Rat.Fraction.Order.Basic.le_max_left
      _ _))
  have bound (vertex) (contained : (geometry.box source.column source.row).Contains (surface.mesh.coordinate vertex)) :
      Bounded (PrimitivePoint.sub (original vertex) (original t.first))
        (max (boundarySlope firstBounds) (boundarySlope secondBounds)) :=
    ⟨by
      have estimate := (Primitives.local_increment_bound
        firstPrimitives firstBounds refines _ _ inside.1 contained).trans
        (Purelib.Data.Rat.Fraction.Order.Basic.le_max_left _ (boundarySlope secondBounds))
      simpa only [-eq_self, -iff_self, original, PrimitivePoint.sub,
        ← conjugate_sub, Basic.normSq_eq_canonical, conjugateNorm] using estimate,
      (Primitives.local_increment_bound
        secondPrimitives secondBounds refines _ _ inside.1 contained).trans
          (Purelib.Data.Rat.Fraction.Order.Basic.le_max_right _ _)⟩
  have error (vertex) (contained : (geometry.box source.column source.row).Contains (surface.mesh.coordinate vertex)) :
      Bounded (PrimitivePoint.sub
        (PrimitivePoint.sub (changed vertex) (changed t.first))
        (PrimitivePoint.sub (original vertex) (original t.first)))
        (16 * max firstRequest.globalBound secondRequest.globalBound) :=
    ⟨by
      have estimate := (GridPrimitiveAccuracy.shared_local_increment_bound
        firstRequest left refines _ _ _ _ inside.1 contained).trans
        (Arithmetic.mul_le_mul_of_nonneg_left_direct (Purelib.Data.Rat.Fraction.Order.Basic.le_max_left _
          secondRequest.globalBound) (by decide))
      simpa only [-eq_self, -iff_self, original, changed, PrimitivePoint.sub,
        ← conjugate_sub, Basic.normSq_eq_canonical, conjugateNorm] using estimate,
      (GridPrimitiveAccuracy.shared_local_increment_bound
        secondRequest right refines _ _ _ _ inside.1 contained).trans
      (Arithmetic.mul_le_mul_of_nonneg_left_direct (Purelib.Data.Rat.Fraction.Order.Basic.le_max_right _ _) (by
        decide))⟩
  have boundedFirst := bound t.second inside.2.1
  have boundedLast := bound t.third inside.2.2
  have scalar := PrimitivePoint.area_difference_bound
    (first := PrimitivePoint.sub (original t.second) (original t.first))
    (last := PrimitivePoint.sub (original t.third) (original t.first))
    (changedFirst := PrimitivePoint.sub (changed t.second) (changed t.first))
    (changedLast := PrimitivePoint.sub (changed t.third) (changed t.first))
    ((Basic.Canonical.normSq_nonneg _).trans boundedFirst.1) errorNonnegative small
    boundedFirst boundedLast (error t.second inside.2.1) (error t.third inside.2.2)
  simpa only [-eq_self, -iff_self, Basic.normSq_eq_canonical, Polygon.Stokes.triangleWedgeArea,
    Polygon.Stokes.edgeArea, PrimitivePoint.sub] using scalar

open Purelib.Algebra in
open Purelib.Data in
open Purelib.Data.Gaussian.Norm in
open Purelib.Data.Gaussian.Norm.Sum in
open Purelib.Topology in
/-- Bound the shared conjugate boundary area against the sum of actual local triangle areas.

Finite Stokes cancellation and the common triangle estimate give the squared face-count factor with the original two
primitive requests. -/
theorem shared_boundary_conjugate_error {triangles : List (ModelTriangle geometry)}
    {surface : OwnedTriangulation triangles}
    (left : SharedPrimitiveValues firstAnchors firstOffsets surface)
    (right : SharedPrimitiveValues secondAnchors secondOffsets surface)
    (small : 16 * max firstRequest.globalBound secondRequest.globalBound ≤ 1) :
    normSq (Polygon.Stokes.edgeListArea (fun vertex : Fin surface.mesh.vertices.length => ⟨conj (left.values vertex),
      right.values vertex⟩)
        surface.mesh.triangulation.boundary -
      FiniteSum.Fin.sumFin (fun face : Fin (triangles.map ModelTriangle.triangle).length =>
        let triangle := surface.mesh.triangulation.faces face
        let source := surface.faceSource face
        let original := fun vertex : Fin surface.mesh.vertices.length => (⟨conj (firstPrimitives.value source.column
          source.row (surface.mesh.coordinate vertex)),
          secondPrimitives.value source.column source.row (surface.mesh.coordinate vertex)⟩ : PrimitivePoint)
        triangleWedgeArea (original triangle.first) (original triangle.second) (original triangle.third))) ≤
      ((triangles.map ModelTriangle.triangle).length : Rat.Fraction.Rational) ^ 2 *
        (32 * (max (boundarySlope firstBounds) (boundarySlope secondBounds) + 1) *
          (16 * max firstRequest.globalBound secondRequest.globalBound)) := by
  let actual := fun face : Fin (triangles.map ModelTriangle.triangle).length =>
    let triangle := surface.mesh.triangulation.faces face
    triangleWedgeArea ⟨conj (left.values triangle.first), right.values triangle.first⟩
      ⟨conj (left.values triangle.second), right.values triangle.second⟩
      ⟨conj (left.values triangle.third), right.values triangle.third⟩
  let original := fun face : Fin (triangles.map ModelTriangle.triangle).length =>
    let triangle := surface.mesh.triangulation.faces face
    let source := surface.faceSource face
    let values := fun vertex : Fin surface.mesh.vertices.length => (⟨conj (firstPrimitives.value source.column
      source.row (surface.mesh.coordinate vertex)),
      secondPrimitives.value source.column source.row (surface.mesh.coordinate vertex)⟩ : PrimitivePoint)
    triangleWedgeArea (values triangle.first) (values triangle.second) (values triangle.third)
  have estimate := Indexed.normSq_sumFin_le
    (fun face : Fin (triangles.map ModelTriangle.triangle).length => actual face - original face)
    (32 * (max (boundarySlope firstBounds) (boundarySlope secondBounds) + 1) *
      (16 * max firstRequest.globalBound secondRequest.globalBound))
    (fun face => by
      have scalar := shared_triangle_conjugate_error firstRequest secondRequest firstAnchors secondAnchors
        firstOffsets secondOffsets refines left right face small
      simpa only [-eq_self, -iff_self, Basic.normSq_eq_canonical] using scalar)
  rw [FiniteSum.Fin.sumFin_sub] at estimate
  have actualEq : FiniteSum.Fin.sumFin actual =
      Polygon.Stokes.edgeListArea (fun vertex : Fin surface.mesh.vertices.length => ⟨conj (left.values vertex),
        right.values vertex⟩)
        surface.mesh.triangulation.boundary :=
    surface.mesh.wedgeSum_eq_boundaryArea (fun vertex : Fin surface.mesh.vertices.length =>
      (⟨conj (left.values vertex), right.values vertex⟩ : PrimitivePoint))
  rw [actualEq] at estimate
  simpa only [-eq_self, -iff_self, Basic.normSq_eq_canonical] using estimate

end Purelib.Riemann.Integration.RectangularSharedConjugateError
