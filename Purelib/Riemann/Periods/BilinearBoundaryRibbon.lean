module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Vector.Basic
import Purelib.Topology.Surface.Cut.PrimitiveJumps

public import Purelib.Integration.Path.BoundaryRibbon
public import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Tactic.Ring

@[expose] public section

/-! Two-differential ribbon comparison consuming existing scalar traces.
The endpoint correction remains part of the cached exact identity. -/

namespace Purelib.Riemann.Periods.BilinearBoundaryRibbon

open Purelib.Topology.Polygon.Stokes (PrimitivePoint edgeArea)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Integration.Path.BoundaryRibbon (Coordinate Ribbon sum_increasing)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_add sumFin_sub)
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)

attribute [local congr] Purelib.Algebra.FiniteSum.Fin.sumFin_congr

namespace Bilinear

open Purelib.Topology in
open Purelib.Data in
/-- The bilinear edge correction from the two endpoint errors and their drift. -/
def correction (first last firstError lastError : PrimitivePoint) : Gaussian.Basic.Canonical :=
  edgeArea firstError ((Polygon.Stokes.PrimitivePoint.sub last) first) + edgeArea lastError
    ((Polygon.Stokes.PrimitivePoint.sub last) first) +
    edgeArea firstError ((Polygon.Stokes.PrimitivePoint.sub lastError) firstError)

open Purelib.Topology in
/-- The difference of paired edge areas splits into the local correction and an endpoint term. -/
theorem area_difference (firstLeft lastLeft firstRight lastRight : PrimitivePoint) :
    edgeArea firstLeft lastLeft - edgeArea firstRight lastRight =
      correction firstRight lastRight ((Polygon.Stokes.PrimitivePoint.sub firstLeft) firstRight)
        ((Polygon.Stokes.PrimitivePoint.sub lastLeft) lastRight) +
        (edgeArea lastRight ((Polygon.Stokes.PrimitivePoint.sub lastLeft) lastRight) - edgeArea firstRight
          ((Polygon.Stokes.PrimitivePoint.sub firstLeft) firstRight)) := by
  simp only [edgeArea, correction, Polygon.Stokes.PrimitivePoint.sub]
  ring1

open Purelib.Riemann in
open Purelib.Integration in
open Purelib.Topology in
open Purelib.Data in
/-- Bound one bilinear edge correction from endpoint error, slope and error drift.

The two primitive-coordinate bounds retain the same step length, giving quadrance at most eight times error times the
slope-and-drift factor times step squared. -/
theorem correction_bound {first last firstError lastError : PrimitivePoint} {error slope drift step :
  Path.BoundaryRibbon.Coordinate}
    (firstLe : (Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded firstError) error) (lastLe :
      (Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded lastError) error)
    (rightLe : (Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded ((Polygon.Stokes.PrimitivePoint.sub last) first))
      (slope * step ^ 2))
    (driftLe : (Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded ((Polygon.Stokes.PrimitivePoint.sub lastError)
      firstError)) (drift * step ^ 2)) :
    Data.Gaussian.Norm.Basic.normSq (correction first last firstError lastError) ≤ 8 * error * (4 * slope + drift) *
      step ^ 2 := by
  have firstBound := Readings.PrimitiveAreaBounds.PrimitivePoint.area_bound firstLe rightLe
  rw [← Gaussian.Norm.Basic.normSq_eq_canonical] at firstBound
  have lastBound := Readings.PrimitiveAreaBounds.PrimitivePoint.area_bound lastLe rightLe
  rw [← Gaussian.Norm.Basic.normSq_eq_canonical] at lastBound
  have driftBound := Readings.PrimitiveAreaBounds.PrimitivePoint.area_bound firstLe driftLe
  rw [← Gaussian.Norm.Basic.normSq_eq_canonical] at driftBound
  have pair := (Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
    (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add firstBound lastBound) (by decide))
  exact (Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
    ((Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add pair driftBound) (by decide)).trans_eq
      (by ring1))

end Bilinear

open Purelib.Algebra in
open Purelib.Integration in
open Purelib.Data in
set_option genInjectivity false in
/-- Cached two-differential ribbon areas, edge corrections and endpoint contribution.

Every cache has an exact equation to the same two retained scalar ribbons. The difference subtracts both right area and
the retained endpoint term from left area. -/
structure Bilinear (first second : Path.BoundaryRibbon.Ribbon count) where
  /-- The materialized correction for each retained ribbon edge. -/ corrections : Data.Vector
    Gaussian.Basic.Canonical count
  /-- Each correction is computed from the exact ribbon endpoints and their retained errors. -/ corrections_eq : ∀ edge,
    corrections edge = Bilinear.correction
    ⟨first.right edge.castSucc, second.right edge.castSucc⟩ ⟨first.right edge.succ, second.right edge.succ⟩
    ⟨first.errors edge.castSucc, second.errors edge.castSucc⟩ ⟨first.errors edge.succ, second.errors edge.succ⟩
  /-- The cached total area from the two left ribbon readings. -/ leftArea : Gaussian.Basic.Canonical
  /-- The left-area cache equals the finite sum of actual left edge pairings. -/ leftArea_eq : leftArea =
    FiniteSum.Fin.sumFin (fun edge : Fin count => edgeArea
    ⟨first.left edge.castSucc, second.left edge.castSucc⟩ ⟨first.left edge.succ, second.left edge.succ⟩)
  /-- The cached total area from the two right ribbon readings. -/ rightArea : Gaussian.Basic.Canonical
  /-- The right-area cache equals the finite sum of actual right edge pairings. -/ rightArea_eq : rightArea =
    FiniteSum.Fin.sumFin (fun edge : Fin count => edgeArea
    ⟨first.right edge.castSucc, second.right edge.castSucc⟩ ⟨first.right edge.succ, second.right edge.succ⟩)
  /-- The cached final-minus-initial endpoint error pairing. -/ endpoint : Gaussian.Basic.Canonical
  /-- The endpoint cache reads the exact first and last retained ribbon values and errors. -/ endpoint_eq : endpoint =
    edgeArea ⟨first.right (Fin.last count), second.right (Fin.last count)⟩ ⟨first.errors (Fin.last count), second.errors
      (Fin.last count)⟩ -
    edgeArea ⟨first.right 0, second.right 0⟩ ⟨first.errors 0, second.errors 0⟩
  /-- The cached area difference after subtracting the endpoint contribution. -/ difference : Gaussian.Basic.Canonical
  /-- The difference equals left area minus right area minus endpoint contribution. -/ difference_eq : difference =
    leftArea - rightArea - endpoint

constructive_injectivity Bilinear

namespace Bilinear

variable {count : Nat} {first second : Ribbon count}

open Purelib.Algebra in
open Purelib.Integration in
open Purelib.Data in
/-- Materialize the bilinear ribbon's corrections, two areas and endpoint contribution once. -/
def build (first second : Path.BoundaryRibbon.Ribbon count) : Bilinear first second :=
  let corrections := Vector.Basic.vectorOfFn fun edge : Fin count => correction
    ⟨first.right edge.castSucc, second.right edge.castSucc⟩ ⟨first.right edge.succ, second.right edge.succ⟩
    ⟨first.errors edge.castSucc, second.errors edge.castSucc⟩ ⟨first.errors edge.succ, second.errors edge.succ⟩
  let leftArea := FiniteSum.Fin.sumFin fun edge : Fin count => edgeArea
    ⟨first.left edge.castSucc, second.left edge.castSucc⟩ ⟨first.left edge.succ, second.left edge.succ⟩
  let rightArea := FiniteSum.Fin.sumFin fun edge : Fin count => edgeArea
    ⟨first.right edge.castSucc, second.right edge.castSucc⟩ ⟨first.right edge.succ, second.right edge.succ⟩
  let endpoint :=
    edgeArea ⟨first.right (Fin.last count), second.right (Fin.last count)⟩ ⟨first.errors (Fin.last count), second.errors
      (Fin.last count)⟩ -
    edgeArea ⟨first.right 0, second.right 0⟩ ⟨first.errors 0, second.errors 0⟩
  ⟨corrections, Vector.Basic.vectorOfFn_apply _, leftArea, rfl, rightArea, rfl, endpoint, rfl,
    leftArea - rightArea - endpoint, rfl⟩

open Purelib.Algebra in
open Purelib.Integration in
open Purelib.Topology in
/-- The endpoint-corrected ribbon difference equals the sum of retained edge corrections. -/
theorem difference_eq_sum (ribbon : Bilinear first second) : ribbon.difference = FiniteSum.Fin.sumFin ribbon.corrections
  := by
  rw [ribbon.difference_eq, ribbon.leftArea_eq, ribbon.rightArea_eq, ← FiniteSum.Fin.sumFin_sub]
  have edges := FiniteSum.Fin.sumFin_congr (fun edge : Fin count => area_difference
    (⟨first.left edge.castSucc, second.left edge.castSucc⟩ : PrimitivePoint)
    ⟨first.left edge.succ, second.left edge.succ⟩
    ⟨first.right edge.castSucc, second.right edge.castSucc⟩ ⟨first.right edge.succ, second.right edge.succ⟩)
  have readback (vertex : Fin (count + 1)) :
      (Polygon.Stokes.PrimitivePoint.sub (⟨first.left vertex, second.left vertex⟩ : PrimitivePoint)) ⟨first.right
        vertex, second.right vertex⟩ =
        ⟨first.errors vertex, second.errors vertex⟩ := by
    rw [first.errors_eq, second.errors_eq]
    rfl
  simp only [readback, ← ribbon.corrections_eq] at edges
  rw [edges, FiniteSum.Fin.sumFin_add, Path.BoundaryRibbon.sum_increasing (fun vertex => edgeArea
    ⟨first.right vertex, second.right vertex⟩ ⟨first.errors vertex, second.errors vertex⟩), ribbon.endpoint_eq]
  ring1

open Purelib.Riemann in
open Purelib.Integration in
open Purelib.Data in
/-- Bound the cached corrected ribbon difference using common pointwise error and increment bounds.

The finite-sum estimate retains the actual edge count and pays eight times error times the slope-and-drift factor times
total count-scaled step squared. -/
theorem difference_bound (ribbon : Bilinear first second) {error slope drift step : Path.BoundaryRibbon.Coordinate}
    (errors : ∀ vertex, (Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded (⟨first.errors vertex, second.errors
      vertex⟩ : PrimitivePoint)) error)
    (increments : ∀ edge : Fin count,
      (Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded (⟨first.right edge.succ - first.right edge.castSucc,
        second.right edge.succ - second.right edge.castSucc⟩ : PrimitivePoint)) (slope * step ^ 2))
    (drifts : ∀ edge : Fin count,
      (Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded (⟨first.errors edge.succ - first.errors edge.castSucc,
        second.errors edge.succ - second.errors edge.castSucc⟩ : PrimitivePoint)) (drift * step ^ 2)) :
    Data.Gaussian.Norm.Basic.normSq ribbon.difference ≤ 8 * error * (4 * slope + drift) * ((count :
      Path.BoundaryRibbon.Coordinate) * step) ^ 2 := by
  rw [ribbon.difference_eq_sum]
  have bounded := Gaussian.Norm.Sum.Indexed.normSq_sumFin_le (fun edge => ribbon.corrections edge)
    (8 * error * (4 * slope + drift) * step ^ 2) (fun edge => by
      rw [ribbon.corrections_eq]
      exact correction_bound (errors edge.castSucc) (errors edge.succ) (increments edge) (drifts edge))
  exact bounded.trans_eq (by ring1)

end Bilinear
end Purelib.Riemann.Periods.BilinearBoundaryRibbon
