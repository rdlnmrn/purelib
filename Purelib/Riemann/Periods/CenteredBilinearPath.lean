module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.Rat.Fraction
import Purelib.Data.Vector.Basic
public import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Surface.Cut.PrimitiveJumps

import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Riemann.Periods.BilinearBoundaryRibbon
import Purelib.Topology.Surface.Boundary.HandleAreaBounds
import Purelib.Tactic.Ring

public section

/-! Centered paired path areas, with the exact origin-to-endpoint term.
Comparing total increments alone cannot replace these finite path areas. -/
namespace Purelib.Riemann.Periods.CenteredBilinearPath
open Purelib.Topology
open Purelib.Algebra
open Purelib.Data

open Purelib.Riemann.Periods.BilinearBoundaryRibbon
open Purelib.Topology.Surface.Boundary.HandleAreaBounds

open Purelib.Topology.Polygon.Stokes (PrimitivePoint edgeArea)
open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_add sumFin_sub)
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
/-- The rational scalar type for centered path comparison bounds. -/
abbrev Coordinate := Rat.Fraction.Rational

variable {count : Nat}

/-- Sum the bilinear edge areas along the finite primitive-point path. -/
@[expose] def area (values : Fin (count + 1) → PrimitivePoint) :=
  FiniteSum.Fin.sumFin (fun edge : Fin count => edgeArea (values edge.castSucc) (values edge.succ))

open Purelib.Integration in
/-- Translating a primitive path changes its area by the exact origin-to-endpoint term. -/
theorem area_translate (values : Fin (count + 1) → PrimitivePoint) (origin : PrimitivePoint) :
    area values = area (fun vertex => (Polygon.Stokes.PrimitivePoint.sub (values vertex)) origin) +
      (edgeArea origin (values (Fin.last count)) - edgeArea origin (values 0)) := by
  have edges := FiniteSum.Fin.sumFin_congr (fun edge : Fin count => show
    edgeArea (values edge.castSucc) (values edge.succ) =
      edgeArea ((Polygon.Stokes.PrimitivePoint.sub (values edge.castSucc)) origin) ((Polygon.Stokes.PrimitivePoint.sub
        (values edge.succ)) origin) +
        (edgeArea origin (values edge.succ) - edgeArea origin (values edge.castSucc)) by
    simp only [edgeArea, Polygon.Stokes.PrimitivePoint.sub]
    ring1)
  unfold area
  rw [edges, FiniteSum.Fin.sumFin_add, Path.BoundaryRibbon.sum_increasing (fun vertex => edgeArea origin (values
    vertex))]

set_option genInjectivity false in
/-- Cached centered path points, centered area, endpoint term and original area.

Every readback uses the same finite primitive path, and the exact decomposition retains the endpoint contribution. -/
structure Sample (values : Fin (count + 1) → PrimitivePoint) where
  /-- The materialized path points after subtracting the original first point. -/ centered : Data.Vector
    PrimitivePoint (count + 1)
  /-- Every centered cache entry equals the original point minus the retained origin. -/ centered_eq : ∀ vertex,
    centered vertex = (Polygon.Stokes.PrimitivePoint.sub (values vertex)) (values 0)
  /-- The cached area of the centered finite path. -/ centeredArea : Gaussian.Basic.Canonical
  /-- The centered-area cache is the area of the actual cached centered points. -/ centeredArea_eq : centeredArea = area
    (fun vertex => centered vertex)
  /-- The cached pairing of the original origin with the total endpoint increment. -/ endpoint :
    Gaussian.Basic.Canonical
  /-- The endpoint cache uses the original first point and actual final-minus-first increment. -/ endpoint_eq : endpoint
    = edgeArea (values 0) ((Polygon.Stokes.PrimitivePoint.sub (values (Fin.last count))) (values 0))
  /-- The cached original finite path area. -/ originalArea : Gaussian.Basic.Canonical
  /-- The original-area cache equals the area of the original point sequence. -/ originalArea_eq : originalArea = area
    values
  /-- The cached original area equals centered area plus endpoint contribution. -/ decomposition : originalArea =
    centeredArea + endpoint

constructive_injectivity Sample

namespace Sample

variable {values : Fin (count + 1) → PrimitivePoint}

/-- Materialize the centered point vector and exact area decomposition once. -/
@[expose] def build (values : Fin (count + 1) → PrimitivePoint) : Sample values :=
  let centered := Vector.Basic.vectorOfFn fun vertex => (Polygon.Stokes.PrimitivePoint.sub (values vertex)) (values 0)
  let centeredArea := area (fun vertex => centered vertex)
  let endpoint := edgeArea (values 0) ((Polygon.Stokes.PrimitivePoint.sub (values (Fin.last count))) (values 0))
  { centered := centered
    centered_eq := fun vertex => Vector.Basic.vectorOfFn_apply _ vertex
    centeredArea := centeredArea
    centeredArea_eq := rfl
    endpoint := endpoint
    endpoint_eq := rfl
    originalArea := centeredArea + endpoint
    originalArea_eq := by
      have translation := area_translate values (values 0)
      have endpointEq : edgeArea (values 0) (values (Fin.last count)) - edgeArea (values 0) (values 0) = endpoint := by
        dsimp only [endpoint, edgeArea, Polygon.Stokes.PrimitivePoint.sub]
        ring1
      rw [endpointEq] at translation
      have centeredEq : area (fun vertex => centered vertex) = area (fun vertex => (Polygon.Stokes.PrimitivePoint.sub
        (values vertex)) (values 0)) := by
        unfold area
        apply FiniteSum.Fin.sumFin_congr
        intro edge
        dsimp only [centered]
        rw [Vector.Basic.vectorOfFn_apply, Vector.Basic.vectorOfFn_apply]
      change area (fun vertex => centered vertex) + endpoint = area values
      rw [centeredEq]
      exact translation.symm
    decomposition := rfl }

open Purelib.Riemann in
/-- Bound the difference of two path areas after removing their exact endpoint contributions.

The right centered path has a common nonnegative magnitude bound, and centered point errors have a common nonnegative
bound at most one. The finite estimate pays the actual edge count squared. -/
theorem comparison {first last : Fin (count + 1) → PrimitivePoint} (left : Sample first) (right : Sample last)
    {magnitude error : Coordinate} (nonnegative : 0 ≤ magnitude) (errorNonnegative : 0 ≤ error) (small : error ≤ 1)
    (bounded : ∀ vertex, (Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded (right.centered vertex)) magnitude)
    (accurate : ∀ vertex, (Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded ((Polygon.Stokes.PrimitivePoint.sub
      (left.centered vertex)) (right.centered vertex))) error) :
    Data.Gaussian.Norm.Basic.normSq ((left.originalArea - right.originalArea) - (left.endpoint - right.endpoint)) ≤
      (count : Coordinate) ^ 2 * (32 * (magnitude + 1) * error) := by
  have estimate := Gaussian.Norm.Sum.Indexed.normSq_sumFin_le
    (fun edge : Fin count => edgeArea (left.centered edge.castSucc) (left.centered edge.succ) -
      edgeArea (right.centered edge.castSucc) (right.centered edge.succ))
    (32 * (magnitude + 1) * error)
    (fun edge => PrimitivePoint.area_difference_bound
      (first := right.centered edge.castSucc) (last := right.centered edge.succ)
      (changedFirst := left.centered edge.castSucc) (changedLast := left.centered edge.succ) nonnegative
        errorNonnegative small
      (bounded edge.castSucc) (bounded edge.succ) (accurate edge.castSucc) (accurate edge.succ))
  rw [FiniteSum.Fin.sumFin_sub] at estimate
  have equal : (left.originalArea - right.originalArea) - (left.endpoint - right.endpoint) =
      left.centeredArea - right.centeredArea := by
    rw [left.decomposition, right.decomposition]
    ring1
  rw [equal, left.centeredArea_eq, right.centeredArea_eq]
  exact estimate

end Sample
end Purelib.Riemann.Periods.CenteredBilinearPath

end

namespace Purelib.Riemann.Periods.CenteredBilinearPath

open Purelib
open Purelib.Data
open Purelib.Algebra
open Purelib.Topology

/-- Pointwise equal retained vertex readings have equal centered sample areas.

Both cached samples retain their original data and specification equalities.
Each edge uses the same centered endpoint values after the supplied scalar transport. -/
public theorem Sample.centeredArea_congr {size : Nat} {first last : Fin (size + 1) → Polygon.Stokes.PrimitivePoint}
    (left : Sample first) (right : Sample last) (equal : ∀ vertex, first vertex = last vertex) :
    left.centeredArea = right.centeredArea := by
  rw [left.centeredArea_eq, right.centeredArea_eq]
  apply FiniteSum.Fin.sumFin_congr
  intro edge
  have readback (vertex) : left.centered vertex = right.centered vertex := by
    rw [left.centered_eq, right.centered_eq, equal vertex, equal 0]
  exact congrArg₂ Polygon.Stokes.edgeArea (readback edge.castSucc) (readback edge.succ)

end Purelib.Riemann.Periods.CenteredBilinearPath
