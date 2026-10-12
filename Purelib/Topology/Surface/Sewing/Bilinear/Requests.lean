module
import Purelib.Algebra.FiniteSum.Fin.Rational
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
public import Purelib.Approximation.Rational.Budget.Aggregate
public import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.CCL.Calculus.WeightedAggregateBudget
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.Bilinear.Samples
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.SewnPrimitiveAccounting
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
public import Purelib.Topology.Surface.Sewing.Bilinear.Errors
public import Purelib.Topology.Surface.Sewing.SewnPrimitiveRequests
import Purelib.Data.Gaussian.Basic
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Field
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Data.Rat.Fraction
import Purelib.Data.Vector.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Data.Int.Cast.Defs
import Purelib.Tactic.Ring

public section

/-! Geometry-first contact requests paying the complete bilinear sewing
error. Both differential samples consume the same cached request. -/

namespace Purelib.Topology.Surface.Sewing.Bilinear.Requests

open Purelib.Algebra

open Purelib.Approximation.Rational.Budget

open Purelib.CCL.Calculus

open Purelib.Data.Gaussian.Norm.Basic

open Purelib.Data.Rat

open Purelib.Riemann.Readings.PrimitiveAreaBounds

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Sewing.Bilinear

open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces

open Purelib.Topology.Polygon.Stokes (OrientedTriangle PrimitivePoint triangleWedgeArea)

open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Algebra.FiniteSum.Fin (sumFin)
open Purelib.Topology.Surface.Sewing.SewingTree (SewnPatch)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveAccounting (Shape shape)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces (Coordinate)
open Purelib.Topology.Surface.Sewing.PrimitiveSewing (PrimitiveValues)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveRequests (LocalAccuracy totalCharge_le)
open Purelib.Topology.Surface.Sewing.Bilinear.Errors (traceAt)
open _root_.Purelib.Topology.Surface.Sewing.Bilinear renaming Samples -> Bilinear
open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces (FaceBank)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveAccounting (trace_allowance_le)

variable {vertexCount faceCount : Nat} {faces : Fin faceCount → Stokes.OrientedTriangle vertexCount}
  {patch : SewingTree.SewnPatch faces}

set_option genInjectivity false in
/-- Cached contact tolerance paying the complete bilinear sewing area error.

The retained assembly profile determines amplification; the magnitude bound, full face count and positive target
determine the weighted local error and contact tolerance. -/
structure AreaRequest (patch : SewingTree.SewnPatch faces) (magnitude target : SewnPrimitiveFaces.Coordinate) where
  /-- The requested total area-error target is strictly positive. -/ positive : 0 < target
  /-- The supplied primitive magnitude bound is nonnegative. -/ nonnegative : 0 ≤ magnitude
  /-- Cached sewing depth and amplification profile of the original assembly. -/ profile : SewnPrimitiveAccounting.Shape
  /-- The retained profile is computed from the exact original assembly. -/ profile_eq : profile =
    SewnPrimitiveAccounting.shape patch.assembly
  /-- Cached conversion factor from contact tolerance to face allowance. -/ amplification :
    SewnPrimitiveFaces.Coordinate
  /-- The amplification is the retained profile depth times its factor. -/ amplification_eq : amplification =
    (profile.depth : SewnPrimitiveFaces.Coordinate) * profile.factor
  /-- Cached factor converting primitive increment error to bilinear area error. -/ weight :
    SewnPrimitiveFaces.Coordinate
  /-- The area weight is thirty-two times the supplied magnitude plus one. -/ weight_eq : weight = 32 * (magnitude + 1)
  /-- Cached local face-error allowance, capped at one. -/ error : SewnPrimitiveFaces.Coordinate
  /-- The local error pays the weighted total target over the complete retained face count. -/ error_eq : error = min 1
    (Aggregate.perTerm
    (Weighted.allowance target weight) patch.cut.triangles.length)
  /-- Cached contact tolerance consumed by both original scalar samples. -/ tolerance : SewnPrimitiveFaces.Coordinate
  /-- The contact tolerance pays the retained local error under assembly amplification. -/ tolerance_eq : tolerance =
    Weighted.allowance error amplification

constructive_injectivity AreaRequest

namespace AreaRequest

variable {magnitude target : SewnPrimitiveFaces.Coordinate}

/-- Cache the original assembly profile and all weighted allowances for the supplied magnitude and target. -/
@[expose] def build (patch : SewingTree.SewnPatch faces) (magnitude target : SewnPrimitiveFaces.Coordinate)
    (nonnegative : 0 ≤ magnitude) (positive : 0 < target) : AreaRequest patch magnitude target :=
  let profile := SewnPrimitiveAccounting.shape patch.assembly
  let amplification := Aggregate.countCoordinate profile.depth *
    Aggregate.countCoordinate profile.factor
  let weight := 32 * (magnitude + 1)
  let error := min 1 (Aggregate.perTerm
    (Weighted.allowance target weight) patch.cut.triangles.length)
  ⟨positive, nonnegative, profile, rfl, amplification, by
    dsimp only [amplification]
    rw [Aggregate.countCoordinate_eq, Aggregate.countCoordinate_eq],
    weight, rfl, error, rfl, Weighted.allowance error amplification, rfl⟩

/-- The retained assembly amplification is nonnegative. -/
theorem amplification_nonnegative (request : AreaRequest patch magnitude target) : 0 ≤ request.amplification :=
  by
  rw [request.amplification_eq]
  exact Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _))
    (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _))

/-- A nonnegative input magnitude gives a nonnegative bilinear area weight. -/
theorem weight_nonnegative (request : AreaRequest patch magnitude target) : 0 ≤ request.weight := by
  rw [request.weight_eq]
  exact Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) (add_nonneg request.nonnegative (by decide))

/-- The retained per-face error allowance is positive. -/
theorem error_positive (request : AreaRequest patch magnitude target) : 0 < request.error := by
  rw [request.error_eq]
  exact Fraction.Order.Basic.lt_min (by decide) (Aggregate.perTerm_positive
    (Weighted.allowance_positive request.positive request.weight_nonnegative) _)

/-- The retained contact tolerance is positive. -/
theorem tolerance_positive (request : AreaRequest patch magnitude target) : 0 < request.tolerance := by
  rw [request.tolerance_eq]
  exact Weighted.allowance_positive request.error_positive request.amplification_nonnegative

open Purelib.Topology.Surface.Sewing.Bilinear.Requests.AreaRequest in
/-- Contact accuracy at the retained tolerance pays each original cached face allowance. -/
theorem trace_bound {localValues : Fin faceCount → PrimitiveSewing.PrimitiveValues 3}
    (request : AreaRequest patch magnitude target) (surface : SewnPrimitiveSamples.CachedSample patch
      localValues)
    (accurate : SewnPrimitiveRequests.LocalAccuracy request.tolerance surface.sewn.readings)
    (position : Fin patch.cut.triangles.length) : (Errors.traceAt surface position).allowance ≤ request.error := by
  have member : Errors.traceAt surface position ∈ (FaceBank.build surface.sewn.readings).entries := by
    rw [← surface.faces_eq]
    exact List.getElem_mem _
  have estimate := SewnPrimitiveAccounting.trace_allowance_le surface.sewn.readings (Errors.traceAt surface position)
    member
  have charged := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (SewnPrimitiveRequests.totalCharge_le
    accurate)
    (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le (SewnPrimitiveAccounting.shape patch.assembly).depth))
  have paid : request.amplification * request.tolerance ≤ request.error := by
    rw [request.tolerance_eq]
    exact Weighted.mul_allowance_le request.error_positive.le request.amplification_nonnegative
  have equal : (SewnPrimitiveAccounting.shape patch.assembly).depth * ((SewnPrimitiveAccounting.shape
    patch.assembly).factor * request.tolerance) =
      request.amplification * request.tolerance := by
    rw [request.amplification_eq, request.profile_eq]
    ring1
  exact (estimate.trans charged).trans (equal.le.trans paid)

/-- The two original contact-accuracy certificates pay the complete requested bilinear boundary-area error. -/
theorem accurate {leftLocal rightLocal : Fin faceCount → PrimitiveSewing.PrimitiveValues 3}
    {left : SewnPrimitiveSamples.CachedSample patch leftLocal} {right : SewnPrimitiveSamples.CachedSample patch
      rightLocal}
    (request : AreaRequest patch magnitude target) (sample : Samples left right)
    (leftAccurate : SewnPrimitiveRequests.LocalAccuracy request.tolerance left.sewn.readings)
    (rightAccurate : SewnPrimitiveRequests.LocalAccuracy request.tolerance right.sewn.readings)
    (bounded : ∀ position (index : Fin 3),
      (PrimitivePoint.Bounded (⟨leftLocal (Errors.traceAt left position).source index - leftLocal (Errors.traceAt left
        position).source 0,
        rightLocal (Errors.traceAt left position).source index - rightLocal (Errors.traceAt left position).source 0⟩ :
          Purelib.Topology.Polygon.Stokes.PrimitivePoint)) magnitude) :
    Data.Gaussian.Norm.Basic.normSq (sample.boundaryArea - FiniteSum.Fin.sumFin (fun position =>
      Stokes.triangleWedgeArea
      ⟨leftLocal (Errors.traceAt left position).source 0, rightLocal (Errors.traceAt left position).source 0⟩
      ⟨leftLocal (Errors.traceAt left position).source 1, rightLocal (Errors.traceAt left position).source 1⟩
      ⟨leftLocal (Errors.traceAt left position).source 2, rightLocal (Errors.traceAt left position).source 2⟩)) < target
        := by
  have small : request.error ≤ 1 := by rw [request.error_eq]; exact Fraction.Order.Basic.min_le_left _ _
  have estimate := Errors.boundary_area_error sample (fun _ => request.error) request.nonnegative
    (fun _ => request.error_positive.le) (fun _ => small)
    (request.trace_bound left leftAccurate) (request.trace_bound right rightAccurate) bounded
  rw [FiniteSum.Fin.Rational.sum_constant, ← request.weight_eq] at estimate
  have weighted : request.weight * request.error ≤
      Aggregate.perTerm target patch.cut.triangles.length := by
    have errorLe : request.error ≤ Aggregate.perTerm
        (Weighted.allowance target request.weight) patch.cut.triangles.length := by
      rw [request.error_eq]
      exact Fraction.Order.Basic.min_le_right _ _
    exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct errorLe
      request.weight_nonnegative).trans
      (WeightedAggregateBudget.weighted_perTerm_le request.positive request.weight_nonnegative _)
  have countNonnegative := Fraction.Cast.Order.natCast_le_direct (Nat.zero_le patch.cut.triangles.length)
  exact estimate.trans_lt ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct weighted countNonnegative)
    countNonnegative).trans_lt (Aggregate.count_mul_perTerm_lt request.positive _))

end AreaRequest
end Purelib.Topology.Surface.Sewing.Bilinear.Requests
