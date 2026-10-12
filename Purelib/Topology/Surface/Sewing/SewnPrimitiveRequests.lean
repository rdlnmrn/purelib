module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Order
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.PolygonSewing
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
public import Purelib.Topology.Surface.Sewing.SewnPrimitiveBoundary
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
public import Purelib.Topology.Surface.Sewing.SewnPrimitiveAccounting
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Data.Int.Cast.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Data.Nat.Init
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Vector.Basic
import Purelib.Topology.Surface.Sewing.SewingProjection
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.NatCast
import Purelib.Tactic.Ring

/-!
# Geometry-first accuracy requests for sewn primitives

The finite sewing shape fixes an amplification before local polynomials are
selected. Certified local mismatches then bound the sum of actual seam
charges and the squared errors of every sewn face. This does not assert that
arbitrary local polynomials meet the requested tolerance; the analytic edge
controls supply those separate local obligations.
-/

public section

namespace Purelib.Topology.Surface.Sewing.SewnPrimitiveRequests

open Purelib.Data
open Purelib.Algebra
open Purelib.Data.Gaussian.Norm.Basic
open Purelib.Data.Rat
open Purelib.Topology.Polygon
open Purelib.Topology.Surface.Cut
open Purelib.Topology.Surface.Cut.Patch
open Purelib.Topology.Surface.Sewing
open Purelib.Topology.Surface.Sewing.PolygonSewing.PolygonStokes
open Purelib.Topology.Surface.Sewing.PrimitiveSewing
open Purelib.Topology.Surface.Sewing.PrimitiveSewing.CutPatch
open Purelib.Topology.Surface.Sewing.SewnPrimitiveBoundary.FaceBank
open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces

open Purelib.Topology.Surface.Cut.Patch (CutPatch)
open Purelib.Topology.Surface.Sewing.PrimitiveSewing (PrimitiveValues)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces (FaceBank Coordinate)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveAccounting
open Purelib.Topology.Surface.Sewing.SewnPrimitiveBoundary (TriangleEdgeOwner boundaryOwner seam_charge_le)
open Purelib.Topology.Surface.Sewing.PrimitiveSewing.EndpointGluing (PrimitiveSew)

open Purelib.Topology.Polygon.Stokes (OrientedEdge OrientedTriangle)

open Purelib.Data.Gaussian.Basic.Canonical

variable {vertexCount faceCount : Nat} {faces : Fin faceCount → Stokes.OrientedTriangle vertexCount}
  {localValues : Fin faceCount → PrimitiveSewing.PrimitiveValues 3}

/-- Recover the assembly's geometry profile from its indexed reading tree. -/
private abbrev readingShape {indices : List (Fin faceCount)} {boundary : List (Stokes.OrientedEdge vertexCount)}
    {patch : Patch.CutPatch faces indices boundary} {assembly : CutPatch.Assembly faces patch}
    {values : PrimitiveSewing.PrimitiveValues patch.count} (_readings : Assembly.Readings localValues assembly values) :
      Shape := SewnPrimitiveAccounting.shape assembly

/-- Existence of original boundary owners whose local seam increments meet a common tolerance.

The comparison uses the retained face-bank readbacks at those owners, keeping their inherited sewing discrepancies
separate. -/
@[expose] def LocalMismatch {firstIndices secondIndices : List (Fin faceCount)}
      {firstBoundary secondBoundary : List (Stokes.OrientedEdge vertexCount)}
      {first : Patch.CutPatch faces firstIndices firstBoundary} {second : Patch.CutPatch faces secondIndices
        secondBoundary}
      {leftValues : PrimitiveSewing.PrimitiveValues first.count} {rightValues : PrimitiveSewing.PrimitiveValues
        second.count}
      {firstEdge : Stokes.OrientedEdge first.count} {secondEdge : Stokes.OrientedEdge second.count}
      (left : SewnPrimitiveFaces.FaceBank first localValues leftValues) (right : SewnPrimitiveFaces.FaceBank second
        localValues rightValues)
      (_joined : EndpointGluing.PrimitiveSew leftValues rightValues firstEdge secondEdge) (tolerance :
        SewnPrimitiveFaces.Coordinate) : Prop :=
  ∃ (firstOwner : SewnPrimitiveBoundary.TriangleEdgeOwner first.triangles firstEdge) (secondOwner :
    SewnPrimitiveBoundary.TriangleEdgeOwner second.triangles secondEdge),
    Data.Gaussian.Norm.Basic.normSq ((EdgeReading.build left firstOwner).localIncrement +
      (EdgeReading.build right secondOwner).localIncrement) ≤ tolerance

/-- Each obligation uses original face increments at retained geometric owners, not the already modified sewn
increments.

The recursive certificate follows the assembly tree and retains the local mismatch bound at every actual sewing seam. -/
@[expose] def LocalAccuracy (tolerance : SewnPrimitiveFaces.Coordinate) :
    {indices : List (Fin faceCount)} → {boundary : List (Stokes.OrientedEdge vertexCount)} →
    {patch : Patch.CutPatch faces indices boundary} → {assembly : CutPatch.Assembly faces patch} →
    {values : PrimitiveSewing.PrimitiveValues patch.count} → Assembly.Readings localValues assembly values → Prop
  | _, _, _, _, _, .triangle _ => True
  | _, _, _, _, _, .sew left right joined =>
      Purelib.Topology.Surface.Sewing.SewnPrimitiveRequests.LocalAccuracy tolerance left ∧
        Purelib.Topology.Surface.Sewing.SewnPrimitiveRequests.LocalAccuracy tolerance right ∧
        SewnPrimitiveRequests.LocalMismatch (FaceBank.build left) (FaceBank.build right) joined tolerance

/-- Uniform original-contact accuracy bounds all actual sewing charges by the assembly factor.

Each seam is charged using its retained local tolerance. The recursive estimate includes both subassemblies and the full
assembly-depth factor. -/
theorem totalCharge_le {indices : List (Fin faceCount)} {boundary : List (Stokes.OrientedEdge vertexCount)}
    {patch : Patch.CutPatch faces indices boundary} {assembly : CutPatch.Assembly faces patch}
    {values : PrimitiveSewing.PrimitiveValues patch.count} {readings : Assembly.Readings localValues assembly values}
    {tolerance : SewnPrimitiveFaces.Coordinate} : SewnPrimitiveRequests.LocalAccuracy tolerance readings →
      SewnPrimitiveAccounting.totalCharge readings ≤ ((SewnPrimitiveAccounting.shape assembly).factor :
        SewnPrimitiveFaces.Coordinate) * tolerance := by
  induction readings with
  | triangle =>
      intro _
      change (0 : SewnPrimitiveFaces.Coordinate) ≤ 0 * tolerance
      rewrite [Fraction.Field.zero_mul_direct]
      exact Fraction.Order.Basic.le_refl _
  | sew left right joined ihLeft ihRight =>
      rintro ⟨leftAccurate, rightAccurate, firstOwner, secondOwner, matched⟩
      have ihLeft := ihLeft leftAccurate
      have ihRight := ihRight rightAccurate
      let leftReading := EdgeReading.build (FaceBank.build left) firstOwner
      let rightReading := EdgeReading.build (FaceBank.build right) secondOwner
      have leftBound := SewnPrimitiveAccounting.trace_allowance_le left leftReading.trace (by
        rw [leftReading.trace_eq]
        exact List.getElem_mem _)
      have rightBound := SewnPrimitiveAccounting.trace_allowance_le right rightReading.trace (by
        rw [rightReading.trace_eq]
        exact List.getElem_mem _)
      have newBound := (SewnPrimitiveBoundary.seam_charge_le joined leftReading rightReading tolerance matched).trans
        (Fraction.Order.Arithmetic.add_le_add_direct (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Fraction.Order.Arithmetic.add_le_add_direct leftBound rightBound) (by decide)) (Fraction.Order.Basic.le_refl
          _))
      exact Shape.charge_bound (SewnPrimitiveRequests.readingShape left) (SewnPrimitiveRequests.readingShape right) _ _
        _ tolerance ihLeft ihRight newBound

/-- Independent face translations introduce no mismatch. This includes zero local data on an arbitrarily deep assembly,
with no error floor. -/
theorem localAccuracy_of_constant {indices : List (Fin faceCount)} {boundary : List (Stokes.OrientedEdge vertexCount)}
    {patch : Patch.CutPatch faces indices boundary} {assembly : CutPatch.Assembly faces patch}
    {values : PrimitiveSewing.PrimitiveValues patch.count} (readings : Assembly.Readings localValues assembly values)
    (constant : ∀ source index, localValues source index = localValues source 0)
    {tolerance : SewnPrimitiveFaces.Coordinate} (nonnegative : 0 ≤ tolerance) : SewnPrimitiveRequests.LocalAccuracy
      tolerance readings := by
  have zero (source : Fin faceCount) (first last : Fin 3) : localValues source last - localValues source first = 0 := by
    rw [constant source last, constant source first, Gaussian.Basic.sub_self]
  induction readings with
  | triangle => exact True.intro
  | sew left right joined ihLeft ihRight =>
      refine ⟨ihLeft, ihRight, SewnPrimitiveBoundary.boundaryOwner _ _ ?_, SewnPrimitiveBoundary.boundaryOwner _ _ ?_,
        ?_⟩
      · exact BoundarySplit.edge_mem _
      · exact BoundarySplit.edge_mem _
      · rw [EdgeReading.localIncrement_eq,
          EdgeReading.localIncrement_eq,
          zero, zero, Gaussian.Basic.add_zero, Gaussian.Norm.Basic.normSq_zero]
        exact nonnegative

namespace Shape

/-- Integer factor paying both affine errors of every face through the assembly depth. -/
@[expose] def amplification (profile : SewnPrimitiveAccounting.Shape) : Nat := 2 * profile.faces * profile.depth *
  profile.factor

/-- Executable rational representation of the exact integer amplification. -/
@[expose] def amplificationCoordinate (profile : SewnPrimitiveAccounting.Shape) : Coordinate :=
  Fraction.Cast.fromInt (Int.ofNat (Shape.amplification profile))

/-- The cached amplification equals twice the face count times depth times charge factor. -/
theorem amplificationCoordinate_eq (profile : SewnPrimitiveAccounting.Shape) :
    Shape.amplificationCoordinate profile = 2 * (profile.faces : SewnPrimitiveFaces.Coordinate) * profile.depth *
      profile.factor := by
  have equal : Shape.amplificationCoordinate profile = ((Shape.amplification profile) : SewnPrimitiveFaces.Coordinate)
    :=
    (Fraction.Cast.natCast_eq_fromInt (Shape.amplification profile)).symm
  rw [equal]
  simp only [amplification, NatCast.mul, Nat.cast_ofNat, -eq_self]
  rfl

/-- The assembly's rational amplification is nonnegative. -/
theorem amplification_nonnegative (profile : SewnPrimitiveAccounting.Shape) : 0 ≤ Shape.amplificationCoordinate profile
  := by
  have equal : Shape.amplificationCoordinate profile = ((Shape.amplification profile) : SewnPrimitiveFaces.Coordinate)
    :=
    (Fraction.Cast.natCast_eq_fromInt (Shape.amplification profile)).symm
  rw [equal]
  exact Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)

end Shape

variable {indices : List (Fin faceCount)} {boundary : List (Stokes.OrientedEdge vertexCount)}
  {patch : Patch.CutPatch faces indices boundary} {assembly : CutPatch.Assembly faces patch}

set_option genInjectivity false in
/-- Cache the geometry-only amplification in binary rational form.

The request retains the indexed assembly profile, its exact amplification and a local tolerance determined by the
aggregate target. -/
structure Request (assembly : CutPatch.Assembly faces patch) (target : SewnPrimitiveFaces.Coordinate) where
  /-- The requested aggregate squared-error target is strictly positive. -/ target_positive : 0 < target
  /-- Retained geometry-only accounting profile. -/ profile : SewnPrimitiveAccounting.Shape
  /-- The cached profile is exactly the original assembly's computed shape. -/ profile_eq : profile =
    SewnPrimitiveAccounting.shape assembly
  /-- Cached rational factor paying every face's inherited errors. -/ amplification : SewnPrimitiveFaces.Coordinate
  /-- The retained factor is the profile's exact amplification coordinate. -/ amplification_eq : amplification =
    SewnPrimitiveRequests.Shape.amplificationCoordinate profile
  /-- Cached common local-contact tolerance. -/ tolerance : SewnPrimitiveFaces.Coordinate
  /-- The tolerance divides the target by one plus the retained amplification. -/ tolerance_eq : tolerance = target /
    (amplification + 1)

constructive_injectivity Request

namespace Request

variable {target : SewnPrimitiveFaces.Coordinate}

/-- Compute a geometry profile and retain a local tolerance for a positive aggregate target. -/
@[expose] def build (assembly : CutPatch.Assembly faces patch) (target : SewnPrimitiveFaces.Coordinate) (positive : 0 <
  target) : SewnPrimitiveRequests.Request assembly target :=
  let profile := SewnPrimitiveAccounting.shape assembly
  let amplification := SewnPrimitiveRequests.Shape.amplificationCoordinate profile
  ⟨positive, profile, rfl, amplification, rfl, target / (amplification + 1), rfl⟩

/-- The request's retained aggregate amplification is nonnegative. -/
theorem amplification_nonnegative (request : SewnPrimitiveRequests.Request assembly target) : 0 ≤ request.amplification
  := by
  rw [request.amplification_eq]
  exact SewnPrimitiveRequests.Shape.amplification_nonnegative request.profile

/-- The request's retained local tolerance is strictly positive. -/
theorem tolerance_positive (request : SewnPrimitiveRequests.Request assembly target) : 0 < request.tolerance := by
  rw [request.tolerance_eq]
  exact Fraction.Order.Field.div_pos_direct request.target_positive
    (Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct request.amplification_nonnegative (by decide))

/-- Aggregate amplification times the chosen local tolerance is strictly below the target.

The target is positive and the denominator is the retained nonnegative amplification plus one, so the unused unit gives
a strict payment margin. -/
theorem paid (request : SewnPrimitiveRequests.Request assembly target) : request.amplification * request.tolerance <
  target := by
  have strict : request.amplification < request.amplification + 1 := by
    have shifted := Fraction.Order.Arithmetic.add_lt_add_left_direct (left := (0 : Coordinate)) (right := 1) (by decide)
      request.amplification
    rewrite [Fraction.add_comm request.amplification (0 : Coordinate), Fraction.zero_add] at shifted
    exact shifted
  have bound := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct strict request.tolerance_positive
  apply bound.trans_eq
  rw [request.tolerance_eq, Fraction.Field.mul_comm]
  exact Fraction.Field.div_mul_cancel_of_ne _ _
    (Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct request.amplification_nonnegative (by decide)).ne'

/-- All faces are paid by the requested target, even when the geometry changes between requests. No bound here treats
face count as a constant. -/
theorem accurate (request : SewnPrimitiveRequests.Request assembly target) {values : PrimitiveSewing.PrimitiveValues
  patch.count}
    (readings : Assembly.Readings localValues assembly values)
    (locallyAccurate : SewnPrimitiveRequests.LocalAccuracy request.tolerance readings) : (FaceBank.build
      readings).squaredErrors < target := by
  have scaleNonnegative : (0 : SewnPrimitiveFaces.Coordinate) ≤ 2 * ((SewnPrimitiveAccounting.shape assembly).faces :
    SewnPrimitiveFaces.Coordinate) * (SewnPrimitiveAccounting.shape assembly).depth :=
    Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)))
      (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _))
  have bound := (SewnPrimitiveAccounting.aggregate_le readings).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (SewnPrimitiveRequests.totalCharge_le locallyAccurate)
      scaleNonnegative)
  have factorEq : request.amplification =
      2 * ((SewnPrimitiveAccounting.shape assembly).faces : SewnPrimitiveFaces.Coordinate) *
        (SewnPrimitiveAccounting.shape assembly).depth * (SewnPrimitiveAccounting.shape assembly).factor := by
    rw [request.amplification_eq, SewnPrimitiveRequests.Shape.amplificationCoordinate_eq, request.profile_eq]
  apply (bound.trans_eq ?_).trans_lt request.paid
  rw [factorEq]
  ring1

end Request

end Purelib.Topology.Surface.Sewing.SewnPrimitiveRequests

end
