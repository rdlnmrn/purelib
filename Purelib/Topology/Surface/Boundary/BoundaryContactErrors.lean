module
import Purelib.Algebra.NatCast
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Order
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewnPrimitiveAccounting
import Purelib.Topology.Surface.Sewing.SewnPrimitiveBoundary
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
import Purelib.Topology.Surface.Sewing.SewnPrimitiveRequests
import Purelib.Topology.Surface.Word.ProjectedEdgePairs
public import Purelib.Topology.Surface.Boundary.BoundaryContactSources
import Purelib.Data.Vector.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Data.Int.Cast.Defs
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Tactic.Ring

open Purelib

open Purelib.Data

open Purelib.Data.Gaussian.Norm.Basic

open Purelib.Data.Rat

open Purelib.Data.Rat.Fraction

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Boundary

open Purelib.Topology.Surface.Cut

open Purelib.Topology.Surface.Cut.Patch

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Sewing.PrimitiveSewing.CutPatch

open Purelib.Topology.Surface.Sewing.SewnPrimitiveBoundary.FaceBank

open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts

open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts.FaceBank

open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces

open Purelib.Topology.Surface.Word

public section

/-!
# Paying exposed cut-pair errors after all ancestor sewings

A paired boundary defect is the original two-face mismatch plus the errors
of both retained source readings. The bound pays all three terms, even when
the original local mismatch vanishes but prior sewings changed the values.
-/

namespace Purelib.Topology.Surface.Boundary.BoundaryContactErrors

open Purelib.Topology.Surface.Cut.Patch (CutPatch)
open Purelib.Topology.Surface.Word.ProjectedEdgePairs (ProjectedEdgePair)
open Purelib.Topology.Surface.Sewing.PrimitiveSewing (PrimitiveValues)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces (FaceBank Coordinate)
open _root_.Purelib.Topology.Surface.Boundary (BoundaryContactSources)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveBoundary (TriangleEdgeOwner)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveAccounting (Shape shape totalCharge trace_allowance_le)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveRequests (LocalAccuracy totalCharge_le)

open Purelib.Topology.Polygon.Stokes (OrientedEdge OrientedTriangle)

open Purelib.Data.Gaussian.Basic.Canonical

variable {vertexCount faceCount : Nat} {faces : Fin faceCount → Stokes.OrientedTriangle vertexCount}
  {indices : List (Fin faceCount)} {boundary : List (Stokes.OrientedEdge vertexCount)}
  {patch : Patch.CutPatch faces indices boundary} {pair : ProjectedEdgePairs.ProjectedEdgePair patch.vertexLabels}
  {localValues : Fin faceCount → PrimitiveSewing.PrimitiveValues 3} {values : PrimitiveSewing.PrimitiveValues
    patch.count}

namespace BoundaryContactSources

/-- Squared norm of the summed increments on the two exposed cut edges. -/
@[expose] def mismatch (_sources : BoundaryContactSources patch pair) (values :
  PrimitiveSewing.PrimitiveValues patch.count) : Coordinate :=
  Data.Gaussian.Norm.Basic.normSq ((values pair.first.finish - values pair.first.start) + (values pair.second.finish -
    values
    pair.second.start))

open Purelib.Topology.Surface.Boundary.BoundaryContactErrors
/-- Bound an exposed-pair mismatch by both inherited reading errors and its original source mismatch. -/
theorem mismatch_le (sources : BoundaryContactSources patch pair) (bank :
  SewnPrimitiveFaces.FaceBank patch localValues values) :
    mismatch sources values ≤
      4 * ((EdgeReading.build bank sources.first).allowance + (EdgeReading.build bank sources.second).allowance) +
        2 * SourceContact.mismatch sources.contact localValues := by
  let first := EdgeReading.build bank sources.first
  let second := EdgeReading.build bank sources.second
  have equal : (values pair.first.finish - values pair.first.start) + (values pair.second.finish - values
    pair.second.start) =
      (first.error + second.error) + (SourceEdge.increment sources.contact.left localValues + SourceEdge.increment
        sources.contact.right localValues) := by
    rw [first.error_eq, second.error_eq, EdgeReading.source_increment first, EdgeReading.source_increment second,
      sources.first_eq, sources.second_eq]
    ring1
  unfold mismatch
  rw [equal]
  have errors := (Gaussian.Norm.Bounds.normSq_add_le_two first.error second.error).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add first.error_bound second.error_bound) (by
      decide))
  exact (Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add errors le_rfl) (by decide)).trans_eq (by
      change 2 * (2 * (first.allowance + second.allowance) + SourceContact.mismatch sources.contact localValues) = _
      ring1))

/-- Uniform local accuracy bounds the exposed-pair mismatch using assembly depth and charge factor. -/
theorem mismatch_le_of_localAccuracy {assembly : CutPatch.Assembly faces patch}
    (sources : BoundaryContactSources patch pair) (readings : Assembly.Readings localValues
      assembly values)
    {tolerance : SewnPrimitiveFaces.Coordinate} (accurate : SewnPrimitiveRequests.LocalAccuracy tolerance readings)
    (matched : SourceContact.mismatch sources.contact localValues ≤ tolerance) :
    mismatch sources values ≤ (32 * ((SewnPrimitiveAccounting.shape assembly).depth :
      SewnPrimitiveFaces.Coordinate) * (SewnPrimitiveAccounting.shape assembly).factor + 2) * tolerance := by
  have allowance {edge : Stokes.OrientedEdge patch.count} (owner : SewnPrimitiveBoundary.TriangleEdgeOwner
    patch.triangles edge) :
      (EdgeReading.build (FaceBank.build readings) owner).allowance ≤
        4 * ((SewnPrimitiveAccounting.shape assembly).depth : SewnPrimitiveFaces.Coordinate) *
          SewnPrimitiveAccounting.totalCharge readings := by
    let reading := EdgeReading.build (FaceBank.build readings) owner
    have bound := SewnPrimitiveAccounting.trace_allowance_le readings reading.trace (by
      rw [reading.trace_eq]
      exact List.getElem_mem _)
    change reading.allowance ≤ _
    rw [reading.allowance_eq]
    exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct bound (by decide)).trans_eq (by ring1)
  have depthNonnegative : (0 : SewnPrimitiveFaces.Coordinate) ≤ 32 * ((SewnPrimitiveAccounting.shape assembly).depth :
    SewnPrimitiveFaces.Coordinate) := by
    have nonnegative : (0 : SewnPrimitiveFaces.Coordinate) ≤ ((32 * (SewnPrimitiveAccounting.shape assembly).depth :
      Nat) : SewnPrimitiveFaces.Coordinate) :=
      Cast.Order.natCast_le_direct (Nat.zero_le _)
    simpa only [Algebra.NatCast.mul, Nat.cast_ofNat] using nonnegative
  calc
    _ ≤ 4 * ((EdgeReading.build (FaceBank.build readings) sources.first).allowance +
        (EdgeReading.build (FaceBank.build readings) sources.second).allowance) +
          2 * SourceContact.mismatch sources.contact localValues := mismatch_le sources _
    _ ≤ 4 * (4 * ((SewnPrimitiveAccounting.shape assembly).depth : SewnPrimitiveFaces.Coordinate) *
      SewnPrimitiveAccounting.totalCharge readings +
        4 * ((SewnPrimitiveAccounting.shape assembly).depth : SewnPrimitiveFaces.Coordinate) *
          SewnPrimitiveAccounting.totalCharge readings) + 2 * tolerance :=
      add_le_add (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (add_le_add (allowance sources.first) (allowance sources.second)) (by decide))
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct matched (by decide))
    _ = (32 * ((SewnPrimitiveAccounting.shape assembly).depth : SewnPrimitiveFaces.Coordinate)) *
      SewnPrimitiveAccounting.totalCharge readings + 2 * tolerance := by
      ring1
    _ ≤ (32 * ((SewnPrimitiveAccounting.shape assembly).depth : SewnPrimitiveFaces.Coordinate)) *
      ((SewnPrimitiveAccounting.shape assembly).factor * tolerance) + 2 * tolerance :=
      add_le_add (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (SewnPrimitiveRequests.totalCharge_le
        accurate) depthNonnegative) le_rfl
    _ = _ := by ring1

end BoundaryContactSources

set_option genInjectivity false in
/-- One geometric scalar request pays both inherited sewing errors and the exposed pair's original local mismatch. -/
structure BoundaryContactRequest (assembly : CutPatch.Assembly faces patch) (target : SewnPrimitiveFaces.Coordinate)
  where
  /-- Strict positivity of the requested mismatch target. -/ positive : 0 < target
  /-- Retained finite depth and charge profile of the assembly. -/ profile : SewnPrimitiveAccounting.Shape
  /-- The retained profile belongs to this exact assembly. -/ profile_eq : profile = SewnPrimitiveAccounting.shape
    assembly
  /-- Cached scalar accounting for inherited sewing and original contact errors. -/ amplification :
    SewnPrimitiveFaces.Coordinate
  /-- The amplification is 32 times depth times factor, plus two. -/ amplification_eq : amplification = (32 *
    profile.depth * profile.factor + 2 : Nat)
  /-- Allocated uniform tolerance for local readings and source matching. -/ tolerance : SewnPrimitiveFaces.Coordinate
  /-- The tolerance is the target divided by one plus the retained amplification. -/ tolerance_eq : tolerance = target /
    (amplification + 1)

constructive_injectivity BoundaryContactRequest

namespace BoundaryContactRequest

variable {assembly : CutPatch.Assembly faces patch} {target : SewnPrimitiveFaces.Coordinate}

open Purelib.Topology.Surface.Boundary in
/-- Allocate contact tolerance from a retained assembly profile and a positive target.

The exact profile equation is preserved, and the tolerance divides the target by one plus its amplification. -/
@[expose] def ofProfile (profile : SewnPrimitiveAccounting.Shape) (profileEq : profile = SewnPrimitiveAccounting.shape
  assembly) (target : SewnPrimitiveFaces.Coordinate) (positive : 0 < target) :
    BoundaryContactRequest assembly target :=
  let amplification := Cast.fromInt (Int.ofNat (32 * profile.depth * profile.factor + 2))
  ⟨positive, profile, profileEq, amplification, (Cast.natCast_eq_fromInt _).symm, target / (amplification + 1), rfl⟩

open Purelib.Topology.Surface.Boundary in
open Purelib.Topology.Surface.Boundary.BoundaryContactErrors in
/-- Compute the assembly profile once and allocate a contact-error request. -/
@[expose] def build (assembly : CutPatch.Assembly faces patch) (target : SewnPrimitiveFaces.Coordinate) (positive : 0 <
  target) : BoundaryContactRequest assembly target :=
  ofProfile (SewnPrimitiveAccounting.shape assembly) rfl target positive

open Purelib.Topology.Surface.Boundary in
/-- The retained contact-error amplification is nonnegative. -/
theorem amplification_nonnegative (request : BoundaryContactRequest assembly target) : 0 ≤
  request.amplification := by
  rw [request.amplification_eq]
  exact Cast.Order.natCast_le_direct (Nat.zero_le _)

open Purelib.Topology.Surface.Boundary
open Purelib.Topology.Surface.Boundary.BoundaryContactErrors
/-- A positive target gives a strictly positive local contact tolerance. -/
theorem tolerance_positive (request : BoundaryContactRequest assembly target) : 0 <
  request.tolerance := by
  rw [request.tolerance_eq]
  exact Fraction.Order.Field.div_pos_direct request.positive
    (Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct (amplification_nonnegative
      request) (by decide))

/-- The amplification times the allocated tolerance is strictly below the target. -/
theorem paid (request : BoundaryContactRequest assembly target) : request.amplification *
  request.tolerance < target := by
  have strict : request.amplification < request.amplification + 1 := (by
    have translated :=
      Fraction.Order.Arithmetic.add_lt_add_left_direct (by decide : (0 : SewnPrimitiveFaces.Coordinate) < 1)
        request.amplification
    exact ((Fraction.Field.add_comm request.amplification 0).trans (Fraction.Field.zero_add
      request.amplification)).symm.trans_lt translated)
  apply (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct
    strict (tolerance_positive request)).trans_eq
  rw [request.tolerance_eq, Fraction.Field.mul_comm]
  exact Fraction.Field.div_mul_cancel_of_ne _ _
    (Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct (amplification_nonnegative
      request) (by decide)).ne'

/-- Accurate sewing readings and matched source contacts meet the requested exposed-pair bound. -/
theorem accurate (request : BoundaryContactRequest assembly target) (sources :
  BoundaryContactSources patch pair)
    (readings : Assembly.Readings localValues assembly values)
    (locallyAccurate : SewnPrimitiveRequests.LocalAccuracy request.tolerance readings) (matched : SourceContact.mismatch
      sources.contact localValues ≤ request.tolerance) :
    BoundaryContactSources.mismatch sources values < target := by
  have equal : request.amplification = 32 * ((SewnPrimitiveAccounting.shape assembly).depth :
    SewnPrimitiveFaces.Coordinate) * (SewnPrimitiveAccounting.shape assembly).factor + 2 := by
    rw [request.amplification_eq, request.profile_eq]
    simp only [-eq_self, -iff_self, Algebra.NatCast.add, Algebra.NatCast.mul, Nat.cast_ofNat]
    rfl
  exact (BoundaryContactSources.mismatch_le_of_localAccuracy sources readings locallyAccurate matched).trans_lt (equal ▸
    paid request)

end BoundaryContactRequest
end Purelib.Topology.Surface.Boundary.BoundaryContactErrors
