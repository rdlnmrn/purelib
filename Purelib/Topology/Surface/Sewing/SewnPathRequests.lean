module
import Purelib.Data.List.Map
import Purelib.Algebra.NatCast
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Rational.Squares
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
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
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.SewnPrimitiveAccounting
import Purelib.Topology.Surface.Sewing.SewnPrimitiveBoundary
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
import Purelib.Topology.Surface.Sewing.SewnPrimitiveRequests
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
public import Purelib.Topology.Surface.Sewing.SewnPrimitivePaths
public import Purelib.Topology.Surface.Sewing.SewnPrimitiveRefinement
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Data.Int.Cast.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Data.Nat.Init
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

open Purelib.Data.Rat.Fraction.Order

public section

/-!
# Geometry-first tolerances for complete sewn paths

The original contact mismatches pay every ancestor sewing charge and every
occurrence in a requested path. The bound retains both path-length factors,
including repeated or reversed edges. Geometry fixes the tolerance before
local primitive data are acquired; no exact seam matching is assumed.
-/

section

open Purelib.Algebra
open Purelib.Data.List

open Purelib.Algebra.FiniteSum.Rational

open Purelib.Approximation.Rational

open Purelib.Approximation.Rational.Geometric

open Purelib.Approximation.Rational.Geometric.Basic

open Purelib.Data.Rat

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Cut

open Purelib.Topology.Surface.Cut.Patch

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Sewing.PrimitiveSewing.CutPatch

open Purelib.Topology.Surface.Sewing.SewnPrimitiveBoundary.FaceBank

open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts

open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces

open Purelib.Topology.Surface.Sewing.SewnPrimitivePaths

open Purelib.Topology.Surface.Sewing.SewnPrimitivePaths.SewnPrimitiveFaces

open Purelib.Topology.Surface.Sewing.SewnPrimitivePaths.SewnPrimitiveFaces.PathSources

namespace Purelib.Topology.Surface.Sewing.SewnPathRequests

open Purelib.Topology.Polygon.Stokes (OrientedEdge OrientedTriangle)

open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Algebra.FiniteSum.Rational.Squares (coordinateSum)
open Purelib.Topology.Surface.Cut.Patch (CutPatch)
open Purelib.Topology.Surface.Sewing.PrimitiveSewing (PrimitiveValues)
open Purelib.Topology.Surface.Sewing.SewnPrimitivePaths.SewnPrimitiveFaces (OrientedOwner PathTerm PathSources)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces (FaceBank)
open Purelib.Topology.Surface.Sewing.SewingTree (SewnPatch)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts (ContactBank SourceContact)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveRefinement (ContactRates)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveAccounting (Shape shape totalCharge trace_allowance_le)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveRequests (LocalAccuracy)

variable {vertexCount faceCount : Nat} {faces : Fin faceCount → OrientedTriangle vertexCount}
  {indices : List (Fin faceCount)} {boundary : List (OrientedEdge vertexCount)}
  {patch : CutPatch faces indices boundary} {assembly : CutPatch.Assembly faces patch}
  {localValues : Fin faceCount → PrimitiveValues 3} {values : PrimitiveValues
    patch.count}

/-- A retained path term pays at most four times the assembly depth times its total sewing charge. -/
private theorem term_allowance_le (readings : Assembly.Readings localValues assembly values)
    (route : OrientedOwner patch) :
    (PathTerm.build (FaceBank.build readings) route).allowance ≤ 4 * ((shape assembly).depth :
      Rational) * totalCharge readings := by
  let reading := EdgeReading.build (FaceBank.build readings) route.owner
  have bounded := trace_allowance_le readings reading.trace (by
      rw [reading.trace_eq];
      exact List.getElem_mem _)
  change reading.allowance ≤ _
  rw [reading.allowance_eq]
  exact (Arithmetic.mul_le_mul_of_nonneg_left_direct bounded (by decide)).trans_eq (by ring1)

/-- Sum the inherited allowance bound over every retained route occurrence. -/
private theorem terms_allowance_le (readings : Assembly.Readings localValues assembly values)
    (routes : List (OrientedOwner patch)) :
    coordinateSum ((routes.map (PathTerm.build (FaceBank.build
      readings))).map PathTerm.allowance) ≤
      (routes.length : Rational) * (4 * ((shape assembly).depth : Rational) *
        totalCharge readings) := by
  induction routes with
  | nil => change (0 : Rational) ≤ 0 * _; rw [Fraction.Field.zero_mul_direct]
  | cons route routes ih =>
      exact (add_le_add (term_allowance_le readings route) ih).trans_eq (by
        simp only [List.length_cons, NatCast.add, Nat.cast_one, -eq_self, -iff_self]
        ring1)

/-- This is the allowance of the actual retained path sample, not merely a separate bound on its error. No face or path
count is silently constant. -/
theorem PathSources.build_bound_le {edges : List (OrientedEdge patch.count)}
    (sources : PathSources patch edges) (readings : Assembly.Readings localValues assembly values)
    {tolerance : Rational} (accurate : LocalAccuracy tolerance readings) :
    (Sample.build sources (FaceBank.build readings)).bound ≤
      4 * (edges.length : Rational) * edges.length * (shape assembly).depth *
        (shape assembly).factor * tolerance := by
  have lengthEq : sources.entries.length = edges.length := by
    have equal := congrArg List.length sources.edges_eq
    rw [Map.length_map] at equal
    exact equal
  rw [Sample.bound_eq]
  change ((sources.entries.map (PathTerm.build (FaceBank.build readings))).length : Rational) *
    coordinateSum ((sources.entries.map (PathTerm.build (FaceBank.build readings))).map PathTerm.allowance) ≤ _
  rw [Map.length_map]
  have sumBound := terms_allowance_le readings sources.entries
  have scaled := Arithmetic.mul_le_mul_of_nonneg_left_direct sumBound
    (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le sources.entries.length))
  rw [lengthEq] at scaled
  rw [lengthEq]
  have nonnegative : (0 : Rational) ≤ 4 * (edges.length : Rational) * edges.length *
    (shape assembly).depth := by
    exact Arithmetic.mul_nonneg_direct
      (Arithmetic.mul_nonneg_direct
        (Arithmetic.mul_nonneg_direct (by decide) (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le
          _)))
        (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)))
      (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _))
  calc
    _ ≤ (edges.length : Rational) * (edges.length * (4 * ((shape assembly).depth :
      Rational) * totalCharge readings)) := scaled
    _ = (4 * (edges.length : Rational) * edges.length * (shape assembly).depth) *
      totalCharge readings := by
      ring1
    _ ≤ (4 * (edges.length : Rational) * edges.length * (shape assembly).depth) *
      ((shape assembly).factor * tolerance) :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct (SewnPrimitiveRequests.totalCharge_le accurate)
        nonnegative
    _ = _ := by ring1

namespace Shape

/-- Geometry's integer amplification for paths up to a fixed length.

It retains both length factors together with the assembly depth and sewing-charge factor. -/
@[expose] def pathAmplification (profile : Shape) (lengthBound : Nat) : Nat :=
  4 * lengthBound * lengthBound * profile.depth * profile.factor

/-- Casting the path amplification gives its rational product formula. -/
theorem pathAmplification_cast (profile : Shape) (lengthBound : Nat) :
    (pathAmplification profile lengthBound : Rational) =
      4 * (lengthBound : Rational) * lengthBound * profile.depth * profile.factor := by
  simp only [pathAmplification, NatCast.mul, Nat.cast_ofNat, -eq_self, -iff_self]
  rfl

/-- Increasing the allowed path length cannot decrease its amplification. -/
theorem pathAmplification_mono (profile : Shape) {first last : Nat} (order : first ≤ last) :
    pathAmplification profile first ≤ pathAmplification profile last :=
  Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.mul_le_mul_left _ order) order))

end Shape

set_option genInjectivity false in
/-- A common length bound pays an entire finite family with one local contact tolerance. Numeric fields and geometry are
retained as data. -/
structure PathRequest (assembly : CutPatch.Assembly faces patch) (lengthBound : Nat) (target : Rational) where
  /-- The requested total path-error target is strictly positive. -/ target_positive : 0 < target
  /-- Cached geometric accounting profile of the assembly. -/ profile : Shape
  /-- The cached profile is the original assembly's computed profile. -/ profile_eq : profile =
    shape assembly
  /-- Cached rational amplification for the permitted path length. -/ amplification : Rational
  /-- The amplification is the rational cast of the profile's exact integer path factor. -/ amplification_eq :
    amplification = (Shape.pathAmplification profile lengthBound : Rational)
  /-- Cached tolerance for each local contact mismatch. -/ tolerance : Rational
  /-- The tolerance is the target divided by one plus the amplification. -/ tolerance_eq : tolerance = target /
    (amplification + 1)

constructive_injectivity PathRequest

namespace PathRequest

variable {lengthBound : Nat} {target : Rational}

/-- Reuse a geometry profile already retained by a surface preparation. -/
@[expose] def ofProfile (profile : Shape) (profileEq : profile = shape
  assembly) (lengthBound : Nat) (target : Rational)
    (positive : 0 < target) : PathRequest assembly lengthBound target :=
  let amplification := Fraction.Cast.fromInt (Int.ofNat (Shape.pathAmplification profile lengthBound))
  ⟨positive, profile, profileEq, amplification, (Fraction.Cast.natCast_eq_fromInt _).symm,
    target / (amplification + 1), rfl⟩

/-- Construct a path request from the assembly's computed profile and a positive target. -/
@[expose] def build (assembly : CutPatch.Assembly faces patch) (lengthBound : Nat) (target : Rational)
    (positive : 0 < target) : PathRequest assembly lengthBound target :=
  ofProfile (shape assembly) rfl lengthBound target positive

/-- The retained path amplification is nonnegative. -/
theorem amplification_nonnegative (request : PathRequest assembly lengthBound target) : 0 ≤
  request.amplification := by
  rw [request.amplification_eq]
  exact Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)

/-- Dividing a positive target by the shifted amplification gives a positive tolerance. -/
theorem tolerance_positive (request : PathRequest assembly lengthBound target) : 0 < request.tolerance
  := by
  rw [request.tolerance_eq]
  exact Field.div_pos_direct request.target_positive
    (Arithmetic.add_pos_of_nonneg_of_pos_direct request.amplification_nonnegative (by decide))

/-- The amplification times the chosen local tolerance is strictly below the target. -/
theorem paid (request : PathRequest assembly lengthBound target) : request.amplification *
  request.tolerance < target := by
  have strict : request.amplification < request.amplification + 1 := by
    have shifted := Arithmetic.add_lt_add_left_direct (by decide : (0 : Rational) < 1)
      request.amplification
    calc
      request.amplification = request.amplification + 0 := (_root_.add_zero request.amplification).symm
      _ < request.amplification + 1 := shifted
  apply (Arithmetic.mul_lt_mul_of_pos_right_direct strict request.tolerance_positive).trans_eq
  rw [request.tolerance_eq, Fraction.Field.mul_comm]
  exact Fraction.Field.div_mul_cancel_of_ne _ _
    (Arithmetic.add_pos_of_nonneg_of_pos_direct request.amplification_nonnegative (by decide)).ne'

/-- Local contact accuracy pays the bound of each retained path within the requested length. -/
theorem accurate (request : PathRequest assembly lengthBound target)
    (readings : Assembly.Readings localValues assembly values)
    (locallyAccurate : LocalAccuracy request.tolerance readings)
    {edges : List (OrientedEdge patch.count)} (sources : PathSources patch edges) (length_le :
      edges.length ≤ lengthBound) :
    (Sample.build sources (FaceBank.build readings)).bound < target := by
  have bounded := PathSources.build_bound_le sources readings locallyAccurate
  rw [← Shape.pathAmplification_cast] at bounded
  have amplified : (Shape.pathAmplification (shape assembly) edges.length :
    Rational) ≤ request.amplification := by
    rw [request.amplification_eq, request.profile_eq]
    exact Fraction.Cast.Order.natCast_le_direct (Shape.pathAmplification_mono _ length_le)
  exact bounded.trans_lt ((Arithmetic.mul_le_mul_of_nonneg_right_direct amplified
    request.tolerance_positive.le).trans_lt request.paid)

/-- Reuse the actual sample's checked face cache; do not rebuild a sewing in order to establish its path allowance. -/
theorem cached_accurate {patch : SewnPatch faces} (request : PathRequest patch.assembly
  lengthBound target)
    (sample : CachedSample patch localValues)
    (locallyAccurate : LocalAccuracy request.tolerance sample.sewn.readings)
    {edges : List (OrientedEdge patch.cut.count)} (sources : PathSources patch.cut edges)
      (length_le : edges.length ≤ lengthBound) :
    (CachedSample.pathSample sample sources).bound < target := by
  change (Sample.build sources sample.faces).bound < target
  rw [sample.faces_eq]
  exact request.accurate sample.sewn.readings locallyAccurate sources length_le

open Purelib.Topology.Surface.Sewing.SewnPathRequests.PathRequest in
set_option genInjectivity false in
/-- A finite path-error floor can be combined with any other scalar budget before numerical construction. Every later
index remains valid. -/
structure Refinement {contacts : ContactBank assembly} {family : Nat → Fin faceCount →
  PrimitiveValues 3}
    (request : PathRequest assembly lengthBound target) (rates : ContactRates
      contacts family) (floor : Nat) where
  /-- Selected family index meeting the local tolerance. -/ index : Nat
  /-- The selected index respects the original lower floor. -/ later : floor ≤ index
  /-- The retained total contact rate at this index is strictly below the local tolerance. -/ accurate :
    Basic.quarterRadius rates.total index < request.tolerance

constructive_injectivity Refinement

namespace Refinement

variable {contacts : ContactBank assembly} {family : Nat → Fin faceCount →
  PrimitiveValues 3}
  {request : PathRequest assembly lengthBound target} {rates :
    ContactRates contacts family} {floor : Nat}

/-- Find a refinement index at or above the floor meeting the path request's tolerance.

The finite geometric search uses the retained total contact rate and the request's positive tolerance. -/
@[expose] def build (request : PathRequest assembly lengthBound target) (rates :
  ContactRates contacts family) (floor : Nat) :
    Refinement request rates floor :=
  ⟨Search.firstQuarterBelow rates.total floor request.tolerance,
    Search.firstQuarterBelow_ge _ _ _,
    Search.firstQuarterBelow_accurate rates.total rates.total_nonnegative floor _ request.tolerance_positive⟩

/-- Every retained contact remains within tolerance at any index beyond the refinement floor. -/
theorem mismatch_lt_of_le (refinement : Refinement request rates floor) {index : Nat} (later :
  refinement.index ≤ index)
    (contact : SourceContact faces) (member : contact ∈ contacts.entries) :
    contact.mismatch (family index) < request.tolerance :=
  (rates.mismatch_le index contact member).trans_lt
    ((quarterRadius_antitone rates.total_nonnegative later).trans_lt refinement.accurate)

/-- Certify the actual cached path sample at any sufficiently refined family index.

Pointwise readback links its local values to the family; the bound applies to paths within the request's retained length
limit. -/
theorem cached_accurate {patch : SewnPatch faces} {contacts : ContactBank
  patch.assembly}
    {request : PathRequest patch.assembly lengthBound target} {rates :
      ContactRates contacts family}
    (refinement : Refinement request rates floor) {index : Nat} (later : refinement.index ≤ index)
    (sample : CachedSample patch localValues) (readback : ∀ source, localValues source = family
      index source)
    {edges : List (OrientedEdge patch.cut.count)} (sources : PathSources patch.cut edges)
      (length_le : edges.length ≤ lengthBound) :
    (CachedSample.pathSample sample sources).bound < target := by
  apply request.cached_accurate sample ?_ sources length_le
  apply SewnPrimitiveContacts.localAccuracy_of_sourceContacts sample.sewn.readings
  intro contact member
  have bounded := refinement.mismatch_lt_of_le later contact (by rw [contacts.entries_eq]; exact member)
  simpa only [SourceContact.mismatch, SourceEdge.increment, readback, -eq_self, -iff_self] using bounded.le

end Refinement
end PathRequest
end Purelib.Topology.Surface.Sewing.SewnPathRequests

end
