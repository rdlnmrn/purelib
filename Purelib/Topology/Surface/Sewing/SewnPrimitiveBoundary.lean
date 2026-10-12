module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Membership
import Purelib.Data.List.Map
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingProjection
public import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Topology.Surface.Sewing.VertexSewing
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Data.Int.Cast.Defs
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Vector.Basic
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

open Purelib.Data

open Purelib.Data.Gaussian.Norm.Basic

open Purelib.Data.Rat

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

open Purelib.Topology.Surface.Cut

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Sewing.PrimitiveSewing

open Purelib.Topology.Surface.Sewing.SewingProjection

public section

/-!
# Local face readings on actual sewn boundary edges

An executable geometric owner identifies a triangle occurrence and its two
corners. It can be cached before choosing primitive accuracy. Reading that
owner from a face bank performs no geometric search and retains the local
increment, actual discrepancy and inherited error allowance. At a join the
two inherited errors are paid separately from the local-model mismatch.
-/

namespace Purelib.Topology.Surface.Sewing.SewnPrimitiveBoundary

open Purelib.Data.List

open Purelib.Topology.Surface.Cut.Patch (CutPatch)
open Purelib.Topology.Surface.Sewing.PrimitiveSewing (PrimitiveValues)

open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces

open Purelib.Topology.Polygon.Stokes (OrientedEdge OrientedTriangle)
open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib.Data.Gaussian.Basic.Canonical

set_option genInjectivity false in
/-- A boundary edge retains its triangle occurrence and two corner indices.

The position identifies the original cut-list occurrence, with exact endpoint
readbacks and positive membership in that triangle boundary. -/
structure TriangleEdgeOwner {count : Nat} (triangles : List (Stokes.OrientedTriangle count)) (edge : Stokes.OrientedEdge
  count) where
  /-- Position of the original triangle occurrence in the retained list. -/ position : Fin triangles.length
  /-- Corner index at the oriented edge's start. -/ first : Fin 3
  /-- Corner index at the oriented edge's finish. -/ last : Fin 3
  /-- The selected starting corner is the actual cut-edge start. -/ start_eq : SewnPrimitiveFaces.corner
    triangles[position.val] first = edge.start
  /-- The selected finishing corner is the actual cut-edge finish. -/ finish_eq : SewnPrimitiveFaces.corner
    triangles[position.val] last = edge.finish
  /-- The edge occurs positively in the selected triangle boundary. -/ boundary_mem : edge ∈
    triangles[position.val].boundary

constructive_injectivity TriangleEdgeOwner

namespace TriangleEdgeOwner

variable {count : Nat} {edge : Stokes.OrientedEdge count}

/-- Identify the corners of an edge in the first triangle's oriented boundary.

The original three edges are checked in boundary order. Incidence identifies
the final edge when the first two equalities fail. -/
@[expose] def head (triangle : Stokes.OrientedTriangle count) (tail : List (Stokes.OrientedTriangle count))
    (member : edge ∈ triangle.boundary) : SewnPrimitiveBoundary.TriangleEdgeOwner (triangle :: tail) edge :=
  if first : edge = ⟨triangle.first, triangle.second⟩ then
    ⟨⟨0, Nat.zero_lt_succ tail.length⟩, 0, 1, by rw [first]; rfl, by rw [first]; rfl, member⟩
  else if second : edge = ⟨triangle.second, triangle.third⟩ then
    ⟨⟨0, Nat.zero_lt_succ tail.length⟩, 1, 2, by rw [second]; rfl, by rw [second]; rfl, member⟩
  else
    have third : edge = ⟨triangle.third, triangle.first⟩ := by
      rcases Membership.mem_cons.mp member with equal | rest
      · exact (first equal).elim
      · rcases Membership.mem_cons.mp rest with equal | rest
        · exact (second equal).elim
        · exact Membership.mem_singleton.mp rest
    ⟨⟨0, Nat.zero_lt_succ tail.length⟩, 2, 0, by rw [third]; rfl, by rw [third]; rfl, member⟩

/-- Shift an existing triangle occurrence past a newly prepended triangle.

The original corner indices and incidence certificates are retained, while
the position advances by one in the new cut-list spine. -/
@[expose] def prepend {triangles : List (Stokes.OrientedTriangle count)} (owner :
  SewnPrimitiveBoundary.TriangleEdgeOwner triangles edge)
    (triangle : Stokes.OrientedTriangle count) : SewnPrimitiveBoundary.TriangleEdgeOwner (triangle :: triangles) edge :=
  ⟨owner.position.succ, owner.first, owner.last, owner.start_eq, owner.finish_eq, owner.boundary_mem⟩

/-- Locate the first incident triangle in the retained finite list.

The incidence witness makes the lookup total. Each skipped triangle advances
the retained position without changing the selected edge or its corner data. -/
@[expose] def find (edge : Stokes.OrientedEdge count) : (triangles : List (Stokes.OrientedTriangle count)) →
    edge ∈ triangles.flatMap OrientedTriangle.boundary → SewnPrimitiveBoundary.TriangleEdgeOwner triangles edge
  | [], member => (List.not_mem_nil member).elim
  | triangle :: triangles, member =>
      if inside : edge ∈ triangle.boundary then TriangleEdgeOwner.head triangle triangles inside
      else (Purelib.Topology.Surface.Sewing.SewnPrimitiveBoundary.TriangleEdgeOwner.find edge triangles
        ((Membership.mem_append.mp member).resolve_left inside)).prepend triangle

end TriangleEdgeOwner

variable {vertexCount faceCount : Nat} {faces : Fin faceCount → Stokes.OrientedTriangle vertexCount}
  {indices : List (Fin faceCount)} {boundary : List (Stokes.OrientedEdge vertexCount)}
  {patch : Patch.CutPatch faces indices boundary} {localValues : Fin faceCount → PrimitiveSewing.PrimitiveValues 3}
  {values : PrimitiveSewing.PrimitiveValues patch.count}

/-- Locate a cut-boundary edge in the patch's retained triangle occurrence list.

The patch incidence certificate supplies the finite lookup's membership witness. -/
@[expose] def boundaryOwner (patch : Patch.CutPatch faces indices boundary) (edge : Stokes.OrientedEdge patch.count)
    (member : edge ∈ patch.boundary) : SewnPrimitiveBoundary.TriangleEdgeOwner patch.triangles edge :=
  SewnPrimitiveBoundary.TriangleEdgeOwner.find edge patch.triangles
    ((EdgeReordering.mem_iff patch.incidence edge).mpr (Membership.mem_append.mpr (Or.inl member)))

namespace FaceTrace

/-- Bound an arbitrary corner-to-corner increment discrepancy by four times its face allowance. -/
theorem two_point_error_bound {count : Nat} {values : PrimitiveSewing.PrimitiveValues count}
    (trace : SewnPrimitiveFaces.FaceTrace localValues values) (first last : Fin 3) :
    Data.Gaussian.Norm.Basic.normSq ((values (SewnPrimitiveFaces.corner trace.triangle last) - values
      (SewnPrimitiveFaces.corner
      trace.triangle first)) -
      (localValues trace.source last - localValues trace.source first)) ≤ 4 * trace.allowance := by
  have equal : (values (SewnPrimitiveFaces.corner trace.triangle last) - values (SewnPrimitiveFaces.corner
    trace.triangle first)) -
      (localValues trace.source last - localValues trace.source first) = trace.errors last - trace.errors first := by
    rw [trace.errors_eq, trace.errors_eq]
    ring1
  rw [equal]
  exact (Gaussian.Norm.Bounds.normSq_sub_le_two _ _).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (add_le_add (trace.error_bound last) (trace.error_bound first)) (by decide)).trans_eq (by ring1))

end FaceTrace

namespace FaceBank

/-- A face bank has exactly one trace for each original cut triangle occurrence.

The retained mapped-triangle equality transports length through the original
finite bank entries, preserving their order and multiplicity. -/
theorem entries_length (bank : SewnPrimitiveFaces.FaceBank patch localValues values) : bank.entries.length =
  patch.triangles.length := by
  have lengths := congrArg List.length bank.triangles_eq
  rw [Map.length_map] at lengths
  exact lengths

/-- The cached trace at a retained position has the original cut triangle at that position.

The supplied bank bound indexes its existing entry. The cached mapped-list
equality identifies that entry's triangle with the same original cut occurrence. -/
theorem triangle_at (bank : SewnPrimitiveFaces.FaceBank patch localValues values) (index : Nat) (bound : index <
  bank.entries.length) :
    (bank.entries[index]).triangle = patch.triangles[index]'(by rw [← FaceBank.entries_length bank]; exact bound) := by
  have atIndex := List.getElem_of_eq bank.triangles_eq (i := index) (by rw [Map.length_map]; exact bound)
  rw [Map.getElem_map] at atIndex
  exact atIndex

set_option genInjectivity false in
/-- A cached face reading retains a preselected geometric owner.

The reading stores its original bank trace, local increment, actual sewn
discrepancy and inherited allowance with their exact defining equations. -/
structure EdgeReading (bank : SewnPrimitiveFaces.FaceBank patch localValues values) {edge : Stokes.OrientedEdge
  patch.count}
    (owner : SewnPrimitiveBoundary.TriangleEdgeOwner patch.triangles edge) where
  /-- Cached face trace selected by the original owner position. -/ trace : SewnPrimitiveFaces.FaceTrace localValues
    values
  /-- The cached trace is the existing bank entry at the retained bounded position. -/ trace_eq : trace =
    bank.entries[owner.position.val]'(by rw [FaceBank.entries_length bank]; exact owner.position.isLt)
  /-- The selected trace retains the owner's original cut triangle. -/ triangle_eq : trace.triangle =
    patch.triangles[owner.position.val]
  /-- Cached increment of the original local face values. -/ localIncrement : Gaussian.Basic.Canonical
  /-- The local increment subtracts the owner's starting corner value from its finishing corner value. -/
    localIncrement_eq : localIncrement = localValues trace.source owner.last - localValues trace.source owner.first
  /-- Cached discrepancy between sewn and original local increments. -/ error : Gaussian.Basic.Canonical
  /-- The discrepancy subtracts the retained local increment from the actual sewn increment. -/ error_eq : error =
    (values edge.finish - values edge.start) - localIncrement
  /-- Cached squared-error allowance for this oriented edge. -/ allowance : SewnPrimitiveFaces.Coordinate
  /-- The edge allowance is exactly four times the selected face allowance. -/ allowance_eq : allowance = 4 *
    trace.allowance

constructive_injectivity EdgeReading

namespace EdgeReading

variable {bank : SewnPrimitiveFaces.FaceBank patch localValues values} {edge : Stokes.OrientedEdge patch.count}
  {owner : Purelib.Topology.Surface.Sewing.SewnPrimitiveBoundary.TriangleEdgeOwner patch.triangles edge}

/-- Read a preselected triangle owner from the existing face bank.

The construction caches the original local increment, actual sewn discrepancy and fourfold inherited face allowance
without a new ownership search. -/
@[expose] def build (bank : SewnPrimitiveFaces.FaceBank patch localValues values) (owner :
  SewnPrimitiveBoundary.TriangleEdgeOwner patch.triangles edge) : FaceBank.EdgeReading bank owner :=
  let trace := bank.entries[owner.position.val]'(by rw [FaceBank.entries_length bank]; exact owner.position.isLt)
  let increment := localValues trace.source owner.last - localValues trace.source owner.first
  { trace := trace
    trace_eq := rfl
    triangle_eq := FaceBank.triangle_at bank owner.position.val _
    localIncrement := increment
    localIncrement_eq := rfl
    error := (values edge.finish - values edge.start) - increment
    error_eq := rfl
    allowance := 4 * trace.allowance
    allowance_eq := rfl }

/-- The squared norm of the cached edge discrepancy is at most its retained allowance. -/
theorem error_bound (reading : FaceBank.EdgeReading bank owner) : Data.Gaussian.Norm.Basic.normSq reading.error ≤
  reading.allowance :=
  by
  have bound := SewnPrimitiveBoundary.FaceTrace.two_point_error_bound reading.trace owner.first owner.last
  rw [reading.triangle_eq, owner.start_eq, owner.finish_eq, ← reading.localIncrement_eq] at bound
  rw [reading.error_eq, reading.allowance_eq]
  exact bound

/-- The sewn increment differs from the retained local increment by at most the inherited allowance. -/
theorem increment_error_bound (reading : FaceBank.EdgeReading bank owner) :
    Data.Gaussian.Norm.Basic.normSq ((values edge.finish - values edge.start) - reading.localIncrement) ≤
      reading.allowance := by
  rw [← reading.error_eq]
  exact reading.error_bound

end EdgeReading
end FaceBank

/-- Compare the actual seam with its two original local face increments. The original model mismatch is the only new
analytic obligation; neither inherited face error is replaced by an exact-matching assumption. -/
theorem seam_charge_le {firstIndices secondIndices : List (Fin faceCount)}
    {firstBoundary secondBoundary : List (Stokes.OrientedEdge vertexCount)}
    {first : Patch.CutPatch faces firstIndices firstBoundary} {second : Patch.CutPatch faces secondIndices
      secondBoundary}
    {leftValues : PrimitiveSewing.PrimitiveValues first.count} {rightValues : PrimitiveSewing.PrimitiveValues
      second.count}
    {leftBank : SewnPrimitiveFaces.FaceBank first localValues leftValues} {rightBank : SewnPrimitiveFaces.FaceBank
      second localValues rightValues}
    {firstEdge : Stokes.OrientedEdge first.count} {secondEdge : Stokes.OrientedEdge second.count}
    {firstOwner : SewnPrimitiveBoundary.TriangleEdgeOwner first.triangles firstEdge} {secondOwner :
      SewnPrimitiveBoundary.TriangleEdgeOwner second.triangles secondEdge}
    (joined : EndpointGluing.PrimitiveSew leftValues rightValues firstEdge secondEdge)
    (left : SewnPrimitiveBoundary.FaceBank.EdgeReading leftBank firstOwner) (right :
      SewnPrimitiveBoundary.FaceBank.EdgeReading rightBank secondOwner)
    (mismatch : SewnPrimitiveFaces.Coordinate) (matched : Data.Gaussian.Norm.Basic.normSq (left.localIncrement +
      right.localIncrement) ≤
      mismatch) :
    joined.charge ≤ 16 * (left.trace.allowance + right.trace.allowance) + 2 * mismatch := by
  have bound := joined.charge_le left.localIncrement right.localIncrement left.allowance right.allowance mismatch
    left.increment_error_bound right.increment_error_bound matched
  rw [left.allowance_eq, right.allowance_eq] at bound
  exact bound.trans_eq (by ring1)

end Purelib.Topology.Surface.Sewing.SewnPrimitiveBoundary
