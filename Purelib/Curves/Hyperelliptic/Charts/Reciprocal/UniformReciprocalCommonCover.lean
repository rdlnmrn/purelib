module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Membership
import Purelib.Data.Nat.Order
import Purelib.Data.Nat.Subtraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.UniformPrimitiveMesh
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Init.Data.List.Lemmas
import Init.Data.Nat.Basic
import Init.Data.Nat.MinMax
import Init.Prelude
import Purelib.Data.Rat.Fraction.Order.Basic

public section

/-! A common dyadic mesh reads owners from both existing reciprocal covers.
Ownership contains the entire interval, not only one selected endpoint. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Riemann.Branches

open Purelib.Riemann.Meshes

open Purelib.Data.List Purelib.Data.Nat

open Purelib.Riemann.Branches.ClearSheetContinuation
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (Endpoint ParameterEdge dyadicEdges)
open Purelib.Riemann.Meshes.UniformPrimitiveMesh (firstEndpoint lastEndpoint)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels (Data)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cover Cell Cells)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)

/-- Every original dyadic subedge inherits the retained interval endpoint order.

Induction follows the supplied finite depth. The two midpoint bounds certify the retained left and right branches, and
membership selects the same displayed subedge. -/
theorem dyadic_ordered (depth : Nat) (left right : Subdivision.Endpoint)
    (ordered : left.parameter ≤ right.parameter) {edge : Subdivision.ParameterEdge}
    (member : edge ∈ Subdivision.dyadicEdges depth left right) : edge.left.parameter ≤ edge.right.parameter := by
  induction depth generalizing left right with
  | zero => cases Membership.mem_singleton.mp member; exact ordered
  | succ depth ih =>
      rcases Membership.mem_append.mp member with member | member
      · exact ih _ _ (ClearSheetContinuation.left_le_midpoint ordered) member
      · exact ih _ _ (ClearSheetContinuation.midpoint_le_right ordered) member

/-- Every retained dyadic subedge lies between the original outer interval endpoints.

The finite subdivision keeps its original outer endpoints at every level. The midpoint inequalities and retained branch
membership bound both endpoints of the same subedge. -/
private theorem dyadic_range (depth : Nat) (left right : Subdivision.Endpoint)
    (ordered : left.parameter ≤ right.parameter) {edge : Subdivision.ParameterEdge}
    (member : edge ∈ Subdivision.dyadicEdges depth left right) :
    left.parameter ≤ edge.left.parameter ∧ edge.right.parameter ≤ right.parameter := by
  induction depth generalizing left right with
  | zero => cases Membership.mem_singleton.mp member; exact ⟨le_rfl, le_rfl⟩
  | succ depth ih =>
      rcases Membership.mem_append.mp member with member | member
      · have found := ih _ _ (ClearSheetContinuation.left_le_midpoint ordered) member
        exact ⟨found.1, found.2.trans (ClearSheetContinuation.midpoint_le_right ordered)⟩
      · have found := ih _ _ (ClearSheetContinuation.midpoint_le_right ordered) member
        exact ⟨(ClearSheetContinuation.left_le_midpoint ordered).trans found.1, found.2⟩

/-- Every original finer dyadic edge lies wholly inside an edge of the retained coarser subdivision.

The supplied coarse and extra depths split the same recursive dyadic mesh. The witness is an actual edge of the coarse
mesh whose endpoints contain the full finer interval. -/
private theorem dyadic_owner (coarse extra : Nat) (left right : Subdivision.Endpoint)
    (ordered : left.parameter ≤ right.parameter) {edge : Subdivision.ParameterEdge}
    (member : edge ∈ Subdivision.dyadicEdges (coarse + extra) left right) :
    ∃ owner ∈ Subdivision.dyadicEdges coarse left right,
      owner.left.parameter ≤ edge.left.parameter ∧ edge.right.parameter ≤ owner.right.parameter := by
  induction coarse generalizing left right with
  | zero =>
      rw [Nat.zero_add] at member
      exact ⟨⟨left, right⟩, List.mem_cons_self ..,
        Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover.dyadic_range extra left right ordered
        member⟩
  | succ coarse ih =>
      rw [Nat.succ_add] at member
      rcases Membership.mem_append.mp member with member | member
      · obtain ⟨owner, retained, bounds⟩ := ih _ _ (ClearSheetContinuation.left_le_midpoint ordered) member
        exact ⟨owner, Membership.mem_append.mpr (Or.inl retained), bounds⟩
      · obtain ⟨owner, retained, bounds⟩ := ih _ _ (ClearSheetContinuation.midpoint_le_right ordered) member
        exact ⟨owner, Membership.mem_append.mpr (Or.inr retained), bounds⟩

variable {genus count : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
  {differential : Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}

set_option genInjectivity false in
/-- Retain the actual cell and its owner edge from the original cover.

The owner edge belongs to the supplied cached cover spine. Its original reciprocal cell is retained with inequalities
containing both endpoints of the requested interval. -/
structure IntervalOwner (data : UniformReciprocalModels.Data patch count) (edges : List Subdivision.ParameterEdge) (edge
  : Subdivision.ParameterEdge) where
  /-- The retained original cover edge containing the entire requested interval. -/ owner : Subdivision.ParameterEdge
  /-- The retained owner edge belongs to the original cached cover spine. -/ member : owner ∈ edges
  /-- The original cached reciprocal model of the retained owner edge. -/ cell : UniformReciprocalCover.Cell data owner
  /-- The requested interval starts at or after its retained owner's original lower endpoint. -/ lower :
    owner.left.parameter ≤ edge.left.parameter
  /-- The requested interval finishes at or before its retained owner's original upper endpoint. -/ upper :
    edge.right.parameter ≤ owner.right.parameter

constructive_injectivity IntervalOwner

namespace Cells

/-- Scan the original cached cell spine for an owner containing the entire requested interval, retaining that exact
existing model.

The first cell satisfying both endpoint inequalities is returned. A rejected head keeps the supplied coverage witness in
the remaining spine, and recursion retains the original model of the selected cell. -/
@[expose] def locateInterval (edge : Subdivision.ParameterEdge) : {edges : List Subdivision.ParameterEdge} →
  UniformReciprocalCover.Cells data edges →
    (∃ owner ∈ edges, owner.left.parameter ≤ edge.left.parameter ∧ edge.right.parameter ≤ owner.right.parameter) →
    Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover.IntervalOwner data edges edge
  | [], .nil, covered => by
      exact False.elim (by
        obtain ⟨owner, member, _⟩ := covered
        exact List.not_mem_nil member)
  | owner :: remaining, .cons head tail, covered =>
      if bounds : owner.left.parameter ≤ edge.left.parameter ∧ edge.right.parameter ≤ owner.right.parameter then
        ⟨owner, List.mem_cons_self .., head, bounds.1, bounds.2⟩
      else
        let found := Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover.Cells.locateInterval
          edge tail (by
          obtain ⟨other, member, inside⟩ := covered
          rcases Membership.mem_cons.mp member with same | member
          · subst other; exact False.elim (bounds inside)
          · exact ⟨other, member, inside⟩)
        ⟨found.owner, List.mem_cons_of_mem _ found.member, found.cell, found.lower, found.upper⟩

end Cells

/-- Locate an original finer dyadic interval in the existing retained reciprocal cover.

The retained depth bound embeds the interval in an actual edge of the cover mesh. The cached cell spine is scanned in
its original order without recomputing any reciprocal model. -/
@[expose] def Cover.intervalOwner (cover : UniformReciprocalCover.Cover data) (depth : Nat) (later : cover.mesh.depth ≤
  depth)
    (edge : Subdivision.ParameterEdge) (member : edge ∈ Subdivision.dyadicEdges depth UniformPrimitiveMesh.firstEndpoint
      UniformPrimitiveMesh.lastEndpoint) :
    Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover.IntervalOwner data cover.mesh.edges edge :=
  Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover.Cells.locateInterval edge cover.cells (by
    rw [cover.mesh.edges_eq]
    apply Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover.dyadic_owner cover.mesh.depth (depth -
      cover.mesh.depth) UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint (by decide)
    rw [Subtraction.add_sub_of_le later]
    exact member)

variable {otherCount : Nat} {other : Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {otherParent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve other}
  {otherPatch : Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch otherParent} {otherData :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data otherPatch otherCount}

set_option genInjectivity false in
/-- One original common dyadic interval with both original cover owners and their cached models.

The ordered interval retains its containing edge and existing cell from each input cover. The two input differential and
parent owners remain distinct. -/
structure CommonInterval (left : UniformReciprocalCover.Cover data) (right : UniformReciprocalCover.Cover otherData)
  where
  /-- The retained common dyadic interval. -/ edge : Subdivision.ParameterEdge
  /-- The retained common interval endpoints are ordered. -/ ordered : edge.left.parameter ≤ edge.right.parameter
  /-- The original first-cover cell owning the entire common interval. -/ first :
    Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover.IntervalOwner data left.mesh.edges edge
  /-- The original second-cover cell owning the entire common interval. -/ second :
    Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover.IntervalOwner otherData right.mesh.edges edge

constructive_injectivity CommonInterval

/-- Retain both original cover owners for each common dyadic interval in its original edge-list order.

Each supplied edge is located separately in the two retained cached covers. The resulting entry keeps those exact owners
and models, and recursion preserves the original common edge order. -/
@[expose] def commonEntries (left : UniformReciprocalCover.Cover data) (right : UniformReciprocalCover.Cover otherData)
  (depth : Nat)
    (leftLater : left.mesh.depth ≤ depth) (rightLater : right.mesh.depth ≤ depth) :
    (edges : List Subdivision.ParameterEdge) → (∀ edge ∈ edges, edge ∈ Subdivision.dyadicEdges depth
      UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint) →
    List (Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover.CommonInterval left right)
  | [], _ => []
  | edge :: remaining, members =>
      ⟨edge, Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover.dyadic_ordered depth
        UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint (by decide) (members edge
        List.mem_cons_self),
        Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover.Cover.intervalOwner left depth leftLater
          edge (members edge List.mem_cons_self),
        Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover.Cover.intervalOwner right depth rightLater
          edge (members edge List.mem_cons_self)⟩ ::
        Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover.commonEntries left right depth
          leftLater rightLater remaining
          (fun edge member => members edge (List.mem_cons_of_mem _ member))

/-- The retained common entries read back exactly the original common dyadic edge list.

Structural induction retains each displayed interval edge while transporting the readback equality for the unchanged
tail. No retained owner or reciprocal cell is recomputed. -/
theorem commonEntries_edges (left : UniformReciprocalCover.Cover data) (right : UniformReciprocalCover.Cover otherData)
  (depth : Nat)
    (leftLater : left.mesh.depth ≤ depth) (rightLater : right.mesh.depth ≤ depth)
    (edges : List Subdivision.ParameterEdge) (members : ∀ edge ∈ edges, edge ∈ Subdivision.dyadicEdges depth
      UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint) :
    (Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover.commonEntries left right depth leftLater
      rightLater edges members).map
      Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover.CommonInterval.edge = edges := by
  induction edges with
  | nil => rfl
  | cons edge remaining ih => exact congrArg (List.cons edge) (ih _)

set_option genInjectivity false in
/-- The ordered common mesh is complete, and every stored interval has both original cell owners. Neither cover nor any
inverse model is recomputed.

The common depth is the maximum of the two retained mesh depths. Its ordered interval caches read back the complete
dyadic edge list and retain both original cover cells. -/
structure CommonCover (left : UniformReciprocalCover.Cover data) (right : UniformReciprocalCover.Cover otherData) where
  /-- The retained common dyadic refinement depth. -/ depth : Nat
  /-- The common depth is exactly the maximum of the two original cover depths. -/ depth_eq : depth = max
    left.mesh.depth right.mesh.depth
  /-- The ordered common dyadic intervals retaining both original cover owners. -/ intervals : List
    (Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover.CommonInterval left right)
  /-- The retained interval list reads back the exact complete dyadic mesh at the common depth. -/ edges_eq :
    intervals.map Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover.CommonInterval.edge =
    Subdivision.dyadicEdges depth UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint

constructive_injectivity CommonCover

/-- Cache the complete common dyadic mesh at the maximum original depth and retain each interval's two existing cover
owners.

The input cover depths determine the same finite subdivision. Its entries are built once in their displayed order,
retaining both cached reciprocal cells and the exact edge readback certificate. -/
@[expose] def CommonCover.build (left : UniformReciprocalCover.Cover data) (right : UniformReciprocalCover.Cover
  otherData) : Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover.CommonCover left right :=
  let depth := max left.mesh.depth right.mesh.depth
  let edges := Subdivision.dyadicEdges depth UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint
  ⟨depth, rfl, Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover.commonEntries left right depth
    (Order.le_max_left ..) (Order.le_max_right ..) edges (fun _ member => member),
    Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover.commonEntries_edges left right depth
      (Order.le_max_left ..) (Order.le_max_right ..) edges (fun _ member => member)⟩

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover
