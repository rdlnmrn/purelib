module
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.List.Membership
meta import Purelib.Elab.ConstructiveInjectivity

import Purelib.Data.List.Permutation
public import Purelib.Topology.Mesh.TriangleSourceUniqueness
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.SewingProjection
import Purelib.Topology.Surface.Sewing.SewnPrimitiveBoundary
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Topology.Mesh.SourceContactPositivity
public import Purelib.Topology.Surface.Word.ProjectedEdgePairs
public import Purelib.Data.Vector.Dependent
import Purelib.Data.Vector.Basic
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Data

open Purelib.Data.Vector

open Purelib.Topology.Mesh.TriangleSourceUniqueness

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Cut

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Sewing.SewingProjection

open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts

open Purelib.Topology.Surface.Word

open Purelib.Topology.Surface.Word.ProjectedEdgePairs

public section

/-!
# Original face contacts of the exposed paired cut edges

These pairs have not been consumed by the assembly's sewing tree. Their
actual cut-edge owners and original source contacts are retained separately.
The pairing's incidence certificate constructs every membership obligation;
generated banks may provide the same owners and exact source equations.
-/

namespace Purelib.Topology.Surface.Boundary

open Purelib.Topology.Surface.Cut.Patch (CutPatch)
open Purelib.Topology.Surface.Word.ProjectedEdgePairs (ProjectedEdgePair ProjectedEdgePairing)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveBoundary (TriangleEdgeOwner boundaryOwner)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts (SourceContact)

open Purelib.Topology.Polygon.Stokes (OrientedEdge OrientedTriangle)

variable {vertexCount faceCount : Nat} {faces : Fin faceCount → Stokes.OrientedTriangle vertexCount}
  {indices : List (Fin faceCount)} {boundary : List (Stokes.OrientedEdge vertexCount)}
  {patch : Patch.CutPatch faces indices boundary}

set_option genInjectivity false in
/-- Original face ownership of an exposed pair of cut edges.

The two triangle owners are linked to the actual left and right source edges of one retained contact. -/
structure BoundaryContactSources (patch : Patch.CutPatch faces indices boundary) (pair :
  ProjectedEdgePairs.ProjectedEdgePair patch.vertexLabels) where
  /-- Original triangle owner of the first exposed cut edge. -/ first : SewnPrimitiveBoundary.TriangleEdgeOwner
    patch.triangles pair.first
  /-- Original triangle owner of the second exposed cut edge. -/ second : SewnPrimitiveBoundary.TriangleEdgeOwner
    patch.triangles pair.second
  /-- Retained opposite contact between the original source edges. -/ contact : SewnPrimitiveContacts.SourceContact
    faces
  /-- The contact's left edge is the first retained triangle owner's source edge. -/ first_eq : contact.left =
    TriangleEdgeOwner.sourceEdge first
  /-- The contact's right edge is the second retained triangle owner's source edge. -/ second_eq : contact.right =
    TriangleEdgeOwner.sourceEdge second

constructive_injectivity BoundaryContactSources

namespace BoundaryContactSources

open Purelib.Topology.Surface.Boundary
/-- Construct original face contacts from membership of both paired edges in the cut boundary. -/
@[expose] def build (patch : Patch.CutPatch faces indices boundary) (pair : ProjectedEdgePairs.ProjectedEdgePair
  patch.vertexLabels)
    (firstMember : pair.first ∈ patch.boundary) (secondMember : pair.second ∈ patch.boundary) :
      BoundaryContactSources patch pair :=
  let first := SewnPrimitiveBoundary.boundaryOwner patch pair.first firstMember
  let second := SewnPrimitiveBoundary.boundaryOwner patch pair.second secondMember
  ⟨first, second, ⟨TriangleEdgeOwner.sourceEdge first, TriangleEdgeOwner.sourceEdge second, by
    rw [TriangleEdgeOwner.sourceEdge_project first, TriangleEdgeOwner.sourceEdge_project second]
    exact pair.opposite⟩, rfl, rfl⟩

/-- Both retained source edges occur with positive face-boundary orientation. -/
theorem positive {pair : ProjectedEdgePairs.ProjectedEdgePair patch.vertexLabels} (sources :
  BoundaryContactSources patch pair) :
    SourceEdge.Positive sources.contact.left faces ∧
      SourceEdge.Positive sources.contact.right faces := by
  rw [sources.first_eq, sources.second_eq]
  exact ⟨TriangleEdgeOwner.sourceEdge_positive sources.first,
    TriangleEdgeOwner.sourceEdge_positive sources.second⟩

end BoundaryContactSources

namespace BoundaryContactSources

/-- Each edge of a retained pair occurs in the complete paired occurrence list. -/
private theorem occurrence_members {source target : Nat} {labels : Fin source → Fin target}
    (pairs : List (ProjectedEdgePairs.ProjectedEdgePair labels)) (pair : ProjectedEdgePairs.ProjectedEdgePair labels)
      (member : pair ∈ pairs) :
    pair.first ∈ ProjectedEdgePair.occurrences pairs ∧ pair.second ∈ ProjectedEdgePair.occurrences pairs := by
  induction pairs with
  | nil => exact (List.not_mem_nil member).elim
  | cons first rest ih =>
      rcases Data.List.Membership.mem_cons.mp member with same | member
      · cases same
        exact ⟨List.mem_cons_self, List.mem_cons_of_mem _ List.mem_cons_self⟩
      · have members := ih member
        exact ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ members.1),
          List.mem_cons_of_mem _ (List.mem_cons_of_mem _ members.2)⟩

end BoundaryContactSources

namespace BoundaryContactSources

open Purelib.Topology.Surface.Boundary in
set_option genInjectivity false in
/-- Cached source ownership and contacts for every exposed boundary pair.

Dependent entries use the original pair indices, and the contact list is exactly their ordered readback. -/
structure BoundaryContactBank (patch : Patch.CutPatch faces indices boundary)
    (pairing : ProjectedEdgePairs.ProjectedEdgePairing patch.vertexLabels patch.boundary) where
  /-- Dependent source-ownership entries indexed by the original exposed pairs. -/ entries : Data.Vector.DependentVector
    (fun index : Fin pairing.pairs.length => BoundaryContactSources patch
    (pairing.pairs[index.val]'index.isLt))
  /-- Cached ordered contact list read from the retained entries. -/ contacts : List
    (SewnPrimitiveContacts.SourceContact faces)
  /-- The contact list is exactly the materialization of the dependent entry readbacks. -/ contacts_eq : contacts =
    List.ofFn (fun index => (entries.get index).contact)

constructive_injectivity BoundaryContactBank

end BoundaryContactSources

namespace BoundaryContactSources

open Purelib.Topology.Surface.Boundary in
/-- The pairing incidence witness puts both edges of every retained pair in the cut boundary. -/
theorem paired_boundary_members (pairing : ProjectedEdgePairs.ProjectedEdgePairing patch.vertexLabels patch.boundary)
    (pair : ProjectedEdgePairs.ProjectedEdgePair patch.vertexLabels) (member : pair ∈ pairing.pairs) :
    pair.first ∈ patch.boundary ∧ pair.second ∈ patch.boundary := by
  have members := occurrence_members pairing.pairs pair member
  exact ⟨(EdgeReordering.mem_iff pairing.incidence pair.first).mpr (Data.List.Membership.mem_append.mpr (Or.inr
    members.1)),
    (EdgeReordering.mem_iff pairing.incidence pair.second).mpr (Data.List.Membership.mem_append.mpr (Or.inr members.2))⟩

end BoundaryContactSources

namespace BoundaryContactSources.BoundaryContactBank

variable {pairing : ProjectedEdgePairs.ProjectedEdgePairing patch.vertexLabels patch.boundary}

open Purelib.Topology.Surface.Boundary in
open Purelib.Topology.Surface.Boundary.BoundaryContactSources in
open _root_.Purelib.Topology.Surface.Boundary renaming BoundaryContactSources -> BoundaryContactSources in
/-- Build and cache source ownership for the exact exposed boundary pairing. -/
@[expose] def build (patch : Patch.CutPatch faces indices boundary) (pairing : ProjectedEdgePairs.ProjectedEdgePairing
  patch.vertexLabels patch.boundary) :
    BoundaryContactBank patch pairing :=
  let entries := DependentVector.ofFn fun index : Fin pairing.pairs.length =>
    let pair := pairing.pairs[index.val]'index.isLt
    let members := paired_boundary_members pairing pair (List.getElem_mem _)
    BoundaryContactSources.build patch pair members.1 members.2
  ⟨entries, List.ofFn fun index => (entries.get index).contact, rfl⟩

open Purelib.Topology.Surface.Boundary in
/-- The contact at any retained pair index occurs in the cached contact list. -/
theorem contact_mem (bank : BoundaryContactBank patch pairing) (index : Fin pairing.pairs.length)
  :
    (bank.entries.get index).contact ∈ bank.contacts := by
  rw [bank.contacts_eq]
  exact List.Permutation.ofFn_mem _ index

open Purelib.Topology.Surface.Boundary in
open Purelib.Topology.Surface.Boundary.BoundaryContactSources in
open _root_.Purelib.Topology.Surface.Boundary renaming BoundaryContactSources -> BoundaryContactSources in
/-- Every contact in the bank has two positively oriented source edges. -/
theorem positive (bank : BoundaryContactBank patch pairing) (contact :
  SewnPrimitiveContacts.SourceContact faces) (member : contact ∈ bank.contacts) :
    SourceEdge.Positive contact.left faces ∧ SourceEdge.Positive contact.right faces := by
  rw [bank.contacts_eq] at member
  rcases Data.List.OfFn.Basic.mem_ofFn.mp member with ⟨index, equal⟩
  rw [← equal]
  exact BoundaryContactSources.positive (bank.entries.get index)

end BoundaryContactSources.BoundaryContactBank
end Purelib.Topology.Surface.Boundary
