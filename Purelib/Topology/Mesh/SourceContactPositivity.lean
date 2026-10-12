module
import Purelib.Data.List.Membership

import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.PolygonSewing
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
public import Purelib.Topology.Mesh.TriangleSourceUniqueness

public section

/-!
# Positive source occurrences for every actual sewing contact

Both sources come from retained oriented boundary owners. Positivity is
therefore a consequence of the assembly, not an extra preparation premise.
The same guarantee applies to a generated bank with checked coverage.
-/

namespace Purelib.Topology.Mesh.SourceContactPositivity

open Purelib.Data.List

open Purelib.Topology.Mesh.TriangleSourceUniqueness
open Purelib.Topology.Polygon
open Purelib.Topology.Surface.Cut
open Purelib.Topology.Surface.Cut.Patch
open Purelib.Topology.Surface.Sewing
open Purelib.Topology.Surface.Sewing.PolygonSewing
open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts

open Purelib.Topology.Surface.Cut.Patch (CutPatch)
open Purelib.Topology.Surface.Sewing.PolygonSewing.PolygonStokes (BoundarySplit)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts (SourceContact ContactBank sourceContacts)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts.SourceContact (ofSeam)

open Purelib.Topology.Polygon.Stokes (OrientedEdge OrientedTriangle)

variable {vertexCount faceCount : Nat} {faces : Fin faceCount → Stokes.OrientedTriangle vertexCount}

/-- Both sources of a retained sewing seam are positive oriented face occurrences.

The seam and its supplied opposite-edge equation retain the original boundary owners on both sides. -/
theorem SourceContact.ofSeam_positive
    {firstIndices secondIndices : List (Fin faceCount)}
    {firstBoundary secondBoundary : List (Stokes.OrientedEdge vertexCount)}
    {first : Patch.CutPatch faces firstIndices firstBoundary} {second : Patch.CutPatch faces secondIndices
      secondBoundary}
    {firstBase : PolygonStokes.BoundarySplit firstBoundary} {secondBase : PolygonStokes.BoundarySplit secondBoundary}
    (seam : CutPatch.Seam first second firstBase secondBase)
    (opposite : secondBase.edge = firstBase.edge.reverse) :
    SourceEdge.Positive (SourceContact.ofSeam seam opposite).left faces ∧ SourceEdge.Positive (SourceContact.ofSeam seam
      opposite).right faces :=
  ⟨TriangleEdgeOwner.sourceEdge_positive _, TriangleEdgeOwner.sourceEdge_positive _⟩

variable {indices : List (Fin faceCount)} {boundary : List (Stokes.OrientedEdge vertexCount)}
  {patch : Patch.CutPatch faces indices boundary}

open Purelib.Topology.Mesh.SourceContactPositivity in
/-- Every contact extracted from a finite sewing assembly has positive sources on both sides.

Positivity is proved for the actual retained contact occurrences in the extraction list. -/
theorem sourceContacts_positive (assembly : CutPatch.Assembly faces patch) :
    ∀ contact ∈ SewnPrimitiveContacts.sourceContacts assembly, SourceEdge.Positive contact.left faces ∧
      SourceEdge.Positive contact.right faces := by
  induction assembly with
  | triangle => intro contact member; exact (List.not_mem_nil member).elim
  | sew left right firstBase secondBase opposite seam ihLeft ihRight =>
      intro contact member
      rcases Membership.mem_cons.mp member with equal | member
      · cases equal
        exact SourceContact.ofSeam_positive seam opposite
      · exact (Membership.mem_append.mp member).elim (ihLeft contact) (ihRight contact)

open Purelib.Topology.Mesh in
/-- Every entry of a checked assembly contact bank has positive sources.

The bank equality transports membership to the contact list extracted from that same assembly. -/
theorem ContactBank.positive {assembly : CutPatch.Assembly faces patch} (contacts : SewnPrimitiveContacts.ContactBank
  assembly)
    (contact : SewnPrimitiveContacts.SourceContact faces) (member : contact ∈ contacts.entries) :
    SourceEdge.Positive contact.left faces ∧ SourceEdge.Positive contact.right faces :=
  SourceContactPositivity.sourceContacts_positive assembly contact (contacts.entries_eq ▸ member)

end Purelib.Topology.Mesh.SourceContactPositivity

end
