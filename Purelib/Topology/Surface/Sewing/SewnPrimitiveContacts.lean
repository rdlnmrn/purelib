module
import Purelib.Data.List.Map
import Purelib.Data.List.Append
import Purelib.Data.List.Membership
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic

import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.PolygonSewing
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewnPrimitiveBoundary
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
import Purelib.Topology.Surface.Sewing.VertexSewing
public import Purelib.Topology.Surface.Sewing.SewnPrimitiveRequests
import Purelib.Topology.Surface.Sewing.SewingProjection
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Tactic.QuotientFreeOmega

/-!
# Geometry-only source contacts for a retained cut assembly

Every sewn edge is traced back to two original face corners before selecting
primitive accuracy. The resulting finite contact list identifies the actual
local increments for every later sample, including after nonzero ancestor
corrections. Bounds on this list therefore discharge the whole-tree local
accuracy obligations without caller-supplied seam readback equations.
-/

public section

namespace Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts

open Purelib.Data.List

open Purelib.Data
open Purelib.Data.Gaussian.Norm.Basic
open Purelib.Data.Rat
open Purelib.Topology.Polygon
open Purelib.Topology.Surface.Cut
open Purelib.Topology.Surface.Cut.Patch
open Purelib.Topology.Surface.Sewing
open Purelib.Topology.Surface.Sewing.PolygonSewing
open Purelib.Topology.Surface.Sewing.PrimitiveSewing
open Purelib.Topology.Surface.Sewing.PrimitiveSewing.CutPatch
open Purelib.Topology.Surface.Sewing.SewnPrimitiveBoundary
open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
open Purelib.Topology.Surface.Sewing.VertexSewing

open Purelib.Topology.Surface.Cut.Patch (CutPatch)
open Purelib.Topology.Surface.Sewing.PrimitiveSewing (PrimitiveValues)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces (FaceBank Coordinate corner corner_map)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveRequests (LocalMismatch LocalAccuracy Request)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveBoundary (TriangleEdgeOwner boundaryOwner)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveBoundary.FaceBank (EdgeReading)
open Purelib.Topology.Surface.Sewing.PolygonSewing.PolygonStokes (BoundarySplit)

open Purelib.Topology.Polygon.Stokes (OrientedEdge OrientedTriangle)
open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib.Data.Gaussian.Basic.Canonical

set_option genInjectivity false in
/-- An oriented increment owned by one original face occurrence.

The source and its ordered corner indices remain available before any primitive values are selected. -/
structure SourceEdge (faceCount : Nat) where
  /-- Index of the original face occurrence. -/ source : Fin faceCount
  /-- Starting corner of the original oriented increment. -/ first : Fin 3
  /-- Finishing corner of the original oriented increment. -/ last : Fin 3

constructive_injectivity SourceEdge

namespace SourceEdge

/-- Project the retained source face's ordered corners to an oriented mesh edge. -/
@[expose] def project {vertexCount faceCount : Nat} (edge : SewnPrimitiveContacts.SourceEdge faceCount)
    (faces : Fin faceCount → Stokes.OrientedTriangle vertexCount) : Stokes.OrientedEdge vertexCount :=
  ⟨corner (faces edge.source) edge.first, SewnPrimitiveFaces.corner (faces edge.source) edge.last⟩

/-- Subtract the original starting corner reading from the finishing corner reading. -/
@[expose] def increment {faceCount : Nat} (edge : SewnPrimitiveContacts.SourceEdge faceCount)
    (values : Fin faceCount → PrimitiveSewing.PrimitiveValues 3) : Gaussian.Basic.Canonical :=
  values edge.source edge.last - values edge.source edge.first

end SourceEdge

variable {vertexCount faceCount : Nat} {faces : Fin faceCount → Stokes.OrientedTriangle vertexCount}
  {indices : List (Fin faceCount)} {boundary : List (Stokes.OrientedEdge vertexCount)}
  {patch : Patch.CutPatch faces indices boundary} {edge : Stokes.OrientedEdge patch.count}

/-- The original source is obtained from the retained occurrence order, not from a search for matching projected
coordinates.

The bounded position selects the assembly's original face index, and the two retained corners preserve the oriented
edge. -/
@[expose] def TriangleEdgeOwner.sourceEdge (owner : SewnPrimitiveBoundary.TriangleEdgeOwner patch.triangles edge) :
  SewnPrimitiveContacts.SourceEdge faceCount :=
  ⟨indices[owner.position.val]'(by rw [← patch.triangles_length]; exact owner.position.isLt), owner.first, owner.last⟩

/-- The original source edge projects to the owner's actual cut edge.

The cached triangle-list equation identifies the face at the retained bounded position; the owner's corner equations
then recover the projected edge. -/
theorem TriangleEdgeOwner.sourceEdge_project (owner : SewnPrimitiveBoundary.TriangleEdgeOwner patch.triangles edge) :
    SewnPrimitiveContacts.SourceEdge.project (TriangleEdgeOwner.sourceEdge owner) faces = OrientedEdge.map
      patch.vertexLabels edge := by
  have triangle := List.getElem_of_eq patch.triangles_eq (i := owner.position.val)
    (by rw [Map.length_map]; exact owner.position.isLt)
  have sourceBound : owner.position.val < indices.length := by
    rewrite [← patch.triangles_length]
    exact owner.position.isLt
  rewrite [Map.getElem_map (OrientedTriangle.map patch.vertexLabels) patch.triangles
    owner.position.val owner.position.isLt (by rewrite [Map.length_map]; exact owner.position.isLt),
    Map.getElem_map faces indices owner.position.val sourceBound
      (by rewrite [Map.length_map]; exact sourceBound)] at triangle
  change (⟨corner (faces _) owner.first, SewnPrimitiveFaces.corner (faces _) owner.last⟩ : Stokes.OrientedEdge
    vertexCount) = _
  dsimp only [TriangleEdgeOwner.sourceEdge]
  rw [← triangle, SewnPrimitiveFaces.corner_map, SewnPrimitiveFaces.corner_map, owner.start_eq, owner.finish_eq]
  rfl

namespace FaceBank.EdgeReading

variable {localValues : Fin faceCount → PrimitiveSewing.PrimitiveValues 3} {values : PrimitiveSewing.PrimitiveValues
  patch.count}
  {bank : SewnPrimitiveFaces.FaceBank patch localValues values} {owner : SewnPrimitiveBoundary.TriangleEdgeOwner
    patch.triangles edge}

/-- The cached face reading retains the original source occurrence selected by its owner.

Both readbacks use the owner's retained bounded position in the same face bank, whose source-list equation identifies
the original occurrence. -/
theorem source_eq (reading : FaceBank.EdgeReading bank owner) : reading.trace.source =
  (SewnPrimitiveContacts.TriangleEdgeOwner.sourceEdge owner).source := by
  rw [reading.trace_eq]
  have source := List.getElem_of_eq bank.sources_eq (i := owner.position.val)
    (by rw [Map.length_map, FaceBank.entries_length bank]; exact owner.position.isLt)
  have entryBound : owner.position.val < bank.entries.length := by
    rewrite [FaceBank.entries_length bank]
    exact owner.position.isLt
  rewrite [Map.getElem_map (fun trace => trace.source) bank.entries owner.position.val entryBound
    (by rewrite [Map.length_map]; exact entryBound)] at source
  exact source

/-- The cached local increment equals the original source edge's increment. -/
theorem source_increment (reading : FaceBank.EdgeReading bank owner) :
    reading.localIncrement = SewnPrimitiveContacts.SourceEdge.increment
      (SewnPrimitiveContacts.TriangleEdgeOwner.sourceEdge owner) localValues := by
  rw [reading.localIncrement_eq, EdgeReading.source_eq reading]
  rfl

end FaceBank.EdgeReading

set_option genInjectivity false in
/-- Projected reversal is certified from the actual sewing operation.

The two retained source-face edges project to opposite mesh traversals; their primitive readings remain separate data.
-/
structure SourceContact (faces : Fin faceCount → Stokes.OrientedTriangle vertexCount) where
  /-- Original source increment on the first side of the seam. -/ left : SewnPrimitiveContacts.SourceEdge faceCount
  /-- Original source increment on the second side of the seam. -/ right : SewnPrimitiveContacts.SourceEdge faceCount
  /-- The projected right edge is the reverse of the projected left edge. -/ opposite : right.project faces =
    (left.project faces).reverse

constructive_injectivity SourceContact

namespace SourceContact

/-- Squared norm of the sum of two oppositely oriented original increments. -/
@[expose] def mismatch (contact : SewnPrimitiveContacts.SourceContact faces) (values : Fin faceCount →
  PrimitiveSewing.PrimitiveValues 3) : Fraction.Rational :=
  Data.Gaussian.Norm.Basic.normSq (contact.left.increment values + contact.right.increment values)

variable {firstIndices secondIndices : List (Fin faceCount)}
  {firstBoundary secondBoundary : List (Stokes.OrientedEdge vertexCount)}
  {first : Patch.CutPatch faces firstIndices firstBoundary} {second : Patch.CutPatch faces secondIndices secondBoundary}
  {firstBase : PolygonStokes.BoundarySplit firstBoundary} {secondBase : PolygonStokes.BoundarySplit secondBoundary}

/-- Recover both original source increments and their projected reversal from a retained seam. -/
@[expose] def ofSeam (seam : CutPatch.Seam first second firstBase secondBase)
    (opposite : secondBase.edge = firstBase.edge.reverse) : SewnPrimitiveContacts.SourceContact faces :=
  let left := SewnPrimitiveBoundary.boundaryOwner first seam.firstLift.split.edge seam.firstLift.split.edge_mem
  let right := SewnPrimitiveBoundary.boundaryOwner second seam.secondLift.split.edge seam.secondLift.split.edge_mem
  ⟨TriangleEdgeOwner.sourceEdge left, SewnPrimitiveContacts.TriangleEdgeOwner.sourceEdge right, by
    rw [SewnPrimitiveContacts.TriangleEdgeOwner.sourceEdge_project right,
      SewnPrimitiveContacts.TriangleEdgeOwner.sourceEdge_project left, seam.secondLift.edge_eq, seam.firstLift.edge_eq]
    exact opposite⟩

/-- A source-contact mismatch bound supplies the seam's local accuracy certificate.

The construction retains the two boundary owners and uses the existing face banks for their numeric readbacks. -/
theorem localMismatch (seam : CutPatch.Seam first second firstBase secondBase)
    (opposite : secondBase.edge = firstBase.edge.reverse)
    {localValues : Fin faceCount → PrimitiveSewing.PrimitiveValues 3}
    {leftValues : PrimitiveSewing.PrimitiveValues first.count} {rightValues : PrimitiveSewing.PrimitiveValues
      second.count}
    (left : SewnPrimitiveFaces.FaceBank first localValues leftValues) (right : SewnPrimitiveFaces.FaceBank second
      localValues rightValues)
    (joined : EndpointGluing.PrimitiveSew leftValues rightValues seam.firstLift.split.edge seam.secondLift.split.edge)
    {tolerance : SewnPrimitiveFaces.Coordinate} (bounded : (SourceContact.ofSeam seam opposite).mismatch localValues ≤
      tolerance) :
    SewnPrimitiveRequests.LocalMismatch left right joined tolerance := by
  refine ⟨boundaryOwner first seam.firstLift.split.edge seam.firstLift.split.edge_mem,
    SewnPrimitiveBoundary.boundaryOwner second seam.secondLift.split.edge seam.secondLift.split.edge_mem, ?_⟩
  rw [SewnPrimitiveContacts.FaceBank.EdgeReading.source_increment,
    SewnPrimitiveContacts.FaceBank.EdgeReading.source_increment]
  exact bounded

end SourceContact

/-- Geometry-only enumeration, in the same root/left/right order as the actual seam charges.

A triangle contributes no contact. A sewing node contributes its own retained seam followed by the left and right
contact lists in that order. -/
@[expose] def sourceContacts : {indices : List (Fin faceCount)} → {boundary : List (Stokes.OrientedEdge vertexCount)} →
    {patch : Patch.CutPatch faces indices boundary} → CutPatch.Assembly faces patch → List
      (SewnPrimitiveContacts.SourceContact faces)
  | _, _, _, .triangle _ => []
  | _, _, _, .sew left right _ _ opposite seam =>
      SewnPrimitiveContacts.SourceContact.ofSeam seam opposite ::
        (Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts.sourceContacts left ++
        Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts.sourceContacts right)

/-- An assembly has exactly one fewer source contact than original face occurrences. -/
theorem sourceContacts_length (assembly : CutPatch.Assembly faces patch) :
    (SewnPrimitiveContacts.sourceContacts assembly).length + 1 = indices.length := by
  induction assembly with
  | triangle => rfl
  | sew left right firstBase secondBase opposite seam ihLeft ihRight =>
      simp only [SewnPrimitiveContacts.sourceContacts, List.length_cons, Append.length_append]
      omega

/-- Original local face bounds pay every seam, even when previous joins have already changed the sewn vertex readings.
-/
theorem localAccuracy_of_sourceContacts {localValues : Fin faceCount → PrimitiveSewing.PrimitiveValues 3}
    {assembly : CutPatch.Assembly faces patch} {values : PrimitiveSewing.PrimitiveValues patch.count}
    (readings : Assembly.Readings localValues assembly values) {tolerance : SewnPrimitiveFaces.Coordinate}
    (bounded : ∀ contact ∈ SewnPrimitiveContacts.sourceContacts assembly, contact.mismatch localValues ≤ tolerance) :
    SewnPrimitiveRequests.LocalAccuracy tolerance readings := by
  induction readings with
  | triangle => exact True.intro
  | sew left right joined ihLeft ihRight =>
      refine ⟨ihLeft (fun contact member => bounded contact (List.mem_cons_of_mem _
        (Membership.mem_append.mpr (Or.inl member)))),
        ihRight (fun contact member => bounded contact (List.mem_cons_of_mem _
          (Membership.mem_append.mpr (Or.inr member)))), ?_⟩
      exact SewnPrimitiveContacts.SourceContact.localMismatch _ _ (FaceBank.build left) (FaceBank.build right) joined
        (bounded _ List.mem_cons_self)

set_option genInjectivity false in
/-- Generated geometry caches need only reproduce the certified source contacts.

The entries retain the assembly's exact root/left/right contact order, with an equation linking the cache to its
original enumeration. -/
structure ContactBank (assembly : CutPatch.Assembly faces patch) where
  /-- Cached source contacts in the assembly's original traversal order. -/ entries : List
    (SewnPrimitiveContacts.SourceContact faces)
  /-- The cached list is exactly the source contacts computed from this assembly. -/ entries_eq : entries =
    SewnPrimitiveContacts.sourceContacts assembly

constructive_injectivity ContactBank

namespace ContactBank

variable {assembly : CutPatch.Assembly faces patch}

/-- Cache the original assembly's finite source-contact enumeration. -/
@[expose] def build (assembly : CutPatch.Assembly faces patch) : SewnPrimitiveContacts.ContactBank assembly :=
  ⟨sourceContacts assembly, rfl⟩

/-- Bounds on all cached original contacts certify the sewn face bank's requested total error. -/
theorem accurate (contacts : SewnPrimitiveContacts.ContactBank assembly) {target : SewnPrimitiveFaces.Coordinate}
    (request : SewnPrimitiveRequests.Request assembly target) {localValues : Fin faceCount →
      PrimitiveSewing.PrimitiveValues 3}
    {values : PrimitiveSewing.PrimitiveValues patch.count} (readings : Assembly.Readings localValues assembly values)
    (bounded : ∀ contact ∈ contacts.entries, contact.mismatch localValues ≤ request.tolerance) :
    (FaceBank.build readings).squaredErrors < target :=
  request.accurate readings (SewnPrimitiveContacts.localAccuracy_of_sourceContacts readings
    (fun contact member => bounded contact (by rw [contacts.entries_eq]; exact member)))

end ContactBank

end Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts

end
