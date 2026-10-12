module

meta import Purelib.Elab.ConstructiveInjectivity

import Purelib.Topology.Mesh.IndexedQuadrilaterals
import Purelib.Topology.Polygon.Stokes
public import Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness
public import Purelib.Topology.Mesh.DualWalks
import Purelib.Tactic.QuotientFreeOmega

public section

/-!
# Dual steps through retained quadrilateral subdivisions

An occurrence stores the two actual triangle indices and their exact face
equations. Diagonal links and side-to-side steps consume those indices;
they do not search or triangulate a second time.
-/

namespace Purelib.Topology.Mesh.QuadrilateralDual
open Purelib.Topology.Mesh

open Purelib.Topology.Polygon

open Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness

open Purelib.Topology.Mesh.IndexedQuadrilaterals (IndexedQuadrilateral)

variable {vertexCount faceCount : Nat}

set_option genInjectivity false in
/-- Locate both triangles of a quadrilateral in a retained finite face bank.

The two bounded indices come with exact equations identifying their faces with the prescribed subdivision triangles. -/
structure QuadOccurrence (faces : Fin faceCount → Stokes.OrientedTriangle vertexCount)
    (quad : IndexedQuadrilaterals.IndexedQuadrilateral vertexCount) where
  /-- The retained index of the first subdivision triangle. -/ first : Fin faceCount
  /-- The retained index of the second subdivision triangle. -/ second : Fin faceCount
  /-- The face at the first retained index is the first subdivision triangle. -/ first_eq : faces first =
    quad.firstTriangle
  /-- The face at the second retained index is the second subdivision triangle. -/ second_eq : faces second =
    quad.secondTriangle

constructive_injectivity QuadOccurrence

namespace QuadOccurrence

variable {faces : Fin faceCount → Stokes.OrientedTriangle vertexCount} {quad :
  IndexedQuadrilaterals.IndexedQuadrilateral vertexCount}

/-- Select the retained first or second triangle index by a Boolean flag. -/
@[expose] def triangle (located : QuadrilateralDual.QuadOccurrence faces quad) (upper : Bool) : Fin faceCount :=
  if upper then located.second else located.first

/-- Connect both retained subdivision triangles across their shared diagonal.

The original face equations retain the diagonal in both triangle boundaries,
with the reversed orientation required by the second face. -/
@[expose] def diagonal (located : QuadrilateralDual.QuadOccurrence faces quad) : DualWalks.DualWalk faces located.first
  located.second :=
  .cons quad.diagonal
    (by rw [located.first_eq]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    (by rw [located.second_eq]; exact List.mem_cons_self) (.nil _)

/-- Connect either retained subdivision triangle to either other one.

Equal endpoint flags give an empty walk; different flags use the retained diagonal in the required orientation. -/
@[expose] def connect (located : QuadrilateralDual.QuadOccurrence faces quad) : (firstUpper lastUpper : Bool) →
    DualWalks.DualWalk faces (located.triangle firstUpper) (located.triangle lastUpper)
  | false, false => .nil _
  | false, true => located.diagonal
  | true, false => located.diagonal.reverse
  | true, true => .nil _

/-- Select which subdivision triangle contains a rectangular edge kind. -/
@[expose] def upperSide : RectangleEdge.Kind → Bool
  | .bottom | .right | .downDiagonal => false
  | .upDiagonal | .top | .left => true

/-- Each rectangular edge kind lies in its selected retained triangle boundary.

The supplied occurrence equations identify both triangle faces. Each of the
six cases retains its exact ordered edge occurrence in the selected boundary. -/
theorem edge_mem (located : QuadrilateralDual.QuadOccurrence faces quad) (kind : RectangleEdge.Kind) :
    IndexedQuadrilateral.edge quad kind ∈ (faces (located.triangle (QuadOccurrence.upperSide kind))).boundary := by
  cases kind
  · change _ ∈ (faces located.first).boundary
    rw [located.first_eq]
    exact List.Mem.head _
  · change _ ∈ (faces located.first).boundary
    rw [located.first_eq]
    exact List.Mem.tail _ (List.Mem.head _)
  · change _ ∈ (faces located.first).boundary
    rw [located.first_eq]
    exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  · change _ ∈ (faces located.second).boundary
    rw [located.second_eq]
    exact List.Mem.head _
  · change _ ∈ (faces located.second).boundary
    rw [located.second_eq]
    exact List.Mem.tail _ (List.Mem.head _)
  · change _ ∈ (faces located.second).boundary
    rw [located.second_eq]
    exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))

/-- Cross the displayed reversed seam between two retained quadrilaterals.

The supplied edge-reversal equation identifies the original side occurrences.
The resulting walk connects their retained triangle indices through that seam. -/
@[expose] def across {other : IndexedQuadrilaterals.IndexedQuadrilateral vertexCount} (located :
  QuadrilateralDual.QuadOccurrence faces quad)
    (next : QuadrilateralDual.QuadOccurrence faces other) (firstSide nextSide : RectangleEdge.Kind)
    (opposite : IndexedQuadrilateral.edge other nextSide = (IndexedQuadrilateral.edge quad firstSide).reverse) :
    DualWalks.DualWalk faces (located.triangle (QuadOccurrence.upperSide firstSide)) (next.triangle
      (QuadOccurrence.upperSide nextSide)) :=
  .cons (IndexedQuadrilateral.edge quad firstSide) (located.edge_mem firstSide)
    (by rw [← opposite]; exact next.edge_mem nextSide) (.nil _)

/-- Connect requested triangles through their retained diagonal moves and seam.

The original source and destination flags choose the diagonal walks. Their
concatenation retains the supplied reversed side occurrence between them. -/
@[expose] def connectAcross {other : IndexedQuadrilaterals.IndexedQuadrilateral vertexCount} (located :
  QuadrilateralDual.QuadOccurrence faces quad)
    (next : QuadrilateralDual.QuadOccurrence faces other) (firstSide nextSide : RectangleEdge.Kind)
    (opposite : IndexedQuadrilateral.edge other nextSide = (IndexedQuadrilateral.edge quad firstSide).reverse)
      (firstUpper lastUpper : Bool) :
    DualWalks.DualWalk faces (located.triangle firstUpper) (next.triangle lastUpper) :=
  (located.connect firstUpper (QuadOccurrence.upperSide firstSide)).append
    ((located.across next firstSide nextSide opposite).append (next.connect (QuadOccurrence.upperSide nextSide)
      lastUpper))

/-- Reindex a retained occurrence into another finite face bank.

The supplied index map and face equations transport both original triangle
positions while preserving their exact subdivision-face identities. -/
@[expose] def map {otherCount : Nat} (located : QuadrilateralDual.QuadOccurrence faces quad)
    (otherFaces : Fin otherCount → Stokes.OrientedTriangle vertexCount) (index : Fin faceCount → Fin otherCount)
    (equations : ∀ old, otherFaces (index old) = faces old) : QuadrilateralDual.QuadOccurrence otherFaces quad :=
  ⟨index located.first, index located.second, (equations located.first).trans located.first_eq,
    (equations located.second).trans located.second_eq⟩

/-- Transport a retained quadrilateral occurrence after prepending a face to its bank.

Both stored indices are shifted by Fin.succ, preserving the original face equations. -/
@[expose] def prepend {triangles : List (Stokes.OrientedTriangle vertexCount)}
    (located : QuadrilateralDual.QuadOccurrence (fun index : Fin triangles.length => triangles[index.val]) quad)
    (head : Stokes.OrientedTriangle vertexCount) :
    QuadrilateralDual.QuadOccurrence (fun index : Fin (head :: triangles).length => (head :: triangles)[index.val]) quad
      :=
  located.map _ Fin.succ (fun _ => rfl)

end QuadOccurrence

end Purelib.Topology.Mesh.QuadrilateralDual
