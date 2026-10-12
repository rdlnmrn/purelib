module

import Purelib.Data.List.Membership
import Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness
import Purelib.Topology.Mesh.DualWalks
import Purelib.Topology.Mesh.IndexedQuadrilaterals
import Purelib.Topology.Polygon.Stokes
public import Purelib.Topology.Surface.Sewing.VertexSewing
public import Purelib.Topology.Mesh.QuadrilateralDual

/-!
# Dual walks that retain one actual surface vertex

Ordinary face connectivity is insufficient for gluing the different cut
occurrences of one surface vertex. Here every crossed seam contains that
same vertex. The quadrilateral constructors only cross a diagonal when
both incident triangles contain the requested vertex.
-/

namespace Purelib.Topology.Mesh.CornerWalks

public section

open Purelib.Topology.Mesh

open Purelib.Topology.Mesh.IndexedQuadrilaterals

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Sewing.VertexSewing

open Purelib.Data.List

open Purelib.Topology.Mesh.QuadrilateralDual
open Purelib.Topology.Mesh.DualWalks (DualWalk)
open Purelib.Topology.Mesh.IndexedQuadrilaterals (IndexedQuadrilateral)
open Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness

open Purelib.Topology.Polygon.Stokes (OrientedEdge OrientedTriangle)

variable {vertexCount faceCount : Nat} {faces : Fin faceCount → Stokes.OrientedTriangle vertexCount}

/-- A vertex is one of the three displayed corners of an oriented triangle. -/
@[expose] def OrientedTriangle.ContainsVertex (triangle : Stokes.OrientedTriangle vertexCount) (vertex : Fin
  vertexCount) : Prop :=
  vertex = triangle.first ∨ vertex = triangle.second ∨ vertex = triangle.third

section
open Purelib.Topology.Mesh.CornerWalks
/-- Relabeling a triangle preserves membership of the relabeled corner.

Each original corner identity is transported by the supplied label function. The resulting disjunction identifies the
same corner position in the relabeled triangle. -/
theorem OrientedTriangle.ContainsVertex.map {target : Nat} {triangle : Stokes.OrientedTriangle vertexCount}
    {vertex : Fin vertexCount} (contains : OrientedTriangle.ContainsVertex triangle vertex) (labels : Fin vertexCount →
      Fin target) :
    OrientedTriangle.ContainsVertex (OrientedTriangle.map labels triangle) (labels vertex) :=
  contains.elim (fun same => Or.inl (congrArg labels same)) (fun rest => rest.elim
    (fun same => Or.inr (Or.inl (congrArg labels same))) (fun same => Or.inr (Or.inr (congrArg labels same))))

/-- Either endpoint of a boundary edge is a corner of its triangle.

The boundary contains precisely the triangle's three directed edges. Splitting its original list membership identifies
the retained edge and its two endpoint corners. -/
theorem OrientedTriangle.edge_contains {triangle : Stokes.OrientedTriangle vertexCount} {edge : Stokes.OrientedEdge
  vertexCount}
    (member : edge ∈ triangle.boundary) {vertex : Fin vertexCount}
    (atVertex : vertex = edge.start ∨ vertex = edge.finish) : OrientedTriangle.ContainsVertex triangle vertex := by
  rcases Membership.mem_cons.mp member with same | member
  · cases same
    exact atVertex.elim Or.inl (fun same => Or.inr (Or.inl same))
  · rcases Membership.mem_cons.mp member with same | member
    · cases same
      exact atVertex.elim (fun same => Or.inr (Or.inl same)) (fun same => Or.inr (Or.inr same))
    · have same := Membership.mem_singleton.mp member
      cases same
      exact atVertex.elim (fun same => Or.inr (Or.inr same)) Or.inl

end

namespace DualWalk

/-- Every seam crossed by a dual walk contains the same retained vertex.

The empty walk satisfies this condition, and each step retains endpoint incidence together with the condition on its
tail. -/
@[expose] def AtVertex (vertex : Fin vertexCount) : {first last : Fin faceCount} → DualWalks.DualWalk faces first last →
  Prop
  | _, _, .nil _ => True
  | _, _, .cons edge _ _ tail => (vertex = edge.start ∨ vertex = edge.finish) ∧
    Purelib.Topology.Mesh.CornerWalks.DualWalk.AtVertex vertex tail

open Purelib.Topology.Mesh.CornerWalks
/-- Concatenating walks through one vertex preserves their seam incidence.

The original first walk supplies the head incidence at each step. Its finite tail joins the unchanged second walk with
the same retained vertex. -/
theorem AtVertex.append {vertex : Fin vertexCount} {first middle last : Fin faceCount}
    {left : DualWalks.DualWalk faces first middle} {right : DualWalks.DualWalk faces middle last}
    (leftAt : DualWalk.AtVertex vertex left) (rightAt : DualWalk.AtVertex vertex right) : DualWalk.AtVertex vertex
      (left.append right) := by
  induction left with
  | nil => exact rightAt
  | cons edge firstMember nextMember tail ih => exact ⟨leftAt.1, ih leftAt.2 rightAt⟩

/-- Reversing a dual walk preserves the vertex incident to every seam.

Every original seam exchanges its two endpoints. Reversal of the finite tail and concatenation retain the same vertex at
all reversed steps. -/
theorem AtVertex.reverse {vertex : Fin vertexCount} {first last : Fin faceCount}
    {path : DualWalks.DualWalk faces first last} (atVertex : DualWalk.AtVertex vertex path) : DualWalk.AtVertex vertex
      path.reverse := by
  induction path with
  | nil => trivial
  | cons edge firstMember nextMember tail ih =>
      exact (ih atVertex.2).append ⟨atVertex.1.symm, trivial⟩

/-- Transport a corner property along seams incident to that corner.

Each original step supplies the predicate transport through its retained seam and endpoint incidence. Finite induction
passes the resulting property along the same walk to its final face. -/
theorem AtVertex.preserves {vertex : Fin vertexCount} (predicate : Fin faceCount → Prop)
    (step : ∀ {first next}, ∀ edge ∈ (faces first).boundary, edge.reverse ∈ (faces next).boundary →
      (vertex = edge.start ∨ vertex = edge.finish) → predicate first → predicate next) :
    {first last : Fin faceCount} → (path : DualWalks.DualWalk faces first last) → DualWalk.AtVertex vertex path →
      predicate first → predicate last
  | _, _, .nil _, _, initial => initial
  | _, _, .cons edge firstMember nextMember tail, atVertex, initial =>
      Purelib.Topology.Mesh.CornerWalks.DualWalk.AtVertex.preserves predicate step tail atVertex.2 (step edge
        firstMember nextMember atVertex.1 initial)

end DualWalk

open Purelib.Topology.Mesh.CornerWalks in
/-- Actual triangle-to-triangle routes inside each vertex star.

For any two supplied incident triangles, the retained finite dual walk crosses only seams containing their same original
vertex. The output keeps both face indices and its incidence certificate. -/
abbrev VertexConnection (faces : Fin faceCount → Stokes.OrientedTriangle vertexCount) :=
  (vertex : Fin vertexCount) → (first last : Fin faceCount) →
    OrientedTriangle.ContainsVertex (faces first) vertex → OrientedTriangle.ContainsVertex (faces last) vertex →
      { path : DualWalks.DualWalk faces first last // DualWalk.AtVertex vertex path }

namespace QuadOccurrence

variable {quad other : IndexedQuadrilaterals.IndexedQuadrilateral vertexCount} {vertex : Fin vertexCount}

open Purelib.Topology.Mesh.CornerWalks
/-- A corner of either retained triangle is one of the quadrilateral's four corners.

The retained occurrence identifies the selected triangle with its original subdivision triangle. Its three displayed
corners are therefore among the same four quadrilateral vertices. -/
theorem corner_of_contains (located : QuadrilateralDual.QuadOccurrence faces quad) (upper : Bool)
    (contains : OrientedTriangle.ContainsVertex (faces (located.triangle upper)) vertex) :
    vertex = quad.first ∨ vertex = quad.second ∨ vertex = quad.third ∨ vertex = quad.fourth := by
  cases upper
  · rw [show located.triangle false = located.first from rfl, located.first_eq] at contains
    exact contains.elim Or.inl (fun remaining => remaining.elim
      (fun same => Or.inr (Or.inl same)) (fun same => Or.inr (Or.inr (Or.inl same))))
  · rw [show located.triangle true = located.second from rfl, located.second_eq] at contains
    exact contains.elim Or.inl (fun remaining => remaining.elim
      (fun same => Or.inr (Or.inr (Or.inl same))) (fun same => Or.inr (Or.inr (Or.inr same))))

/-- An endpoint of a quadrilateral edge belongs to its selected incident triangle.

The retained edge-membership certificate selects the original triangle boundary. Its endpoint incidence identifies a
corner of that same triangle. -/
theorem contains_of_edge (located : QuadrilateralDual.QuadOccurrence faces quad) (kind : RectangleEdge.Kind)
    (atVertex : vertex = ((IndexedQuadrilateral.edge quad kind)).start ∨ vertex = ((IndexedQuadrilateral.edge quad
      kind)).finish) :
    OrientedTriangle.ContainsVertex (faces (located.triangle (QuadOccurrence.upperSide kind))) vertex :=
  OrientedTriangle.edge_contains (located.edge_mem kind) atVertex

/-- A vertex shared by both subdivision triangles lies on their diagonal.

The two corners opposite the diagonal must be distinct. -/
private theorem on_diagonal (quad : IndexedQuadrilaterals.IndexedQuadrilateral vertexCount) (distinct : quad.second ≠
  quad.fourth)
    (first : OrientedTriangle.ContainsVertex quad.firstTriangle vertex) (last : OrientedTriangle.ContainsVertex
      quad.secondTriangle vertex) :
    vertex = quad.diagonal.start ∨ vertex = quad.diagonal.finish := by
  rcases first with first | second | third
  · exact Or.inr first
  · rcases last with first | third | fourth
    · exact Or.inr first
    · exact Or.inl third
    · exact (distinct (second.symm.trans fourth)).elim
  · exact Or.inl third

/-- The retained diagonal step crosses a seam incident to either diagonal endpoint. -/
theorem diagonal_at (located : QuadrilateralDual.QuadOccurrence faces quad)
    (atVertex : vertex = quad.diagonal.start ∨ vertex = quad.diagonal.finish) :
    DualWalk.AtVertex vertex located.diagonal := ⟨atVertex, trivial⟩

/-- The local connection between two incident triangles stays at their common vertex.

Distinct opposite corners ensure that a required diagonal crossing contains that vertex. -/
theorem connect_at (located : QuadrilateralDual.QuadOccurrence faces quad) (distinct : quad.second ≠ quad.fourth)
    (firstUpper lastUpper : Bool)
    (first : OrientedTriangle.ContainsVertex (faces (located.triangle firstUpper)) vertex)
    (last : OrientedTriangle.ContainsVertex (faces (located.triangle lastUpper)) vertex) :
    DualWalk.AtVertex vertex (located.connect firstUpper lastUpper) := by
  cases firstUpper <;> cases lastUpper
  · trivial
  · exact QuadOccurrence.diagonal_at located (QuadOccurrence.on_diagonal quad distinct
      (located.first_eq ▸ first) (located.second_eq ▸ last))
  · exact (QuadOccurrence.diagonal_at located (QuadOccurrence.on_diagonal quad distinct
      (located.first_eq ▸ last) (located.second_eq ▸ first))).reverse
  · trivial

/-- Crossing the displayed opposite seam preserves incidence to a seam endpoint. -/
theorem across_at (located : QuadrilateralDual.QuadOccurrence faces quad) (next : QuadrilateralDual.QuadOccurrence faces
  other)
    (firstSide nextSide : RectangleEdge.Kind) (opposite : (IndexedQuadrilateral.edge other nextSide) =
      ((IndexedQuadrilateral.edge quad firstSide)).reverse)
    (atVertex : vertex = ((IndexedQuadrilateral.edge quad firstSide)).start ∨ vertex = ((IndexedQuadrilateral.edge quad
      firstSide)).finish) :
    DualWalk.AtVertex vertex (located.across next firstSide nextSide opposite) := ⟨atVertex, trivial⟩

/-- Connect two retained quadrilateral occurrences through a shared vertex.

The supplied opposite seam and distinct opposite corners ensure that both local diagonal moves and the seam crossing
remain in the same vertex star. -/
theorem connectAcross_at (located : QuadrilateralDual.QuadOccurrence faces quad) (next :
  QuadrilateralDual.QuadOccurrence faces other)
    (firstDistinct : quad.second ≠ quad.fourth) (lastDistinct : other.second ≠ other.fourth)
    (firstSide nextSide : RectangleEdge.Kind) (opposite : (IndexedQuadrilateral.edge other nextSide) =
      ((IndexedQuadrilateral.edge quad firstSide)).reverse)
    (firstUpper lastUpper : Bool)
    (first : OrientedTriangle.ContainsVertex (faces (located.triangle firstUpper)) vertex)
    (last : OrientedTriangle.ContainsVertex (faces (next.triangle lastUpper)) vertex)
    (atVertex : vertex = ((IndexedQuadrilateral.edge quad firstSide)).start ∨ vertex = ((IndexedQuadrilateral.edge quad
      firstSide)).finish) :
    DualWalk.AtVertex vertex (located.connectAcross next firstSide nextSide opposite firstUpper lastUpper) := by
  have nextAt : vertex = ((IndexedQuadrilateral.edge other nextSide)).start ∨ vertex = ((IndexedQuadrilateral.edge other
    nextSide)).finish := by
    rw [opposite]
    exact atVertex.symm
  exact (QuadOccurrence.connect_at located firstDistinct firstUpper (QuadOccurrence.upperSide firstSide) first
    (QuadOccurrence.contains_of_edge located firstSide atVertex)).append
    ((QuadOccurrence.across_at located next firstSide nextSide opposite atVertex).append
      (QuadOccurrence.connect_at next lastDistinct (QuadOccurrence.upperSide nextSide) lastUpper
        (QuadOccurrence.contains_of_edge next nextSide nextAt) last))

end QuadOccurrence
end
end Purelib.Topology.Mesh.CornerWalks
