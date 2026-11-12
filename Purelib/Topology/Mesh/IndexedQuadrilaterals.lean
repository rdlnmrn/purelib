module

meta import Purelib.Elab.ConstructiveInjectivity

public import Purelib.Topology.Polygon.Stokes
public import Purelib.Topology.Mesh.TriangleSourceUniqueness
import Purelib.Data.List.Membership
import Purelib.Topology.Mesh.EdgeCancellation
import Purelib.Data.Gaussian.Basic
import Purelib.Tactic.Ring

open Purelib.Topology.Mesh.EdgeCancellation
open _root_.Purelib.Topology.Mesh renaming EdgeCancellation -> EdgeCancellation

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

public section

/-!
# Indexed quadrilaterals and their actual diagonal cancellation

The diagonal of the two-triangle subdivision occurs in both orientations.
The explicit incidence reordering exposes exactly the four original sides,
independently of any chosen primitive values or geometric embedding.
-/

namespace Purelib.Topology.Mesh.IndexedQuadrilaterals

open Purelib.Topology.Polygon.Stokes (EdgeReordering OrientedEdge OrientedTriangle PrimitivePoint edgeArea_reverse
  edgeListArea pairedEdgeOccurrences triangleBoundaryArea triangleBoundaryArea_eq_wedgeArea triangleWedgeArea)

set_option genInjectivity false in
/-- Four ordered bounded vertices defining a quadrilateral subdivision.

The two triangles share the diagonal from the first vertex to the third; distinctness of the vertices is not required.
-/
structure IndexedQuadrilateral (count : Nat) where
  /-- The first bounded vertex in the boundary order. -/ first : Fin count
  /-- The second bounded vertex in the boundary order. -/ second : Fin count
  /-- The third bounded vertex in the boundary order. -/ third : Fin count
  /-- The fourth bounded vertex in the boundary order. -/ fourth : Fin count

constructive_injectivity IndexedQuadrilateral

namespace IndexedQuadrilateral

open Purelib.Topology.Surface.Sewing

open Purelib.Data.List
open Purelib.Topology.Mesh
open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts (SourceEdge)

variable {count : Nat}

section
open Purelib.Topology.Mesh
/-- The oriented triangle on the first, second and third vertices. -/
@[expose] def firstTriangle (quad : IndexedQuadrilateral count) : Stokes.OrientedTriangle count :=
  ⟨quad.first, quad.second, quad.third⟩
/-- The oriented triangle on the first, third and fourth vertices. -/
@[expose] def secondTriangle (quad : IndexedQuadrilateral count) : Stokes.OrientedTriangle count
  := ⟨quad.first, quad.third, quad.fourth⟩
/-- The ordered pair of triangles in the quadrilateral subdivision. -/
@[expose] def triangles (quad : IndexedQuadrilateral count) : List (Stokes.OrientedTriangle count)
  := [quad.firstTriangle, quad.secondTriangle]

/-- The four oriented exterior sides in their cyclic order. -/
@[expose] def boundary (quad : IndexedQuadrilateral count) : List (Stokes.OrientedEdge count) :=
  [⟨quad.first, quad.second⟩, ⟨quad.second, quad.third⟩, ⟨quad.third, quad.fourth⟩, ⟨quad.fourth, quad.first⟩]

/-- The shared diagonal oriented from the third vertex to the first. -/
@[expose] def diagonal (quad : IndexedQuadrilateral count) : Stokes.OrientedEdge count :=
  ⟨quad.third, quad.first⟩

/-- Move the two diagonal occurrences past the last two exterior sides. -/
theorem incidence (quad : IndexedQuadrilateral count) :
    Stokes.EdgeReordering (quad.triangles.flatMap OrientedTriangle.boundary)
      (quad.boundary ++ Stokes.pairedEdgeOccurrences [quad.diagonal]) := by
  refine .cons ⟨quad.first, quad.second⟩ (.cons ⟨quad.second, quad.third⟩ ?_)
  exact EdgeReordering.append_swap [quad.diagonal, quad.diagonal.reverse]
    [⟨quad.third, quad.fourth⟩, ⟨quad.fourth, quad.first⟩] []

end

open Purelib.Topology.Mesh in
open Purelib.Topology.Mesh.IndexedQuadrilaterals in
/-- The two triangle wedge areas sum to the quadrilateral boundary area.

The equality holds for arbitrary primitive values at the indexed vertices; the two diagonal contributions cancel with
opposite orientations. -/
theorem wedge_eq_boundary (quad : IndexedQuadrilateral count) (primitive : Fin count →
  Stokes.PrimitivePoint) :
    Stokes.triangleWedgeArea (primitive quad.first) (primitive quad.second) (primitive quad.third) +
      Stokes.triangleWedgeArea (primitive quad.first) (primitive quad.third) (primitive quad.fourth) =
      Stokes.edgeListArea primitive quad.boundary := by
  rw [← Stokes.triangleBoundaryArea_eq_wedgeArea, ← Stokes.triangleBoundaryArea_eq_wedgeArea]
  simp only [Stokes.triangleBoundaryArea, boundary, Stokes.edgeListArea]
  rw [Stokes.edgeArea_reverse (primitive quad.third) (primitive quad.first)]
  ring1

/-- Read one of the four SAME signed vertex occurrences in boundary order. -/
def corner (quad : IndexedQuadrilateral count) : Fin 4 → Fin count :=
  Fin.cases quad.first (Fin.cases quad.second (Fin.cases quad.third (Fin.cases quad.fourth Fin.elim0)))

/-- Corner zero is the original first signed vertex. -/
theorem corner_zero (quad : IndexedQuadrilateral count) : quad.corner 0 = quad.first := by rfl

/-- Corner one is the original second signed vertex. -/
theorem corner_one (quad : IndexedQuadrilateral count) : quad.corner 1 = quad.second := by rfl

/-- Corner two is the original third signed vertex. -/
theorem corner_two (quad : IndexedQuadrilateral count) : quad.corner 2 = quad.third := by rfl

/-- Corner three is the original fourth signed vertex. -/
theorem corner_three (quad : IndexedQuadrilateral count) : quad.corner 3 = quad.fourth := by rfl

/-- The two original triangle occurrences indexed in their retained order. -/
def faces (quad : IndexedQuadrilateral count) (index : Fin 2) : Stokes.OrientedTriangle count :=
  if index.val = 0 then quad.firstTriangle else quad.secondTriangle

/-- The first indexed face is the original lower-diagonal triangle. -/
theorem faces_zero (quad : IndexedQuadrilateral count) : quad.faces 0 = quad.firstTriangle := by rfl

/-- The second indexed face is the original upper-diagonal triangle. -/
theorem faces_one (quad : IndexedQuadrilateral count) : quad.faces 1 = quad.secondTriangle := by rfl

/-- Four original source occurrences in bottom, right, top and left order.

The first two belong to the first triangle. The final two belong to the
second triangle, preserving its third-to-first closing orientation.
-/
def boundarySources : List (SourceEdge 2) :=
  [⟨0, 0, 1⟩, ⟨0, 1, 2⟩, ⟨1, 1, 2⟩, ⟨1, 2, 0⟩]

/-- Each retained source is a positive oriented occurrence of its actual triangle. -/
theorem boundarySources_positive (quad : IndexedQuadrilateral count) :
    ∀ source ∈ boundarySources,
      TriangleSourceUniqueness.SourceEdge.Positive source quad.faces := by
  intro source member
  rcases Membership.mem_cons.mp member with same | member
  · subst source
    exact List.mem_cons_self
  · rcases Membership.mem_cons.mp member with same | member
    · subst source
      exact List.mem_cons_of_mem _ List.mem_cons_self
    · rcases Membership.mem_cons.mp member with same | member
      · subst source
        exact List.mem_cons_of_mem _ List.mem_cons_self
      · rcases Membership.mem_cons.mp member with same | member
        · subst source
          exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
        · exact (List.not_mem_nil member).elim

/-- Projecting those SAME source occurrences gives the exact original quadrilateral boundary. -/
theorem boundarySources_project (quad : IndexedQuadrilateral count) :
    boundarySources.map (fun source => source.project quad.faces) = quad.boundary := by
  rfl

/-- Read one actual exterior side occurrence in the original cyclic order. -/
def boundaryEdge (quad : IndexedQuadrilateral count) : Fin 4 → Stokes.OrientedEdge count :=
  Fin.cases ⟨quad.first, quad.second⟩ (Fin.cases ⟨quad.second, quad.third⟩
    (Fin.cases ⟨quad.third, quad.fourth⟩ (Fin.cases ⟨quad.fourth, quad.first⟩ Fin.elim0)))

/-- Every selected exterior side is an actual original ordered boundary occurrence. -/
theorem boundaryEdge_mem (quad : IndexedQuadrilateral count) :
    ∀ side, quad.boundaryEdge side ∈ quad.boundary := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun impossible => nomatch impossible))))
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))

/-- Preserve whether an indexed source is an exterior side, shared diagonal, or stationary corner.

The direction flag reverses the SAME original edge. The alternatives are
selected from source face/corner positions, so repeated signed vertex
indices are not collapsed by equality or coordinate lookup.
-/
abbrev EdgeOccurrence (quad : IndexedQuadrilateral count) (source : SourceEdge 2) :=
  (Σ side : Fin 4, {reverse : Bool // source.project quad.faces =
    if reverse then (quad.boundaryEdge side).reverse else quad.boundaryEdge side}) ⊕
  ({reverse : Bool // source.project quad.faces = if reverse then quad.diagonal.reverse else quad.diagonal} ⊕
    {position : Fin 4 // source.project quad.faces = ⟨quad.corner position, quad.corner position⟩})

/-- Classify each literal original source occurrence without comparing vertex labels or coordinates.

All eighteen face/corner cases retain their real direction. Stationary
formal corners and repeated indices remain separate occurrences; no root,
Point, query, row, join or observation is acquired.
-/
def edgeOccurrence (quad : IndexedQuadrilateral count) (source : SourceEdge 2) : quad.EdgeOccurrence source := by
  rcases source with ⟨face, first, last⟩
  refine Fin.cases ?_ (Fin.cases ?_ (fun impossible => nomatch impossible)) face
  · refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun impossible => nomatch impossible))) first
    · refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun impossible => nomatch impossible))) last
      · exact .inr (.inr ⟨0, by rfl⟩)
      · exact .inl ⟨0, false, by rfl⟩
      · exact .inr (.inl ⟨true, by rfl⟩)
    · refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun impossible => nomatch impossible))) last
      · exact .inl ⟨0, true, by rfl⟩
      · exact .inr (.inr ⟨1, by rfl⟩)
      · exact .inl ⟨1, false, by rfl⟩
    · refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun impossible => nomatch impossible))) last
      · exact .inr (.inl ⟨false, by rfl⟩)
      · exact .inl ⟨1, true, by rfl⟩
      · exact .inr (.inr ⟨2, by rfl⟩)
  · refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun impossible => nomatch impossible))) first
    · refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun impossible => nomatch impossible))) last
      · exact .inr (.inr ⟨0, by rfl⟩)
      · exact .inr (.inl ⟨true, by rfl⟩)
      · exact .inl ⟨3, true, by rfl⟩
    · refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun impossible => nomatch impossible))) last
      · exact .inr (.inl ⟨false, by rfl⟩)
      · exact .inr (.inr ⟨2, by rfl⟩)
      · exact .inl ⟨2, false, by rfl⟩
    · refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun impossible => nomatch impossible))) last
      · exact .inl ⟨3, false, by rfl⟩
      · exact .inl ⟨2, true, by rfl⟩
      · exact .inr (.inr ⟨3, by rfl⟩)

/-- Read the original quadrilateral corner of one literal source-face corner. -/
def faceCorner : Fin 2 → Fin 3 → Fin 4 :=
  Fin.cases (Fin.cases 0 (Fin.cases 1 (Fin.cases 2 Fin.elim0)))
    (Fin.cases (Fin.cases 0 (Fin.cases 2 (Fin.cases 3 Fin.elim0))) Fin.elim0)

/-- Original source-face corner lookup retains its exact quadrilateral occurrence.

The equation is about bounded indices. Coincident coordinate or root
labels do not identify any of these six original corner occurrences.
-/
theorem faceCorner_eq (quad : IndexedQuadrilateral count) : ∀ face corner,
    quad.corner (faceCorner face corner) = SewnPrimitiveFaces.corner (quad.faces face) corner := by
  refine Fin.cases ?_ (Fin.cases ?_ (fun impossible => nomatch impossible))
  · refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun impossible => nomatch impossible))) <;>
      rfl
  · refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun impossible => nomatch impossible))) <;>
      rfl

end IndexedQuadrilateral

end Purelib.Topology.Mesh.IndexedQuadrilaterals
