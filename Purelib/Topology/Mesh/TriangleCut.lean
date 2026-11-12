module

public import Purelib.Topology.Surface.Cut.Patch
public import Purelib.Topology.Mesh.TriangleSourceUniqueness
import Purelib.Topology.Surface.Sewing.PolygonSewing
import Purelib.Data.List.Map
import Purelib.Data.List.Membership
import Purelib.Topology.Surface.Sewing.VertexSewing

/-! # The original sewn patch for a triangle cut on two incident sides

The five slots retain, in order, the original apex, first cut, second old
corner, third old corner and second cut. Equal coordinate values never
identify these distinct occurrences. The three original child faces are
sewn at their literal opposite diagonal occurrences.
-/

public section

namespace Purelib.Topology.Mesh.TriangleCut

open Purelib.Data.List
open Purelib.Topology.Polygon.Stokes (OrientedTriangle OrientedEdge)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts (SourceEdge)
open Purelib.Topology.Surface.Sewing
open Purelib.Topology.Surface.Cut.Patch (CutPatch)
open Purelib.Topology.Surface.Sewing.PolygonSewing.PolygonStokes (BoundarySplit)

/-- The three actual child faces on the five retained ordered cut slots. -/
def faces : Fin 3 → OrientedTriangle 5 :=
  Fin.cases ⟨0, 1, 4⟩ (Fin.cases ⟨1, 2, 3⟩ (Fin.cases ⟨1, 3, 4⟩ Fin.elim0))

/-- The first child retains the original apex and both computed side cuts. -/
theorem faces_zero : faces 0 = ⟨0, 1, 4⟩ := by rfl

/-- The second child retains the first cut and both original opposite corners. -/
theorem faces_one : faces 1 = ⟨1, 2, 3⟩ := by rfl

/-- The third child retains the first cut, third original corner and second cut. -/
theorem faces_two : faces 2 = ⟨1, 3, 4⟩ := by rfl

/-- Select the second child's last side, from the third corner to the first cut. -/
private def secondSeam : BoundarySplit (faces 1).boundary :=
  ⟨[⟨1, 2⟩, ⟨2, 3⟩], ⟨3, 1⟩, [], rfl⟩

/-- Select the third child's first side, the literal reverse of that same seam. -/
private def thirdSeam : BoundarySplit (faces 2).boundary :=
  ⟨[], ⟨1, 3⟩, [⟨3, 4⟩, ⟨4, 1⟩], rfl⟩

/-- Retain the existing sewn quadrilateral on the side opposite the original apex. -/
private def opposite : CutPatch faces [1, 2] [⟨1, 2⟩, ⟨2, 3⟩, ⟨3, 4⟩, ⟨4, 1⟩] :=
  let second := CutPatch.triangle faces 1
  let third := CutPatch.triangle faces 2
  let seam := CutPatch.Seam.build second third secondSeam thirdSeam
  CutPatch.sew second third secondSeam thirdSeam rfl seam

/-- Select the first child's cut-to-cut side. -/
private def apexSeam : BoundarySplit (faces 0).boundary :=
  ⟨[⟨0, 1⟩], ⟨1, 4⟩, [⟨4, 0⟩], rfl⟩

/-- Select its actual opposite occurrence on the retained other two children. -/
private def oppositeSeam : BoundarySplit (count := 5) [⟨1, 2⟩, ⟨2, 3⟩, ⟨3, 4⟩, ⟨4, 1⟩] :=
  ⟨[⟨1, 2⟩, ⟨2, 3⟩, ⟨3, 4⟩], ⟨4, 1⟩, [], rfl⟩

/-- The exact original subdivided perimeter, starting at the second cut occurrence.

The cyclic order is second-cut/apex/first-cut/second-corner/third-corner.
Both split old sides retain their literal ordered sub-occurrences.
-/
def boundary : List (OrientedEdge 5) :=
  [⟨4, 0⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨2, 3⟩, ⟨3, 4⟩]

/-- The exact five displayed perimeter occurrences are retained in that cyclic order. -/
theorem perimeter_eq : boundary = [⟨4, 0⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨2, 3⟩, ⟨3, 4⟩] := by rfl

/-- Original source-face/corner occurrences for the five subdivided exterior sides. -/
def sources : List (SourceEdge 3) :=
  [⟨0, 2, 0⟩, ⟨0, 0, 1⟩, ⟨1, 0, 1⟩, ⟨1, 1, 2⟩, ⟨2, 1, 2⟩]

/-- Every retained exterior source is a positive occurrence of its actual refined child face. -/
theorem sources_positive : ∀ source ∈ sources, TriangleSourceUniqueness.SourceEdge.Positive source faces := by
  intro source member
  rcases Membership.mem_cons.mp member with same | member
  · subst source
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases Membership.mem_cons.mp member with same | member
    · subst source
      exact List.mem_cons_self
    · rcases Membership.mem_cons.mp member with same | member
      · subst source
        exact List.mem_cons_self
      · rcases Membership.mem_cons.mp member with same | member
        · subst source
          exact List.mem_cons_of_mem _ List.mem_cons_self
        · rcases Membership.mem_cons.mp member with same | member
          · subst source
            exact List.mem_cons_of_mem _ List.mem_cons_self
          · exact (List.not_mem_nil member).elim

/-- Those same source occurrences project to the exact ordered subdivided perimeter. -/
theorem sources_project : sources.map (fun source => source.project faces) = boundary := by rfl

/-- Construct the genuine three-face cut patch using both original opposite seams.

The original triangle constructors and two cached seam occurrences supply
all incidence and closed-boundary fields. Coordinate geometry, root lift
and primitive values are separate; no final patch certificate is an input.
-/
def build : CutPatch faces [0, 1, 2] boundary :=
  let first := CutPatch.triangle faces 0
  let rest := opposite
  let seam := CutPatch.Seam.build first rest apexSeam oppositeSeam
  CutPatch.sew first rest apexSeam oppositeSeam rfl seam

/-- Projecting the retained child faces returns their exact ordered original source occurrences. -/
theorem triangles_eq : build.triangles.map (VertexSewing.OrientedTriangle.map build.vertexLabels) =
    [faces 0, faces 1, faces 2] := build.triangles_eq

/-- Projecting the retained perimeter returns those same five ordered side occurrences. -/
theorem boundary_eq : build.boundary.map (VertexSewing.OrientedEdge.map build.vertexLabels) = boundary :=
  build.boundary_eq

/-- The two actual internal seams project to the cut-to-cut and third-corner-to-first-cut occurrences. -/
theorem seams_eq : build.seams.map (VertexSewing.OrientedEdge.map build.vertexLabels) = [⟨1, 4⟩, ⟨3, 1⟩] := by rfl

/-- The two actual opposite child-source occurrences at each ordered internal seam. -/
def seamSources : Fin 2 → SourceEdge 3 × SourceEdge 3 :=
  Fin.cases (⟨0, 1, 2⟩, ⟨2, 2, 0⟩)
    (Fin.cases (⟨1, 2, 0⟩, ⟨2, 0, 1⟩) Fin.elim0)

/-- Both sides of each seam are positive occurrences of their actual original child faces. -/
theorem seamSources_positive : ∀ index,
    TriangleSourceUniqueness.SourceEdge.Positive (seamSources index).1 faces ∧
      TriangleSourceUniqueness.SourceEdge.Positive (seamSources index).2 faces := by
  refine Fin.cases ?_ (Fin.cases ?_ (fun impossible => nomatch impossible))
  · exact ⟨List.mem_cons_of_mem _ List.mem_cons_self,
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  · exact ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), List.mem_cons_self⟩

/-- The original child-source seam occurrences project to literal opposite indexed edges. -/
theorem seamSources_opposite : ∀ index,
    ((seamSources index).2.project faces) = ((seamSources index).1.project faces).reverse := by
  refine Fin.cases ?_ (Fin.cases ?_ (fun impossible => nomatch impossible)) <;> rfl

/-- Those ordered first seam occurrences are exactly the SAME retained sewn patch's seam labels. -/
theorem seamSources_project :
    [(seamSources 0).1.project faces, (seamSources 1).1.project faces] =
      build.seams.map (VertexSewing.OrientedEdge.map build.vertexLabels) := seams_eq.symm

end Purelib.Topology.Mesh.TriangleCut

end
