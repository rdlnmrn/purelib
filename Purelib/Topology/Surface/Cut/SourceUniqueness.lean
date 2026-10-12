module
import Purelib.Data.List.Nodup

import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
public import Purelib.Topology.Surface.Sewing.SewnPrimitivePaths
import Purelib.Topology.Surface.Sewing.SewnPrimitiveBoundary
import Purelib.Tactic.QuotientFreeOmega

public section

/-! Unique source faces identify actual cut occurrences, including their
orientation. No equality of values at different cut vertices is assumed. -/
namespace Purelib.Topology.Surface.Cut.SourceUniqueness

open Purelib
open Purelib.Data.Rat

open Purelib.Topology.Polygon.Stokes (OrientedEdge OrientedTriangle)
open Purelib.Topology.Surface.Cut.Patch (CutPatch)
open Purelib.Topology.Surface.Sewing.SewnPrimitivePaths.SewnPrimitiveFaces (OrientedOwner PathSources)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces (corner)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts (SourceEdge)

variable {vertexCount faceCount : Nat} {faces : Fin faceCount → Topology.Polygon.Stokes.OrientedTriangle vertexCount}
  {indices : List (Fin faceCount)} {boundary : List (Topology.Polygon.Stokes.OrientedEdge vertexCount)}
  {patch : Topology.Surface.Cut.Patch.CutPatch faces indices boundary}

namespace OrientedOwner

/-- The retained source index reads the original face-index list at its certified position. -/
private theorem source_index (route : Topology.Surface.Sewing.SewnPrimitivePaths.SewnPrimitiveFaces.OrientedOwner patch)
  :
    route.sourceEdge.source = indices[route.owner.position.val]'(by
      rw [← patch.triangles_length]; exact route.owner.position.isLt) := by
  rcases route with ⟨edge, owner, reversed⟩
  cases reversed <;> rfl

/-- Recover the cut edge from the exact local corners selected by its retained source edge. -/
private theorem cutEdge_corners (route : Topology.Surface.Sewing.SewnPrimitivePaths.SewnPrimitiveFaces.OrientedOwner
  patch) :
    route.cutEdge = ⟨corner patch.triangles[route.owner.position.val] route.sourceEdge.first,
      Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces.corner patch.triangles[route.owner.position.val]
        route.sourceEdge.last⟩ := by
  rcases route with ⟨edge, owner, reversed⟩
  cases reversed <;> simp only [Topology.Surface.Sewing.SewnPrimitivePaths.SewnPrimitiveFaces.OrientedOwner.cutEdge,
    Topology.Surface.Sewing.SewnPrimitivePaths.SewnPrimitiveFaces.OrientedOwner.sourceEdge, if_neg Bool.false_ne_true,
    if_pos (rfl : true = true),
    Topology.Surface.Sewing.SewnPrimitiveContacts.TriangleEdgeOwner.sourceEdge, owner.start_eq, owner.finish_eq,
      -eq_self, -iff_self]
  all_goals rfl

open Purelib in
/-- Unique original face indices make equal source edges identify the original cut edges. -/
theorem cutEdge_eq_of_source_eq (unique : indices.Nodup) {left right :
  Topology.Surface.Sewing.SewnPrimitivePaths.SewnPrimitiveFaces.OrientedOwner patch}
    (equal : left.sourceEdge = right.sourceEdge) : left.cutEdge = right.cutEdge := by
  have source := congrArg Topology.Surface.Sewing.SewnPrimitiveContacts.SourceEdge.source equal
  rw [Topology.Surface.Cut.SourceUniqueness.OrientedOwner.source_index,
    Topology.Surface.Cut.SourceUniqueness.OrientedOwner.source_index] at source
  have position : left.owner.position = right.owner.position := Fin.ext
    (Data.List.Nodup.getElem_index_injective unique _ _ source)
  rw [Topology.Surface.Cut.SourceUniqueness.OrientedOwner.cutEdge_corners,
    Topology.Surface.Cut.SourceUniqueness.OrientedOwner.cutEdge_corners]
  simp only [position, equal, -eq_self, -iff_self]
  rfl

end OrientedOwner

namespace PathSources

open Purelib
/-- Equal ordered source-edge readings identify the original cut-edge lists under unique face indices. -/
private theorem edges_of_sources (unique : indices.Nodup) :
    ∀ (left right : List (Topology.Surface.Sewing.SewnPrimitivePaths.SewnPrimitiveFaces.OrientedOwner patch)),
    left.map Topology.Surface.Sewing.SewnPrimitivePaths.SewnPrimitiveFaces.OrientedOwner.sourceEdge = right.map
      Topology.Surface.Sewing.SewnPrimitivePaths.SewnPrimitiveFaces.OrientedOwner.sourceEdge →
    left.map Topology.Surface.Sewing.SewnPrimitivePaths.SewnPrimitiveFaces.OrientedOwner.cutEdge = right.map
      Topology.Surface.Sewing.SewnPrimitivePaths.SewnPrimitiveFaces.OrientedOwner.cutEdge
  | [], [], _ => rfl
  | [], _ :: _, equal => by cases equal
  | _ :: _, [], equal => by cases equal
  | left :: tail, right :: rest, equal => by
      have parts := List.cons.inj equal
      exact congrArg₂ List.cons (Topology.Surface.Cut.SourceUniqueness.OrientedOwner.cutEdge_eq_of_source_eq unique
        parts.1)
        (Purelib.Topology.Surface.Cut.SourceUniqueness.PathSources.edges_of_sources unique tail rest parts.2)

/-- Equal retained source lists recover the exact original path-edge lists. -/
theorem edges_eq_of_sources_eq (unique : indices.Nodup)
    {leftEdges rightEdges : List (Topology.Polygon.Stokes.OrientedEdge patch.count)}
    (left : Topology.Surface.Sewing.SewnPrimitivePaths.SewnPrimitiveFaces.PathSources patch leftEdges) (right :
      Topology.Surface.Sewing.SewnPrimitivePaths.SewnPrimitiveFaces.PathSources patch rightEdges)
    (equal : left.sources = right.sources) : leftEdges = rightEdges := by
  rw [left.sources_eq, right.sources_eq] at equal
  exact left.edges_eq.symm.trans ((Topology.Surface.Cut.SourceUniqueness.PathSources.edges_of_sources unique
    left.entries right.entries equal).trans right.edges_eq)

end PathSources
end Purelib.Topology.Surface.Cut.SourceUniqueness
