module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Append
import Purelib.Data.List.Membership
public import Purelib.Topology.Chain.PathBoundary

public import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Mesh.EdgeCancellation
import Purelib.Tactic.QuotientFreeOmega

public section

/-!
# Ordered sewing of finite polygon boundaries

Selecting an edge retains the two cyclic pieces on either side of that
occurrence.  Sewing two oppositely oriented selected edges joins the
remaining pieces in their original cyclic order.  Other matching edges are
not identified: they remain displayed cuts.  This is distinct from the
unordered cancellation used to compute a mesh's external boundary.
-/

namespace Purelib.Topology.Surface.Sewing.PolygonSewing.PathEndpoints

open Purelib.Topology.Chain

open Purelib.Topology.Mesh.EdgeCancellation
open _root_.Purelib.Topology.Mesh renaming EdgeCancellation -> EdgeCancellation

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

open Purelib.Data.List

open Purelib.Topology.Chain.PathBoundary (PathEndpoints)
variable {Vertex Edge : Type} {edgeStart edgeFinish : Edge → Vertex}

/-- Concatenate certified original paths sharing their middle vertex. -/
theorem append {left right : List Edge} {start middle finish : Vertex}
    (first : PathBoundary.PathEndpoints edgeStart edgeFinish left start middle)
    (second : PathBoundary.PathEndpoints edgeStart edgeFinish right middle finish) :
    PathBoundary.PathEndpoints edgeStart edgeFinish (left ++ right) start finish := by
  induction first with
  | nil => exact second
  | cons tail ih => exact .cons (ih second)

/-- Split a certified concatenated path at its original list boundary and retain the intermediate vertex. -/
theorem split_append (left right : List Edge) {start finish : Vertex}
    (path : PathBoundary.PathEndpoints edgeStart edgeFinish (left ++ right) start finish) :
    ∃ middle, PathBoundary.PathEndpoints edgeStart edgeFinish left start middle ∧
      PathBoundary.PathEndpoints edgeStart edgeFinish right middle finish := by
  induction left generalizing start with
  | nil => exact ⟨start, .nil _, path⟩
  | cons edge tail ih =>
      cases path with
      | cons rest =>
          rcases ih rest with ⟨middle, first, second⟩
          exact ⟨middle, .cons first, second⟩

end Purelib.Topology.Surface.Sewing.PolygonSewing.PathEndpoints

namespace Purelib.Topology.Surface.Sewing.PolygonSewing.PolygonStokes

open Purelib.Topology.Chain

open Purelib.Topology.Mesh.EdgeCancellation
open _root_.Purelib.Topology.Mesh renaming EdgeCancellation -> EdgeCancellation

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

open Purelib.Data.List

open Purelib.Topology.Polygon.Stokes (EdgeReordering OrientedEdge)

open Purelib.Topology.Chain.PathBoundary (PathEndpoints)

namespace EdgeReordering

/-- Reverse a finite certificate of edge-occurrence reordering. -/
theorem symm {count : Nat} {left right : List (Stokes.OrientedEdge count)} (ordering : Stokes.EdgeReordering left right)
  :
    Stokes.EdgeReordering right left := by
  induction ordering with
  | nil => exact .nil
  | cons edge tail ih => exact .cons edge ih
  | swap first second remaining => exact .swap second first remaining
  | trans first second ihFirst ihSecond => exact .trans ihSecond ihFirst

end EdgeReordering

set_option genInjectivity false in
/-- A specified occurrence of an edge in an ordered boundary.

The retained prefix and suffix identify the exact occurrence even when
endpoints repeat. Its prefix length is the executable sewing position. -/
structure BoundarySplit {count : Nat} (boundary : List (Stokes.OrientedEdge count)) where
  /-- Ordered original prefix before the selected occurrence. -/ before : List (Stokes.OrientedEdge count)
  /-- Exact original edge occurrence selected for sewing. -/ edge : Stokes.OrientedEdge count
  /-- Ordered original suffix after the selected occurrence. -/ after : List (Stokes.OrientedEdge count)
  /-- The original boundary is exactly prefix, selected occurrence and suffix. -/ equation : boundary = before ++ edge
    :: after

constructive_injectivity BoundarySplit

namespace BoundarySplit

variable {count : Nat} {boundary : List (Stokes.OrientedEdge count)}

/-- Read the original cyclic tail after removing the selected edge occurrence. -/
@[expose] def rest (split : BoundarySplit boundary) : List (Stokes.OrientedEdge count) := split.after ++
  split.before

/-- The selected edge occurrence belongs to the original boundary list.

The retained split equation locates the selected edge after its stored prefix.
Its head membership is transported through that original concatenation. -/
theorem edge_mem (split : BoundarySplit boundary) : split.edge ∈ boundary := by
  cases split with
  | mk before edge after equation =>
      cases equation
      exact Membership.mem_append.mpr (Or.inr List.mem_cons_self)

section
open Purelib.Topology.Surface.Sewing.PolygonSewing.PolygonStokes.BoundarySplit
/-- Removing the selected occurrence shortens the original boundary by exactly one edge.

The cyclic tail retains the original suffix followed by its prefix. Their
lengths account for every boundary occurrence except the selected seam edge. -/
theorem rest_length (split : BoundarySplit boundary) : split.rest.length + 1 = boundary.length := by
  cases split with
  | mk before edge after equation =>
      cases equation
      simp only [rest, Append.length_append, List.length_cons]
      omega

/-- Rotate the selected original occurrence to the front of its retained cyclic tail.

The occurrence-reordering certificate moves the stored prefix after the suffix.
No repeated occurrence is removed or identified during this rotation. -/
theorem ordering (split : BoundarySplit boundary) : Stokes.EdgeReordering boundary (split.edge ::
  split.rest) := by
  cases split with
  | mk before edge after equation =>
      cases equation
      simpa only [Append.append_nil, List.cons_append, rest] using
        EdgeReordering.append_swap before (edge :: after) []

end

/-- The remaining cyclic tail runs from the selected edge's finish back to its start. -/
theorem rest_path (split : BoundarySplit boundary) {anchor : Fin count}
    (closed : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish boundary anchor anchor) :
    PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish split.rest split.edge.finish split.edge.start :=
      by
  rw [split.equation] at closed
  rcases PolygonSewing.PathEndpoints.split_append split.before (split.edge :: split.after) closed with ⟨middle, first,
    last⟩
  cases last with
  | cons remaining => exact PolygonSewing.PathEndpoints.append remaining first

set_option genInjectivity false in
/-- A selected occurrence retains its exact requested position.

The selected boundary split stores the original prefix, edge and suffix.
Its prefix length equals the supplied natural coordinate. -/
structure Positioned (boundary : List (Stokes.OrientedEdge count)) (position : Nat) where
  /-- Retained original boundary occurrence selected at the requested position. -/ split : BoundarySplit
    boundary
  /-- The retained prefix length is exactly the requested original position. -/ position_eq : split.before.length =
    position

constructive_injectivity Positioned

/-- The requested occurrence lies outside this displayed finite boundary. -/
structure InvalidPosition (boundary : List (Stokes.OrientedEdge count)) (position : Nat) : Type where
  /-- The requested position is outside the original finite boundary length. -/ outOfBounds : boundary.length ≤ position

open Purelib.Topology.Surface.Sewing.PolygonSewing.PolygonStokes.BoundarySplit in
/-- Scan for the exact occurrence or prove that its position is out of bounds.

Each successor consumes the original head and coordinate together. Success
retains that occurrence and its prefix, while failure retains the length bound. -/
@[expose] def checkAt : (boundary : List (Stokes.OrientedEdge count)) → (position : Nat) →
    Except (InvalidPosition boundary position) (Positioned boundary position)
  | [], _ => .error ⟨Nat.zero_le _⟩
  | edge :: rest, 0 => .ok ⟨⟨[], edge, rest, rfl⟩, rfl⟩
  | edge :: rest, position + 1 =>
      match checkAt rest position with
      | .error invalid => .error ⟨Nat.succ_le_succ invalid.outOfBounds⟩
      | .ok found => .ok
          ⟨⟨edge :: found.split.before, found.split.edge, found.split.after,
            congrArg (List.cons edge) found.split.equation⟩,
           congrArg Nat.succ found.position_eq⟩

end BoundarySplit

/-- The exact ordered seam operation retains both unglued cyclic tails.

Both selected boundaries retain their ordered prefixes and suffixes. Opposite
seam occurrences are moved to the end after the two cyclic tails are joined. -/
theorem sew_ordering {count : Nat} {left right : List (Stokes.OrientedEdge count)}
    (first : BoundarySplit left) (second : BoundarySplit right) (opposite : second.edge =
      first.edge.reverse) :
    Stokes.EdgeReordering (left ++ right) ((first.rest ++ second.rest) ++ [first.edge, first.edge.reverse]) := by
  have rotated := (EdgeReordering.append_right first.ordering right).trans
    (EdgeReordering.append_left (first.edge :: first.rest) second.ordering)
  rw [opposite] at rotated
  have gathered : Stokes.EdgeReordering ((first.edge :: first.rest) ++ first.edge.reverse :: second.rest)
      (first.edge :: first.edge.reverse :: (first.rest ++ second.rest)) :=
    .cons first.edge (PolygonStokes.EdgeReordering.symm
      (EdgeReordering.move_head first.edge.reverse first.rest second.rest))
  have moved : Stokes.EdgeReordering (first.edge :: first.edge.reverse :: (first.rest ++ second.rest))
      ((first.rest ++ second.rest) ++ [first.edge, first.edge.reverse]) := by
    simpa only [Append.append_nil, List.cons_append, List.nil_append] using
      EdgeReordering.append_swap [first.edge, first.edge.reverse] (first.rest ++ second.rest) []
  exact rotated.trans (gathered.trans moved)

/-- Sewing two opposite selected occurrences produces a closed path from their original cyclic tails. -/
theorem sew_closed {count : Nat} {left right : List (Stokes.OrientedEdge count)}
    (first : BoundarySplit left) (second : BoundarySplit right) (opposite : second.edge =
      first.edge.reverse)
    {leftAnchor rightAnchor : Fin count}
    (leftClosed : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish left leftAnchor leftAnchor)
    (rightClosed : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish right rightAnchor rightAnchor) :
    PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish (first.rest ++ second.rest) first.edge.finish
      first.edge.finish := by
  have secondPath := second.rest_path rightClosed
  rw [opposite] at secondPath
  exact PolygonSewing.PathEndpoints.append (first.rest_path leftClosed) secondPath

end Purelib.Topology.Surface.Sewing.PolygonSewing.PolygonStokes
