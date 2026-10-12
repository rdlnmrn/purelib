module
meta import Purelib.Elab.ConstructiveInjectivity

public import Purelib.Data.List.Membership
import Purelib.Topology.Polygon.Stokes
public import Purelib.Topology.Surface.Sewing.PolygonSewing
import Purelib.Topology.Surface.Sewing.SewingTree

public section

/-!
# Proof-producing seam search

The first reversed edge occurrence is retained with its cyclic prefix and
suffix.  Failure proves absence, and searching both boundaries proves that
two patches have no available seam.  This search chooses only one seam;
other matching occurrences remain cuts in the sewn patch.
-/

namespace Purelib.Topology.Surface.Sewing.SewingSearch

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

open Purelib.Topology.Surface.Sewing.PolygonSewing

open Purelib.Data.List

open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Topology.Surface.Sewing.PolygonSewing.PolygonStokes (BoundarySplit)

set_option genInjectivity false in
/-- The exact first reversed boundary occurrence, or proof that the original boundary contains none.

Absence excludes the original edge reverse from the entire retained list. A found
case stores its exact cyclic prefix and suffix, including repeated occurrences. -/
inductive ReverseSplitSearch {count : Nat} (edge : Stokes.OrientedEdge count) (boundary : List (Stokes.OrientedEdge
  count)) where
  /-- Certify absence of the original edge's reverse from the supplied boundary. -/ | absent (missing : edge.reverse ∉
    boundary)
  /-- Retain the selected original boundary occurrence and its exact reversal equation. -/ | found (split :
    PolygonStokes.BoundarySplit boundary) (equal : split.edge = edge.reverse)

constructive_injectivity ReverseSplitSearch

/-- Reversed endpoint equalities identify the original second edge with the first edge's reverse. -/
theorem reverseEdge_eq {count : Nat} {first second : Stokes.OrientedEdge count}
    (equal : second.start = first.finish ∧ second.finish = first.start) : second = first.reverse := by
  cases first
  cases second
  cases equal.1
  cases equal.2
  rfl

/-- Scan the original boundary for a reversed edge while retaining its exact prefix and suffix. -/
@[expose] def reverseSplit {count : Nat} (edge : Stokes.OrientedEdge count) :
    (boundary : List (Stokes.OrientedEdge count)) → SewingSearch.ReverseSplitSearch edge boundary
  | [] => .absent (fun member => List.not_mem_nil member)
  | head :: tail =>
      if equal : head.start = edge.finish ∧ head.finish = edge.start then
        .found ⟨[], head, tail, rfl⟩ (SewingSearch.reverseEdge_eq equal)
      else
        match Purelib.Topology.Surface.Sewing.SewingSearch.reverseSplit edge tail with
        | .absent missing => .absent (by
            intro member
            rcases Membership.mem_cons.mp member with same | remaining
            · exact equal ⟨congrArg OrientedEdge.start same.symm, congrArg OrientedEdge.finish same.symm⟩
            · exact missing remaining)
        | .found split same =>
            .found ⟨head :: split.before, split.edge, split.after, congrArg (List.cons head) split.equation⟩ same

set_option genInjectivity false in
/-- Two original opposite selected boundary occurrences, or proof that no such seam exists.

A successful result retains both actual cyclic occurrences and their reversal
equation. Absence excludes a seam between the two original boundary lists. -/
inductive SeamSearch {count : Nat} (left right : List (Stokes.OrientedEdge count)) where
  /-- Certify that no original left-boundary edge has its reverse in the right boundary. -/ | absent (missing : ∀ edge ∈
    left, edge.reverse ∉ right)
  /-- Retain both selected original boundary occurrences and their opposite-orientation certificate. -/ | found (first :
    PolygonStokes.BoundarySplit left) (second : PolygonStokes.BoundarySplit right) (opposite : second.edge =
    first.edge.reverse)

constructive_injectivity SeamSearch

namespace SeamSearch

/-- Search both original boundary lists for one exact opposite seam occurrence pair. -/
@[expose] def find {count : Nat} : (left right : List (Stokes.OrientedEdge count)) → SewingSearch.SeamSearch left right
  | [], _ => .absent (fun _ member => (List.not_mem_nil member).elim)
  | edge :: tail, right =>
      match SewingSearch.reverseSplit edge right with
      | .found second opposite => .found ⟨[], edge, tail, rfl⟩ second opposite
      | .absent missing =>
          match Purelib.Topology.Surface.Sewing.SewingSearch.SeamSearch.find tail right with
          | .found first second opposite =>
              .found ⟨edge :: first.before, first.edge, first.after, congrArg (List.cons edge) first.equation⟩ second
                opposite
          | .absent remaining => .absent (by
              intro other member
              rcases Membership.mem_cons.mp member with same | tailMember
              · cases same; exact missing
              · exact remaining other tailMember)

end SeamSearch

end Purelib.Topology.Surface.Sewing.SewingSearch
