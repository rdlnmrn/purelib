module
meta import Purelib.Elab.ConstructiveInjectivity

public import Purelib.Topology.Mesh.EdgeCancellation
import Purelib.Topology.Polygon.Stokes
public import Purelib.Topology.Surface.Sewing.VertexSewing
import Purelib.Topology.Surface.Sewing.SewingProjection
import Purelib.Data.List.Membership
import Purelib.Data.List.Append
import Purelib.Tactic.QuotientFreeOmega

public section

/-!
# Pairing cut occurrences without identifying their vertices

The scan matches reversed *surface labels*, while retaining both cut edges.
Its incidence equation is in the cut bank. Consequently arbitrary primitive
values on different occurrences are preserved, not cancelled as though they
descended to the surface. The residual list has no projected reverse pair.
-/

namespace Purelib.Topology.Surface.Word.ProjectedEdgePairs

open Purelib.Data.List

open Purelib.Topology.Mesh.EdgeCancellation
open _root_.Purelib.Topology.Mesh renaming EdgeCancellation -> EdgeCancellation

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

open Purelib.Topology.Surface.Sewing.SewingProjection

open Purelib.Topology.Surface.Sewing.VertexSewing

open Purelib.Topology.Polygon.Stokes (EdgeReordering OrientedEdge)

variable {source target : Nat}

set_option genInjectivity false in
/-- Two actual cut occurrences above opposite orientations of one surface edge.

The two retained cut edges have reversed projected surface labels. Their distinct cut vertices and any primitive values
assigned to those vertices remain independent. -/
structure ProjectedEdgePair (labels : Fin source → Fin target) where
  /-- First actual cut-edge occurrence of the projected pair. -/ first : Stokes.OrientedEdge source
  /-- Second actual cut-edge occurrence of the projected pair. -/ second : Stokes.OrientedEdge source
  /-- Their projected surface edges have opposite orientation. -/ opposite : OrientedEdge.map labels second =
    (OrientedEdge.map labels first).reverse

constructive_injectivity ProjectedEdgePair

namespace ProjectedEdgePair

/-- Flatten the retained cut pairs into their ordered first and second occurrences.

Each pair contributes its first edge followed by its second edge, and recursion retains the order of the supplied pair
list. -/
@[expose] def occurrences {labels : Fin source → Fin target} :
    List (ProjectedEdgePair labels) → List (Stokes.OrientedEdge source)
  | [] => []
  | pair :: pairs => pair.first :: pair.second ::
    occurrences pairs

/-- Every projected occurrence in the paired list has its reverse represented there.

The certificate for each retained pair supplies the opposite projected orientation. Membership is transported through
the two displayed occurrences without identifying their cut endpoints. -/
theorem reverse_mem {labels : Fin source → Fin target} {edge : Stokes.OrientedEdge target} :
    (pairs : List (ProjectedEdgePair labels)) →
    edge ∈ (occurrences pairs).map (OrientedEdge.map labels) →
    edge.reverse ∈ (occurrences pairs).map (OrientedEdge.map labels)
  | [], member => (List.not_mem_nil member).elim
  | pair :: pairs, member => by
      rcases Membership.mem_cons.mp member with same | member
      · cases same
        exact List.mem_cons_of_mem _ (Membership.mem_cons.mpr (Or.inl pair.opposite.symm))
      · rcases Membership.mem_cons.mp member with same | member
        · cases same
          rw [pair.opposite, OrientedEdge.reverse_reverse]
          exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (reverse_mem pairs member))

end ProjectedEdgePair

set_option genInjectivity false in
/-- Certified finite search for an opposite projected edge occurrence.

A found result retains the actual cut edge, remainder, length decrement, inclusion and exact occurrence reordering;
absence excludes every original candidate. -/
inductive ProjectedReverseSearch (labels : Fin source → Fin target)
    (edge : Stokes.OrientedEdge source) (edges : List (Stokes.OrientedEdge source)) where
  /-- Certify that no original candidate projects to the selected edge's reverse. -/ | absent (missing : ∀ other ∈
    edges, OrientedEdge.map labels other ≠ (OrientedEdge.map labels edge).reverse)
  /-- Retain an opposite original cut occurrence with its exact remainder and reordering certificates. -/ | found (other
    : Stokes.OrientedEdge source) (remaining : List (Stokes.OrientedEdge source))
      (opposite : OrientedEdge.map labels other = (OrientedEdge.map labels edge).reverse)
      (length_eq : remaining.length + 1 = edges.length)
      (subset : ∀ next ∈ remaining, next ∈ edges)
      (ordering : Stokes.EdgeReordering edges (other :: remaining))

constructive_injectivity ProjectedReverseSearch

/-- Scan the original cut occurrences for the first edge with reverse projected orientation.

A successful branch retains the first matching occurrence and the remaining ordered list. An unsuccessful branch
excludes every supplied candidate, and recursive success retains an exact occurrence reordering. -/
@[expose] def findProjectedReverse (labels : Fin source → Fin target) (edge : Stokes.OrientedEdge source) :
    (edges : List (Stokes.OrientedEdge source)) → ProjectedReverseSearch labels edge edges
  | [] => .absent (fun _ member => (List.not_mem_nil member).elim)
  | first :: rest =>
      if opposite : OrientedEdge.map labels first = (OrientedEdge.map labels edge).reverse then
        .found first rest opposite rfl (fun _ member => List.mem_cons_of_mem _ member) (EdgeReordering.refl _)
      else
        match findProjectedReverse labels edge rest with
        | .absent missing => .absent (by
            intro other member
            rcases Membership.mem_cons.mp member with same | member
            · cases same; exact opposite
            · exact missing other member)
        | .found other remaining opposite length_eq subset ordering =>
            .found other (first :: remaining) opposite (by
              simpa only [List.length_cons] using congrArg Nat.succ length_eq)
              (by
                intro next member
                rcases Membership.mem_cons.mp member with same | member
                · exact Membership.mem_cons.mpr (Or.inl same)
                · exact List.mem_cons_of_mem _ (subset next member))
              ((EdgeReordering.cons first ordering).trans (.swap first other remaining))

set_option genInjectivity false in
/-- Complete, cached decomposition of the supplied cut boundary.

The residual boundary and matched pairs retain every original occurrence through an exact reordering. Nondegenerate
projected edges certify that no two residual occurrences have opposite projected orientations. -/
structure ProjectedEdgePairing (labels : Fin source → Fin target)
    (edges : List (Stokes.OrientedEdge source)) where
  /-- Residual original cut occurrences without projected reverse pairs. -/ boundary : List (Stokes.OrientedEdge source)
  /-- Retained pairs of distinct occurrences matched by projected orientation. -/ pairs : List
    (ProjectedEdgePair labels)
  /-- Exact reordering of the original cut list into residual boundary and paired occurrences. -/ incidence :
    Stokes.EdgeReordering edges (boundary ++ ProjectedEdgePairs.ProjectedEdgePair.occurrences pairs)
  /-- No two retained residual occurrences have reversed projected edges. -/ noReverse : ∀ first ∈ boundary, ∀ second ∈
    boundary,
    OrientedEdge.map labels second ≠ (OrientedEdge.map labels first).reverse

constructive_injectivity ProjectedEdgePairing

namespace ProjectedEdgePairing

variable {labels : Fin source → Fin target} {edges : List (Stokes.OrientedEdge source)}

/-- Every retained residual boundary edge is an original cut occurrence.

The incidence reordering transports membership from the left summand of the retained boundary-and-pairs list back to the
supplied cut list. -/
theorem boundary_subset (pairing : ProjectedEdgePairing labels edges)
    {edge : Stokes.OrientedEdge source} (member : edge ∈ pairing.boundary) : edge ∈ edges :=
  (EdgeReordering.mem_iff pairing.incidence edge).mpr (Membership.mem_append.mpr (Or.inl member))

/-- Pair original cut occurrences using their projected reversals within a certified length bound.

Nondegenerate projected edges ensure the residual boundary contains no reverse pair; the original cut-bank incidence is
retained throughout. -/
@[expose] def buildFuel (labels : Fin source → Fin target) : (fuel : Nat) →
    (edges : List (Stokes.OrientedEdge source)) → edges.length ≤ fuel →
    (∀ edge ∈ edges, labels edge.start ≠ labels edge.finish) → ProjectedEdgePairing labels edges
  | 0, [], _, _ => ⟨[], [], .nil, fun _ member => (List.not_mem_nil member).elim⟩
  | 0, _ :: _, bound, _ => (Nat.not_succ_le_zero _ bound).elim
  | _ + 1, [], _, _ => ⟨[], [], .nil, fun _ member => (List.not_mem_nil member).elim⟩
  | fuel + 1, edge :: rest, bound, nonloop =>
      match findProjectedReverse labels edge rest with
      | .absent missing =>
          let tail := buildFuel labels fuel rest
            (Nat.le_of_succ_le_succ bound)
            (fun next member => nonloop next (List.mem_cons_of_mem _ member))
          { boundary := edge :: tail.boundary
            pairs := tail.pairs
            incidence := .cons edge tail.incidence
            noReverse := by
              intro first firstMember second secondMember equal
              rcases Membership.mem_cons.mp firstMember with firstSame | firstMember
              · cases firstSame
                rcases Membership.mem_cons.mp secondMember with secondSame | secondMember
                · cases secondSame
                  exact nonloop edge List.mem_cons_self (congrArg OrientedEdge.start equal)
                · exact missing second (tail.boundary_subset secondMember) equal
              · rcases Membership.mem_cons.mp secondMember with secondSame | secondMember
                · cases secondSame
                  apply missing first (tail.boundary_subset firstMember)
                  exact ((congrArg OrientedEdge.reverse equal).trans (OrientedEdge.reverse_reverse _)).symm
                · exact tail.noReverse first firstMember second secondMember equal }
      | .found other remaining opposite length_eq subset ordering =>
          have remainingBound : remaining.length ≤ fuel := by
            have smaller := Nat.le_of_succ_le_succ bound
            omega
          let tail := buildFuel labels fuel
            remaining remainingBound
            (fun next member => nonloop next (List.mem_cons_of_mem _ (subset next member)))
          { boundary := tail.boundary
            pairs := ⟨edge, other, opposite⟩ :: tail.pairs
            incidence := (EdgeReordering.cons edge ordering).trans
              ((EdgeReordering.cons edge (.cons other tail.incidence)).trans (by
                simpa only [List.cons_append, List.nil_append, ProjectedEdgePairs.ProjectedEdgePair.occurrences,
                  Append.append_assoc] using
                  EdgeReordering.append_swap [edge, other] tail.boundary
                    (ProjectedEdgePairs.ProjectedEdgePair.occurrences tail.pairs)))
            noReverse := tail.noReverse }

/-- The scan is bounded by the number of displayed occurrences.

The displayed list length is the initial fuel. The supplied nondegeneracy evidence is retained while each recursive step
consumes at least one original occurrence. -/
@[expose] def build (labels : Fin source → Fin target) (edges : List (Stokes.OrientedEdge source))
    (nonloop : ∀ edge ∈ edges, labels edge.start ≠ labels edge.finish) : ProjectedEdgePairing labels
      edges :=
  buildFuel labels edges.length edges (Nat.le_refl _) nonloop

end ProjectedEdgePairing

end Purelib.Topology.Surface.Word.ProjectedEdgePairs
