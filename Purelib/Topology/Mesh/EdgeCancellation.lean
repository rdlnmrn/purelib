module
public import Purelib.Data.List.Append
public import Purelib.Data.List.Membership

public import Purelib.Topology.Polygon.Stokes
import Purelib.Tactic.QuotientFreeOmega
meta import Mathlib.Tactic.Linter.Lint
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Proof-producing finite internal-edge cancellation

A bounded scan pairs reversed edge occurrences and returns the remaining
boundary together with an exact incidence reordering.  It works for arbitrary
finite face data; there is no successful-search premise.  The remaining
boundary contains no pair of reversed occurrences.
-/

namespace Purelib.Topology.Mesh

open Purelib.Data.List

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes (OrientedEdge)

namespace EdgeCancellation.EdgeReordering

variable {vertexCount : Nat}

/-- Every edge occurrence list has its identity reordering. -/
public theorem refl : (edges : List (Stokes.OrientedEdge vertexCount)) -> Stokes.EdgeReordering edges edges
  | [] => .nil
  | edge :: rest => .cons edge (Purelib.Topology.Mesh.EdgeCancellation.EdgeReordering.refl rest)

/-- Extend an occurrence reordering by an unchanged suffix. -/
public theorem append_right {left right : List (Stokes.OrientedEdge vertexCount)}
    (ordering : Stokes.EdgeReordering left right) (suffix : List (Stokes.OrientedEdge vertexCount)) :
    Stokes.EdgeReordering (left ++ suffix) (right ++ suffix) := by
  induction ordering with
  | nil => exact EdgeReordering.refl suffix
  | cons edge remaining inductionHypothesis => exact .cons edge inductionHypothesis
  | swap first second remaining => exact .swap first second (remaining ++ suffix)
  | trans first second firstHypothesis secondHypothesis => exact .trans firstHypothesis secondHypothesis

/-- Extend an occurrence reordering by an unchanged prefix. -/
public theorem append_left (leading : List (Stokes.OrientedEdge vertexCount))
    {left right : List (Stokes.OrientedEdge vertexCount)} (ordering : Stokes.EdgeReordering left right) :
    Stokes.EdgeReordering (leading ++ left) (leading ++ right) := by
  induction leading with
  | nil => exact ordering
  | cons edge rest inductionHypothesis => exact .cons edge inductionHypothesis

/-- Move the leading edge past a finite prefix using adjacent swaps. -/
public theorem move_head (edge : Stokes.OrientedEdge vertexCount) (leading suffix : List (Stokes.OrientedEdge
  vertexCount)) :
    Stokes.EdgeReordering (edge :: (leading ++ suffix)) (leading ++ edge :: suffix) := by
  induction leading with
  | nil => exact EdgeReordering.refl _
  | cons first rest inductionHypothesis =>
      exact .trans (.swap edge first (rest ++ suffix)) (.cons first inductionHypothesis)

/-- Exchange two consecutive edge blocks while retaining their common suffix.

Adjacent swaps move each occurrence past the other block. The resulting certificate retains the ordered entries in each
block and the unchanged suffix. -/
public theorem append_swap (left right suffix : List (Stokes.OrientedEdge vertexCount)) :
    Stokes.EdgeReordering (left ++ right ++ suffix) (right ++ left ++ suffix) := by
  induction left with
  | nil => simpa only [List.nil_append, Append.append_nil] using EdgeReordering.refl (right ++ suffix)
  | cons first rest inductionHypothesis =>
      have moved := EdgeReordering.move_head first right (rest ++ suffix)
      exact .trans (.cons first inductionHypothesis) (by
        simpa only [Append.append_assoc, List.cons_append] using moved)

end EdgeCancellation.EdgeReordering

namespace EdgeCancellation

/-- Two oriented edges with equal start and finish indices are equal. -/
public theorem edge_eq_of_endpoints {count : Nat} {left right : Stokes.OrientedEdge count}
    (start : left.start = right.start) (finish : left.finish = right.finish) : left = right := by
  cases left
  cases right
  cases start
  cases finish
  rfl

end EdgeCancellation

namespace EdgeCancellation

set_option genInjectivity false in
/-- A reverse lookup either proves absence or returns the exact residual list and a reordering that moves the found
occurrence to the front.

The successful branch retains the original count, residual membership and exact incidence reordering; the absent branch
certifies that the reversed occurrence is missing. -/
public inductive ReverseSearch {count : Nat} (edge : Stokes.OrientedEdge count)
    (edges : List (Stokes.OrientedEdge count)) where
  /-- Certify that the requested reversed edge does not occur in the supplied list. -/ | absent (missing : edge.reverse
    ∉ edges)
  /-- Retain the residual list and a reordering that moves the found reversed occurrence first. -/ | found (remaining :
    List (Stokes.OrientedEdge count))
      (length_eq : remaining.length + 1 = edges.length)
      (subset : forall other, other ∈ remaining -> other ∈ edges)
      (ordering : Stokes.EdgeReordering edges (edge.reverse :: remaining))

constructive_injectivity ReverseSearch

end EdgeCancellation

namespace EdgeCancellation.ReverseSearch.found

end EdgeCancellation.ReverseSearch.found

namespace EdgeCancellation.ReverseSearch.found

end EdgeCancellation.ReverseSearch.found

namespace EdgeCancellation

/-- Search a finite edge list for an occurrence opposite to the requested edge.

Success retains the residual list, its size and membership guarantees, and an exact reordering; absence proves the
reversed edge is missing. -/
@[expose] public def findReverse {count : Nat} (edge : Stokes.OrientedEdge count) :
    (edges : List (Stokes.OrientedEdge count)) -> EdgeCancellation.ReverseSearch edge edges
  | [] => .absent (fun member => List.not_mem_nil member)
  | first :: rest =>
      if equal : first.start = edge.finish ∧ first.finish = edge.start then
        .found rest rfl (fun _ member => List.mem_cons_of_mem _ member)
          (by
            have equalEdge : first = edge.reverse := EdgeCancellation.edge_eq_of_endpoints equal.1 equal.2
            rw [equalEdge]
            exact EdgeReordering.refl _)
      else
        match Purelib.Topology.Mesh.EdgeCancellation.findReverse edge rest with
        | .absent missing => .absent (by
            intro member
            rcases Membership.mem_cons.mp member with same | inRest
            · exact equal ⟨congrArg OrientedEdge.start same.symm, congrArg OrientedEdge.finish same.symm⟩
            · exact missing inRest)
        | .found remaining length_eq subset ordering =>
            .found (first :: remaining) (by simpa only [List.length_cons] using congrArg Nat.succ length_eq)
              (by
                intro other member
                rcases Membership.mem_cons.mp member with same | inRemaining
                · exact Membership.mem_cons.mpr (Or.inl same)
                · exact List.mem_cons_of_mem _ (subset other inRemaining))
              (.trans (.cons first ordering) (.swap first edge.reverse remaining))

end EdgeCancellation

set_option genInjectivity false in
/-- Cached boundary and internal edges with an exact incidence certificate. Generated schedules may fill this same
interface with any checked reordering.

The boundary retains original occurrences and has no reversed pair at distinct positions. The incidence witness relates
it and the canceled pairs to the original ordered edge list. -/
public structure EdgeCancellation {count : Nat} (edges : List (Stokes.OrientedEdge count)) where
  /-- Unpaired edge occurrences retained as the boundary. -/ boundary : List (Stokes.OrientedEdge count)
  /-- One oriented representative of each canceled pair. -/ internalEdges : List (Stokes.OrientedEdge count)
  /-- Exact reordering into boundary occurrences followed by opposite internal pairs. -/ incidence :
    Stokes.EdgeReordering edges (boundary ++ Stokes.pairedEdgeOccurrences internalEdges)
  /-- Every retained boundary edge occurs in the original input list. -/ boundary_subset : forall edge, edge ∈ boundary
    -> edge ∈ edges
  /-- Distinct positions in the retained boundary do not carry reversed edges. -/ noReversePair : boundary.Pairwise (fun
    left right => left ≠ right.reverse)

constructive_injectivity EdgeCancellation

namespace EdgeCancellation.mk

end EdgeCancellation.mk

namespace EdgeCancellation.mk

end EdgeCancellation.mk

namespace EdgeCancellation

/-- Cancel opposite edge occurrences with a supplied length bound on the fuel.

The recursive result retains boundary and internal edges, their exact incidence reordering, and the absence of reversed
pairs in the boundary. -/
@[expose] public def cancelFuel {count : Nat} : (fuel : Nat) ->
    (edges : List (Stokes.OrientedEdge count)) -> edges.length <= fuel -> EdgeCancellation edges
  | 0, [], _ => ⟨[], [], .nil, fun _ member => (List.not_mem_nil member).elim, .nil⟩
  | 0, _ :: _, bound => (Nat.not_succ_le_zero _ bound).elim
  | _ + 1, [], _ => ⟨[], [], .nil, fun _ member => (List.not_mem_nil member).elim, .nil⟩
  | fuel + 1, edge :: rest, bound =>
      match EdgeCancellation.findReverse edge rest with
      | .absent missing =>
          let tail := Purelib.Topology.Mesh.EdgeCancellation.cancelFuel fuel rest (Nat.le_of_succ_le_succ bound)
          { boundary := edge :: tail.boundary
            internalEdges := tail.internalEdges
            incidence := .cons edge tail.incidence
            boundary_subset := by
              intro other member
              rcases Membership.mem_cons.mp member with same | inTail
              · exact Membership.mem_cons.mpr (Or.inl same)
              · exact List.mem_cons_of_mem _ (tail.boundary_subset other inTail)
            noReversePair := .cons (by
              intro other member same
              apply missing
              have reversed : edge.reverse = other := by rw [same, OrientedEdge.reverse_reverse]
              rw [reversed]
              exact tail.boundary_subset other member) tail.noReversePair }
      | .found remaining length_eq subset ordering =>
          have remainingBound : remaining.length <= fuel := by
            have smaller := Nat.le_of_succ_le_succ bound
            omega
          let tail := Purelib.Topology.Mesh.EdgeCancellation.cancelFuel fuel remaining remainingBound
          { boundary := tail.boundary
            internalEdges := edge :: tail.internalEdges
            incidence := .trans (.cons edge ordering)
              (.trans (.cons edge (.cons edge.reverse tail.incidence)) (by
                simpa only [List.cons_append, List.nil_append, Stokes.pairedEdgeOccurrences, Append.append_assoc] using
                  EdgeReordering.append_swap [edge, edge.reverse] tail.boundary
                    (Stokes.pairedEdgeOccurrences tail.internalEdges)))
            boundary_subset := fun other member =>
              List.mem_cons_of_mem _ (subset other (tail.boundary_subset other member))
            noReversePair := tail.noReversePair }

end EdgeCancellation

namespace EdgeCancellation

/-- Cancel all possible reversed pairs with fuel bounded by the input length. -/
@[expose] public def cancelEdges {count : Nat} (edges : List (Stokes.OrientedEdge count)) :
  EdgeCancellation edges :=
  EdgeCancellation.cancelFuel edges.length edges (Nat.le_refl _)

end EdgeCancellation

namespace EdgeCancellation

/-- Every finite indexed triangle bank has automatically computed incidence data, including literal shared-vertex
internal-edge cancellation. -/
@[expose] public def triangulateFaces {vertexCount faceCount : Nat}
    (faces : Fin faceCount -> Stokes.OrientedTriangle vertexCount) : Stokes.Triangulation vertexCount faceCount :=
  let cancellation := EdgeCancellation.cancelEdges (Stokes.triangleEdgeOccurrences faces)
  { faces := faces
    boundary := cancellation.boundary
    internalEdges := cancellation.internalEdges
    incidence := cancellation.incidence }

end EdgeCancellation

namespace EdgeCancellation

/-- Automatic incidence cancellation preserves the supplied face table exactly. -/
public theorem triangulateFaces_faces {vertexCount faceCount : Nat}
    (faces : Fin faceCount -> Stokes.OrientedTriangle vertexCount) (index : Fin faceCount) :
    (EdgeCancellation.triangulateFaces faces).faces index = faces index := rfl

end EdgeCancellation

namespace EdgeCancellation

/-- The boundary produced by automatic triangulation contains no reversed edge pair. -/
public theorem triangulateFaces_noReversePair {vertexCount faceCount : Nat}
    (faces : Fin faceCount -> Stokes.OrientedTriangle vertexCount) :
    (EdgeCancellation.triangulateFaces faces).boundary.Pairwise (fun left right => left ≠ right.reverse) :=
  (EdgeCancellation.cancelEdges (Stokes.triangleEdgeOccurrences faces)).noReversePair

end EdgeCancellation

end Purelib.Topology.Mesh
