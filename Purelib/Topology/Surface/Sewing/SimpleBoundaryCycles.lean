module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Append
import Purelib.Data.List.Map
import Purelib.Data.List.Membership
import Purelib.Data.List.Nodup
import Purelib.Data.List.Pairwise
public import Purelib.Topology.Chain.PathBoundary

public import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PolygonSewing
import Purelib.Data.List.Permutation
import Purelib.Tactic.QuotientFreeOmega

public section

/-!
# Exact support of disjoint simple boundary cycles

A simple closed word with at least three edges cannot contain a retraced
pair. The proof rotates to a displayed occurrence and uses only finite path
endpoints and source-vertex uniqueness. It also excludes reverse pairs
between cycles whose combined source list is duplicate-free.
-/

section

open Purelib.Data

open Purelib.Data.List

open Purelib.Topology.Chain

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

open Purelib.Topology.Surface.Sewing.PolygonSewing

open Purelib.Topology.Polygon.Stokes (OrientedEdge)

open Purelib.Topology.Chain.PathBoundary (PathEndpoints)

namespace Purelib.Topology.Surface.Sewing.SimpleBoundaryCycles

variable {count : Nat}

/-- Membership in a flattened finite list is membership in one of its original sublists.

The witness identifies an actual component list and an occurrence in that
component; both directions retain their finite membership constructors. -/
theorem mem_flatten {Alpha : Type} {value : Alpha} {words : List (List Alpha)} :
    value ∈ words.flatten ↔ ∃ word ∈ words, value ∈ word := by
  induction words with
  | nil =>
      exact ⟨fun member => (List.not_mem_nil member).elim,
        fun ⟨_, member, _⟩ => (List.not_mem_nil member).elim⟩
  | cons head words ih =>
      change value ∈ head ++ words.flatten ↔ _
      constructor
      · intro member
        rcases Membership.mem_append.mp member with inHead | inTail
        · exact ⟨head, List.mem_cons_self, inHead⟩
        · rcases ih.mp inTail with ⟨word, wordMember, member⟩
          exact ⟨word, List.mem_cons_of_mem _ wordMember, member⟩
      · rintro ⟨word, wordMember, member⟩
        rcases Membership.mem_cons.mp wordMember with rfl | inTail
        · exact Membership.mem_append.mpr (.inl member)
        · exact Membership.mem_append.mpr (.inr (ih.mpr ⟨word, inTail, member⟩))

/-- In a word with distinct source vertices, equal edge starts identify the edge occurrences.

Source uniqueness excludes two different displayed occurrences with the
same source, including head-to-tail comparisons. -/
theorem edge_eq_of_start_eq : ∀ {word : List (Stokes.OrientedEdge count)},
    (word.map OrientedEdge.start).Nodup → ∀ {first last : Stokes.OrientedEdge count},
    first ∈ word → last ∈ word → first.start = last.start → first = last
  | [], _, _, _, member, _, _ => (List.not_mem_nil member).elim
  | head :: tail, simple, first, last, firstMember, lastMember, equal => by
      have pairwiseParts := List.pairwise_cons.mp simple
      have parts : head.start ∉ tail.map OrientedEdge.start ∧ (tail.map OrientedEdge.start).Nodup :=
        ⟨fun member => pairwiseParts.1 head.start member rfl, pairwiseParts.2⟩
      rcases Membership.mem_cons.mp firstMember with rfl | firstTail
      · rcases Membership.mem_cons.mp lastMember with rfl | lastTail
        · rfl
        · exact (parts.1 (equal ▸ Map.mem_map_of_mem lastTail)).elim
      · rcases Membership.mem_cons.mp lastMember with rfl | lastTail
        · exact (parts.1 (equal ▸ Map.mem_map_of_mem firstTail)).elim
        · exact Purelib.Topology.Surface.Sewing.SimpleBoundaryCycles.edge_eq_of_start_eq parts.2 firstTail lastTail
            equal

/-- Distinct source vertices imply distinct oriented edges.

Any equal edge occurrences have equal sources. The supplied pairwise
source inequalities therefore also exclude repeated edges. -/
theorem edges_nodup {word : List (Stokes.OrientedEdge count)} (simple : (word.map OrientedEdge.start).Nodup) :
  word.Nodup :=
  (Pairwise.pairwise_map.mp simple).imp (fun different same => different (congrArg OrientedEdge.start same))

/-- The start of a nonempty oriented path is the first edge's source.

The retained nonempty path constructor identifies its source with the
first edge, without changing the endpoint witnesses. -/
private theorem head_start {head : Stokes.OrientedEdge count} {tail : List (Stokes.OrientedEdge count)} {start finish :
  Fin count}
    (path : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish (head :: tail) start finish) : start =
      head.start := by
  cases path
  rfl

/-- Removing a path's first edge leaves a path from its finish to the original endpoint.

The tail keeps the final endpoint and starts at the removed edge's finish.
The path constructor supplies this certificate directly. -/
private theorem tail_path {head : Stokes.OrientedEdge count} {tail : List (Stokes.OrientedEdge count)} {start finish :
  Fin count}
    (path : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish (head :: tail) start finish) :
    PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish tail head.finish finish := by
  cases path with
  | cons tail => exact tail

/-- Rotating two consecutive blocks preserves distinct source vertices.

The two displayed blocks exchange position while retaining their own
source lists and the cross-block inequalities. -/
private theorem rotate_simple {before after : List (Stokes.OrientedEdge count)}
    (simple : ((before ++ after).map OrientedEdge.start).Nodup) :
    ((after ++ before).map OrientedEdge.start).Nodup := by
  rw [Map.map_append] at simple ⊢
  have parts := List.Permutation.nodup_append_parts simple
  exact Nodup.nodup_append parts.2.1 parts.1 (fun _ member _ other => Ne.symm (parts.2.2 _ other _ member))

/-- The first edge of a simple closed word of length at least three has no reverse occurrence.

A reverse occurrence would repeat a source in the retained closed path.
The length bound supplies the third occurrence needed to exclude this case. -/
private theorem head_no_reverse {head : Stokes.OrientedEdge count} {tail : List (Stokes.OrientedEdge count)} {anchor :
  Fin count}
    (closed : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish (head :: tail) anchor anchor)
    (simple : ((head :: tail).map OrientedEdge.start).Nodup) (long : 3 ≤ (head :: tail).length) :
    head.reverse ∉ head :: tail := by
  cases closed with
  | cons rest =>
      cases tail with
      | nil => simp only [List.length_cons, List.length_nil] at long; omega
      | cons next remaining =>
          have nextStart := SimpleBoundaryCycles.head_start rest
          have nextMember : next ∈ head :: next :: remaining := List.mem_cons_of_mem _ List.mem_cons_self
          have headFresh : head.start ∉ (next :: remaining).map OrientedEdge.start :=
            fun member => (List.pairwise_cons.mp simple).1 head.start member rfl
          intro reverseMember
          have nextEq := SimpleBoundaryCycles.edge_eq_of_start_eq simple nextMember reverseMember nextStart.symm
          have nextFinish : next.finish = head.start := congrArg OrientedEdge.finish nextEq
          have final := SimpleBoundaryCycles.tail_path rest
          cases remaining with
          | nil => simp only [List.length_cons, List.length_nil] at long; omega
          | cons third remaining =>
              have thirdStart := SimpleBoundaryCycles.head_start final
              have repeated : head.start = third.start := nextFinish.symm.trans thirdStart
              apply headFresh
              rw [repeated]
              exact List.mem_cons_of_mem _ List.mem_cons_self

/-- A simple closed word of length at least three contains no edge together with its reverse.

Rotation exposes the selected occurrence while retaining path endpoints and source uniqueness. -/
theorem no_reverse {word : List (Stokes.OrientedEdge count)} {anchor : Fin count}
    (closed : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish word anchor anchor)
    (simple : (word.map OrientedEdge.start).Nodup) (long : 3 ≤ word.length)
    {edge : Stokes.OrientedEdge count} (member : edge ∈ word) : edge.reverse ∉ word := by
  rcases Membership.split_of_mem member with ⟨before, after, rfl⟩
  obtain ⟨middle, initial, final⟩ :=
    PathEndpoints.split_append before (edge :: after) closed
  have rotated := PathEndpoints.append final initial
  have rotatedSimple := SimpleBoundaryCycles.rotate_simple simple
  have rotatedLength : 3 ≤ (edge :: after ++ before).length := by
    simp only [Append.length_append, List.length_cons] at long ⊢
    omega
  have absent := SimpleBoundaryCycles.head_no_reverse rotated rotatedSimple rotatedLength
  intro reverseMember
  apply absent
  rcases Membership.mem_append.mp reverseMember with inBefore | inAfter
  · exact List.mem_cons_of_mem _ (Membership.mem_append.mpr (Or.inr inBefore))
  · exact Membership.mem_append.mpr (Or.inl inAfter)

/-- An edge's finish is a path source vertex or the final endpoint.

Following the retained path either finds the next displayed source or
reaches its certified final endpoint. -/
private theorem finish_mem_or_endpoint {word : List (Stokes.OrientedEdge count)} {start finish : Fin count}
    (path : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish word start finish)
    {edge : Stokes.OrientedEdge count} (member : edge ∈ word) :
    edge.finish ∈ word.map OrientedEdge.start ∨ edge.finish = finish := by
  induction path with
  | nil => exact (List.not_mem_nil member).elim
  | @cons head remaining finish tail ih =>
      rcases Membership.mem_cons.mp member with rfl | inTail
      · cases remaining with
        | nil => cases tail; exact .inr rfl
        | cons next remaining =>
            exact .inl (List.mem_cons_of_mem _ (by rw [SimpleBoundaryCycles.head_start tail]; exact List.mem_cons_self))
      · exact (ih inTail).elim (fun member => .inl (List.mem_cons_of_mem _ member)) Or.inr

/-- Every edge finish in a closed path also occurs as a source vertex.

Closedness identifies the endpoint with the first displayed source.
Every edge finish consequently occurs in the retained source list. -/
theorem finish_mem {word : List (Stokes.OrientedEdge count)} {anchor : Fin count}
    (closed : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish word anchor anchor)
    {edge : Stokes.OrientedEdge count} (member : edge ∈ word) : edge.finish ∈ word.map OrientedEdge.start := by
  rcases finish_mem_or_endpoint closed member with inWord | endpoint
  · exact inWord
  · cases closed with
    | nil => exact (List.not_mem_nil member).elim
    | cons => rw [endpoint]; exact List.mem_cons_self

/-- Global source uniqueness implies source uniqueness in each retained component word.

Membership selects one retained component. Its mapped sources inherit
their duplicate-freeness from the flattened source certificate. -/
theorem member_simple {words : List (List (Stokes.OrientedEdge count))}
    (simple : (words.flatten.map OrientedEdge.start).Nodup)
    {word : List (Stokes.OrientedEdge count)} (member : word ∈ words) : (word.map OrientedEdge.start).Nodup := by
  induction words with
  | nil => exact (List.not_mem_nil member).elim
  | cons head words ih =>
      rw [List.flatten_cons, Map.map_append] at simple
      have parts := List.Permutation.nodup_append_parts simple
      rcases Membership.mem_cons.mp member with rfl | inTail
      · exact parts.1
      · exact ih parts.2.1 inTail

/-- Closed cycles of length at least three with globally distinct sources contain no reverse pair.

A reverse occurrence would share a source with an occurrence in the
selected cycle. Global source uniqueness reduces this to the cycle's exclusion. -/
theorem flatten_no_reverse {words : List (List (Stokes.OrientedEdge count))}
    (closed : ∀ word ∈ words, ∃ anchor, PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish word anchor
      anchor)
    (simple : (words.flatten.map OrientedEdge.start).Nodup) (long : ∀ word ∈ words, 3 ≤ word.length)
    {edge : Stokes.OrientedEdge count} (member : edge ∈ words.flatten) : edge.reverse ∉ words.flatten := by
  rcases SimpleBoundaryCycles.mem_flatten.mp member with ⟨word, wordMember, edgeMember⟩
  obtain ⟨anchor, path⟩ := closed word wordMember
  rcases Map.mem_map.mp (finish_mem path edgeMember) with ⟨next, nextMember, nextStart⟩
  intro reverseMember
  have nextEq := SimpleBoundaryCycles.edge_eq_of_start_eq simple (SimpleBoundaryCycles.mem_flatten.mpr ⟨word,
    wordMember, nextMember⟩) reverseMember nextStart
  exact SimpleBoundaryCycles.no_reverse path (SimpleBoundaryCycles.member_simple simple wordMember) (long word
    wordMember) edgeMember (nextEq ▸ nextMember)

end Purelib.Topology.Surface.Sewing.SimpleBoundaryCycles

namespace Purelib.Topology.Surface.Sewing.SimpleBoundaryCycles.PolygonStokes

open Purelib.Topology.Polygon.Stokes (OrientedEdge)

open Purelib.Topology.Chain.PathBoundary (PathEndpoints)

set_option genInjectivity false in
/-- A finite cycle decomposition of precisely the uncancelled oriented boundary.

The source-uniqueness certificate proves simplicity within each cycle and
separates the source vertices of all retained occurrences. -/
structure BoundaryCycleDecomposition {count : Nat} (occurrences : List (Stokes.OrientedEdge count)) where
  /-- Finite list of original oriented boundary cycles. -/ cycles : List (List (Stokes.OrientedEdge count))
  /-- Each retained cycle is an oriented path returning to an explicit anchor. -/ closed : ∀ cycle ∈ cycles, ∃ anchor,
    PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish cycle anchor anchor
  /-- Each cycle contains at least three edges. -/ min_length : ∀ cycle ∈ cycles, 3 ≤ cycle.length
  /-- All displayed cycle occurrences have distinct source vertices. -/ sources_unique : (cycles.flatten.map
    OrientedEdge.start).Nodup
  /-- Displayed edges are exactly original occurrences whose reverse does not occur. -/ edge_iff : ∀ edge, edge ∈
    cycles.flatten ↔ edge ∈ occurrences ∧ edge.reverse ∉ occurrences

constructive_injectivity BoundaryCycleDecomposition

namespace BoundaryCycleDecomposition

variable {count : Nat} {occurrences : List (Stokes.OrientedEdge count)}

/-- The displayed boundary-cycle occurrences are duplicate-free. -/
theorem edges_unique (boundary : PolygonStokes.BoundaryCycleDecomposition occurrences) : boundary.cycles.flatten.Nodup
  :=
  SimpleBoundaryCycles.edges_nodup boundary.sources_unique

/-- The retained boundary-cycle list contains no oriented edge together with its reverse. -/
theorem no_reverse (boundary : PolygonStokes.BoundaryCycleDecomposition occurrences)
    {edge : Stokes.OrientedEdge count} (member : edge ∈ boundary.cycles.flatten) : edge.reverse ∉
      boundary.cycles.flatten :=
  SimpleBoundaryCycles.flatten_no_reverse boundary.closed boundary.sources_unique boundary.min_length member

end BoundaryCycleDecomposition
end Purelib.Topology.Surface.Sewing.SimpleBoundaryCycles.PolygonStokes

end
