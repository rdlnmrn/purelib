module
public import Purelib.Algebra.Group.Negation
import Purelib.Algebra.Ring.IntCast
import Purelib.Data.List.Pairwise
import Purelib.Data.List.Append
import Purelib.Data.List.Membership
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.Map
import Purelib.Topology.Chain.PathBoundary

import Purelib.Data.List.Permutation
import Purelib.Topology.Polygon.Stokes
public import Purelib.Topology.Surface.Sewing.SimpleBoundaryCycles
public import Purelib.Topology.Surface.Boundary.BoundaryCoordinates
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Algebra.Ring.Int.Defs
import Purelib.Tactic.QuotientFreeOmega
meta import Mathlib.Tactic.Linter.Lint

section
open Purelib.Algebra
-- Preserve the retained subtraction dictionary while selecting its owned zero certificate.
attribute [local instance 2000] Group.Negation.subNegZeroMonoid

open Purelib

open Purelib.Algebra

open Purelib.Data

open Purelib.Data.List

open Purelib.Topology.Chain

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

public section

/-!
# Integer multiples of the actual physical boundary cycles

At a physical vertex there is one incoming and one outgoing boundary edge.
Integer conservation therefore makes the coefficient constant along each
displayed cycle. The construction retains those coefficients and the original
cycle words; it does not identify closedness with a zero period.
-/

namespace Purelib.Topology.Surface.Sewing.PhysicalCycleCoordinates

open Purelib.Topology.Surface.Sewing.SimpleBoundaryCycles.PolygonStokes (BoundaryCycleDecomposition)
open Purelib.Topology.Surface.Cut.BoundaryWord (CutAlphabet)

open Purelib.Topology.Surface.Sewing.SimpleBoundaryCycles
open Purelib.Topology.Surface.Boundary.BoundaryCoordinates

open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib.Topology.Chain.PathBoundary (PathEndpoints edgeBoundaryAt vertexIndicator)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_zero sumFin_sub sumFin_ite_eq)

namespace BoundaryCycleDecomposition

variable {count : Nat} {occurrences : List (Stokes.OrientedEdge count)}

/-- A nonempty certified path starts at its first original edge's start vertex. -/
private theorem head_start {head : Stokes.OrientedEdge count} {tail : List (Stokes.OrientedEdge count)} {start finish :
  Fin count}
    (path : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish (head :: tail) start finish) : start =
      head.start := by
  cases path
  rfl

/-- A nonempty path's finish list is its tail's start list followed by the final vertex. -/
private theorem finish_list {head : Stokes.OrientedEdge count} {tail : List (Stokes.OrientedEdge count)} {start finish :
  Fin count}
    (path : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish (head :: tail) start finish) :
    (head :: tail).map OrientedEdge.finish = tail.map OrientedEdge.start ++ [finish] := by
  induction tail generalizing head start with
  | nil => cases path with | cons final => cases final; rfl
  | cons next rest ih =>
      cases path with
      | cons remaining =>
          have first : head.finish = next.start := head_start remaining
          rw [List.map_cons, ih remaining, first]
          rfl

/-- A closed original cycle has start and finish lists related by cyclic reordering. -/
private theorem finish_permutation {cycle : List (Stokes.OrientedEdge count)} {anchor : Fin count}
    (closed : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish cycle anchor anchor) :
    List.Perm (cycle.map OrientedEdge.start) (cycle.map OrientedEdge.finish) := by
  cases cycle with
  | nil => exact .nil
  | cons head tail =>
      have first : anchor = head.start := by cases closed; rfl
      rw [finish_list closed, first]
      simpa only [Data.List.Append.append_nil, List.map_cons] using
        List.Permutation.move_head head.start (tail.map OrientedEdge.start) []

/-- Extend a retained list permutation by the same right-hand tail. -/
private theorem append_right {Alpha : Type} {first last : List Alpha}
    (permutation : List.Perm first last) (tail : List Alpha) : List.Perm (first ++ tail) (last ++ tail) := by
  induction permutation with
  | nil => exact List.Permutation.refl _
  | cons head _ ih => exact .cons head ih
  | swap first last rest => exact .swap first last (rest ++ tail)
  | trans _ _ first last => exact first.trans last

/-- The full bank of original closed cycles has permuted start and finish lists. -/
private theorem finishes_permutation (cycles : List (List (Stokes.OrientedEdge count)))
    (closed : ∀ cycle ∈ cycles, ∃ anchor, PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish cycle anchor
      anchor) :
    List.Perm (cycles.flatten.map OrientedEdge.start) (cycles.flatten.map OrientedEdge.finish) := by
  induction cycles with
  | nil => exact .nil
  | cons cycle cycles ih =>
      obtain ⟨anchor, path⟩ := closed cycle List.mem_cons_self
      rw [List.flatten_cons, Data.List.Map.map_append, Data.List.Map.map_append]
      exact (append_right (finish_permutation path) _).trans
        (List.Permutation.append_left _ (ih (fun other member => closed other (List.mem_cons_of_mem _ member))))

/-- Unique original boundary sources imply unique original boundary finishes. -/
theorem finishes_unique (boundary : PolygonStokes.BoundaryCycleDecomposition occurrences) :
    (boundary.cycles.flatten.map OrientedEdge.finish).Nodup :=
  List.Permutation.nodup (finishes_permutation boundary.cycles boundary.closed)
    boundary.sources_unique

/-- Unique retained endpoint readings identify two edges with the same endpoint. -/
private theorem edge_eq_of_endpoint {word : List (Stokes.OrientedEdge count)} (endpoint : Stokes.OrientedEdge count →
  Fin count)
    (unique : (word.map endpoint).Nodup) {first last : Stokes.OrientedEdge count}
    (firstMember : first ∈ word) (lastMember : last ∈ word) (equal : endpoint first = endpoint last) : first = last :=
      by
  induction word with
  | nil => exact (List.not_mem_nil firstMember).elim
  | cons head tail ih =>
      have parts := List.pairwise_cons.mp unique
      rcases Data.List.Membership.mem_cons.mp firstMember with rfl | firstTail
      · rcases Data.List.Membership.mem_cons.mp lastMember with rfl | lastTail
        · rfl
        · exact (parts.1 _ (equal ▸ Map.mem_map_of_mem lastTail) rfl).elim
      · rcases Data.List.Membership.mem_cons.mp lastMember with rfl | lastTail
        · exact (parts.1 _ (equal ▸ Map.mem_map_of_mem firstTail) rfl).elim
        · exact ih parts.2 firstTail lastTail

/-- Original boundary edges with equal finishes are identical. -/
theorem edge_eq_of_finish_eq (boundary : PolygonStokes.BoundaryCycleDecomposition occurrences)
    {first last : Stokes.OrientedEdge count} (firstMember : first ∈ boundary.cycles.flatten)
    (lastMember : last ∈ boundary.cycles.flatten) (equal : first.finish = last.finish) : first = last :=
  edge_eq_of_endpoint OrientedEdge.finish (finishes_unique
    boundary) firstMember lastMember equal

end BoundaryCycleDecomposition

section PhysicalCycleCoordinates

open SewingRetraction (wordValue wordValue_append)
open Purelib.Topology.Surface.Boundary.BoundaryCoordinates (WordCoordinates)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)

variable {count size : Nat} {occurrences : List (Stokes.OrientedEdge count)}
  {boundary : PolygonStokes.BoundaryCycleDecomposition occurrences}
  {generators : Fin size → Stokes.OrientedEdge count} {row : Fin size → Int}

/-- Sum original generator coefficients whose edges start at the supplied surface vertex. -/
@[expose] def coefficientAt (generators : Fin size → Stokes.OrientedEdge count) (row : Fin size → Int) (vertex : Fin
  count) : Int :=
  FiniteSum.Fin.sumFin fun index => if vertex = (generators index).start then row index else 0

/-- Unique boundary endpoints recover the exact coefficient of a retained generator. -/
private theorem endpoint_coefficient (endpoint : Stokes.OrientedEdge count → Fin count)
    (unique : (boundary.cycles.flatten.map endpoint).Nodup)
    (injective : Function.Injective generators)
    (supported : ∀ index, row index ≠ 0 → generators index ∈ boundary.cycles.flatten)
    (selected : Fin size) (member : generators selected ∈ boundary.cycles.flatten) :
    FiniteSum.Fin.sumFin (fun index => if endpoint (generators selected) = endpoint (generators index) then row index
      else 0) = row selected := by
  refine (FiniteSum.Fin.sumFin_congr ?_).trans (FiniteSum.Fin.sumFin_ite_eq selected row)
  intro index
  by_cases same : index = selected
  · subst index
    rw [if_pos rfl, if_pos rfl]
  · rw [if_neg same]
    by_cases zero : row index = 0
    · rw [zero]; split <;> rfl
    · apply if_neg
      intro equal
      apply same
      exact injective (PhysicalCycleCoordinates.BoundaryCycleDecomposition.edge_eq_of_endpoint endpoint unique
        (supported index zero) member equal.symm)

section
open Purelib.Topology.Surface.Sewing.PhysicalCycleCoordinates
/-- The source coefficient at an original supported generator is its retained integer row entry. -/
theorem coefficientAt_generator (injective : Function.Injective generators)
    (supported : ∀ index, row index ≠ 0 → generators index ∈ boundary.cycles.flatten)
    (selected : Fin size) (member : generators selected ∈ boundary.cycles.flatten) :
    coefficientAt generators row (generators selected).start = row selected :=
  endpoint_coefficient OrientedEdge.start boundary.sources_unique injective supported selected
    member

/-- Integer conservation makes the original coefficient equal at both ends of each physical edge. -/
theorem coefficientAt_edge (injective : Function.Injective generators)
    (supported : ∀ index, row index ≠ 0 → generators index ∈ boundary.cycles.flatten)
    (covered : ∀ edge ∈ boundary.cycles.flatten, ∃ index, generators index = edge)
    (closed : ∀ vertex, FiniteSum.Fin.sumFin (fun index => row index *
      PathBoundary.edgeBoundaryAt OrientedEdge.start OrientedEdge.finish (generators index) vertex) = 0)
    {edge : Stokes.OrientedEdge count} (member : edge ∈ boundary.cycles.flatten) :
    coefficientAt generators row edge.finish = coefficientAt generators row edge.start := by
  obtain ⟨selected, rfl⟩ := covered edge member
  have conserved := closed (generators selected).finish
  have expanded : FiniteSum.Fin.sumFin (fun index => row index *
      PathBoundary.edgeBoundaryAt OrientedEdge.start OrientedEdge.finish (generators index) (generators
        selected).finish) =
      FiniteSum.Fin.sumFin (fun index => if (generators selected).finish = (generators index).finish then row index else
        0) -
      coefficientAt generators row (generators selected).finish := by
    refine (FiniteSum.Fin.sumFin_congr ?_).trans (FiniteSum.Fin.sumFin_sub _ _)
    intro index
    rw [PathBoundary.edgeBoundaryAt, PathBoundary.vertexIndicator, PathBoundary.vertexIndicator, mul_sub]
    split <;> split <;> simp only [-eq_self, -iff_self, mul_one, mul_zero] <;> rfl
  rw [expanded, endpoint_coefficient OrientedEdge.finish
    (PhysicalCycleCoordinates.BoundaryCycleDecomposition.finishes_unique boundary) injective supported selected member]
    at conserved
  rw [coefficientAt_generator injective supported selected member]
  omega

end

/-- Edgewise constant vertex weights agree with the original path-start weight at every edge source. -/
private theorem path_sources {path : List (Stokes.OrientedEdge count)} {start finish : Fin count}
    (endpoints : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish path start finish)
    (weight : Fin count → Int)
    (constant : ∀ edge ∈ path, weight edge.finish = weight edge.start)
    {edge : Stokes.OrientedEdge count} (member : edge ∈ path) : weight edge.start = weight start := by
  induction endpoints with
  | nil => exact (List.not_mem_nil member).elim
  | @cons head tail finish rest ih =>
      rcases Data.List.Membership.mem_cons.mp member with rfl | inTail
      · rfl
      · exact (ih (fun other member => constant other (List.mem_cons_of_mem _ member)) inTail).trans
          (constant head List.mem_cons_self)

section
open Purelib.Topology.Surface.Sewing.PhysicalCycleCoordinates
/-- Read a physical cycle's integer coefficient at its first edge, using zero for the empty cycle. -/
@[expose] def cycleCoefficient (generators : Fin size → Stokes.OrientedEdge count) (row : Fin size → Int) : List
  (Stokes.OrientedEdge count) → Int
  | [] => 0
  | edge :: _ => coefficientAt generators row edge.start

/-- A supported closed integer row has one constant coefficient along each original physical cycle. -/
theorem cycle_constant (injective : Function.Injective generators)
    (supported : ∀ index, row index ≠ 0 → generators index ∈ boundary.cycles.flatten)
    (covered : ∀ edge ∈ boundary.cycles.flatten, ∃ index, generators index = edge)
    (closed : ∀ vertex, FiniteSum.Fin.sumFin (fun index => row index *
      PathBoundary.edgeBoundaryAt OrientedEdge.start OrientedEdge.finish (generators index) vertex) = 0)
    {cycle : List (Stokes.OrientedEdge count)} (cycleMember : cycle ∈ boundary.cycles)
    {edge : Stokes.OrientedEdge count} (member : edge ∈ cycle) :
    coefficientAt generators row edge.start = cycleCoefficient generators row cycle := by
  obtain ⟨anchor, endpoints⟩ := boundary.closed cycle cycleMember
  have constant (edge : Stokes.OrientedEdge count) (member : edge ∈ cycle) :
      coefficientAt generators row edge.finish = coefficientAt generators row edge.start :=
    coefficientAt_edge injective supported covered closed (SimpleBoundaryCycles.mem_flatten.mpr
      ⟨cycle, cycleMember, member⟩)
  cases cycle with
  | nil => exact (List.not_mem_nil member).elim
  | cons head tail =>
      exact (path_sources endpoints _ constant member).trans
        (path_sources endpoints _ constant List.mem_cons_self).symm

end

/-- Pointwise equality on an original edge word preserves its Gaussian evaluation. -/
private theorem word_congr (first last : Stokes.OrientedEdge count → Gaussian.Basic.Canonical) (word : List
  (Stokes.OrientedEdge count))
    (equal : ∀ edge ∈ word, first edge = last edge) : wordValue first word = wordValue last word := by
  induction word with
  | nil => rfl
  | cons edge rest ih =>
      rw [wordValue, wordValue, equal edge List.mem_cons_self,
        ih (fun other member => equal other (List.mem_cons_of_mem _ member))]

/-- Evaluating an edge word by the zero reading gives zero. -/
private theorem word_zero (word : List (Stokes.OrientedEdge count)) : wordValue (fun _ => 0) word = 0 := by
  induction word with
  | nil => rfl
  | cons edge rest ih => rw [wordValue, ih, zero_add]

/-- A unique original occurrence reads its selected Gaussian value exactly once. -/
private theorem word_selected (selected : Stokes.OrientedEdge count) (value : Gaussian.Basic.Canonical)
    {word : List (Stokes.OrientedEdge count)} (unique : word.Nodup) (member : selected ∈ word) :
    wordValue (fun edge => if edge = selected then value else 0) word = value := by
  induction word with
  | nil => exact (List.not_mem_nil member).elim
  | cons head tail ih =>
      have parts := List.pairwise_cons.mp unique
      rcases Data.List.Membership.mem_cons.mp member with rfl | inTail
      · have zero : wordValue (fun edge => if edge = selected then value else 0) tail = 0 :=
          (word_congr _ _ tail (fun edge member => if_neg (fun (same : edge = selected) =>
            parts.1 _ (same ▸ member) rfl))).trans (word_zero tail)
        rw [wordValue, if_pos rfl, zero, add_zero]
      · rw [wordValue, if_neg (fun (same : head = selected) => parts.1 _ (same.symm ▸ inTail) rfl), ih parts.2 inTail,
          zero_add]

/-- Finite summation of edge readings commutes with evaluation of the original edge word. -/
private theorem word_sum (values : Fin size → Stokes.OrientedEdge count → Gaussian.Basic.Canonical) (word : List
  (Stokes.OrientedEdge count)) :
    FiniteSum.Fin.sumFin (fun index => wordValue (values index) word) = wordValue (fun edge => FiniteSum.Fin.sumFin (fun
      index => values index edge)) word := by
  induction word with
  | nil => exact FiniteSum.Fin.sumFin_zero
  | cons head tail ih =>
      change FiniteSum.Fin.sumFin (fun index => values index head + wordValue (values index) tail) = _
      rw [FiniteSum.Fin.sumFin_add, ih]
      rfl

open Purelib.Topology.Surface.Sewing.PhysicalCycleCoordinates in
/-- The original supported generator combination equals its coefficient-weighted physical boundary reading. -/
theorem readback (injective : Function.Injective generators)
    (supported : ∀ index, row index ≠ 0 → generators index ∈ boundary.cycles.flatten)
    (covered : ∀ edge ∈ boundary.cycles.flatten, ∃ index, generators index = edge)
    (value : Stokes.OrientedEdge count → Gaussian.Basic.Canonical) :
    WordCoordinates.combine row (fun index => value (generators index)) =
      wordValue (fun edge => (coefficientAt generators row edge.start : Gaussian.Basic.Canonical) * value edge)
        boundary.cycles.flatten := by
  calc
    _ = FiniteSum.Fin.sumFin (fun index => wordValue (fun edge => if edge = generators index then
        (row index : Gaussian.Basic.Canonical) * value edge else 0) boundary.cycles.flatten) := by
      apply FiniteSum.Fin.sumFin_congr
      intro index
      by_cases zero : row index = 0
      · rw [zero, Algebra.Ring.IntCast.cast_zero, zero_mul]
        exact ((word_congr _ _ _ (fun edge _ => by split <;> (try simp only [-eq_self,
          -iff_self, zero_mul]) <;> rfl)).trans (word_zero _)).symm
      · have replaced := word_congr
          (fun edge => if edge = generators index then (row index : Gaussian.Basic.Canonical) * value edge else 0)
          (fun edge => if edge = generators index then (row index : Gaussian.Basic.Canonical) * value (generators index)
            else 0)
          boundary.cycles.flatten (fun edge _ => by split <;> rename_i same; rw [same]; rfl)
        exact (replaced.trans (word_selected _ _ boundary.edges_unique (supported index
          zero))).symm
    _ = wordValue (fun edge => FiniteSum.Fin.sumFin (fun index => if edge = generators index then
        (row index : Gaussian.Basic.Canonical) * value edge else 0)) boundary.cycles.flatten :=
          word_sum _ _
    _ = _ := by
      apply word_congr
      intro edge member
      obtain ⟨selected, rfl⟩ := covered edge member
      rw [coefficientAt_generator injective supported selected member]
      refine (FiniteSum.Fin.sumFin_congr ?_).trans (FiniteSum.Fin.sumFin_ite_eq selected
        (fun index => (row index : Gaussian.Basic.Canonical) * value (generators selected)))
      intro index
      by_cases same : index = selected
      · subst index
        rw [if_pos rfl, if_pos rfl]
      · rw [if_neg same, if_neg (fun equal => same (injective equal).symm)]

open Purelib.Topology.Surface.Sewing.PhysicalCycleCoordinates in
set_option genInjectivity false in
/-- Cached integer multiples of the original displayed boundary cycles. The readback certificate relates these rows to
the supplied generator vector. -/
structure Data (boundary : PolygonStokes.BoundaryCycleDecomposition occurrences)
    (generators : Fin size → Stokes.OrientedEdge count) (row : Fin size → Int) where
  /-- Cached integer multiplicities paired with the original ordered boundary cycle words. -/ rows : List (Int × List
    (Stokes.OrientedEdge count))
  /-- Reading the cycle words recovers the original boundary decomposition exactly. -/ words_eq : rows.map Prod.snd =
    boundary.cycles
  /-- Each original edge in a retained row has that row's cached coefficient. -/ constant : ∀ entry ∈ rows, ∀ edge ∈
    entry.2, coefficientAt generators row edge.start = entry.1
  /-- Every Gaussian edge valuation reads the same original generator row through the retained physical cycles. -/
    readback : ∀ value : Stokes.OrientedEdge count → Gaussian.Basic.Canonical,
    WordCoordinates.combine row (fun index => value (generators index)) =
      wordValue (fun edge => (coefficientAt generators row edge.start : Gaussian.Basic.Canonical) * value edge)
        boundary.cycles.flatten

constructive_injectivity Data

/-- Cache whole original boundary cycles with their conserved integer multiplicities.

Injective generators, complete physical coverage and the original zero-boundary certificate establish exact row and
value readbacks. -/
@[expose] def build (boundary : PolygonStokes.BoundaryCycleDecomposition occurrences) (generators : Fin size →
  Stokes.OrientedEdge count) (row : Fin size → Int)
    (injective : Function.Injective generators)
    (supported : ∀ index, row index ≠ 0 → generators index ∈ boundary.cycles.flatten)
    (covered : ∀ edge ∈ boundary.cycles.flatten, ∃ index, generators index = edge)
    (closed : ∀ vertex, FiniteSum.Fin.sumFin (fun index => row index *
      PathBoundary.edgeBoundaryAt OrientedEdge.start OrientedEdge.finish (generators index) vertex) = 0) :
        Data boundary generators row where
  rows := boundary.cycles.map (fun cycle => (cycleCoefficient generators row cycle, cycle))
  words_eq := by
    induction boundary.cycles with
    | nil => rfl
    | cons cycle cycles ih => exact congrArg (List.cons cycle) ih
  constant := by
    intro entry member edge inWord
    obtain ⟨cycle, cycleMember, rfl⟩ := Map.mem_map.mp member
    exact cycle_constant injective supported covered closed cycleMember inWord
  readback := PhysicalCycleCoordinates.readback injective supported covered

open Purelib.Topology.Surface.Sewing.PhysicalCycleCoordinates
/-- A constant retained cycle coefficient factors out of its original Gaussian word reading. -/
private theorem word_constant (value : Stokes.OrientedEdge count → Gaussian.Basic.Canonical) (weight : Int)
    (word : List (Stokes.OrientedEdge count))
    (constant : ∀ edge ∈ word, coefficientAt generators row edge.start = weight) :
    wordValue (fun edge => (coefficientAt generators row edge.start : Gaussian.Basic.Canonical) * value edge) word =
      (weight : Gaussian.Basic.Canonical) * wordValue value word := by
  induction word with
  | nil => exact (mul_zero _).symm
  | cons edge rest ih =>
      rw [wordValue, wordValue, constant edge List.mem_cons_self,
        ih (fun other member => constant other (List.mem_cons_of_mem _ member)), mul_add]

namespace Data

/-- Evaluate the cached whole loops with any edge readings. Antisymmetry is unnecessary here because their original
orientations are retained. -/
theorem value_eq (data : Data boundary generators row) (value : Stokes.OrientedEdge count
  → Gaussian.Basic.Canonical) :
    WordCoordinates.combine row (fun index => value (generators index)) =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (data.rows.map (fun entry => (entry.1 : Gaussian.Basic.Canonical) *
        wordValue value entry.2)) := by
  have source := congrArg (fun words => wordValue
    (fun edge => (coefficientAt generators row edge.start : Gaussian.Basic.Canonical) * value edge) words.flatten)
      data.words_eq
  refine (data.readback value).trans (source.symm.trans ?_)
  have expand : ∀ entries : List (Int × List (Stokes.OrientedEdge count)),
      (∀ entry ∈ entries, ∀ edge ∈ entry.2, coefficientAt generators row edge.start = entry.1) →
      wordValue (fun edge => (coefficientAt generators row edge.start : Gaussian.Basic.Canonical) * value edge)
        (entries.map Prod.snd).flatten =
        Data.Gaussian.Norm.Sum.Basic.gaussianSum (entries.map (fun entry => (entry.1 : Gaussian.Basic.Canonical) *
          wordValue value entry.2)) := by
    intro entries constant
    induction entries with
    | nil => rfl
    | cons entry entries ih =>
        rw [List.map_cons, List.flatten_cons, wordValue_append, word_constant value entry.1
          entry.2
          (constant entry List.mem_cons_self), ih (fun other member => constant other (List.mem_cons_of_mem _ member))]
        rfl
  exact expand data.rows data.constant

end Data

end PhysicalCycleCoordinates
end Purelib.Topology.Surface.Sewing.PhysicalCycleCoordinates

end
