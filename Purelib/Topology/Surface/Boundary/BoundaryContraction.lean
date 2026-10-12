module
import Purelib.Data.List.Map
import Purelib.Data.List.Nodup
import Purelib.Data.Vector.Basic
import Purelib.Topology.Chain.PathBoundary

import Purelib.Data.List.Permutation
import Purelib.Topology.Polygon.Stokes
public import Purelib.Topology.Surface.Sewing.SimpleBoundaryCycles
import Purelib.Tactic.QuotientFreeOmega
meta import Mathlib.Tactic.Linter.Lint
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Append
import Purelib.Data.List.Filter
-- Exposed collapse and representative definitions retain ordered membership decisions.
public import Purelib.Data.List.Membership

public section

/-!
# Executable contraction of disjoint physical boundary cycles

Keep every interior vertex and one displayed source of each boundary cycle.
The retained list has no unused slots. Its normalization identifies exactly
vertices on the same physical cycle, and every assignment constant on those
cycles factors through it. All counts concern the supplied active vertices.
-/

namespace Purelib.Topology.Surface.Boundary

open Purelib
open Purelib.Data
open Purelib.Data.List
open Purelib.Topology.Polygon
open Purelib.Topology.Surface.Sewing
open Purelib.Topology.Surface.Sewing.SimpleBoundaryCycles

open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Topology.Surface.Sewing.SimpleBoundaryCycles.PolygonStokes (BoundaryCycleDecomposition)

namespace BoundaryContraction.DisjointVertexGroups

variable {Alpha : Type} [DecidableEq Alpha]

/-- Replace a vertex in the first matching group by that group's head.

Vertices outside every group remain fixed; the supplied fallback handles empty group heads. -/
@[expose]
def collapse (fallback : Alpha) : List (List Alpha) → Alpha → Alpha
  | [], vertex => vertex
  | group :: groups, vertex =>
      if vertex ∈ group then group.headD fallback else
        collapse fallback groups vertex

omit [DecidableEq Alpha] in
/-- The fallback head of a nonempty list is a member of that list. -/
theorem head_mem (fallback : Alpha) {group : List Alpha} (nonempty : group ≠ []) :
    group.headD fallback ∈ group := by
  cases group with
  | nil => exact (nonempty rfl).elim
  | cons => exact List.mem_cons_self

/-- A vertex outside every displayed group is fixed by collapse.

Every displayed group and its remaining tail are contained in the flattened
groups. The absence evidence excludes each original membership branch. -/
theorem collapse_outside (fallback : Alpha) (groups : List (List Alpha)) (vertex : Alpha)
    (outside : vertex ∉ groups.flatten) : collapse fallback groups vertex = vertex := by
  induction groups with
  | nil => rfl
  | cons group groups ih =>
      rw [collapse, if_neg (fun member => outside (Membership.mem_append.mpr (.inl member)))]
      exact ih (fun member => outside (Membership.mem_append.mpr (.inr member)))

/-- Disjoint group membership identifies the collapsed vertex with its group's head.

Flattened disjointness excludes the vertex from preceding groups. Recursion
therefore reaches the displayed group and retains its actual head. -/
theorem collapse_member (fallback : Alpha) {groups : List (List Alpha)}
    (unique : groups.flatten.Nodup) {group : List Alpha} (member : group ∈ groups)
    {vertex : Alpha} (inGroup : vertex ∈ group) : collapse fallback groups vertex = group.headD
      fallback := by
  induction groups with
  | nil => exact (List.not_mem_nil member).elim
  | cons first groups ih =>
      have parts := Permutation.nodup_append_parts unique
      rcases Membership.mem_cons.mp member with rfl | inTail
      · exact if_pos inGroup
      · have absent : vertex ∉ first := fun inFirst =>
          parts.2.2 vertex inFirst vertex (SimpleBoundaryCycles.mem_flatten.mpr ⟨group, inTail, inGroup⟩) rfl
        rw [collapse, if_neg absent]
        exact ih parts.2.1 inTail

/-- Collapse either fixes the vertex or selects the head of a group containing it. -/
theorem collapse_spec (fallback : Alpha) (groups : List (List Alpha)) (vertex : Alpha) :
    collapse fallback groups vertex = vertex ∨
      ∃ group ∈ groups, vertex ∈ group ∧ collapse fallback groups vertex = group.headD fallback :=
        by
  induction groups with
  | nil => exact .inl rfl
  | cons group groups ih =>
      by_cases member : vertex ∈ group
      · exact .inr ⟨group, List.mem_cons_self, member, if_pos member⟩
      · rw [collapse, if_neg member]
        exact ih.elim Or.inl (fun ⟨found, present, inside, same⟩ =>
          .inr ⟨found, List.mem_cons_of_mem _ present, inside, same⟩)

/-- For nonempty disjoint groups, collapse identifies exactly equal vertices or vertices in one group.

The groups have disjoint occurrences and nonempty heads. A collapsed head
cannot also belong to a different group, which certifies both directions. -/
theorem collapse_eq_iff (fallback : Alpha) {groups : List (List Alpha)}
    (unique : groups.flatten.Nodup) (nonempty : ∀ group ∈ groups, group ≠ []) (first last : Alpha) :
    collapse fallback groups first = collapse fallback groups last ↔
      first = last ∨ ∃ group ∈ groups, first ∈ group ∧ last ∈ group := by
  induction groups with
  | nil => exact ⟨Or.inl, fun same => same.elim id (fun ⟨_, member, _⟩ => (List.not_mem_nil member).elim)⟩
  | cons group groups ih =>
      have parts := Permutation.nodup_append_parts unique
      have headMember := head_mem fallback (nonempty group List.mem_cons_self)
      have tailNonempty := fun entry member => nonempty entry (List.mem_cons_of_mem _ member)
      have tail := ih parts.2.1 tailNonempty
      have outside (vertex : Alpha) (absent : vertex ∉ group) : collapse fallback groups vertex ∉
        group := by
        rcases collapse_spec fallback groups vertex with same | ⟨found, member, _, same⟩
        · rw [same]; exact absent
        · rw [same]
          intro inHead
          exact parts.2.2 _ inHead _ (SimpleBoundaryCycles.mem_flatten.mpr
            ⟨found, member, head_mem fallback (tailNonempty found member)⟩) rfl
      constructor
      · intro equal
        by_cases firstMember : first ∈ group
        · by_cases lastMember : last ∈ group
          · exact .inr ⟨group, List.mem_cons_self, firstMember, lastMember⟩
          · rw [collapse, if_pos firstMember, collapse,
                if_neg lastMember] at equal
            exact (outside last lastMember (equal ▸ headMember)).elim
        · by_cases lastMember : last ∈ group
          · rw [collapse, if_neg firstMember, collapse,
                if_pos lastMember] at equal
            exact (outside first firstMember (equal.symm ▸ headMember)).elim
          · rw [collapse, if_neg firstMember, collapse,
                if_neg lastMember] at equal
            exact (tail.mp equal).elim Or.inl (fun ⟨found, member, inside⟩ =>
              .inr ⟨found, List.mem_cons_of_mem _ member, inside⟩)
      · intro same
        rcases same with rfl | ⟨found, member, firstMember, lastMember⟩
        · rfl
        · exact (collapse_member fallback unique member firstMember).trans
            (collapse_member fallback unique member lastMember).symm

/-- Retain active vertices outside all groups and one head from each group.

The filter keeps each active occurrence outside the displayed groups. Their
heads then follow in group order, using the supplied fallback. -/
@[expose]
def representatives (fallback : Alpha) (active : List Alpha) (groups : List (List Alpha)) : List Alpha :=
  active.filter (fun vertex => decide (vertex ∉ groups.flatten)) ++ groups.map (List.headD · fallback)

/-- Unique active vertices and disjoint nonempty groups give unique representatives.

The outside filter retains the unique active occurrences. Disjoint nonempty
groups provide unique heads, none of which survives the outside filter. -/
theorem representatives_unique (fallback : Alpha) {active : List Alpha} {groups : List (List Alpha)}
    (activeUnique : active.Nodup) (unique : groups.flatten.Nodup)
    (nonempty : ∀ group ∈ groups, group ≠ []) : (DisjointVertexGroups.representatives fallback active groups).Nodup :=
      by
  have heads : (groups.map (List.headD · fallback)).Nodup := by
    induction groups with
    | nil => exact .nil
    | cons group groups ih =>
        have parts := Permutation.nodup_append_parts unique
        apply List.pairwise_cons.mpr
        refine ⟨?_, ?_⟩
        · intro candidate member same
          obtain ⟨found, member, selected⟩ := Map.mem_map.mp member
          have same := same.trans selected.symm
          exact parts.2.2 _ (head_mem fallback (nonempty group List.mem_cons_self)) _
            (SimpleBoundaryCycles.mem_flatten.mpr ⟨found, member,
              head_mem fallback (nonempty found (List.mem_cons_of_mem _ member))⟩) same
        · exact ih parts.2.1 (fun entry member => nonempty entry (List.mem_cons_of_mem _ member))
  apply Nodup.nodup_append (Filter.pairwise_filter _ activeUnique) heads
  intro first firstMember last lastMember same
  have outside := of_decide_eq_true (Filter.mem_filter.mp firstMember).2
  obtain ⟨group, member, headEq⟩ := Map.mem_map.mp lastMember
  apply outside
  rw [same, ← headEq]
  exact SimpleBoundaryCycles.mem_flatten.mpr ⟨group, member, head_mem fallback (nonempty group
    member)⟩

/-- Every active vertex collapses into the retained representative list.

A vertex inside a group collapses to one of its displayed heads. An outside
active vertex survives the filter at its original occurrence. -/
theorem collapse_supported (fallback : Alpha) {active : List Alpha} {groups : List (List Alpha)}
    (nonempty : ∀ group ∈ groups, group ≠ []) {vertex : Alpha} (member : vertex ∈ active) :
    collapse fallback groups vertex ∈ DisjointVertexGroups.representatives fallback active groups
      := by
  by_cases inside : vertex ∈ groups.flatten
  · rcases collapse_spec fallback groups vertex with same | ⟨group, present, _, same⟩
    · obtain ⟨group, groupMember, inGroup⟩ := SimpleBoundaryCycles.mem_flatten.mp inside
      -- The structural specification can choose its left alternative only
      -- when the vertex is already the selected head.
      have headEq : collapse fallback groups vertex ∈ groups.map (List.headD · fallback) := by
        clear same group groupMember inGroup
        induction groups with
        | nil => exact (List.not_mem_nil inside).elim
        | cons group groups ih =>
            by_cases inHead : vertex ∈ group
            · rw [collapse, if_pos inHead]; exact List.mem_cons_self
            · rw [collapse, if_neg inHead]
              exact List.mem_cons_of_mem _ (ih (fun entry present => nonempty entry (List.mem_cons_of_mem _ present))
                ((Membership.mem_append.mp inside).resolve_left inHead))
      exact (Membership.mem_append.mpr (.inr headEq))
    · rw [same]
      exact Membership.mem_append.mpr (.inr (Map.mem_map_of_mem present))
  · rw [collapse_outside fallback groups vertex inside]
    exact Membership.mem_append.mpr (.inl (Filter.mem_filter.mpr ⟨member, decide_eq_true inside⟩))

/-- Every representative is active when every group vertex is active.

The outside filter retains active membership. Each group head belongs to its
nonempty group and hence to the supplied active list. -/
theorem representatives_active (fallback : Alpha) {active : List Alpha} {groups : List (List Alpha)}
    (nonempty : ∀ group ∈ groups, group ≠ []) (included : ∀ vertex ∈ groups.flatten, vertex ∈ active)
    {vertex : Alpha} (member : vertex ∈ DisjointVertexGroups.representatives fallback active groups) : vertex ∈ active
      := by
  rcases Membership.mem_append.mp member with outside | head
  · exact (Filter.mem_filter.mp outside).1
  · obtain ⟨group, present, same⟩ := Map.mem_map.mp head
    rw [← same]
    exact included _ (SimpleBoundaryCycles.mem_flatten.mpr ⟨group, present, head_mem fallback
      (nonempty group present)⟩)

/-- Collapse fixes every retained representative of nonempty disjoint groups.

An outside representative is fixed by absence from every group. A retained
head is fixed by its membership in the corresponding disjoint group. -/
theorem collapse_representative (fallback : Alpha) {active : List Alpha} {groups : List (List Alpha)}
    (unique : groups.flatten.Nodup) (nonempty : ∀ group ∈ groups, group ≠ [])
    {vertex : Alpha} (member : vertex ∈ DisjointVertexGroups.representatives fallback active groups) :
      collapse fallback groups vertex = vertex := by
  rcases Membership.mem_append.mp member with outside | head
  · exact collapse_outside fallback groups vertex (of_decide_eq_true (Filter.mem_filter.mp
      outside).2)
  · obtain ⟨group, present, same⟩ := Map.mem_map.mp head
    rw [← same]
    exact collapse_member fallback unique present (head_mem fallback (nonempty
      group present))

/-- Count retained representatives by replacing each disjoint group's vertices with one head.

The disjoint flattened groups are included in the unique active list. Filtering
partitions that list, and each group contributes one retained head. -/
theorem representatives_count (fallback : Alpha) {active : List Alpha} {groups : List (List Alpha)}
    (activeUnique : active.Nodup) (unique : groups.flatten.Nodup)
    (included : ∀ vertex ∈ groups.flatten, vertex ∈ active) :
    (DisjointVertexGroups.representatives fallback active groups).length + groups.flatten.length = active.length +
      groups.length := by
  let inside := active.filter (fun vertex => decide (vertex ∈ groups.flatten))
  have insideUnique : inside.Nodup := Filter.pairwise_filter _ activeUnique
  have insideIff (vertex : Alpha) : vertex ∈ inside ↔ vertex ∈ groups.flatten :=
    ⟨fun member => of_decide_eq_true (Filter.mem_filter.mp member).2,
      fun member => Filter.mem_filter.mpr ⟨included vertex member, decide_eq_true member⟩⟩
  have sameLength : inside.length = groups.flatten.length := Nat.le_antisymm
    (Nodup.nodup_length_le_of_mem insideUnique unique (fun vertex member => (insideIff vertex).mp member))
    (Nodup.nodup_length_le_of_mem unique insideUnique (fun vertex member => (insideIff vertex).mpr member))
  have partition : (active.filter (fun vertex => decide (vertex ∉ groups.flatten))).length + inside.length =
    active.length := by
    dsimp only [inside]
    clear insideUnique insideIff sameLength included activeUnique
    induction active with
    | nil => rfl
    | cons vertex active ih =>
        by_cases member : vertex ∈ groups.flatten
        · rw [Filter.filter_cons_of_pos (predicate := fun vertex => decide (vertex ∈ groups.flatten)) (head := vertex)
            (decide_eq_true member),
            Filter.filter_cons_of_neg (predicate := fun vertex => decide (vertex ∉ groups.flatten)) (head := vertex) (by
              rw [decide_eq_false (not_not_intro member)]; intro same; cases same)]
          change _ + (active.filter _).length + 1 = _ + 1
          omega0
        · rw [Filter.filter_cons_of_pos (predicate := fun vertex => decide (vertex ∉ groups.flatten)) (head := vertex)
            (decide_eq_true member),
            Filter.filter_cons_of_neg (predicate := fun vertex => decide (vertex ∈ groups.flatten)) (head := vertex) (by
              rw [decide_eq_false member]; intro same; cases same)]
          change (_ + 1) + _ = _ + 1
          omega0
  rw [DisjointVertexGroups.representatives, Append.length_append, Map.length_map]
  omega

/-- An assignment constant on each displayed group has identical values before and after contraction. This is the
factorization law, including vertices outside every contracted boundary. -/
theorem factor {Beta : Type} (fallback : Alpha) {groups : List (List Alpha)}
    (nonempty : ∀ group ∈ groups, group ≠ []) (values : Alpha → Beta)
    (constant : ∀ group ∈ groups, ∀ first ∈ group, ∀ last ∈ group, values first = values last)
    (vertex : Alpha) : values (collapse fallback groups vertex) = values vertex := by
  rcases collapse_spec fallback groups vertex with same | ⟨group, member, inside, same⟩
  · rw [same]
  · rw [same]
    exact constant group member _ (head_mem fallback (nonempty group member)) vertex inside

end BoundaryContraction.DisjointVertexGroups

open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)

set_option genInjectivity false in
/-- Retain representative vertices and the complete normalization table.

The cached cycle source groups preserve their physical boundary owner. The
active list, fallback and exact readback equations certify every retained value. -/
structure BoundaryContraction {count : Nat} {occurrences : List (Stokes.OrientedEdge count)}
    (boundary : PolygonStokes.BoundaryCycleDecomposition occurrences) (active : List (Fin count)) where
  /-- Retained active vertex used when a total construction needs a default. -/ fallback : Fin count
  /-- The fallback is an actual active vertex. -/ fallback_active : fallback ∈ active
  /-- Cached source-vertex lists of the physical boundary cycles. -/ groups : List (List (Fin count))
  /-- The groups are precisely the source lists of the original boundary cycles. -/ groups_eq : groups =
    boundary.cycles.map (List.map OrientedEdge.start)
  /-- Cached active interior vertices and one head per physical cycle. -/ representatives : List (Fin count)
  /-- The representative list is the explicit disjoint-group construction. -/ representatives_eq : representatives =
    _root_.Purelib.Topology.Surface.Boundary.BoundaryContraction.DisjointVertexGroups.representatives fallback active
      groups
  /-- Cached normalization value for every original vertex index. -/ normalize : Data.Vector (Fin count)
    count
  /-- Each cached value agrees with collapse through the retained groups. -/ normalize_eq : ∀ vertex, normalize vertex =
    _root_.Purelib.Topology.Surface.Boundary.BoundaryContraction.DisjointVertexGroups.collapse fallback groups vertex
  /-- The supplied active vertex list has no duplicates. -/ active_unique : active.Nodup
  /-- Every vertex in the physical-cycle groups is active. -/ boundary_active : ∀ vertex ∈ groups.flatten, vertex ∈
    active

constructive_injectivity BoundaryContraction

namespace BoundaryContraction

variable {count : Nat} {occurrences : List (Stokes.OrientedEdge count)}
  {boundary : PolygonStokes.BoundaryCycleDecomposition occurrences} {active : List (Fin count)}

/-- Flattening cycle source lists agrees with taking sources after flattening cycles.

Both constructions traverse the cycles in order. Mapping distributes over
the displayed concatenations and retains every source occurrence. -/
theorem sources_flatten (cycles : List (List (Stokes.OrientedEdge count))) :
    (cycles.map (List.map OrientedEdge.start)).flatten = cycles.flatten.map OrientedEdge.start := by
  induction cycles with
  | nil => rfl
  | cons cycle cycles ih => rw [List.map_cons, List.flatten_cons, List.flatten_cons, Map.map_append, ih]

/-- Cache physical-cycle groups, active representatives, and the full normalization table.

The supplied active list is unique and contains all physical-boundary sources; its retained fallback provides a valid
representative. -/
@[expose]
def build (boundary : PolygonStokes.BoundaryCycleDecomposition occurrences) (active : List (Fin count))
    (fallback : Fin count) (fallback_active : fallback ∈ active) (unique : active.Nodup)
    (boundary_active : ∀ vertex ∈ boundary.cycles.flatten.map OrientedEdge.start, vertex ∈ active) :
    BoundaryContraction boundary active :=
  let groups := boundary.cycles.map (List.map OrientedEdge.start)
  { fallback := fallback
    fallback_active := fallback_active
    groups := groups
    groups_eq := rfl
    representatives := DisjointVertexGroups.representatives fallback active groups
    representatives_eq := rfl
    normalize := Data.Vector.Basic.vectorOfFn (DisjointVertexGroups.collapse fallback groups)
    normalize_eq := Data.Vector.Basic.vectorOfFn_apply _
    active_unique := unique
    boundary_active := fun vertex member => boundary_active vertex (sources_flatten boundary.cycles
      ▸ member) }

/-- The flattened cached groups are exactly the physical cycle source occurrences. -/
theorem groups_flatten (contraction : BoundaryContraction boundary active) :
    contraction.groups.flatten = boundary.cycles.flatten.map OrientedEdge.start := by
  rw [contraction.groups_eq, sources_flatten]

/-- No vertex occurs twice among the retained physical-cycle groups. -/
theorem groups_unique (contraction : BoundaryContraction boundary active) :
  contraction.groups.flatten.Nodup := by
  rw [contraction.groups_flatten]
  exact boundary.sources_unique

/-- Every retained physical-cycle group is nonempty.

Each retained group is the source map of a physical cycle. The original
minimum cycle length excludes an empty source map. -/
theorem groups_nonempty (contraction : BoundaryContraction boundary active) :
    ∀ group ∈ contraction.groups, group ≠ [] := by
  intro group member empty
  rw [contraction.groups_eq] at member
  obtain ⟨cycle, present, same⟩ := Map.mem_map.mp member
  have size := congrArg List.length (same.trans empty)
  rw [Map.length_map, List.length_nil] at size
  have lower := boundary.min_length cycle present
  omega

/-- The cached contracted representative list has no duplicates. -/
theorem unique (contraction : BoundaryContraction boundary active) :
  contraction.representatives.Nodup := by
  rw [contraction.representatives_eq]
  exact DisjointVertexGroups.representatives_unique contraction.fallback contraction.active_unique
    contraction.groups_unique contraction.groups_nonempty

/-- Normalizing an active vertex returns a retained representative. -/
theorem supported (contraction : BoundaryContraction boundary active) {vertex : Fin count} (member :
  vertex ∈ active) :
    contraction.normalize vertex ∈ contraction.representatives := by
  rw [contraction.normalize_eq, contraction.representatives_eq]
  exact DisjointVertexGroups.collapse_supported contraction.fallback contraction.groups_nonempty member

/-- Every retained representative belongs to the original active vertex list. -/
theorem representative_active (contraction : BoundaryContraction boundary active) {vertex : Fin
  count}
    (member : vertex ∈ contraction.representatives) : vertex ∈ active := by
  rw [contraction.representatives_eq] at member
  exact DisjointVertexGroups.representatives_active contraction.fallback contraction.groups_nonempty
    contraction.boundary_active member

/-- The cached normalization fixes retained representatives. -/
theorem readback (contraction : BoundaryContraction boundary active) {vertex : Fin count}
    (member : vertex ∈ contraction.representatives) : contraction.normalize vertex = vertex := by
  rw [contraction.normalize_eq]
  rw [contraction.representatives_eq] at member
  exact DisjointVertexGroups.collapse_representative contraction.fallback contraction.groups_unique
    contraction.groups_nonempty member

/-- Contracting each physical boundary cycle replaces its source vertices with one representative.

The original active list and cycle decomposition supply the inclusion and
disjointness certificates. Mapped source counts preserve their original lengths. -/
theorem count_eq (contraction : BoundaryContraction boundary active) :
    contraction.representatives.length + boundary.cycles.flatten.length = active.length + boundary.cycles.length := by
  have size := DisjointVertexGroups.representatives_count contraction.fallback contraction.active_unique
    contraction.groups_unique contraction.boundary_active
  rw [← contraction.representatives_eq, contraction.groups_flatten, Map.length_map,
    contraction.groups_eq, Map.length_map] at size
  exact size

/-- Equality in the retained table has the precise geometric explanation: the original indices were equal, or both lie
on one displayed cycle.

The cached table has the collapse readback equation. Nonempty disjoint cycle
source lists give the alternatives on the original vertex indices. -/
theorem normalize_eq_iff (contraction : BoundaryContraction boundary active) (first last : Fin
  count) :
    contraction.normalize first = contraction.normalize last ↔ first = last ∨
      ∃ cycle ∈ boundary.cycles, first ∈ cycle.map OrientedEdge.start ∧ last ∈ cycle.map OrientedEdge.start := by
  rw [contraction.normalize_eq, contraction.normalize_eq]
  have collapseSame := DisjointVertexGroups.collapse_eq_iff contraction.fallback contraction.groups_unique
    contraction.groups_nonempty first last
  constructor
  · intro same
    rcases collapseSame.mp same with same | ⟨group, member, inside⟩
    · exact .inl same
    · rw [contraction.groups_eq] at member
      obtain ⟨cycle, present, equal⟩ := Map.mem_map.mp member
      exact .inr ⟨cycle, present, equal ▸ inside⟩
  · intro same
    apply collapseSame.mpr
    rcases same with same | ⟨cycle, member, inside⟩
    · exact .inl same
    · refine .inr ⟨cycle.map OrientedEdge.start, ?_, inside⟩
      rw [contraction.groups_eq]
      exact Map.mem_map_of_mem member

/-- Both endpoints of every retained physical boundary edge normalize equally. -/
theorem edge_collapsed (contraction : BoundaryContraction boundary active) {edge :
  Stokes.OrientedEdge count}
    (member : edge ∈ boundary.cycles.flatten) : contraction.normalize edge.start = contraction.normalize edge.finish :=
      by
  obtain ⟨cycle, cycleMember, member⟩ := SimpleBoundaryCycles.mem_flatten.mp member
  obtain ⟨anchor, closed⟩ := boundary.closed cycle cycleMember
  exact (contraction.normalize_eq_iff _ _).mpr (.inr
    ⟨cycle, cycleMember, Map.mem_map_of_mem member, SimpleBoundaryCycles.finish_mem closed member⟩)

/-- An assignment constant along every path edge has equal endpoint values. -/
private theorem path_constant {Beta : Type} (values : Fin count → Beta)
    {word : List (Stokes.OrientedEdge count)} {first last : Fin count}
    (path : Purelib.Topology.Chain.PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish word first last)
    (constant : ∀ edge ∈ word, values edge.start = values edge.finish) :
    values first = values last := by
  induction path with
  | nil => rfl
  | @cons edge tail last path ih =>
      exact (constant edge List.mem_cons_self).trans (ih (fun entry member => constant entry (List.mem_cons_of_mem _
        member)))

/-- An assignment constant along a path gives each source the final endpoint's value.

At a displayed head source, edge constancy joins the remaining path endpoint
equality. Sources in the tail retain that tail path and the same edge evidence. -/
private theorem path_sources {Beta : Type} (values : Fin count → Beta)
    {word : List (Stokes.OrientedEdge count)} {first last vertex : Fin count}
    (path : Purelib.Topology.Chain.PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish word first last)
    (constant : ∀ edge ∈ word, values edge.start = values edge.finish)
    (member : vertex ∈ word.map OrientedEdge.start) : values vertex = values last := by
  induction path with
  | nil => exact (List.not_mem_nil member).elim
  | @cons edge tail last path ih =>
      have tailConstant := fun entry member => constant entry (List.mem_cons_of_mem _ member)
      rcases Membership.mem_cons.mp member with rfl | inTail
      · exact (constant edge List.mem_cons_self).trans (path_constant values path tailConstant)
      · exact ih tailConstant inTail

/-- Any assignment constant on the actual physical edges factors through the cached normalization, with no separate
cycle-constancy premise. -/
theorem factor {Beta : Type} (contraction : BoundaryContraction boundary active) (values : Fin count
  → Beta)
    (constant : ∀ edge ∈ boundary.cycles.flatten, values edge.start = values edge.finish) (vertex : Fin count) :
    values (contraction.normalize vertex) = values vertex := by
  rw [contraction.normalize_eq]
  apply DisjointVertexGroups.factor contraction.fallback contraction.groups_nonempty values ?_ vertex
  intro group member first firstMember last lastMember
  rw [contraction.groups_eq] at member
  obtain ⟨cycle, cycleMember, equal⟩ := Map.mem_map.mp member
  obtain ⟨anchor, closed⟩ := boundary.closed cycle cycleMember
  have cycleConstant := fun edge member => constant edge (SimpleBoundaryCycles.mem_flatten.mpr ⟨cycle, cycleMember,
    member⟩)
  rw [← equal] at firstMember lastMember
  exact (path_sources values closed cycleConstant firstMember).trans
    (path_sources values closed cycleConstant lastMember).symm

end BoundaryContraction

end Purelib.Topology.Surface.Boundary
