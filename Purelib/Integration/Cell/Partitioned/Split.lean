module
public import Purelib.Integration.Cell.Partitioned
public import Purelib.Integration.Cell.Refinement
public import Purelib.Data.List.OrderedGroups
import Purelib.Data.List.Filter
import Purelib.Data.List.Nodup
import Purelib.Data.List.Map
import Purelib.Data.List.Flatten
import Purelib.Tactic.Ring

/-!
# Indexed splits of partitioned integration cells

Ordered children retain their actual indexed parents, exact domain lengths
and narrowed ranges. Grouping them by the original parent index constructs
the original finite cell-split relation without replacing either owner.
-/

public section

namespace Purelib.Integration.PartitionedCells

open Purelib.Data.Rat
open Purelib.Integration.Partition

set_option genInjectivity false in
/-- Proof that ordered children narrow the original indexed partitioned cells.

The original partition, cells, child partition and actual functions remain
parameters. Every child supplies its original parent index, exact length and
range narrowing; the retained ordered entries read back to the child partition. -/
structure IndexedRefinement {α β : Type} {partition : Unit.Normalized} {cells : List (IntegrationCell α)}
    {domain : α → Partition.Interval} (parents : PartitionedCells partition cells domain)
    (childPartition : Unit.Normalized) (entries : List β) (child : β → Partition.Interval)
    (owner : (entry : β) → Ownership.IntervalOwner partition.intervals (child entry))
    (selected : β → IntegrationCell α) (candidate : β → IntegrationCell α) : Prop where
  /-- The original ordered children are exactly the child partition intervals. -/ domains_eq :
    entries.map child = childPartition.intervals
  /-- Every retained child is a valid unit interval. -/ valid : ∀ entry, (child entry).Valid
  /-- Each child selects the actual cell at its original parent index. -/ selected_read : ∀ entry,
    Purelib.Data.List.getElem? cells (owner entry).index = some (selected entry)
  /-- The selected cell has the original owner domain. -/ selected_domain : ∀ entry,
    domain (selected entry).item = (owner entry).parent
  /-- The candidate child retains its exact original domain length. -/ weight : ∀ entry,
    (candidate entry).weight = (child entry).signedLength
  /-- The candidate range narrows its actual original parent range. -/ ranges : ∀ entry,
    (selected entry).lower ≤ (candidate entry).lower ∧ (candidate entry).upper ≤ (selected entry).upper
  /-- Original parent indices are nondecreasing in retained child order. -/ ordered :
    entries.Pairwise (fun first second => (owner first).index ≤ (owner second).index)

namespace IndexedRefinement

variable {α β : Type} {partition : Unit.Normalized} {cells : List (IntegrationCell α)}
  {domain : α → Partition.Interval} {parents : PartitionedCells partition cells domain}
  {childPartition : Unit.Normalized} {entries : List β} {child : β → Partition.Interval}
  {owner : (entry : β) → Ownership.IntervalOwner partition.intervals (child entry)}
  {selected : β → IntegrationCell α} {candidate : β → IntegrationCell α}

/-- The children selected at an original parent index, in their retained order. -/
@[expose] def childrenAt (_spec : IndexedRefinement parents childPartition entries child owner selected candidate)
    (index : Nat) : List (IntegrationCell α) :=
  (entries.filter (fun entry => decide ((owner entry).index = index))).map candidate

/-- A child at the original parent index selects that exact original cell. -/
private theorem selected_eq_at (spec : IndexedRefinement parents childPartition entries child owner selected candidate)
    (entry : β) (index : Nat) (parent : IntegrationCell α)
    (parentRead : Purelib.Data.List.getElem? cells index = some parent) (same : (owner entry).index = index) :
    selected entry = parent := by
  have selectedRead := spec.selected_read entry
  have atIndex : Purelib.Data.List.getElem? cells index = some (selected entry) :=
    (congrArg (Purelib.Data.List.getElem? cells) same).symm.trans selectedRead
  exact Option.some.inj (atIndex.symm.trans parentRead)

/-- Different original parent indices select different original cells. -/
private theorem selected_ne_at (spec : IndexedRefinement parents childPartition entries child owner selected candidate)
    (entry : β) (index : Nat) (parent : IntegrationCell α)
    (parentRead : Purelib.Data.List.getElem? cells index = some parent) (different : (owner entry).index ≠ index) :
    parent ≠ selected entry := by
  intro equal
  have selectedRead := spec.selected_read entry
  rw [← equal] at selectedRead
  exact different (Purelib.Data.List.Nodup.getElem?_index_injective parents.cells_nodup selectedRead parentRead)

/-- Candidate weights sum to the same retained child-domain lengths. -/
private theorem candidate_weight_sum
    (spec : IndexedRefinement parents childPartition entries child owner selected candidate) :
    ∀ items : List β,
      integrationWeight (items.map candidate) = (items.map (fun entry => (child entry).signedLength)).sum
  | [] => rfl
  | entry :: remaining => by
      change (candidate entry).weight + integrationWeight (remaining.map candidate) =
        (child entry).signedLength + (remaining.map (fun other => (child other).signedLength)).sum
      rw [spec.weight entry, candidate_weight_sum spec remaining]

/-- Selecting one parent index retains exactly that parent's clamped child lengths. -/
private theorem filtered_lengths_eq_clamped
    (spec : IndexedRefinement parents childPartition entries child owner selected candidate)
    (index : Nat) (parent : IntegrationCell α) (parentRead : Purelib.Data.List.getElem? cells index = some parent) :
    ∀ items : List β,
      ((items.filter (fun entry => decide ((owner entry).index = index))).map
        (fun entry => (child entry).signedLength)).sum =
      (items.map (fun entry => (domain parent.item).clampedLength (child entry))).sum
  | [] => rfl
  | entry :: remaining => by
      have parentMember := Purelib.Data.List.mem_of_getElem? cells index parent parentRead
      have tail := filtered_lengths_eq_clamped spec index parent parentRead remaining
      by_cases same : (owner entry).index = index
      · rw [Purelib.Data.List.Filter.filter_cons_of_pos
          (predicate := fun (other : β) => decide ((owner other).index = index)) (decide_eq_true same)]
        have selectedEq := spec.selected_eq_at entry index parent parentRead same
        have length := parents.selected_clamped_length (spec.valid entry) (owner entry) (selected entry)
          (spec.selected_domain entry)
        rw [selectedEq] at length
        change (child entry).signedLength +
          ((remaining.filter (fun other => decide ((owner other).index = index))).map
            (fun other => (child other).signedLength)).sum =
          (domain parent.item).clampedLength (child entry) +
            (remaining.map (fun other => (domain parent.item).clampedLength (child other))).sum
        rw [length, tail]
      · have rejected : ¬ decide ((owner entry).index = index) = true := by
          intro accepted
          exact same (of_decide_eq_true accepted)
        rw [Purelib.Data.List.Filter.filter_cons_of_neg
          (predicate := fun (other : β) => decide ((owner other).index = index)) rejected]
        have selectedMember := Purelib.Data.List.mem_of_getElem? cells (owner entry).index (selected entry)
          (spec.selected_read entry)
        have zero := parents.other_clamped_length (spec.valid entry) (owner entry) (selected entry) parent
          selectedMember parentMember (spec.selected_domain entry)
          (spec.selected_ne_at entry index parent parentRead same)
        change ((remaining.filter (fun other => decide ((owner other).index = index))).map
            (fun other => (child other).signedLength)).sum =
          (domain parent.item).clampedLength (child entry) +
            (remaining.map (fun other => (domain parent.item).clampedLength (child other))).sum
        rw [zero, Fraction.Field.zero_add, tail]

/-- The selected children conserve the exact original parent weight. -/
theorem childrenAt_weight (spec : IndexedRefinement parents childPartition entries child owner selected candidate)
    (index : Nat) (parent : IntegrationCell α) (parentRead : Purelib.Data.List.getElem? cells index = some parent) :
    integrationWeight (spec.childrenAt index) = parent.weight := by
  have parentMember := Purelib.Data.List.mem_of_getElem? cells index parent parentRead
  have parentDomain : domain parent.item ∈ partition.intervals := by
    rw [← parents.1]
    exact Purelib.Data.List.Map.mem_map_of_mem parentMember
  have lengths := Partition.Interval.sum_clampedLength (domain parent.item) (entries.map child)
  rw [Purelib.Data.List.Map.map_map, Purelib.Data.List.Map.map_map] at lengths
  change (entries.map (fun entry => (domain parent.item).clampedLength (child entry))).sum =
    Partition.Interval.lengthSum (entries.map (fun entry =>
      ⟨(domain parent.item).clamp (child entry).start, (domain parent.item).clamp (child entry).finish⟩)) at lengths
  have total := childPartition.clamped_lengthSum (domain parent.item)
    (partition.valid (domain parent.item) parentDomain)
  rw [← spec.domains_eq, Purelib.Data.List.Map.map_map] at total
  change Partition.Interval.lengthSum (entries.map (fun entry =>
    ⟨(domain parent.item).clamp (child entry).start, (domain parent.item).clamp (child entry).finish⟩)) =
      (domain parent.item).signedLength at total
  unfold childrenAt
  rw [candidate_weight_sum spec, filtered_lengths_eq_clamped spec index parent parentRead entries, lengths, total,
    parents.2 parent parentMember]

/-- Every child selected at the original parent index narrows that parent's range. -/
theorem childrenAt_ranges (spec : IndexedRefinement parents childPartition entries child owner selected candidate)
    (index : Nat) (parent : IntegrationCell α) (parentRead : Purelib.Data.List.getElem? cells index = some parent) :
    ∀ cell ∈ spec.childrenAt index, parent.lower ≤ cell.lower ∧ cell.upper ≤ parent.upper := by
  intro cell member
  change cell ∈ (entries.filter (fun entry => decide ((owner entry).index = index))).map candidate at member
  obtain ⟨entry, selectedMember, equal⟩ := Purelib.Data.List.Map.mem_map.mp member
  cases equal
  have same := of_decide_eq_true ((Purelib.Data.List.Filter.mem_filter).mp selectedMember).2
  have selectedEq := spec.selected_eq_at entry index parent parentRead same
  have bounds := spec.ranges entry
  rw [selectedEq] at bounds
  exact bounds

/-- The selected original-index children form one certified split of that exact parent. -/
@[expose] def splitAt (spec : IndexedRefinement parents childPartition entries child owner selected candidate)
    (index : Nat) (parent : IntegrationCell α) (parentRead : Purelib.Data.List.getElem? cells index = some parent) :
    IntegrationSplit parent where
  children := spec.childrenAt index
  weight_conserved := spec.childrenAt_weight index parent parentRead
  lower_refines := fun cell member => (spec.childrenAt_ranges index parent parentRead cell member).1
  upper_refines := fun cell member => (spec.childrenAt_ranges index parent parentRead cell member).2

/-- Group the original candidate children by their retained parent indices. -/
@[expose] def groups (_spec : IndexedRefinement parents childPartition entries child owner selected candidate) :
    List (List (IntegrationCell α)) :=
  (Purelib.Data.List.OrderedGroups.groups (fun entry => (owner entry).index) 0 cells.length entries).map
    (List.map candidate)

/-- The actual groups retain one position for each original parent occurrence. -/
theorem groups_length (spec : IndexedRefinement parents childPartition entries child owner selected candidate) :
    spec.groups.length = cells.length := by
  unfold groups
  rw [Purelib.Data.List.Map.length_map, Purelib.Data.List.OrderedGroups.groups_length]

/-- Every retained child index addresses an actual original parent cell. -/
private theorem indices_bound (spec : IndexedRefinement parents childPartition entries child owner selected candidate) :
    ∀ entry ∈ entries, 0 ≤ (owner entry).index ∧ (owner entry).index < 0 + cells.length := by
  intro entry _
  constructor
  · exact Nat.zero_le _
  · rw [Nat.zero_add]
    exact Purelib.Data.List.index_lt_length_of_getElem? cells (owner entry).index (selected entry)
      (spec.selected_read entry)

/-- The original ordered groups flatten to the actual candidate child list. -/
theorem groups_flatten (spec : IndexedRefinement parents childPartition entries child owner selected candidate) :
    spec.groups.flatten = entries.map candidate := by
  have flattened := Purelib.Data.List.OrderedGroups.groups_flatten (fun entry : β => (owner entry).index)
    cells.length 0 entries spec.ordered spec.indices_bound
  change ((Purelib.Data.List.OrderedGroups.groups (fun entry : β => (owner entry).index) 0 cells.length entries).map
    (List.map candidate)).flatten = entries.map candidate
  rw [← Purelib.Data.List.Flatten.map_flatten, flattened]

/-- Each original group is exactly the children at its parent index. -/
theorem groups_getElem? (spec : IndexedRefinement parents childPartition entries child owner selected candidate)
    (index : Nat) (bound : index < cells.length) :
    Purelib.Data.List.getElem? spec.groups index = some (spec.childrenAt index) := by
  have selectedGroup := Purelib.Data.List.OrderedGroups.groups_getElem? (fun entry : β => (owner entry).index)
    cells.length 0 entries index bound spec.ordered spec.indices_bound
  rw [Nat.zero_add] at selectedGroup
  unfold groups childrenAt
  rw [Purelib.Data.List.getElem?_map, selectedGroup]
  rfl

/-- The actual candidate child frontier is a finite split refinement of the original cells. -/
theorem refines (spec : IndexedRefinement parents childPartition entries child owner selected candidate) :
    IntegrationFrontierRefines (entries.map candidate) cells := by
  have splits : ∀ index parent children, Purelib.Data.List.getElem? cells index = some parent →
      Purelib.Data.List.getElem? spec.groups index = some children →
        ∃ split : IntegrationSplit parent, split.children = children := by
    intro index parent children parentRead childrenRead
    have bound := Purelib.Data.List.index_lt_length_of_getElem? cells index parent parentRead
    have selectedGroup := spec.groups_getElem? index bound
    have equal : spec.childrenAt index = children := Option.some.inj (selectedGroup.symm.trans childrenRead)
    exact ⟨spec.splitAt index parent parentRead, equal⟩
  have refines := IntegrationFrontierRefines.of_indexed_splits cells spec.groups spec.groups_length splits
  rw [spec.groups_flatten] at refines
  exact refines

end IndexedRefinement

end Purelib.Integration.PartitionedCells

end
