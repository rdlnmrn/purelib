module
public import Purelib.Integration.Cell.Basic
public import Purelib.Integration.Partition.Unit.Common
public import Purelib.Integration.Partition.Length
import Purelib.Data.List.GetD
import Purelib.Data.List.Map
import Purelib.Data.List.Membership
import Purelib.Data.List.Pairwise
import Purelib.Data.List.Rat.Linear
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

/-!
# Exact ownership and weights for partitioned integration cells

The certificate is a view of the original partition, ordered cells and
payload-domain function. It stores no replacement owner or copied cells.
Indexed children retain their original parent occurrences and redistribute
the original lengths exactly.
-/

public section

namespace Purelib.Integration

open Purelib.Data.Rat
open Purelib.Integration.Partition
open Purelib.Data.List.Rat.Linear

/-- Certify that original ordered cells have exactly the original partition domains and lengths. -/
@[expose] def PartitionedCells {α : Type} (partition : Unit.Normalized) (cells : List (IntegrationCell α))
    (domain : α → Partition.Interval) : Prop :=
  cells.map (fun cell => domain cell.item) = partition.intervals ∧
    ∀ cell ∈ cells, cell.weight = (domain cell.item).signedLength

namespace PartitionedCells

/-- Original cells with the same original domain occurrence are identical. -/
theorem cell_eq_of_domain_eq {α : Type} {partition : Unit.Normalized} {cells : List (IntegrationCell α)}
    {domain : α → Partition.Interval} (certificate : PartitionedCells partition cells domain)
    {first second : IntegrationCell α} (firstMember : first ∈ cells) (secondMember : second ∈ cells)
    (same : domain first.item = domain second.item) : first = second := by
  have unique : (cells.map (fun cell => domain cell.item)).Nodup := by
    rw [certificate.1]
    exact partition.intervals_nodup
  exact Purelib.Data.List.Map.equal_of_map_unique (fun cell => domain cell.item) unique firstMember secondMember same

/-- The original ordered cells have no repeated occurrences. -/
theorem cells_nodup {α : Type} {partition : Unit.Normalized} {cells : List (IntegrationCell α)}
    {domain : α → Partition.Interval} (certificate : PartitionedCells partition cells domain) : cells.Nodup := by
  have original : (cells.map (fun cell => domain cell.item)).Nodup := by
    rw [certificate.1]
    exact partition.intervals_nodup
  have recover : ∀ entries : List (IntegrationCell α),
      (entries.map (fun cell => domain cell.item)).Nodup → entries.Nodup := by
    intro entries
    induction entries with
    | nil => intro _; exact List.Pairwise.nil
    | cons cell remaining inductionHypothesis =>
        intro unique
        have parts := List.pairwise_cons.mp unique
        apply List.pairwise_cons.mpr
        constructor
        · intro other member equal
          apply parts.1 (domain other.item) (Purelib.Data.List.Map.mem_map_of_mem member)
          exact congrArg (fun entry => domain entry.item) equal
        · exact inductionHypothesis parts.2
  exact recover cells original

/-- An owned child contributes its entire length to its selected original parent. -/
theorem selected_clamped_length {α : Type} {partition : Unit.Normalized} {cells : List (IntegrationCell α)}
    {domain : α → Partition.Interval} (_certificate : PartitionedCells partition cells domain)
    {child : Partition.Interval} (valid : child.Valid) (owner : Ownership.IntervalOwner partition.intervals child)
    (selected : IntegrationCell α) (selectedDomain : domain selected.item = owner.parent) :
    (domain selected.item).clampedLength child = child.signedLength := by
  rw [selectedDomain]
  exact owner.clamp_child_length valid

/-- An owned child contributes zero clamped length to any other original cell. -/
theorem other_clamped_length {α : Type} {partition : Unit.Normalized} {cells : List (IntegrationCell α)}
    {domain : α → Partition.Interval} (certificate : PartitionedCells partition cells domain)
    {child : Partition.Interval} (valid : child.Valid) (owner : Ownership.IntervalOwner partition.intervals child)
    (selected other : IntegrationCell α) (selectedMember : selected ∈ cells) (otherMember : other ∈ cells)
    (selectedDomain : domain selected.item = owner.parent) (distinct : other ≠ selected) :
    (domain other.item).clampedLength child = 0 := by
  have inPartition : domain other.item ∈ partition.intervals := by
    rw [← certificate.1]
    exact Purelib.Data.List.Map.mem_map_of_mem otherMember
  have different : owner.parent ≠ domain other.item := by
    intro equal
    have cellEqual := certificate.cell_eq_of_domain_eq otherMember selectedMember (equal.symm.trans selectedDomain.symm)
    exact distinct cellEqual
  exact owner.other_clamped_length valid (domain other.item) inPartition different

/-- Nonselected original cells contribute zero to one child's clamped sum. -/
private theorem other_clamped_sum_zero {α : Type} {partition : Unit.Normalized} {cells : List (IntegrationCell α)}
    {domain : α → Partition.Interval} (certificate : PartitionedCells partition cells domain)
    {child : Partition.Interval} (valid : child.Valid) (owner : Ownership.IntervalOwner partition.intervals child)
    (selected : IntegrationCell α) (selectedMember : selected ∈ cells)
    (selectedDomain : domain selected.item = owner.parent)
    (value : IntegrationCell α → Fraction.Rational) : ∀ entries : List (IntegrationCell α),
      (∀ cell ∈ entries, cell ∈ cells) → (∀ cell ∈ entries, cell ≠ selected) →
      (entries.map (fun cell => (domain cell.item).clampedLength child * value cell)).sum = 0
  | [], _, _ => rfl
  | cell :: remaining, subset, distinct => by
      have zero := certificate.other_clamped_length valid owner selected cell selectedMember
        (subset cell List.mem_cons_self) selectedDomain (distinct cell List.mem_cons_self)
      have tail := other_clamped_sum_zero certificate valid owner selected selectedMember selectedDomain value remaining
        (fun other member => subset other (List.mem_cons_of_mem cell member))
        (fun other member => distinct other (List.mem_cons_of_mem cell member))
      change (domain cell.item).clampedLength child * value cell +
        (remaining.map (fun other => (domain other.item).clampedLength child * value other)).sum = 0
      rw [zero, Fraction.Field.zero_mul_direct, Fraction.Field.zero_add]
      exact tail

/-- One child assigns its exact weighted value to its selected original parent occurrence. -/
theorem clamped_sum_eq_selected {α : Type} {partition : Unit.Normalized} {cells : List (IntegrationCell α)}
    {domain : α → Partition.Interval} (certificate : PartitionedCells partition cells domain)
    {child : Partition.Interval} (valid : child.Valid) (owner : Ownership.IntervalOwner partition.intervals child)
    (selected : IntegrationCell α) (selectedMember : selected ∈ cells)
    (selectedDomain : domain selected.item = owner.parent)
    (value : IntegrationCell α → Fraction.Rational) :
    (cells.map (fun cell => (domain cell.item).clampedLength child * value cell)).sum =
      child.signedLength * value selected := by
  have general : ∀ entries : List (IntegrationCell α),
      (∀ cell ∈ entries, cell ∈ cells) → entries.Nodup → selected ∈ entries →
        (entries.map (fun cell => (domain cell.item).clampedLength child * value cell)).sum =
          child.signedLength * value selected := by
    intro entries
    induction entries with
    | nil => intro _ _ member; nomatch member
    | cons cell remaining inductionHypothesis =>
        intro subset unique member
        have parts := List.pairwise_cons.mp unique
        have tailSubset : ∀ other ∈ remaining, other ∈ cells :=
          fun other present => subset other (List.mem_cons_of_mem cell present)
        rcases Purelib.Data.List.Membership.mem_cons.mp member with first | later
        · cases first
          have tail := other_clamped_sum_zero certificate valid owner selected selectedMember selectedDomain value
            remaining
            tailSubset (fun other present equal => (parts.1 other present equal.symm).elim)
          have length := owner.clamp_child_length valid
          rw [← selectedDomain] at length
          change (domain selected.item).clampedLength child = child.signedLength at length
          change (domain selected.item).clampedLength child * value selected +
            (remaining.map (fun other => (domain other.item).clampedLength child * value other)).sum = _
          rw [length, tail]
          ring1
        · have different : cell ≠ selected := parts.1 selected later
          have zero := certificate.other_clamped_length valid owner selected cell selectedMember
            (subset cell List.mem_cons_self) selectedDomain different
          have tail := inductionHypothesis tailSubset parts.2 later
          change (domain cell.item).clampedLength child * value cell +
            (remaining.map (fun other => (domain other.item).clampedLength child * value other)).sum = _
          rw [zero, Fraction.Field.zero_mul_direct, Fraction.Field.zero_add]
          exact tail
  exact general cells (fun _ member => member) certificate.cells_nodup selectedMember

/-- Select the actual original cell at a child's indexed parent occurrence. -/
@[expose] def cellAtOwner {α : Type} {partition : Unit.Normalized} {cells : List (IntegrationCell α)}
    {domain : α → Partition.Interval} (certificate : PartitionedCells partition cells domain)
    {child : Partition.Interval} (owner : Ownership.IntervalOwner partition.intervals child) :
    {cell : IntegrationCell α // Purelib.Data.List.getElem? cells owner.index = some cell ∧
      domain cell.item = owner.parent} := by
  have domainReadback := congrArg
    (fun intervals : List Partition.Interval => Purelib.Data.List.getElem? intervals owner.index) certificate.1
  have present := domainReadback.trans owner.at_index
  rw [Purelib.Data.List.getElem?_map] at present
  cases selected : Purelib.Data.List.getElem? cells owner.index with
  | none =>
      rw [selected] at present
      nomatch present
  | some cell =>
      rw [selected] at present
      exact ⟨cell, rfl, Option.some.inj present⟩

/-- Redistribute exact original cell weights over a complete indexed child partition.

Each child keeps its original parent occurrence, and the child list reads
back to the actual normalized partition. Clamped lengths telescope to the
original weights for every supplied value on the retained parent cells. -/
theorem redistributed_weighted_sum {α β : Type} {partition : Unit.Normalized}
    {cells : List (IntegrationCell α)} {domain : α → Partition.Interval}
    (certificate : PartitionedCells partition cells domain) (childrenPartition : Unit.Normalized)
    (children : List β) (child : β → Partition.Interval) (selected : β → IntegrationCell α)
    (domains : children.map child = childrenPartition.intervals)
    (owners : ∀ entry ∈ children, ∃ owner : Ownership.IntervalOwner partition.intervals (child entry),
      selected entry ∈ cells ∧ domain (selected entry).item = owner.parent)
    (value : IntegrationCell α → Fraction.Rational) :
    (children.map (fun entry => (child entry).signedLength * value (selected entry))).sum =
      (cells.map (fun cell => cell.weight * value cell)).sum := by
  have childSum : ∀ entry ∈ children,
      (child entry).signedLength * value (selected entry) =
        (cells.map (fun cell => (domain cell.item).clampedLength (child entry) * value cell)).sum := by
    intro entry member
    have actual : child entry ∈ childrenPartition.intervals := by
      rw [← domains]
      exact Purelib.Data.List.Map.mem_map_of_mem member
    rcases owners entry member with ⟨owner, selectedMember, selectedDomain⟩
    exact (certificate.clamped_sum_eq_selected (childrenPartition.valid (child entry) actual) owner
      (selected entry) selectedMember selectedDomain value).symm
  have parentSum : ∀ cell ∈ cells,
      (children.map (fun entry => (domain cell.item).clampedLength (child entry) * value cell)).sum =
        cell.weight * value cell := by
    intro cell member
    have actual : domain cell.item ∈ partition.intervals := by
      rw [← certificate.1]
      exact Purelib.Data.List.Map.mem_map_of_mem member
    have lengths := Partition.Interval.sum_clampedLength (domain cell.item) (children.map child)
    rw [Purelib.Data.List.Map.map_map, Purelib.Data.List.Map.map_map] at lengths
    change (children.map (fun entry => (domain cell.item).clampedLength (child entry))).sum =
      Partition.Interval.lengthSum (children.map (fun entry =>
        ⟨(domain cell.item).clamp (child entry).start, (domain cell.item).clamp (child entry).finish⟩)) at lengths
    have total := childrenPartition.clamped_lengthSum (domain cell.item) (partition.valid (domain cell.item) actual)
    rw [← domains, Purelib.Data.List.Map.map_map] at total
    change Partition.Interval.lengthSum (children.map (fun entry =>
      ⟨(domain cell.item).clamp (child entry).start, (domain cell.item).clamp (child entry).finish⟩)) =
        (domain cell.item).signedLength at total
    calc
      _ = (children.map (fun entry => (domain cell.item).clampedLength (child entry))).sum * value cell :=
        sum_mul_right (fun entry => (domain cell.item).clampedLength (child entry)) (value cell) children
      _ = (domain cell.item).signedLength * value cell := by rw [lengths, total]
      _ = cell.weight * value cell := by rw [certificate.2 cell member]
  calc
    _ = (children.map (fun entry =>
        (cells.map (fun cell => (domain cell.item).clampedLength (child entry) * value cell)).sum)).sum :=
      sum_congr _ _ children childSum
    _ = (cells.map (fun cell =>
        (children.map (fun entry => (domain cell.item).clampedLength (child entry) * value cell)).sum)).sum :=
      sum_swap (fun cell entry => (domain cell.item).clampedLength (child entry) * value cell) cells children
    _ = _ := sum_congr _ _ cells parentSum

/-- The original lower integral is the finite sum of its retained cell products. -/
private theorem lowerIntegral_sum {α : Type} : ∀ cells : List (IntegrationCell α),
    lowerIntegral cells = (cells.map (fun cell => cell.weight * cell.lower)).sum
  | [] => rfl
  | cell :: remaining => by
      change cell.weight * cell.lower + lowerIntegral remaining =
        cell.weight * cell.lower + (remaining.map (fun other => other.weight * other.lower)).sum
      rw [lowerIntegral_sum remaining]

/-- The original upper integral is the finite sum of its retained cell products. -/
private theorem upperIntegral_sum {α : Type} : ∀ cells : List (IntegrationCell α),
    upperIntegral cells = (cells.map (fun cell => cell.weight * cell.upper)).sum
  | [] => rfl
  | cell :: remaining => by
      change cell.weight * cell.upper + upperIntegral remaining =
        cell.weight * cell.upper + (remaining.map (fun other => other.weight * other.upper)).sum
      rw [upperIntegral_sum remaining]

/-- Parent-admitted readings on a complete child partition lie in the original integral enclosure. -/
theorem child_sum_contains {α β : Type} {partition : Unit.Normalized}
    {cells : List (IntegrationCell α)} {domain : α → Partition.Interval}
    (certificate : PartitionedCells partition cells domain) (childrenPartition : Unit.Normalized)
    (children : List β) (child : β → Partition.Interval) (selected : β → IntegrationCell α)
    (reading : β → Fraction.Rational) (domains : children.map child = childrenPartition.intervals)
    (owners : ∀ entry ∈ children, ∃ owner : Ownership.IntervalOwner partition.intervals (child entry),
      selected entry ∈ cells ∧ domain (selected entry).item = owner.parent)
    (inside : ∀ entry ∈ children, (selected entry).lower ≤ reading entry ∧ reading entry ≤ (selected entry).upper) :
    (integralBound cells).Contains (children.map (fun entry => (child entry).signedLength * reading entry)).sum := by
  have nonnegative : ∀ entry ∈ children, 0 ≤ (child entry).signedLength := by
    intro entry member
    have actual : child entry ∈ childrenPartition.intervals := by
      rw [← domains]
      exact Purelib.Data.List.Map.mem_map_of_mem member
    exact (Partition.Interval.signedLength_pos (childrenPartition.valid (child entry) actual)).le
  have lowerBound := sum_le
    (fun entry => (child entry).signedLength * (selected entry).lower)
    (fun entry => (child entry).signedLength * reading entry) children (fun entry member =>
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (inside entry member).1 (nonnegative entry member))
  have upperBound := sum_le
    (fun entry => (child entry).signedLength * reading entry)
    (fun entry => (child entry).signedLength * (selected entry).upper) children (fun entry member =>
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (inside entry member).2 (nonnegative entry member))
  have lowerSum := certificate.redistributed_weighted_sum childrenPartition children child selected domains owners
    (fun cell => cell.lower)
  have upperSum := certificate.redistributed_weighted_sum childrenPartition children child selected domains owners
    (fun cell => cell.upper)
  rw [← lowerIntegral_sum] at lowerSum
  rw [← upperIntegral_sum] at upperSum
  change lowerIntegral cells ≤ _ ∧ _ ≤ upperIntegral cells
  constructor
  · rw [← lowerSum]
    exact lowerBound
  · rw [← upperSum]
    exact upperBound

/-- Narrowed cells on a complete child partition refine the original integral enclosure.

The candidate cells retain the exact child lengths and narrow their original
indexed parents' ranges. Finite redistribution proves both endpoint bounds. -/
theorem redistributed_refines {α β γ : Type} {partition : Unit.Normalized}
    {cells : List (IntegrationCell α)} {domain : α → Partition.Interval}
    (certificate : PartitionedCells partition cells domain) (childrenPartition : Unit.Normalized)
    (children : List β) (child : β → Partition.Interval) (selected : β → IntegrationCell α)
    (candidate : β → IntegrationCell γ) (domains : children.map child = childrenPartition.intervals)
    (owners : ∀ entry ∈ children, ∃ owner : Ownership.IntervalOwner partition.intervals (child entry),
      selected entry ∈ cells ∧ domain (selected entry).item = owner.parent)
    (weights : ∀ entry ∈ children, (candidate entry).weight = (child entry).signedLength)
    (ranges : ∀ entry ∈ children,
      (selected entry).lower ≤ (candidate entry).lower ∧ (candidate entry).upper ≤ (selected entry).upper) :
    Purelib.Data.Rat.Interval.Refines (integralBound (children.map candidate)) (integralBound cells) := by
  have nonnegative : ∀ entry ∈ children, 0 ≤ (child entry).signedLength := by
    intro entry member
    have actual : child entry ∈ childrenPartition.intervals := by
      rw [← domains]
      exact Purelib.Data.List.Map.mem_map_of_mem member
    exact (Partition.Interval.signedLength_pos (childrenPartition.valid (child entry) actual)).le
  have lowerBound := sum_le
    (fun entry => (child entry).signedLength * (selected entry).lower)
    (fun entry => (child entry).signedLength * (candidate entry).lower) children (fun entry member =>
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (ranges entry member).1 (nonnegative entry member))
  have upperBound := sum_le
    (fun entry => (child entry).signedLength * (candidate entry).upper)
    (fun entry => (child entry).signedLength * (selected entry).upper) children (fun entry member =>
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (ranges entry member).2 (nonnegative entry member))
  have lowerSum := certificate.redistributed_weighted_sum childrenPartition children child selected domains owners
    (fun cell => cell.lower)
  have upperSum := certificate.redistributed_weighted_sum childrenPartition children child selected domains owners
    (fun cell => cell.upper)
  rw [← lowerIntegral_sum] at lowerSum
  rw [← upperIntegral_sum] at upperSum
  have candidateLower : lowerIntegral (children.map candidate) =
      (children.map (fun entry => (child entry).signedLength * (candidate entry).lower)).sum := by
    rw [lowerIntegral_sum, Purelib.Data.List.Map.map_map]
    apply sum_congr
    intro entry member
    change (candidate entry).weight * (candidate entry).lower = _
    rw [weights entry member]
  have candidateUpper : upperIntegral (children.map candidate) =
      (children.map (fun entry => (child entry).signedLength * (candidate entry).upper)).sum := by
    rw [upperIntegral_sum, Purelib.Data.List.Map.map_map]
    apply sum_congr
    intro entry member
    change (candidate entry).weight * (candidate entry).upper = _
    rw [weights entry member]
  constructor
  · change lowerIntegral cells ≤ lowerIntegral (children.map candidate)
    rw [← lowerSum, candidateLower]
    exact lowerBound
  · change upperIntegral (children.map candidate) ≤ upperIntegral cells
    rw [candidateUpper, ← upperSum]
    exact upperBound

end PartitionedCells

end Purelib.Integration

end
