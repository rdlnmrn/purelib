module
public import Purelib.Integration.Cell.Source.Comparison.Intersection
public import Purelib.Integration.Cell.Source.Refinement
public import Purelib.Integration.Cell.Partitioned.Split
import Purelib.Data.List.Nodup
import Purelib.Data.List.Pairwise

/-!
# Original-parent splits of a common source refinement

The actual common children satisfy the shared indexed-refinement contract.
Their original parent indices and exact weights produce the original finite
cell-splitting relation in retained child order.
-/

public section

namespace Purelib.Integration.SourceFrontier.CommonReadings

open Purelib.Data.Rat
open Purelib.Integration.Partition

/-- Ordered valid children retain ordered indices in their original parent partition. -/
private theorem owner_index_le (partition : Unit.Normalized) {first second : Partition.Interval}
    (firstOwner : Ownership.IntervalOwner partition.intervals first)
    (secondOwner : Ownership.IntervalOwner partition.intervals second)
    (firstValid : first.Valid) (secondValid : second.Valid) (ordered : first.start ≤ second.start) :
    firstOwner.index ≤ secondOwner.index := by
  by_contra reverse
  have indexOrder : secondOwner.index < firstOwner.index := Nat.lt_of_not_ge reverse
  have firstBound := Purelib.Data.List.index_lt_length_of_getElem? partition.intervals
    firstOwner.index firstOwner.parent firstOwner.at_index
  have secondBound := Purelib.Data.List.index_lt_length_of_getElem? partition.intervals
    secondOwner.index secondOwner.parent secondOwner.at_index
  have firstRead : partition.intervals[firstOwner.index]'firstBound = firstOwner.parent := Option.some.inj
    ((Purelib.Data.List.getElem?_eq_getElem partition.intervals firstOwner.index firstBound).symm.trans
      firstOwner.at_index)
  have secondRead : partition.intervals[secondOwner.index]'secondBound = secondOwner.parent := Option.some.inj
    ((Purelib.Data.List.getElem?_eq_getElem partition.intervals secondOwner.index secondBound).symm.trans
      secondOwner.at_index)
  have parentStarts := Purelib.Data.List.Pairwise.pairwise_getElem partition.starts_pairwise
    secondOwner.index firstOwner.index secondBound firstBound indexOrder
  rw [secondRead, firstRead] at parentStarts
  have distinct : firstOwner.parent ≠ secondOwner.parent := by
    intro equal
    have same := Purelib.Data.List.Nodup.getElem?_index_injective partition.intervals_nodup
      firstOwner.at_index (equal ▸ secondOwner.at_index)
    exact (Nat.ne_of_gt indexOrder) same
  have member := Purelib.Data.List.mem_of_getElem? partition.intervals secondOwner.index secondOwner.parent
    secondOwner.at_index
  rcases firstOwner.other_disjoint secondOwner.parent member distinct with before | after
  · exact firstValid.2.1.2 (before.trans (parentStarts.trans firstOwner.start_le))
  · exact secondValid.2.1.2 (secondOwner.finish_le.trans (after.trans ordered))

/-- Any retained common collection has nondecreasing original left-parent indices. -/
theorem left_indices {leftSource rightSource : Fraction.Rational → Fraction.Rational}
    {left : SourceFrontier leftSource} {right : SourceFrontier rightSource} (common : CommonReadings left right) :
    common.readings.Pairwise (fun first second => first.entry.leftOwner.index ≤ second.entry.leftOwner.index) := by
  have starts : common.readings.Pairwise (fun first second => first.entry.child.start ≤ second.entry.child.start) := by
    have pairwise := common.refinement.partition.starts_pairwise
    rw [← common.reading_domains] at pairwise
    exact (Purelib.Data.List.Pairwise.pairwise_map
      (function := fun reading : CommonReading left right => reading.entry.child)
      (relation := fun first second : Partition.Interval => first.start ≤ second.start)).mp pairwise
  have ordered : ∀ readings : List (CommonReading left right),
      readings.Pairwise (fun first second => first.entry.child.start ≤ second.entry.child.start) →
      readings.Pairwise (fun first second => first.entry.leftOwner.index ≤ second.entry.leftOwner.index) := by
    intro readings
    induction readings with
    | nil => intro _; exact List.Pairwise.nil
    | cons first rest ih =>
      intro starts
      apply List.pairwise_cons.mpr
      constructor
      · intro second member
        exact owner_index_le left.partition first.entry.leftOwner second.entry.leftOwner first.valid second.valid
          ((List.pairwise_cons.mp starts).1 second member)
      · exact ih (List.pairwise_cons.mp starts).2
  exact ordered common.readings starts

/-- Any retained common collection gives the original indexed split refinement. -/
theorem indexed {source : Fraction.Rational → Fraction.Rational}
    {left right : SourceFrontier source} (common : CommonReadings left right) :
    PartitionedCells.IndexedRefinement left.partitioned common.refinement.partition common.readings
      (fun reading => reading.entry.child) (fun reading => reading.entry.leftOwner)
      (fun reading => reading.leftCell.val) CommonReading.intersectionCell := by
  exact
    { domains_eq := common.reading_domains
      valid := fun reading => reading.valid
      selected_read := fun reading => reading.leftCell.property.1
      selected_domain := fun reading => reading.leftCell.property.2
      weight := fun _ => rfl
      ranges := fun reading => by
        have refines := Interval.intersect_refines_left reading.leftRange reading.rightRange reading.ranges_overlap
        exact ⟨refines.lower, refines.upper⟩
      ordered := common.left_indices }

/-- The intersection of any retained common collection splits the original left frontier. -/
theorem intersection_split {source : Fraction.Rational → Fraction.Rational}
    {left right : SourceFrontier source} (common : CommonReadings left right) :
    IntegrationFrontierRefines common.intersection.cells left.cells := common.indexed.refines

/-- The actual common children meet the shared indexed-refinement contract. -/
theorem commonReadings_indexed {source : Fraction.Rational → Fraction.Rational}
    (left right : SourceFrontier source) :
    let common := commonReadings left right
    PartitionedCells.IndexedRefinement left.partitioned common.refinement.partition common.readings
      (fun reading => reading.entry.child) (fun reading => reading.entry.leftOwner)
      (fun reading => reading.leftCell.val) CommonReading.intersectionCell :=
  (commonReadings left right).indexed

/-- The computed source intersection is an actual finite split refinement of its saved left frontier. -/
theorem commonReadings_intersection_refines {source : Fraction.Rational → Fraction.Rational}
    (left right : SourceFrontier source) :
    IntegrationFrontierRefines (commonReadings left right).intersection.cells left.cells :=
  (commonReadings_indexed left right).refines

end Purelib.Integration.SourceFrontier.CommonReadings

end
