module
public import Purelib.Integration.Cell.Source.Comparison
import Purelib.Data.List.Map
import Purelib.Data.List.Rat.Linear
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Interval.Comparison
import Purelib.Tactic.Ring

/-!
# Exact common-partition weight redistribution

Every common child contributes its full length to the exact retained parent
cell and zero to other parent cells. Finite sum interchange then recovers the
original parent weights without replacing either partition.
-/

public section

namespace Purelib.Integration.SourceFrontier

open Purelib.Data.Rat
open Purelib.Integration.Partition
open Purelib.Data.List.Rat.Linear

namespace CommonReadings

/-- The retained common readings have exactly the common partition's original ordered child domains. -/
theorem reading_domains {leftSource rightSource : Fraction.Rational → Fraction.Rational}
    {left : SourceFrontier leftSource} {right : SourceFrontier rightSource} (common : CommonReadings left right) :
    common.readings.map (fun reading => reading.entry.child) = common.refinement.partition.intervals := by
  have domains := common.cells_domains
  unfold cells at domains
  rw [Purelib.Data.List.Map.map_map] at domains
  exact domains

/-- Clamping all retained common children to a valid original interval recovers its exact length. -/
theorem clampedLength_sum {leftSource rightSource : Fraction.Rational → Fraction.Rational}
    {left : SourceFrontier leftSource} {right : SourceFrontier rightSource}
    (common : CommonReadings left right) (parent : Partition.Interval) (valid : parent.Valid) :
    (common.readings.map (fun reading => parent.clampedLength reading.entry.child)).sum = parent.signedLength := by
  have lengths := Partition.Interval.sum_clampedLength parent (common.readings.map (fun reading => reading.entry.child))
  rw [Purelib.Data.List.Map.map_map, Purelib.Data.List.Map.map_map] at lengths
  change (common.readings.map (fun reading => parent.clampedLength reading.entry.child)).sum =
    Partition.Interval.lengthSum (common.readings.map (fun reading =>
      ⟨parent.clamp reading.entry.child.start, parent.clamp reading.entry.child.finish⟩)) at lengths
  have total := common.refinement.partition.clamped_lengthSum parent valid
  rw [← common.reading_domains, Purelib.Data.List.Map.map_map] at total
  change Partition.Interval.lengthSum (common.readings.map (fun reading =>
    ⟨parent.clamp reading.entry.child.start, parent.clamp reading.entry.child.finish⟩)) = parent.signedLength at total
  exact lengths.trans total

/-- The actual left common-tagged sum lies in the original left frontier enclosure. -/
theorem leftSum_contains {leftSource rightSource : Fraction.Rational → Fraction.Rational}
    {left : SourceFrontier leftSource} {right : SourceFrontier rightSource} (common : CommonReadings left right) :
    (integralBound left.cells).Contains common.leftSum := by
  have contains := left.partitioned.child_sum_contains common.refinement.partition common.readings
    (fun reading => reading.entry.child) (fun reading => reading.leftCell.val) CommonReading.leftReading
    common.reading_domains (fun reading _ => ⟨reading.entry.leftOwner,
      Purelib.Data.List.mem_of_getElem? left.cells reading.entry.leftOwner.index reading.leftCell.val
        reading.leftCell.property.1, reading.leftCell.property.2⟩) (fun reading _ => reading.left_inside)
  change (integralBound left.cells).Contains (weightedEvaluation CommonReading.leftReading
    (common.readings.map CommonReading.exactCell))
  rw [weightedEvaluation_eq_sum, Purelib.Data.List.Map.map_map]
  exact contains

/-- The actual right common-tagged sum lies in the original right frontier enclosure. -/
theorem rightSum_contains {leftSource rightSource : Fraction.Rational → Fraction.Rational}
    {left : SourceFrontier leftSource} {right : SourceFrontier rightSource} (common : CommonReadings left right) :
    (integralBound right.cells).Contains common.rightSum := by
  have contains := right.partitioned.child_sum_contains common.refinement.partition common.readings
    (fun reading => reading.entry.child) (fun reading => reading.rightCell.val) CommonReading.rightReading
    common.reading_domains (fun reading _ => ⟨reading.entry.rightOwner,
      Purelib.Data.List.mem_of_getElem? right.cells reading.entry.rightOwner.index reading.rightCell.val
        reading.rightCell.property.1, reading.rightCell.property.2⟩) (fun reading _ => reading.right_inside)
  change (integralBound right.cells).Contains (weightedEvaluation CommonReading.rightReading
    (common.readings.map CommonReading.exactCell))
  rw [weightedEvaluation_eq_sum, Purelib.Data.List.Map.map_map]
  exact contains

/-- Answers in two original frontier enclosures differ by at most their widths and actual point budget.

The computed common partition retains both original parents. Its actual
source readings give the discrepancy term; their weighted sums lie in the two
original enclosures by exact finite weight redistribution. -/
theorem answers_difference_le {leftSource rightSource : Fraction.Rational → Fraction.Rational}
    {left : SourceFrontier leftSource} {right : SourceFrontier rightSource}
    (common : CommonReadings left right) (leftAnswer rightAnswer : Fraction.Rational)
    (leftInside : (integralBound left.cells).Contains leftAnswer)
    (rightInside : (integralBound right.cells).Contains rightAnswer) :
    Fraction.abs (leftAnswer - rightAnswer) ≤
      (integralBound left.cells).width + (integralBound right.cells).width + common.pointBudget := by
  have compared := Purelib.Data.Rat.Interval.abs_sub_le_of_readings
    leftInside rightInside common.leftSum_contains common.rightSum_contains
  have budget := Fraction.Order.Arithmetic.add_le_add_direct
    (Fraction.Order.Basic.le_refl ((integralBound left.cells).width + (integralBound right.cells).width))
    common.sum_difference_le_pointBudget
  exact Fraction.Order.Basic.le_trans _ _ _ compared budget

/-- A uniform rational discrepancy bounds one actual common-tag reading pair. -/
theorem reading_discrepancy_le {leftSource rightSource : Fraction.Rational → Fraction.Rational}
    {left : SourceFrontier leftSource} {right : SourceFrontier rightSource}
    (reading : CommonReading left right) (bound : Fraction.Rational)
    (pointBound : ∀ point, 0 ≤ point → point ≤ 1 → Fraction.abs (leftSource point - rightSource point) ≤ bound) :
    Fraction.abs (reading.leftReading - reading.rightReading) ≤ bound := by
  have lower : 0 ≤ reading.tag := reading.valid.1.trans reading.tag_inside.1
  have upper : reading.tag ≤ 1 := reading.tag_inside.2.trans reading.valid.2.2
  have leftReading : reading.leftReading = leftSource reading.tag :=
    reading.left_reading_eq.trans (reading.leftCell.val.item.readAt_eq reading.tag)
  have rightReading : reading.rightReading = rightSource reading.tag :=
    reading.right_reading_eq.trans (reading.rightCell.val.item.readAt_eq reading.tag)
  rw [leftReading, rightReading]
  exact pointBound reading.tag lower upper

/-- A uniform rational point discrepancy bounds the actual length-weighted common-point budget. -/
theorem pointBudget_le_of_bound {leftSource rightSource : Fraction.Rational → Fraction.Rational}
    {left : SourceFrontier leftSource} {right : SourceFrontier rightSource}
    (common : CommonReadings left right) (bound : Fraction.Rational)
    (pointBound : ∀ point, 0 ≤ point → point ≤ 1 → Fraction.abs (leftSource point - rightSource point) ≤ bound) :
    common.pointBudget ≤ bound := by
  have each : ∀ cell : IntegrationCell (CommonReading left right), cell ∈ common.cells →
      Fraction.abs (cell.item.leftReading - cell.item.rightReading) ≤ bound := by
    intro cell _
    exact reading_discrepancy_le cell.item bound pointBound
  have weighted := weightedEvaluation_le_weight_mul
    (fun reading : CommonReading left right => Fraction.abs (reading.leftReading - reading.rightReading))
    bound common.cells each
  rw [common.totalWeight, Fraction.Field.one_mul] at weighted
  exact weighted

/-- Equal rational source restrictions give agreement up to the original two enclosure widths. -/
theorem answers_difference_le_of_same {leftSource rightSource : Fraction.Rational → Fraction.Rational}
    {left : SourceFrontier leftSource} {right : SourceFrontier rightSource}
    (common : CommonReadings left right) (leftAnswer rightAnswer : Fraction.Rational)
    (leftInside : (integralBound left.cells).Contains leftAnswer)
    (rightInside : (integralBound right.cells).Contains rightAnswer)
    (same : ∀ point, 0 ≤ point → point ≤ 1 → leftSource point = rightSource point) :
    Fraction.abs (leftAnswer - rightAnswer) ≤ (integralBound left.cells).width + (integralBound right.cells).width := by
  have bound := common.answers_difference_le leftAnswer rightAnswer leftInside rightInside
  rw [common.pointBudget_eq_zero same] at bound
  have identity : (integralBound left.cells).width + (integralBound right.cells).width + 0 =
      (integralBound left.cells).width + (integralBound right.cells).width := by ring1
  rw [identity] at bound
  exact bound

end CommonReadings

end Purelib.Integration.SourceFrontier

end
