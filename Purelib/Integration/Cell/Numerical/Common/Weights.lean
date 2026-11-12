module
public import Purelib.Integration.Cell.Numerical.Common
import Purelib.Data.List.Map
import Purelib.Data.Rat.Interval.Comparison
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

/-!
# Quantitative comparison on common numerical partitions

The actual common-point witnesses lie in their original parent ranges. Exact
weight redistribution compares their sums, and the retained point requests
pay for the observed numerical discrepancy.
-/

public section

namespace Purelib.Integration.NumericalFrontier.CommonReadings

open Purelib.Approximation
open Purelib.Data.Rat
open Purelib.Integration.Partition

/-- Common readings retain the original common partition's ordered child domains. -/
theorem reading_domains {leftSource rightSource : Fraction.Rational → BoundProcess}
    {left : NumericalFrontier leftSource} {right : NumericalFrontier rightSource}
    {request : AccuracyRequest} (common : CommonReadings left right request) :
    common.readings.map (fun reading => reading.entry.child) = common.refinement.partition.intervals := by
  calc
    _ = (common.readings.map CommonReading.entry).map Unit.Common.CommonEntry.child :=
      (Purelib.Data.List.Map.map_map Unit.Common.CommonEntry.child CommonReading.entry common.readings).symm
    _ = common.refinement.partition.intervals := by rw [common.entries_eq, common.refinement.children_eq]

/-- Give every retained common reading its exact original child weight. -/
@[expose] def cells {leftSource rightSource : Fraction.Rational → BoundProcess}
    {left : NumericalFrontier leftSource} {right : NumericalFrontier rightSource}
    {request : AccuracyRequest} (common : CommonReadings left right request) :
    List (IntegrationCell (CommonReading left right request)) := common.readings.map CommonReading.exactCell

/-- The actual common child cells have exact unit total weight. -/
theorem totalWeight {leftSource rightSource : Fraction.Rational → BoundProcess}
    {left : NumericalFrontier leftSource} {right : NumericalFrontier rightSource}
    {request : AccuracyRequest} (common : CommonReadings left right request) :
    integrationWeight common.cells = 1 := by
  have lengths : ∀ cell ∈ common.cells, cell.weight = cell.item.entry.child.signedLength := by
    intro cell member
    obtain ⟨reading, _, equal⟩ := Purelib.Data.List.Map.mem_map.mp member
    cases equal
    rfl
  have domains : common.cells.map (fun cell => cell.item.entry.child) = common.refinement.partition.intervals := by
    unfold cells
    rw [Purelib.Data.List.Map.map_map]
    exact common.reading_domains
  rw [integrationWeight_eq_lengthSum (fun reading : CommonReading left right request => reading.entry.child)
    common.cells lengths, domains]
  exact common.refinement.partition.lengthSum

/-- The weighted sum of the actual left overlap witnesses. -/
@[expose] def leftSum {leftSource rightSource : Fraction.Rational → BoundProcess}
    {left : NumericalFrontier leftSource} {right : NumericalFrontier rightSource}
    {request : AccuracyRequest} (common : CommonReadings left right request) :
    Fraction.Rational := weightedEvaluation CommonReading.leftReading common.cells

/-- The weighted sum of the actual right overlap witnesses. -/
@[expose] def rightSum {leftSource rightSource : Fraction.Rational → BoundProcess}
    {left : NumericalFrontier leftSource} {right : NumericalFrontier rightSource}
    {request : AccuracyRequest} (common : CommonReadings left right request) :
    Fraction.Rational := weightedEvaluation CommonReading.rightReading common.cells

/-- The actual length-weighted discrepancy between both retained point witnesses. -/
@[expose] def pointBudget {leftSource rightSource : Fraction.Rational → BoundProcess}
    {left : NumericalFrontier leftSource} {right : NumericalFrontier rightSource}
    {request : AccuracyRequest} (common : CommonReadings left right request) :
    Fraction.Rational :=
  weightedEvaluation CommonReading.discrepancy common.cells

/-- The left common-tagged sum lies in the original left integral enclosure. -/
theorem leftSum_contains {leftSource rightSource : Fraction.Rational → BoundProcess}
    {left : NumericalFrontier leftSource} {right : NumericalFrontier rightSource}
    {request : AccuracyRequest} (common : CommonReadings left right request) :
    (integralBound left.cells).Contains common.leftSum := by
  have contains := left.partitioned.child_sum_contains common.refinement.partition common.readings
    (fun reading => reading.entry.child) (fun reading => reading.leftCell.val) CommonReading.leftReading
    common.reading_domains (fun reading _ => ⟨reading.entry.leftOwner,
      Purelib.Data.List.mem_of_getElem? left.cells reading.entry.leftOwner.index reading.leftCell.val
        reading.leftCell.property.1, reading.leftCell.property.2⟩) (fun reading _ => reading.left_inside.1)
  change (integralBound left.cells).Contains (weightedEvaluation CommonReading.leftReading
    (common.readings.map CommonReading.exactCell))
  rw [weightedEvaluation_eq_sum, Purelib.Data.List.Map.map_map]
  exact contains

/-- The right common-tagged sum lies in the original right integral enclosure. -/
theorem rightSum_contains {leftSource rightSource : Fraction.Rational → BoundProcess}
    {left : NumericalFrontier leftSource} {right : NumericalFrontier rightSource}
    {request : AccuracyRequest} (common : CommonReadings left right request) :
    (integralBound right.cells).Contains common.rightSum := by
  have contains := right.partitioned.child_sum_contains common.refinement.partition common.readings
    (fun reading => reading.entry.child) (fun reading => reading.rightCell.val) CommonReading.rightReading
    common.reading_domains (fun reading _ => ⟨reading.entry.rightOwner,
      Purelib.Data.List.mem_of_getElem? right.cells reading.entry.rightOwner.index reading.rightCell.val
        reading.rightCell.property.1, reading.rightCell.property.2⟩) (fun reading _ => reading.right_inside.1)
  change (integralBound right.cells).Contains (weightedEvaluation CommonReading.rightReading
    (common.readings.map CommonReading.exactCell))
  rw [weightedEvaluation_eq_sum, Purelib.Data.List.Map.map_map]
  exact contains

/-- The original answers differ by at most both widths and the actual point-discrepancy budget. -/
theorem answers_difference_le {leftSource rightSource : Fraction.Rational → BoundProcess}
    {left : NumericalFrontier leftSource} {right : NumericalFrontier rightSource}
    {request : AccuracyRequest} (common : CommonReadings left right request)
    (leftAnswer rightAnswer : Fraction.Rational) (leftInside : (integralBound left.cells).Contains leftAnswer)
    (rightInside : (integralBound right.cells).Contains rightAnswer) :
    Fraction.abs (leftAnswer - rightAnswer) ≤
      (integralBound left.cells).width + (integralBound right.cells).width + common.pointBudget := by
  have compared := Interval.abs_sub_le_of_readings leftInside rightInside common.leftSum_contains
    common.rightSum_contains
  have discrepancy := weightedEvaluation_abs_sub_le CommonReading.leftReading CommonReading.rightReading common.cells
  have budget := Fraction.Order.Arithmetic.add_le_add_direct
    (Fraction.Order.Basic.le_refl ((integralBound left.cells).width + (integralBound right.cells).width)) discrepancy
  exact compared.trans budget

/-- A uniform bound on the actual retained common readings pays their length-weighted point budget. -/
theorem pointBudget_le_of_reading_bound {leftSource rightSource : Fraction.Rational → BoundProcess}
    {left : NumericalFrontier leftSource} {right : NumericalFrontier rightSource}
    {request : AccuracyRequest} (common : CommonReadings left right request) (bound : Fraction.Rational)
    (pointBound : ∀ reading : CommonReading left right request, reading.discrepancy ≤ bound) :
    common.pointBudget ≤ bound := by
  have each : ∀ cell : IntegrationCell (CommonReading left right request), cell ∈ common.cells →
      cell.item.discrepancy ≤ bound := fun cell _ => pointBound cell.item
  have paid := weightedEvaluation_le_weight_mul CommonReading.discrepancy bound common.cells each
  rw [common.totalWeight, Fraction.Field.one_mul] at paid
  exact paid

/-- Coherent original point states pay for the computed point budget through the actual request.

Each retained pair of point intervals has width below the same positive
request. Their rational witnesses are compared through the original point
process's finite coherence; the original common weights sum exactly to one. -/
theorem pointBudget_le {source : Fraction.Rational → BoundProcess}
    {left right : NumericalFrontier source} {request : AccuracyRequest} (common : CommonReadings left right request)
    (coherent : ∀ point, 0 ≤ point → point ≤ 1 → (source point).Coherent) :
    common.pointBudget ≤ request.tolerance + request.tolerance := by
  have bounded : ∀ cell ∈ common.cells, CommonReading.discrepancy cell.item ≤
      request.tolerance + request.tolerance := by
    intro cell _
    have pointCoherent := coherent cell.item.tag (cell.item.valid.1.trans cell.item.tag_inside.1)
      (cell.item.tag_inside.2.trans cell.item.valid.2.2)
    exact cell.item.reading_difference_le_request pointCoherent
  have paid := weightedEvaluation_le_weight_mul CommonReading.discrepancy
    (request.tolerance + request.tolerance) common.cells bounded
  rw [common.totalWeight, Fraction.Field.one_mul] at paid
  exact paid

end Purelib.Integration.NumericalFrontier.CommonReadings

end
