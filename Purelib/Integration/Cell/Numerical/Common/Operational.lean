module
public import Purelib.Integration.Cell.Numerical.Common.Weights
import Purelib.Data.List.Attach
import Purelib.Data.List.Map
import Purelib.Data.Rat.Interval.Comparison
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Operational replacement of numerical point sources

Each common child retains its original two source observations and an actual
joint scheduler request. Coherence relates each saved point interval to the
corresponding joint result; the scheduler's finite closeness law pays the
remaining point discrepancy.
-/

public section

namespace Purelib.Integration.NumericalFrontier

open Purelib.Approximation
open Purelib.Data.Rat

set_option genInjectivity false in
/-- A retained joint point request for the original common numerical observation.

The original reading retains both indexed parents and cached point requests.
The point-equivalence scheduler, its returned state and both actual interval
readbacks remain attached to that same rational tag. -/
structure JointReading {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource)
    (request budget : AccuracyRequest) where
  /-- The original common child with its two actual point requests. -/ reading : CommonReading left right request
  /-- The original operational equivalence at the same rational tag. -/ equivalent :
    OperationalEquivalence (leftSource reading.tag) (rightSource reading.tag)
  /-- The actual state returned by the original joint scheduler. -/ state : equivalent.State
  /-- The state comes from the original positive joint request. -/ state_eq :
    state = equivalent.request equivalent.initial budget.tolerance budget.positive
  /-- The cached left point interval read from that joint state. -/ leftBound : Purelib.Data.Rat.Interval
  /-- The left interval is the original process readback of that state. -/ left_bound_eq :
    leftBound = (leftSource reading.tag).bound (equivalent.leftState state)
  /-- The cached right point interval read from that joint state. -/ rightBound : Purelib.Data.Rat.Interval
  /-- The right interval is the original process readback of that state. -/ right_bound_eq :
    rightBound = (rightSource reading.tag).bound (equivalent.rightState state)
  /-- The saved left point interval overlaps the actual joint left interval. -/ left_overlap :
    reading.leftPoint.reading.Overlaps leftBound
  /-- The saved right point interval overlaps the actual joint right interval. -/ right_overlap :
    reading.rightPoint.reading.Overlaps rightBound

constructive_injectivity JointReading

/-- Run the original joint point scheduler and retain both actual interval readbacks. -/
@[expose] def requestJointReading {leftSource rightSource : Fraction.Rational → BoundProcess}
    {left : NumericalFrontier leftSource} {right : NumericalFrontier rightSource}
    {request : AccuracyRequest} (reading : CommonReading left right request) (budget : AccuracyRequest)
    (equivalent : OperationalEquivalence (leftSource reading.tag) (rightSource reading.tag))
    (leftCoherent : (leftSource reading.tag).Coherent) (rightCoherent : (rightSource reading.tag).Coherent) :
    JointReading left right request budget :=
  let state := equivalent.request equivalent.initial budget.tolerance budget.positive
  { reading := reading
    equivalent := equivalent
    state := state
    state_eq := rfl
    leftBound := (leftSource reading.tag).bound (equivalent.leftState state)
    left_bound_eq := rfl
    rightBound := (rightSource reading.tag).bound (equivalent.rightState state)
    right_bound_eq := rfl
    left_overlap := reading.leftPoint_overlaps leftCoherent (equivalent.leftState state)
    right_overlap := reading.rightPoint_overlaps rightCoherent (equivalent.rightState state) }

namespace JointReading

/-- The rational bridge witness in the original and joint left point intervals. -/
@[expose] def leftWitness {leftSource rightSource : Fraction.Rational → BoundProcess}
    {left : NumericalFrontier leftSource} {right : NumericalFrontier rightSource} {request budget : AccuracyRequest}
    (joint : JointReading left right request budget) : Fraction.Rational :=
  joint.reading.leftPoint.reading.overlapWitness joint.leftBound

/-- The rational bridge witness in the original and joint right point intervals. -/
@[expose] def rightWitness {leftSource rightSource : Fraction.Rational → BoundProcess}
    {left : NumericalFrontier leftSource} {right : NumericalFrontier rightSource} {request budget : AccuracyRequest}
    (joint : JointReading left right request budget) : Fraction.Rational :=
  joint.reading.rightPoint.reading.overlapWitness joint.rightBound

/-- The joint scheduler and retained point widths pay for the actual common-reading discrepancy. -/
theorem discrepancy_le {leftSource rightSource : Fraction.Rational → BoundProcess}
    {left : NumericalFrontier leftSource} {right : NumericalFrontier rightSource} {request budget : AccuracyRequest}
    (joint : JointReading left right request budget) :
    joint.reading.discrepancy ≤ joint.reading.leftPoint.reading.width + joint.reading.rightPoint.reading.width +
      budget.tolerance := by
  have leftInside := Interval.overlapWitness_inside joint.left_overlap
  have rightInside := Interval.overlapWitness_inside joint.right_overlap
  have leftJoint : ((leftSource joint.reading.tag).bound
      (joint.equivalent.leftState
        (joint.equivalent.request joint.equivalent.initial budget.tolerance budget.positive))).Contains
          joint.leftWitness := by
    have boundEq := joint.left_bound_eq
    rw [joint.state_eq] at boundEq
    rw [← boundEq]
    exact leftInside.2
  have rightJoint : ((rightSource joint.reading.tag).bound
      (joint.equivalent.rightState
        (joint.equivalent.request joint.equivalent.initial budget.tolerance budget.positive))).Contains
          joint.rightWitness := by
    have boundEq := joint.right_bound_eq
    rw [joint.state_eq] at boundEq
    rw [← boundEq]
    exact rightInside.2
  have close := joint.equivalent.close joint.equivalent.initial budget.tolerance budget.positive leftJoint rightJoint
  have bridgeBound : Fraction.abs (joint.leftWitness - joint.rightWitness) ≤ budget.tolerance := by
    change max (joint.leftWitness - joint.rightWitness) (-(joint.leftWitness - joint.rightWitness)) ≤ _
    apply Fraction.Order.Basic.max_le close.1.le
    have reverse : -(joint.leftWitness - joint.rightWitness) = joint.rightWitness - joint.leftWitness := by ring1
    rw [reverse]
    exact close.2.le
  have compared := Interval.abs_sub_le_of_readings joint.reading.left_inside.2 joint.reading.right_inside.2
    leftInside.1 rightInside.1
  exact compared.trans (Fraction.Order.Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl _) bridgeBound)

/-- The two original point requests and joint request pay for this actual point discrepancy. -/
theorem discrepancy_le_requests {leftSource rightSource : Fraction.Rational → BoundProcess}
    {left : NumericalFrontier leftSource} {right : NumericalFrontier rightSource} {request budget : AccuracyRequest}
    (joint : JointReading left right request budget) :
    joint.reading.discrepancy ≤ request.tolerance + request.tolerance + budget.tolerance := by
  have widths := Fraction.Order.Arithmetic.add_le_add_direct joint.reading.left_width_lt.le
    joint.reading.right_width_lt.le
  have paid := Fraction.Order.Arithmetic.add_le_add_direct widths (Fraction.Order.Basic.le_refl budget.tolerance)
  exact joint.discrepancy_le.trans paid

end JointReading

set_option genInjectivity false in
/-- Actual joint point requests for all readings of the original common refinement.

The list retains each original common observation and its own point
equivalence, joint state and cached interval readbacks in the same order. -/
structure JointReadings {leftSource rightSource : Fraction.Rational → BoundProcess}
    {left : NumericalFrontier leftSource} {right : NumericalFrontier rightSource} {request : AccuracyRequest}
    (common : CommonReadings left right request) (budget : AccuracyRequest) where
  /-- The actual joint scheduler results for the common children. -/ readings :
    List (JointReading left right request budget)
  /-- The original common observations are retained in the same order. -/ readings_eq :
    readings.map JointReading.reading = common.readings

constructive_injectivity JointReadings

/-- Run one original joint scheduler for a retained numerical common-point reading. -/
@[expose] def jointForReading {leftSource rightSource : Fraction.Rational → BoundProcess}
    {left : NumericalFrontier leftSource} {right : NumericalFrontier rightSource} {request : AccuracyRequest}
    (budget : AccuracyRequest)
    (equivalent : ∀ point, 0 ≤ point → point ≤ 1 → OperationalEquivalence (leftSource point) (rightSource point))
    (leftCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (leftSource point).Coherent)
    (rightCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (rightSource point).Coherent)
    (reading : CommonReading left right request) : JointReading left right request budget :=
  let lower := reading.valid.1.trans reading.tag_inside.1
  let upper := reading.tag_inside.2.trans reading.valid.2.2
  requestJointReading reading budget (equivalent reading.tag lower upper)
    (leftCoherent reading.tag lower upper) (rightCoherent reading.tag lower upper)

/-- Execute and retain the supplied point-equivalence schedulers for the actual common readings. -/
@[expose] def requestJointReadings {leftSource rightSource : Fraction.Rational → BoundProcess}
    {left : NumericalFrontier leftSource} {right : NumericalFrontier rightSource} {request : AccuracyRequest}
    (common : CommonReadings left right request) (budget : AccuracyRequest)
    (equivalent : ∀ point, 0 ≤ point → point ≤ 1 → OperationalEquivalence (leftSource point) (rightSource point))
    (leftCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (leftSource point).Coherent)
    (rightCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (rightSource point).Coherent) : JointReadings common budget := by
  let readings := common.readings.map (jointForReading budget equivalent leftCoherent rightCoherent)
  exact
    { readings := readings
      readings_eq := by
        change (common.readings.map _).map JointReading.reading = common.readings
        rw [Purelib.Data.List.Map.map_map]
        change common.readings.map id = common.readings
        exact Purelib.Data.List.Map.map_id _ }

/-- The joint comparison preserves the original attached common-reading occurrences and their order. -/
theorem requestJointReadings_original_order {leftSource rightSource : Fraction.Rational → BoundProcess}
    {left : NumericalFrontier leftSource} {right : NumericalFrontier rightSource} {request : AccuracyRequest}
    (common : CommonReadings left right request) (budget : AccuracyRequest)
    (equivalent : ∀ point, 0 ≤ point → point ≤ 1 → OperationalEquivalence (leftSource point) (rightSource point))
    (leftCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (leftSource point).Coherent)
    (rightCoherent : ∀ point, 0 ≤ point → point ≤ 1 → (rightSource point).Coherent) :
    (requestJointReadings common budget equivalent leftCoherent rightCoherent).readings =
      common.readings.attach.map (fun entry =>
        jointForReading budget equivalent leftCoherent rightCoherent entry.val) := by
  change common.readings.map (jointForReading budget equivalent leftCoherent rightCoherent) =
    common.readings.attach.map ((jointForReading budget equivalent leftCoherent rightCoherent) ∘ Subtype.val)
  rw [← Purelib.Data.List.Map.map_map, Purelib.Data.List.attach_map_subtype_val]


namespace JointReadings

/-- The actual common point budget is paid by both saved requests and the joint request.

The proof reads the retained joint result for every original child and uses
the exact original common weights. No pointwise or integral equality is an
extra input to this comparison. -/
theorem pointBudget_le {leftSource rightSource : Fraction.Rational → BoundProcess}
    {left : NumericalFrontier leftSource} {right : NumericalFrontier rightSource} {request budget : AccuracyRequest}
    {common : CommonReadings left right request} (joint : JointReadings common budget) :
    common.pointBudget ≤ request.tolerance + request.tolerance + budget.tolerance := by
  have readingBound : ∀ reading ∈ common.readings,
      reading.discrepancy ≤ request.tolerance + request.tolerance + budget.tolerance := by
    intro reading member
    have present : reading ∈ joint.readings.map JointReading.reading := by
      rw [joint.readings_eq]
      exact member
    obtain ⟨entry, _, equal⟩ := Purelib.Data.List.Map.mem_map.mp present
    have bound := entry.discrepancy_le_requests
    have same : entry.reading.discrepancy = reading.discrepancy := congrArg CommonReading.discrepancy equal
    rw [same] at bound
    exact bound
  have bounded : ∀ cell ∈ common.cells, cell.item.discrepancy ≤
      request.tolerance + request.tolerance + budget.tolerance := by
    intro cell member
    change cell ∈ common.readings.map CommonReading.exactCell at member
    obtain ⟨reading, readingMember, equal⟩ := Purelib.Data.List.Map.mem_map.mp member
    cases equal
    exact readingBound reading readingMember
  have paid := weightedEvaluation_le_weight_mul CommonReading.discrepancy
    (request.tolerance + request.tolerance + budget.tolerance) common.cells bounded
  rw [common.totalWeight, Fraction.Field.one_mul] at paid
  exact paid

/-- Independently constructed numerical answers agree within both widths and both point budgets. -/
theorem answers_difference_le {leftSource rightSource : Fraction.Rational → BoundProcess}
    {left : NumericalFrontier leftSource} {right : NumericalFrontier rightSource} {request budget : AccuracyRequest}
    {common : CommonReadings left right request} (joint : JointReadings common budget)
    (leftAnswer rightAnswer : Fraction.Rational) (leftInside : (integralBound left.cells).Contains leftAnswer)
    (rightInside : (integralBound right.cells).Contains rightAnswer) :
    Fraction.abs (leftAnswer - rightAnswer) ≤
      (integralBound left.cells).width + (integralBound right.cells).width +
        (request.tolerance + request.tolerance + budget.tolerance) := by
  have comparison := common.answers_difference_le leftAnswer rightAnswer leftInside rightInside
  have paid := Fraction.Order.Arithmetic.add_le_add_direct
    (Fraction.Order.Basic.le_refl ((integralBound left.cells).width + (integralBound right.cells).width))
    joint.pointBudget_le
  exact comparison.trans paid

end JointReadings

end Purelib.Integration.NumericalFrontier

end
