module
public import Purelib.Integration.Cell.Numerical
public import Purelib.Integration.Cell.Partitioned
public import Purelib.Approximation.Bound.Overlap
public import Purelib.Approximation.Bound.Operational
import Purelib.Data.Rat.Interval.Comparison
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-!
# Comparing finite numerical point admissions

At a shared rational point, the two original cell ranges overlap every state
of the same point process. Finite point requests force those ranges to
overlap and provide quantitative bounds using an actual observation width.
-/

public section

namespace Purelib.Integration.NumericalFrontier

open Purelib.Approximation
open Purelib.Data.Rat

/-- View the original numerical frontier as its exact partitioned cell occurrences. -/
theorem partitioned {source : Fraction.Rational → BoundProcess} (frontier : NumericalFrontier source) :
    PartitionedCells frontier.partition frontier.cells (fun point => point.interval) :=
  ⟨frontier.domains_eq, frontier.weight_eq⟩

/-- Two admitted cell ranges at the same rational point have a finite overlap witness.

The point's original process is requested at any separating gap. Its
accuracy and the two original pointwise admission laws rule out separation
without selecting a completed value. -/
theorem cell_ranges_overlap_at {source : Fraction.Rational → BoundProcess}
    (left right : NumericalFrontier source) (leftCell : IntegrationCell (NumericalPoint source))
    (rightCell : IntegrationCell (NumericalPoint source))
    (leftMember : leftCell ∈ left.cells) (rightMember : rightCell ∈ right.cells)
    (point : Fraction.Rational)
    (leftInside : leftCell.item.interval.start ≤ point ∧ point ≤ leftCell.item.interval.finish)
    (rightInside : rightCell.item.interval.start ≤ point ∧ point ≤ rightCell.item.interval.finish) :
    leftCell.range.Overlaps rightCell.range := by
  apply (source point).overlaps_of_overlap_all leftCell.range rightCell.range
  · intro state
    exact left.source_overlap leftCell leftMember point leftInside.1 leftInside.2 state
  · intro state
    exact right.source_overlap rightCell rightMember point rightInside.1 rightInside.2 state

/-- An actual point observation bounds the discrepancy between two admitted cell readings.

The error is the two original range widths plus the width of the retained
point-process state. The rational overlap witnesses are constructed from that
same actual state and both original cell ranges. -/
theorem cell_readings_difference_le {source : Fraction.Rational → BoundProcess}
    (left right : NumericalFrontier source) (leftCell : IntegrationCell (NumericalPoint source))
    (rightCell : IntegrationCell (NumericalPoint source))
    (leftMember : leftCell ∈ left.cells) (rightMember : rightCell ∈ right.cells)
    (point : Fraction.Rational)
    (leftInside : leftCell.item.interval.start ≤ point ∧ point ≤ leftCell.item.interval.finish)
    (rightInside : rightCell.item.interval.start ≤ point ∧ point ≤ rightCell.item.interval.finish)
    (state : (source point).State) (leftValue rightValue : Fraction.Rational)
    (leftValueInside : leftCell.range.Contains leftValue) (rightValueInside : rightCell.range.Contains rightValue) :
    Fraction.abs (leftValue - rightValue) ≤ leftCell.range.width + rightCell.range.width +
      ((source point).bound state).width :=
  Interval.abs_sub_le_of_shared_overlap leftValueInside rightValueInside
    (left.source_overlap leftCell leftMember point leftInside.1 leftInside.2 state)
    (right.source_overlap rightCell rightMember point rightInside.1 rightInside.2 state)

/-- A joint point request compares admitted readings from operationally equivalent sources.

The original point-equivalence scheduler produces both actual point states.
The two cell ranges supply rational overlap witnesses with those states, and
the scheduler's original finite closeness law pays the requested discrepancy. -/
theorem cell_readings_difference_le_of_operational
    {leftSource rightSource : Fraction.Rational → BoundProcess}
    (left : NumericalFrontier leftSource) (right : NumericalFrontier rightSource)
    (leftCell : IntegrationCell (NumericalPoint leftSource))
    (rightCell : IntegrationCell (NumericalPoint rightSource))
    (leftMember : leftCell ∈ left.cells) (rightMember : rightCell ∈ right.cells)
    (point : Fraction.Rational)
    (leftInside : leftCell.item.interval.start ≤ point ∧ point ≤ leftCell.item.interval.finish)
    (rightInside : rightCell.item.interval.start ≤ point ∧ point ≤ rightCell.item.interval.finish)
    (equivalent : OperationalEquivalence (leftSource point) (rightSource point))
    (budget : Fraction.Rational) (positive : 0 < budget) (leftValue rightValue : Fraction.Rational)
    (leftValueInside : leftCell.range.Contains leftValue) (rightValueInside : rightCell.range.Contains rightValue) :
    Fraction.abs (leftValue - rightValue) ≤ leftCell.range.width + rightCell.range.width + budget := by
  let joint := equivalent.request equivalent.initial budget positive
  let leftBound := (leftSource point).bound (equivalent.leftState joint)
  let rightBound := (rightSource point).bound (equivalent.rightState joint)
  have leftOverlap := left.source_overlap leftCell leftMember point leftInside.1 leftInside.2
    (equivalent.leftState joint)
  have rightOverlap := right.source_overlap rightCell rightMember point rightInside.1 rightInside.2
    (equivalent.rightState joint)
  have leftWitness : leftCell.range.Contains (leftCell.range.overlapWitness leftBound) ∧
      leftBound.Contains (leftCell.range.overlapWitness leftBound) := Interval.overlapWitness_inside leftOverlap
  have rightWitness : rightCell.range.Contains (rightCell.range.overlapWitness rightBound) ∧
      rightBound.Contains (rightCell.range.overlapWitness rightBound) := Interval.overlapWitness_inside rightOverlap
  have close := equivalent.close equivalent.initial budget positive leftWitness.2 rightWitness.2
  have discrepancy : Fraction.abs
      (leftCell.range.overlapWitness leftBound - rightCell.range.overlapWitness rightBound) ≤ budget := by
    change max (leftCell.range.overlapWitness leftBound - rightCell.range.overlapWitness rightBound)
      (-(leftCell.range.overlapWitness leftBound - rightCell.range.overlapWitness rightBound)) ≤ budget
    apply Fraction.Order.Basic.max_le close.1.le
    have reverse : -(leftCell.range.overlapWitness leftBound - rightCell.range.overlapWitness rightBound) =
        rightCell.range.overlapWitness rightBound - leftCell.range.overlapWitness leftBound := by ring1
    rw [reverse]
    exact close.2.le
  have comparison := Interval.abs_sub_le_of_readings leftValueInside rightValueInside leftWitness.1 rightWitness.1
  exact comparison.trans (Fraction.Order.Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl _) discrepancy)

end Purelib.Integration.NumericalFrontier

end
