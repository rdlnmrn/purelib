module
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Field
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Expectation
import Purelib.Measure.Distribution.Kernel.Basic
import Purelib.Measure.Distribution.Partition.ConditionalExpectation
import Purelib.Measure.Distribution.Partition.Jensen
import Purelib.Measure.Distribution.Partition.Positive
import Purelib.Measure.Event.Family
import Purelib.Measure.Filtration.Basic
public import Purelib.Measure.Filtration.Cellwise
public import Purelib.Measure.Filtration.ConditionalExpectation
import Purelib.Measure.Filtration.Maximal.L1
import Purelib.Measure.Weighted.Event
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Event.RationalOrder
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic

section
public section

/-!
# Finite first-crossing maximal inequality

A displayed list of rational observables has explicit first-crossing events
at every positive threshold.  These events are disjoint.  If each crossing
value transfers its restricted integral to one nonnegative terminal
observable, finite subadditivity and disjoint additivity give the sharp
Doob-style L1 maximal inequality.  The transfer property is explicit data;
there is no unbounded time, stopping-time space, or optional-limit theorem.
-/

namespace Purelib.Measure

open Purelib Purelib.Data.Rat Purelib.Data.List

namespace Filtration

/-- Select items where some retained partition-conditional expectation has square at least the threshold. -/
@[expose]
def conditionalSquareMaximumEvent {α : Type}
    {distribution : Distribution α}
    {finest : PositiveEventPartition distribution}
    (filtration : Filtration distribution finest)
    (terminal : α → Fraction.Rational) (threshold : Fraction.Rational) : α → Bool :=
  unionEvents (filtration.partitions.map fun partition =>
    Measure.atLeastEvent threshold (fun item =>
      partition.conditionalExpectation terminal item ^ 2))

/-- Select items where some retained partition-conditional second moment reaches the threshold. -/
@[expose]
def conditionalSecondMomentMaximumEvent {α : Type}
    {distribution : Distribution α}
    {finest : PositiveEventPartition distribution}
    (filtration : Filtration distribution finest)
    (terminal : α → Fraction.Rational) (threshold : Fraction.Rational) : α → Bool :=
  unionEvents (filtration.partitions.map fun partition =>
    Measure.atLeastEvent threshold
      (partition.conditionalExpectation fun item => terminal item ^ 2))

/-- On every original atom, a conditional-square threshold crossing implies a conditional-second-moment crossing for the
same partition list. -/
private theorem conditionalSquareEvents_implySecondMomentEvents
    {α : Type} (distribution : Distribution α)
    (terminal : α → Fraction.Rational) (threshold : Fraction.Rational) :
    ∀ partitions : List (PositiveEventPartition distribution),
      EventImpliesOn distribution.atoms
        (unionEvents (partitions.map fun partition =>
          Measure.atLeastEvent threshold (fun item =>
            partition.conditionalExpectation terminal item ^ 2)))
        (unionEvents (partitions.map fun partition =>
          Measure.atLeastEvent threshold
            (partition.conditionalExpectation fun item =>
              terminal item ^ 2)))
  | [] => by
      intro atom member selected
      exact Bool.noConfusion selected
  | partition :: remaining => by
      intro atom member selected
      cases headSelected : Measure.atLeastEvent threshold (fun item =>
          partition.conditionalExpectation terminal item ^ 2) atom.item
      · have tailSelected : unionEvents (remaining.map fun candidate =>
            Measure.atLeastEvent threshold (fun item =>
              candidate.conditionalExpectation terminal item ^ 2))
            atom.item = true := by
          simpa only [-eq_self, -iff_self, List.map_cons, unionEvents, unionEvent, headSelected,
            Bool.false_or] using selected
        have tailUpper :=
          conditionalSquareEvents_implySecondMomentEvents distribution
            terminal threshold remaining atom member tailSelected
        simp only [-eq_self, -iff_self, List.map_cons, unionEvents, unionEvent, tailUpper,
          Bool.or_true]; try rfl
      · have thresholdLower : threshold ≤
            partition.conditionalExpectation terminal atom.item ^ 2 :=
          of_decide_eq_true headSelected
        have squareJensen :=
          partition.conditionalExpectation_sq_le terminal atom member
        have upperSelected : Measure.atLeastEvent threshold
            (partition.conditionalExpectation fun item => terminal item ^ 2)
              atom.item = true :=
          decide_eq_true (thresholdLower.trans squareJensen)
        simp only [-eq_self, -iff_self, List.map_cons, unionEvents, unionEvent, upperSelected,
          Bool.true_or]; try rfl

/-- The exact filtration's conditional-square maximum event implies its conditional-second-moment maximum event on every
original atom. -/
theorem conditionalSquareMaximumEvent_implies_secondMoment {α : Type}
    {distribution : Distribution α}
    {finest : PositiveEventPartition distribution}
    (filtration : Filtration distribution finest)
    (terminal : α → Fraction.Rational) (threshold : Fraction.Rational) :
    EventImpliesOn distribution.atoms
      (filtration.conditionalSquareMaximumEvent terminal threshold)
      (filtration.conditionalSecondMomentMaximumEvent terminal threshold) :=
  conditionalSquareEvents_implySecondMomentEvents distribution terminal
    threshold filtration.partitions

/-- A positive squared-value threshold times its conditional-square maximum probability is at most the original second
moment.

The bound uses the exact compatible finite filtration and the original terminal observable, with no square-root choice.
-/
theorem conditionalExpectation_poweredL2_maximal {α : Type}
    {distribution : Distribution α}
    {finest : PositiveEventPartition distribution}
    (filtration : Filtration distribution finest)
    (compatible : filtration.CellwiseCompatible)
    (terminal : α → Fraction.Rational) (threshold : Fraction.Rational)
    (positive : 0 < threshold) :
    threshold * distribution.probability
        (filtration.conditionalSquareMaximumEvent terminal threshold) ≤
      distribution.expectation (fun item => terminal item ^ 2) := by
  have probabilityBound : distribution.probability
        (filtration.conditionalSquareMaximumEvent terminal threshold) ≤
      distribution.probability
        (filtration.conditionalSecondMomentMaximumEvent terminal threshold) :=
    eventWeight_mono
      (filtration.conditionalSquareMaximumEvent_implies_secondMoment
        terminal threshold)
  have scaled :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      probabilityBound positive.le
  have doob := filtration.conditionalExpectation_l1_maximal compatible
    (fun item => terminal item ^ 2) threshold positive (by
      intro atom member
      exact Fraction.Order.Arithmetic.sq_nonneg_direct (terminal atom.item))
  have doobNamed : threshold * distribution.probability
        (filtration.conditionalSecondMomentMaximumEvent terminal threshold) ≤
      distribution.expectation (fun item => terminal item ^ 2) := by
    simpa only [-eq_self, -iff_self, conditionalSecondMomentMaximumEvent,
      conditionalExpectationValues, Map.map_map, Function.comp_def]
      using doob
  exact scaled.trans doobNamed

end Filtration

end Purelib.Measure

end
