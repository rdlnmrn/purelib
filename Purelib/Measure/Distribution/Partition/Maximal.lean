module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Expectation
import Purelib.Measure.Distribution.Maximal.FirstCrossing
public import Purelib.Measure.Distribution.Partition.ConditionalExpectation
import Purelib.Measure.Distribution.Partition.Positive
import Purelib.Measure.Distribution.Partition.Projection
import Purelib.Measure.Event.Family
import Purelib.Data.Rat.Fraction
public import Purelib.Measure.Event.RationalOrder
import Purelib.Measure.Weighted.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic

section
@[expose] public section

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

namespace Distribution

open Purelib in
open Purelib.Data.Rat in
/-- The two-stage list of partition conditional expectation and a nonnegative terminal observable satisfies the
positive-threshold maximal bound. -/
theorem conditionalExpectation_twoStage_l1_maximal {α : Type}
    (distribution : Distribution α) (threshold : Fraction.Rational)
    (positive : 0 < threshold)
    (partition : PositiveEventPartition distribution)
    (terminal : α → Fraction.Rational)
    (terminalNonnegative : ∀ atom, atom ∈ distribution.atoms →
      0 ≤ terminal atom.item) :
    threshold * distribution.probability
        (unionEvents
          ([partition.conditionalExpectation terminal, terminal].map
            (Measure.atLeastEvent threshold))) ≤
      distribution.expectation terminal := by
  apply distribution.twoStage_l1_maximal threshold positive
    (partition.conditionalExpectation terminal) terminal terminalNonnegative
  exact (partition.eventIntegral_conditionalExpectation_atLeast terminal
    threshold).le

end Distribution

end Purelib.Measure

end
