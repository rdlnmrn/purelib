module
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Expectation
import Purelib.Measure.Distribution.Kernel.Basic
public import Purelib.Measure.Distribution.TotalVariation.Basic
import Purelib.Measure.Distribution.TotalVariation.Expectation
import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic

section
@[expose] public section

/-!
# Total variation distance between finite rational laws

The duplicate-free union of two displayed atom catalogues supports their
signed difference.  A decidable comparison of the two singleton masses gives
an executable Hahn event.  For probability distributions this event attains
the largest possible event-probability discrepancy, because the positive and
negative Jordan masses agree.

Thus total variation is an exact rational computation here.  The development
proves its sharp event bound, half-L1 formula, metric laws modulo evaluation
equivalence, contraction under pushforward, and the coupling inequality.
-/

namespace Purelib.Measure

namespace Distribution

open Purelib.Data.Rat in
/-- Binding two original laws through the same finite transition kernel cannot increase total variation distance. -/
theorem totalVariationDistance_bind_le {α β : Type}
    [DecidableEq α] [DecidableEq β]
    (left right : Distribution α) (transition : α → Distribution β) :
    (left.bind transition).totalVariationDistance
        (right.bind transition) ≤
      left.totalVariationDistance right := by
  let event := (left.bind transition).totalVariationEvent
    (right.bind transition)
  let eventProbability := fun item => (transition item).probability event
  calc
    (left.bind transition).totalVariationDistance
          (right.bind transition) =
        (left.bind transition).probability event -
          (right.bind transition).probability event :=
      ((left.bind transition).probability_sub_at_totalVariationEvent
        (right.bind transition)).symm
    _ = left.expectation eventProbability -
        right.expectation eventProbability := by
      rw [left.bind_probability, right.bind_probability]
    _ ≤ Distance.rationalSeparation (left.expectation eventProbability)
        (right.expectation eventProbability) :=
      Fraction.Order.Basic.le_max_left _ _
    _ ≤ left.totalVariationDistance right := by
      apply left.expectation_separation_le_totalVariationDistance_of_unitInterval
        right eventProbability
      · intro item
        exact (transition item).probability_nonneg event
      · intro item
        exact (transition item).probability_le_one event
end Distribution

end Purelib.Measure

end
