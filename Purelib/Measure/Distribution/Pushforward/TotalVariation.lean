module
import Purelib.Data.Rat.Distance.Basic
import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Distribution.TotalVariation.Basic
import Purelib.Measure.Distribution.Kernel.Basic
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
/-- Pushing both finite laws through the same function cannot increase total variation distance. -/
theorem totalVariationDistance_map_le {α β : Type}
    [DecidableEq α] [DecidableEq β]
    (left right : Distribution α) (function : α → β) :
    (left.map function).totalVariationDistance (right.map function) ≤
      left.totalVariationDistance right := by
  let event := (left.map function).totalVariationEvent (right.map function)
  calc
    (left.map function).totalVariationDistance (right.map function) =
        (left.map function).probability event -
          (right.map function).probability event :=
      ((left.map function).probability_sub_at_totalVariationEvent
        (right.map function)).symm
    _ = left.probability (fun item => event (function item)) -
        right.probability (fun item => event (function item)) := by
      rw [left.map_probability, right.map_probability]
    _ ≤ Distance.rationalSeparation
        (left.probability (fun item => event (function item)))
        (right.probability (fun item => event (function item))) :=
      Fraction.Order.Basic.le_max_left _ _
    _ ≤ left.totalVariationDistance right :=
      left.probability_separation_le_totalVariationDistance right _
end Distribution

end Purelib.Measure

end
