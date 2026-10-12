module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction
public import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Weighted.Event
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic

section
@[expose] public section

/-!
# Finite rational probability

A probability distribution is a displayed finite weighted list whose total is
exactly one.  Events are executable Boolean tests, so their probabilities and
expectations are exact rational calculations.
-/

namespace Purelib.Measure
namespace Distribution

open Purelib.Data.Rat
/-- Divide the original intersection probability by the strictly positive probability of the retained conditioning
event. -/
def conditionalProbability {α : Type} (distribution : Distribution α)
    (event condition : α → Bool)
    (_positive : 0 < distribution.probability condition) : Fraction.Rational :=
  distribution.probability (intersectionEvent event condition) /
    distribution.probability condition

/-- Conditional probability on the supplied positive-mass event is nonnegative. -/
theorem conditionalProbability_nonneg {α : Type}
    (distribution : Distribution α) (event condition : α → Bool)
    (positive : 0 < distribution.probability condition) :
    0 ≤ distribution.conditionalProbability event condition positive := by
  apply Fraction.Order.Field.div_nonneg_direct
  · exact distribution.probability_nonneg _
  · exact positive.le

/-- Conditional probability on the supplied positive-mass event is at most one. -/
theorem conditionalProbability_le_one {α : Type}
    (distribution : Distribution α) (event condition : α → Bool)
    (positive : 0 < distribution.probability condition) :
    distribution.conditionalProbability event condition positive ≤ 1 := by
  apply (Fraction.Order.Field.div_le_iff_pos positive).2
  rw [one_mul]
  exact eventWeight_intersection_le_right distribution.atoms event condition
end Distribution

end Purelib.Measure

end
