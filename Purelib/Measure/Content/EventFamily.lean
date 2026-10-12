module

import Purelib.Data.Rat.Fraction.Order
public import Purelib.Measure.Content.Basic
public import Purelib.Measure.Event.Family
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

section
@[expose] public section

/-!
# Finite event families

This is the finite constructive content of subadditivity and disjoint
additivity.  Event families are displayed lists; no countable family or
sigma-additivity principle is introduced.
-/

namespace Purelib.Measure
namespace Distribution
end Distribution

namespace Content

/-- The mass of a finite event union is at most the sum of the original event masses. -/
theorem measure_unionEvents_le_sum {α : Type}
    (content : Content α) (events : List (α → Bool)) :
    content.measure (unionEvents events) ≤
      (events.map content.measure).sum :=
  eventWeight_unionEvents_le_sum content.atoms events

/-- Events disjoint on the exact retained content atoms have union mass equal to their mass sum. -/
theorem measure_unionEvents_of_disjoint {α : Type}
    (content : Content α) {events : List (α → Bool)}
    (disjoint : MutuallyDisjointOn content.atoms events) :
    content.measure (unionEvents events) =
      (events.map content.measure).sum :=
  eventWeight_unionEvents_of_disjoint content.atoms disjoint

end Content

end Purelib.Measure

end
