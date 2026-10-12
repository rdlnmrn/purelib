module
public import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Kernel.Basic

import Purelib.Data.Rat.Fraction.Order
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

/-- The probability of a finite event union is at most the sum of its individual probabilities. -/
theorem probability_unionEvents_le_sum {α : Type}
    (distribution : Distribution α) (events : List (α → Bool)) :
    distribution.probability (unionEvents events) ≤
      (events.map distribution.probability).sum :=
  eventWeight_unionEvents_le_sum distribution.atoms events

/-- Events mutually disjoint on the retained distribution atoms have union probability equal to their probability sum.
-/
theorem probability_unionEvents_of_disjoint {α : Type}
    (distribution : Distribution α) {events : List (α → Bool)}
    (disjoint : MutuallyDisjointOn distribution.atoms events) :
    distribution.probability (unionEvents events) =
      (events.map distribution.probability).sum :=
  eventWeight_unionEvents_of_disjoint distribution.atoms disjoint

end Distribution

namespace Content
end Content

end Purelib.Measure

end
