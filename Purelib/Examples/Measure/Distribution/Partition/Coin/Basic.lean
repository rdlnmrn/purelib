module
public import Purelib.Examples.Measure.Distribution.Coin.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Content.Basic
import Purelib.Measure.Classified.Basic
import Purelib.Measure.Filtration.Basic
public import Purelib.Measure.Distribution.Partition.Basic
import Purelib.Measure.Distribution.Partition.Positive
import Purelib.Measure.EventAlgebra.Simple.Basic
import Purelib.Measure.Event.Chain
import Purelib.Approximation.OneSided.Basic
import Purelib.Measure.Classified.FixedLawProcess
import Purelib.Approximation.OneSided.Located
import Purelib.Measure.Weighted.Event
import Purelib.Measure.EventAlgebra.Basic
import Purelib.Measure.Event.Family
import Purelib.Measure.Weighted.Basic

@[expose] public section

/-!
# Executable finite measure examples

All numerical examples reduce to finite rational calculations checked by the
kernel.  The final examples exercise the generic CCL area-request interface
without postulating a completed CCL value.
-/

namespace Purelib.Examples.Measure.Distribution.Partition.Coin.Basic

open Purelib.Examples
open Purelib.Measure
open Purelib.Examples.Measure.Distribution.Coin.Basic (fairCoin)

/-- The disjoint, covering tails-and-heads event partition of the original fair coin. -/
def coinPartition : EventPartition
  fairCoin where
  events := [fun outcome => !outcome, fun outcome => outcome]
  disjoint := by
    refine ⟨?_, ⟨?_, trivial⟩⟩
    · intro atom member both
      have itemTrue : atom.item = true := by
        simpa only [unionEvents, unionEvent, Bool.or_false] using both.2
      have impossible : false = true := by
        simpa only [itemTrue, Bool.not_true] using both.1
      exact Bool.noConfusion impossible
    · intro atom member both
      have impossible : false = true := by
        simpa only [unionEvents] using both.2
      exact Bool.noConfusion impossible
  covers := by
    intro atom member
    cases atom.item <;> rfl

/-- The probabilities of the two retained partition events sum to one. -/
example : (coinPartition.events.map
  fairCoin.probability).sum = 1 :=
  coinPartition.probabilities_sum_one

end Purelib.Examples.Measure.Distribution.Partition.Coin.Basic

end
