module
import Purelib.Examples.Measure.Distribution.Coin.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Content.Basic
import Purelib.Measure.Classified.Basic
import Purelib.Measure.Filtration.Basic
import Purelib.Measure.Distribution.Partition.Basic
import Purelib.Measure.Distribution.Partition.Positive
import Purelib.Measure.EventAlgebra.Simple.Basic
import Purelib.Measure.Event.Chain
import Purelib.Approximation.OneSided.Basic
import Purelib.Measure.Classified.FixedLawProcess
import Purelib.Approximation.OneSided.Located
import Purelib.Measure.Event.RationalDistance
import Purelib.Measure.Distribution.Lp.L1
import Purelib.Measure.Weighted.Integral
import Purelib.Measure.EventAlgebra.Basic

@[expose] public section

/-!
# Executable finite measure examples

All numerical examples reduce to finite rational calculations checked by the
kernel.  The final examples exercise the generic CCL area-request interface
without postulating a completed CCL value.
-/

namespace Purelib.Examples.Measure.Distribution.Events.Distance.Coin.WorkedExamples

open Purelib.Measure
open Purelib.Examples
open Purelib.Examples.Measure.Distribution.Coin.Basic (fairCoin)

/-- The Boolean event that never selects an outcome. -/
def neverEvent (_ : Bool) : Bool :=
  false

/-- The fair-coin L1 distance between the heads indicator and zero event indicator is one half. -/
example : fairCoin.l1Distance
      (Distribution.indicator (fun outcome => outcome))
      (Distribution.indicator neverEvent) = 1 / 2 := by
  decide

/-- The symmetric difference of heads with the empty event has probability one half. -/
example : fairCoin.probability
    (symmetricDifferenceEvent (fun outcome => outcome)
      neverEvent) = 1 / 2 := by
  decide

/-- Both directions of the heads-versus-empty probability difference are bounded by the symmetric-difference
probability. -/
example :
    fairCoin.probability
      neverEvent -
          fairCoin.probability (fun outcome => outcome) ≤
        fairCoin.probability
          (symmetricDifferenceEvent (fun outcome => outcome)
            neverEvent) ∧
      fairCoin.probability (fun outcome => outcome) -
          fairCoin.probability
            neverEvent ≤
        fairCoin.probability
          (symmetricDifferenceEvent (fun outcome => outcome)
            neverEvent) :=
  fairCoin.probability_close_symmetricDifference
    (fun outcome => outcome) neverEvent

end Purelib.Examples.Measure.Distribution.Events.Distance.Coin.WorkedExamples

end
