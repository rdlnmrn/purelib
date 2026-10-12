module
public import Purelib.Examples.Measure.Distribution.Coin.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Content.Basic
import Purelib.Measure.Classified.Basic
import Purelib.Measure.Filtration.Basic
import Purelib.Measure.Distribution.Partition.Basic
import Purelib.Measure.Distribution.Partition.Positive
import Purelib.Measure.EventAlgebra.Simple.Basic
public import Purelib.Measure.Event.Chain
import Purelib.Approximation.OneSided.Basic
import Purelib.Measure.Classified.FixedLawProcess
import Purelib.Approximation.OneSided.Located
import Purelib.Measure.EventAlgebra.Basic
import Purelib.Measure.Event.Family

@[expose] public section

/-!
# Executable finite measure examples

All numerical examples reduce to finite rational calculations checked by the
kernel.  The final examples exercise the generic CCL area-request interface
without postulating a completed CCL value.
-/

namespace Purelib.Examples.Measure.Distribution.Events.Chain.Coin.WorkedExamples

open Purelib.Examples
open Purelib.Measure
open Purelib.Examples.Measure.Distribution.Coin.Basic (fairCoin)

/-- The empty event, heads and full event form an increasing chain on the original fair-coin atoms. -/
theorem coinIncreasingEventChain :
  IncreasingEventChainOn fairCoin.atoms
    [fun _ => false, fun outcome => outcome, fun _ => true] := by
  constructor
  · intro atom member selected
    exact Bool.noConfusion selected
  · constructor
    · intro atom member selected
      rfl
    · trivial

/-- The increasing chain's finite union has the probability of its final full event. -/
example : fairCoin.probability
      (unionEvents [fun _ => false, fun outcome => outcome, fun _ => true]) =
    fairCoin.probability (fun _ => true) :=
  fairCoin.probability_unionEvents_eq_last_of_increasing
    (fun _ => false) [fun outcome => outcome, fun _ => true]
    coinIncreasingEventChain

/-- The full event, heads and empty event form a decreasing chain on the original fair-coin atoms. -/
theorem coinDecreasingEventChain :
  DecreasingEventChainOn fairCoin.atoms
    [fun _ => true, fun outcome => outcome, fun _ => false] := by
  constructor
  · intro atom member selected
    rfl
  · constructor
    · intro atom member selected
      exact Bool.noConfusion selected
    · trivial

/-- The decreasing chain's finite intersection has the probability of its final empty event. -/
example : fairCoin.probability
      (intersectionEvents (fun _ => true)
        [fun outcome => outcome, fun _ => false]) =
    fairCoin.probability (fun _ => false) :=
  fairCoin.probability_intersectionEvents_eq_last_of_decreasing
    (fun _ => true) [fun outcome => outcome, fun _ => false]
    coinDecreasingEventChain

end Purelib.Examples.Measure.Distribution.Events.Chain.Coin.WorkedExamples

end
