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
import Purelib.Measure.EventAlgebra.Basic
import Purelib.Measure.EventAlgebra.Distribution
import Purelib.Measure.EventAlgebra.Content
public import Purelib.Measure.EventAlgebra.Bool
import Purelib.Measure.Distribution.Content

@[expose] public section

/-!
# Executable finite measure examples

All numerical examples reduce to finite rational calculations checked by the
kernel.  The final examples exercise the generic CCL area-request interface
without postulating a completed CCL value.
-/

namespace Purelib.Examples.Measure.EventAlgebra.Boolean.WorkedExamples

open Purelib.Measure
open Purelib.Examples
open Purelib.Examples.Measure.Distribution.Coin.Basic (fairCoin)

/-- The Boolean event-algebra code selecting heads. -/
def headsEventCode : boolEventAlgebra.Code :=
  (false, true)

/-- The Boolean event-algebra code selecting tails. -/
def tailsEventCode : boolEventAlgebra.Code :=
  (true, false)

/-- The tails atom has signature `[false, false, true, true]` across the four Boolean event codes. -/
example : boolEventAlgebra.signature false =
    [false, false, true, true] := by
  decide

/-- The heads atom has signature `[false, true, false, true]` across the four Boolean event codes. -/
example : boolEventAlgebra.signature true =
    [false, true, false, true] := by
  decide

/-- The heads code has fair-coin content one half. -/
example : boolEventAlgebra.measure fairCoin.toContent
  headsEventCode =
    1 / 2 := by
  decide

/-- The heads event probability is preserved by the signature distribution. -/
example : fairCoin.probability (boolEventAlgebra.evaluate
  headsEventCode) =
    (boolEventAlgebra.signatureDistribution fairCoin).probability
      (boolEventAlgebra.signatureEvent headsEventCode) :=
  boolEventAlgebra.probability_eq_signatureDistribution_probability
    fairCoin headsEventCode

/-- The Boolean atom distribution has two retained atoms. -/
example : (boolEventAlgebra.atomDistribution fairCoin).atoms.length = 2
  := by
  decide

/-- The heads event probability is preserved by the consolidated atom distribution. -/
example : fairCoin.probability (boolEventAlgebra.evaluate
  headsEventCode) =
    (boolEventAlgebra.atomDistribution fairCoin).probability
      (boolEventAlgebra.signatureEvent headsEventCode) :=
  boolEventAlgebra.probability_eq_atomDistribution_probability
    fairCoin headsEventCode

/-- The Boolean atom content has two retained atoms. -/
example :
    (boolEventAlgebra.atomContent fairCoin.toContent).atoms.length = 2
      := by
  decide

/-- The heads event measure is preserved by the atom content. -/
example : boolEventAlgebra.measure fairCoin.toContent
  headsEventCode =
    (boolEventAlgebra.atomContent fairCoin.toContent).measure
      (boolEventAlgebra.signatureEvent headsEventCode) :=
  boolEventAlgebra.measure_eq_atomContent_measure fairCoin.toContent
    headsEventCode

/-- The two event-code measures satisfy finite union-intersection valuation. -/
example : boolEventAlgebra.measure fairCoin.toContent
  headsEventCode +
      boolEventAlgebra.measure fairCoin.toContent
        tailsEventCode =
    boolEventAlgebra.measure fairCoin.toContent
        (boolEventAlgebra.union headsEventCode
          tailsEventCode) +
      boolEventAlgebra.measure fairCoin.toContent
        (boolEventAlgebra.intersection headsEventCode
          tailsEventCode) :=
  boolEventAlgebra.measure_valuation fairCoin.toContent
    headsEventCode
      tailsEventCode

end Purelib.Examples.Measure.EventAlgebra.Boolean.WorkedExamples

end
