module
import Purelib.Data.Rat.Distance.Basic
public import Purelib.Examples.Measure.Distribution.Coin.Basic

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
public import Purelib.Measure.Content.Convergence
import Purelib.Measure.EventAlgebra.Basic
public import Purelib.Measure.Distribution.Content
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Measure.Weighted.Basic

@[expose] public section

/-!
# Executable finite measure examples

All numerical examples reduce to finite rational calculations checked by the
kernel.  The final examples exercise the generic CCL area-request interface
without postulating a completed CCL value.
-/

namespace Purelib.Examples.Measure.Content.Integral.Budget.Coin.WorkedExamples

open Purelib
open Purelib.Examples
open Purelib.Measure
open Purelib.Examples.Measure.Distribution.Coin.Basic (coinNumber fairCoin reverseCoinNumber)

/-- The unit error envelope comparing the fair-coin number and its reversed indicator.

The original finite atoms witness nonnegativity and pointwise domination of the integral difference. -/
def coinIntegralErrorBudget :
  Content.IntegralErrorBudget
    fairCoin.toContent coinNumber
      reverseCoinNumber where
  envelope _ := 1
  envelope_nonnegative atom member := by decide
  dominates atom member := by
    cases atom.item <;> decide

/-- The two fair-coin expectations differ by at most the retained integral-error budget. -/
example : Data.Rat.Distance.rationalSeparation
      (fairCoin.expectation coinNumber)
      (fairCoin.expectation reverseCoinNumber) ≤
    coinIntegralErrorBudget.error :=
  coinIntegralErrorBudget.integral_separation_le

/-- The monotone integral budget from the zero function to the coin-number function.

The original coin-number remainder is nonnegative and bounds the pointwise approximation gap. -/
def coinMonotoneIntegralBudget :
  Content.MonotoneIntegralBudget
    fairCoin.toContent (fun _ => 0) coinNumber where
  remainder := coinNumber
  remainder_nonnegative atom member := by
    cases atom.item <;> decide
  approximation_le atom member := by
    cases atom.item <;> decide
  gap_le_remainder atom member := by
    cases atom.item <;> decide

/-- The monotone coin integral approximation has error strictly below three quarters. -/
example : Data.Rat.Distance.rationalSeparation
      (fairCoin.expectation fun _ => 0)
      (fairCoin.expectation coinNumber) < 3 / 4 := by
  apply coinMonotoneIntegralBudget.accurate (3 / 4)
  decide

end Purelib.Examples.Measure.Content.Integral.Budget.Coin.WorkedExamples

end
