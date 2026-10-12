module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Expectation
import Purelib.Measure.Distribution.Maximal.FirstCrossing
public import Purelib.Measure.Distribution.Partition.ConditionalExpectation
import Purelib.Measure.Distribution.Partition.Maximal
import Purelib.Measure.Event.Family
import Purelib.Measure.Filtration.ConditionalExpectation
import Purelib.Measure.Filtration.Maximal.L1
import Purelib.Measure.Filtration.Maximal.L2
import Purelib.Data.Rat.Fraction
import Purelib.Examples.Measure.Distribution.Coin.Basic
public import Purelib.Examples.Measure.Distribution.Partition.Positive.Coin.Basic
import Purelib.Examples.Measure.Filtration.Coin.WorkedExamples
import Purelib.Measure.Event.RationalOrder

import Purelib.Tactic.QuotientFreeOmega

@[expose] public section

/-!
# Executable finite measure examples

All numerical examples reduce to finite rational calculations checked by the
kernel.  The final examples exercise the generic CCL area-request interface
without postulating a completed CCL value.
-/

namespace Purelib.Examples.Measure.Distribution.Partition.Expectation.Coin.Basic

open Purelib.Data.Rat
open Purelib.Examples
open Purelib.Examples.Measure.Distribution.Coin.Basic (coinPayoff fairCoin)
open Purelib.Examples.Measure.Distribution.Partition.Positive.Coin.Basic (wholeCoinPartition)
open Purelib.Examples.Measure.Filtration.Coin.WorkedExamples (coinFiltration coinFiltrationCellwiseCompatible)

/-- The coin payoff conditioned on the original positive singleton partition. -/
def partitionCoinPayoff : Bool →
  Fraction.Rational :=
  Measure.Distribution.Partition.Positive.Coin.Basic.positiveCoinPartition.conditionalExpectation
    coinPayoff

/-- The coin payoff conditioned on the original whole-event partition. -/
def wholeCoinPayoff : Bool →
  Fraction.Rational :=
  wholeCoinPartition.conditionalExpectation
    coinPayoff

/-- The displayed two-stage payoff process satisfies the L1 maximal bound at threshold five halves. -/
example : (5 / 2 : Fraction.Rational) * fairCoin.probability
      (Purelib.Measure.unionEvents ([wholeCoinPayoff,
        coinPayoff].map
        (Purelib.Measure.atLeastEvent (5 / 2)))) ≤
    fairCoin.expectation coinPayoff := by
  apply fairCoin.twoStage_l1_maximal (5 / 2) (by decide)
  · intro atom member
    cases atom.item <;> decide
  · decide

/-- The whole-partition conditional expectation and terminal payoff satisfy the two-stage L1 maximal bound. -/
example : (5 / 2 : Fraction.Rational) * fairCoin.probability
      (Purelib.Measure.unionEvents
        ([wholeCoinPartition.conditionalExpectation
          coinPayoff,
          coinPayoff].map (Purelib.Measure.atLeastEvent (5 / 2)))) ≤
    fairCoin.expectation coinPayoff :=
  fairCoin.conditionalExpectation_twoStage_l1_maximal
    (5 / 2) (by decide) wholeCoinPartition
      coinPayoff (by
      intro atom member
      cases atom.item <;> decide)

/-- The retained coin filtration's conditional expectations satisfy the L1 maximal bound at threshold five halves. -/
example : (5 / 2 : Fraction.Rational) * fairCoin.probability
      (Purelib.Measure.unionEvents
        ((coinFiltration.conditionalExpectationValues
          coinPayoff).map
          (Purelib.Measure.atLeastEvent (5 / 2)))) ≤
    fairCoin.expectation coinPayoff :=
  coinFiltration.conditionalExpectation_l1_maximal
    coinFiltrationCellwiseCompatible coinPayoff
      (5 / 2) (by decide) (by
      intro atom member
      cases atom.item <;> decide)

/-- The filtration maximum crosses five halves with probability one half, while the terminal payoff expectation is two.
-/
example : fairCoin.probability
      (Purelib.Measure.unionEvents
        ((coinFiltration.conditionalExpectationValues
          coinPayoff).map
          (Purelib.Measure.atLeastEvent (5 / 2)))) = 1 / 2 ∧
    fairCoin.expectation coinPayoff = 2 := by
  decide

/-- The squared conditional-expectation maximum satisfies the L2 maximal bound at threshold five. -/
example : (5 : Fraction.Rational) * fairCoin.probability
      (coinFiltration.conditionalSquareMaximumEvent
        coinPayoff 5) ≤
    fairCoin.expectation (fun outcome => coinPayoff
      outcome ^ 2) :=
  coinFiltration.conditionalExpectation_poweredL2_maximal
    coinFiltrationCellwiseCompatible coinPayoff 5
      (by decide)

/-- The squared maximum event has probability one half and the terminal second moment is five. -/
example : fairCoin.probability
        (coinFiltration.conditionalSquareMaximumEvent
          coinPayoff 5) = 1 / 2 ∧
      fairCoin.expectation (fun outcome => coinPayoff
        outcome ^ 2) = 5 := by
  decide

/-- The displayed two-stage maximum has probability one half and terminal payoff expectation two. -/
example : fairCoin.probability
      (Purelib.Measure.unionEvents ([wholeCoinPayoff,
        coinPayoff].map
        (Purelib.Measure.atLeastEvent (5 / 2)))) = 1 / 2 ∧
    fairCoin.expectation coinPayoff = 2 := by
  decide

end Purelib.Examples.Measure.Distribution.Partition.Expectation.Coin.Basic

end
