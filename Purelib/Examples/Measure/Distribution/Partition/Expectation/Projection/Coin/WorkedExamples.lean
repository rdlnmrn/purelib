module
import Purelib.Data.Rat.Fraction
import Purelib.Examples.Measure.Distribution.Coin.Basic
import Purelib.Examples.Measure.Distribution.Partition.Expectation.Coin.Basic
public import Purelib.Examples.Measure.Distribution.Partition.Positive.Coin.Basic
import Purelib.Examples.Measure.Distribution.Partition.Refinement.Coin.WorkedExamples
import Purelib.Examples.Measure.Filtration.Coin.WorkedExamples

import Purelib.Tactic.QuotientFreeOmega
public import Purelib.Measure.Distribution.Partition.Cellwise
import Purelib.Measure.Filtration.Martingale.Basic
import Purelib.Measure.Distribution.Partition.EssentialBound
import Purelib.Measure.Distribution.Partition.Covariance
import Purelib.Measure.Distribution.Conditioning.Covariance.Basic
import Purelib.Measure.Weighted.Error
import Purelib.Measure.Filtration.Martingale.QuadraticVariation
import Purelib.Measure.Filtration.Martingale.Stopping
import Purelib.Measure.Distribution.Partition.Characterization
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Partition.Positive
import Purelib.Measure.Weighted.Basic
import Purelib.Measure.Distribution.Partition.Projection
import Purelib.Measure.Distribution.Partition.Jensen
import Purelib.Measure.Distribution.Partition.Moments
import Purelib.Measure.Distribution.Stability
import Purelib.Measure.Filtration.ConditionalExpectation

@[expose] public section

/-!
# Executable finite measure examples

All numerical examples reduce to finite rational calculations checked by the
kernel.  The final examples exercise the generic CCL area-request interface
without postulating a completed CCL value.
-/

namespace Purelib.Examples.Measure.Distribution.Partition.Expectation.Projection.Coin.WorkedExamples

open Purelib.Data.Rat
open Purelib.Examples
open Purelib.Measure
open Purelib.Examples.Measure.Distribution
open Purelib.Examples.Measure.Distribution.Coin.Basic (coinNumber coinPayoff fairCoin reverseCoinNumber)
open Purelib.Examples.Measure.Distribution.Partition.Expectation.Coin.Basic (partitionCoinPayoff wholeCoinPayoff)
open Purelib.Examples.Measure.Distribution.Partition.Positive.Coin.Basic (positiveCoinPartition wholeCoinPartition)
open Purelib.Examples.Measure.Filtration.Coin.WorkedExamples (coinFiltration)

/-- The explicit cellwise representation of the zero payoff on the whole-event coin partition. -/
def
  zeroCoinPayoffCellwise
  :
    PositiveEventPartition.CellwiseObservable wholeCoinPartition
      (fun _ : Bool => (0 : Fraction.Rational)) where
  cellValue := fun _ => 0
  agrees := by
    intro event eventMember atom atomMember selected
    rfl

/-- The singleton-partition conditional payoff retains the original values one and three. -/
example : partitionCoinPayoff false = 1 ∧
  partitionCoinPayoff true = 3 := by
  decide

/-- Conditioning the singleton conditional payoff again on the same partition leaves it unchanged. -/
example (outcome : Bool) :
    positiveCoinPartition.conditionalExpectation
      partitionCoinPayoff outcome =
      partitionCoinPayoff outcome :=
  positiveCoinPartition.conditionalExpectation_idempotent
    coinPayoff outcome

/-- Conditioning the fine-partition payoff on the whole-event partition recovers the original coarse payoff. -/
example (outcome : Bool) :
    wholeCoinPartition.conditionalExpectation
      partitionCoinPayoff outcome =
      wholeCoinPayoff outcome :=
  Measure.Distribution.Partition.Refinement.Coin.WorkedExamples.coinPartitionRefinesWhole.conditionalExpectation_tower
    coinPayoff outcome

/-- The retained coin filtration satisfies the conditional-expectation tower identity. -/
example (outcome : Bool) :
    coinFiltration.coarsest.conditionalExpectation
        (positiveCoinPartition.conditionalExpectation
          coinPayoff) outcome =
      coinFiltration.coarsest.conditionalExpectation
        coinPayoff outcome :=
  coinFiltration.conditionalExpectation_tower
    coinPayoff outcome

/-- The canonical coin martingale preserves expectation from its initial value to its terminal conditional payoff. -/
example : fairCoin.expectation
      (positiveCoinPartition.conditionalExpectation
        coinPayoff) =
    fairCoin.expectation
      (coinFiltration.canonicalMartingale
        coinPayoff).initialValue :=
  (coinFiltration.canonicalMartingale
    coinPayoff)
    |>.expectation_terminal_eq_initial

/-- The canonical two-stage coin martingale has expected quadratic variation one. -/
example : ((coinFiltration.canonicalMartingale
  coinPayoff)
    |>.expectedQuadraticVariation) = 1 := by
  decide

/-- The fine payoff second moment equals the coarse payoff second moment plus quadratic variation one. -/
example : fairCoin.poweredL2
  partitionCoinPayoff =
    fairCoin.poweredL2
      wholeCoinPayoff + 1 := by
  have identity := (coinFiltration.canonicalMartingale
    coinPayoff)
    |>.poweredL2_terminal_eq_initial_add_expectedQuadraticVariation
  have variation : ((coinFiltration.canonicalMartingale
    coinPayoff)
      |>.expectedQuadraticVariation) = 1 := by
    decide
  rw [variation] at identity
  simpa only [partitionCoinPayoff,
    wholeCoinPayoff,
    Filtration.canonicalMartingale_initialValue, coinFiltration,
    Filtration.coarsest] using identity

/-- The fine payoff variance equals the coarse payoff variance plus quadratic variation one. -/
example : fairCoin.variance
  partitionCoinPayoff =
    fairCoin.variance
      wholeCoinPayoff + 1 := by
  have identity := (coinFiltration.canonicalMartingale
    coinPayoff)
    |>.variance_terminal_eq_initial_add_expectedQuadraticVariation
  have variation : ((coinFiltration.canonicalMartingale
    coinPayoff)
      |>.expectedQuadraticVariation) = 1 := by
    decide
  rw [variation] at identity
  simpa only [partitionCoinPayoff,
    wholeCoinPayoff,
    Filtration.canonicalMartingale_initialValue, coinFiltration,
    Filtration.coarsest] using identity

/-- The canonical coin martingale's variance is nondecreasing from its coarse to fine stage. -/
example : fairCoin.variance
  wholeCoinPayoff ≤
    fairCoin.variance
      partitionCoinPayoff := by
  simpa only [partitionCoinPayoff,
    wholeCoinPayoff,
    Filtration.canonicalMartingale_initialValue, coinFiltration,
    Filtration.coarsest] using
    (coinFiltration.canonicalMartingale
      coinPayoff)
      |>.variance_initial_le_terminal

/-- Stopping the canonical coin martingale immediately returns its original coarse payoff. -/
example (outcome : Bool) :
    (((coinFiltration.canonicalMartingale
      coinPayoff).stopImmediately)
      |>.stoppedValue) outcome = wholeCoinPayoff
        outcome := by
  simpa only [wholeCoinPayoff,
    Filtration.canonicalMartingale_initialValue, coinFiltration,
    Filtration.coarsest] using
      Filtration.Martingale.StoppingStrategy.stoppedValue_stopImmediately
        (coinFiltration.canonicalMartingale
          coinPayoff) outcome

/-- Continuing the canonical coin martingale to its end returns its original fine payoff. -/
example (outcome : Bool) :
    (((coinFiltration.canonicalMartingale
      coinPayoff).continueToEnd)
      |>.stoppedValue) outcome =
        partitionCoinPayoff outcome := by
  simpa only [partitionCoinPayoff] using
    Filtration.Martingale.StoppingStrategy.stoppedValue_continueToEnd
      (coinFiltration.canonicalMartingale
        coinPayoff) outcome

/-- Immediate stopping preserves the original initial payoff expectation. -/
example : fairCoin.expectation
      ((coinFiltration.canonicalMartingale
        coinPayoff).stopImmediately
        |>.stoppedValue) = fairCoin.expectation
          wholeCoinPayoff := by
  simpa only [wholeCoinPayoff,
    Filtration.canonicalMartingale_initialValue, coinFiltration,
    Filtration.coarsest] using
      (coinFiltration.canonicalMartingale
        coinPayoff).stopImmediately
        |>.expectation_stoppedValue_eq_initial

/-- The original partition refinement makes conditional-payoff variance nondecreasing. -/
example : fairCoin.variance
  wholeCoinPayoff ≤
    fairCoin.variance
      partitionCoinPayoff :=

    Partition.Refinement.Coin.WorkedExamples.coinPartitionRefinesWhole.variance_conditionalExpectation_mono
    coinPayoff

/-- The whole-event conditional payoff is constantly two. -/
example : wholeCoinPayoff false = 2 ∧
  wholeCoinPayoff true = 2 := by
  decide

/-- The zero comparator and whole-event conditional payoff satisfy the squared L2 Pythagorean identity. -/
example : fairCoin.poweredL2Distance coinPayoff (fun _
  => 0) =
    fairCoin.poweredL2Distance coinPayoff
      wholeCoinPayoff +
      fairCoin.poweredL2Distance
        wholeCoinPayoff (fun _ => 0) :=
  wholeCoinPartition.poweredL2Distance_pythagorean
    coinPayoff
    (fun _ => 0) zeroCoinPayoffCellwise

/-- The whole-event conditional payoff is no farther in squared L2 from the payoff than the cellwise zero comparator. -/
example : fairCoin.poweredL2Distance coinPayoff
  wholeCoinPayoff ≤
    fairCoin.poweredL2Distance coinPayoff (fun _ => 0)
      :=
  wholeCoinPartition.poweredL2Distance_conditionalExpectation_le
    coinPayoff
    (fun _ => 0) zeroCoinPayoffCellwise

/-- The displayed squared L2 decomposition is five equals one plus four. -/
example : fairCoin.poweredL2Distance coinPayoff (fun _
  => 0) = 5 ∧
    fairCoin.poweredL2Distance coinPayoff
      wholeCoinPayoff = 1 ∧
      fairCoin.poweredL2Distance
        wholeCoinPayoff (fun _ => 0) = 4 := by
  decide

/-- A cellwise candidate preserving the original cell integrals equals the retained conditional payoff on every source
atom. -/
example (candidate : Bool → Fraction.Rational)
    (cellwise : PositiveEventPartition.CellwiseObservable
      wholeCoinPartition candidate)
    (preserves : ∀ event, event ∈ wholeCoinPartition.events →
      fairCoin.eventIntegral event candidate =
        fairCoin.eventIntegral event coinPayoff) :
    ∀ atom, atom ∈ fairCoin.atoms →
      candidate atom.item = wholeCoinPayoff
        atom.item :=
  wholeCoinPartition.candidate_eq_conditionalExpectation_on_atoms
    coinPayoff candidate cellwise preserves

/-- Conditioning on the whole-event partition cannot increase the payoff variance. -/
example : fairCoin.variance
  wholeCoinPayoff ≤
    fairCoin.variance coinPayoff :=
  wholeCoinPartition.variance_conditionalExpectation_le
    coinPayoff

/-- Conditioning the centered coin payoff cannot increase its powered L1 value. -/
example : fairCoin.poweredL1
      (wholeCoinPartition.conditionalExpectation fun outcome =>
        coinPayoff outcome - 2) ≤
    fairCoin.poweredL1 (fun outcome => coinPayoff
      outcome - 2) :=
  wholeCoinPartition.poweredL1_conditionalExpectation_le
    (fun outcome => coinPayoff outcome - 2)

/-- The conditioned centered payoff has powered L1 zero while the original centered payoff has powered L1 one. -/
example : fairCoin.poweredL1
      (wholeCoinPartition.conditionalExpectation fun outcome =>
        coinPayoff outcome - 2) = 0 ∧
    fairCoin.poweredL1 (fun outcome => coinPayoff
      outcome - 2) = 1 := by
  decide

/-- Conditioning both coin indicators cannot increase their L1 distance. -/
example : fairCoin.l1Distance
      (wholeCoinPartition.conditionalExpectation
        coinNumber)
      (wholeCoinPartition.conditionalExpectation
        reverseCoinNumber) ≤
    fairCoin.l1Distance coinNumber
      reverseCoinNumber :=
  wholeCoinPartition.l1Distance_conditionalExpectation_le
    coinNumber reverseCoinNumber

/-- The conditioned indicator L1 distance is zero while the original distance is one. -/
example : fairCoin.l1Distance
      (wholeCoinPartition.conditionalExpectation
        coinNumber)
      (wholeCoinPartition.conditionalExpectation
        reverseCoinNumber) = 0 ∧
    fairCoin.l1Distance coinNumber
      reverseCoinNumber = 1 := by
  decide

/-- The whole-event conditional coin indicator is nonnegative on every retained atom. -/
example (atom : Weighted Bool) (member : atom ∈ fairCoin.atoms) :
    0 ≤ wholeCoinPartition.conditionalExpectation
      coinNumber atom.item :=
  wholeCoinPartition.conditionalExpectation_nonneg_on_atoms
    coinNumber
    (by
      intro candidate candidateMember
      cases candidate.item <;> decide)
    atom member

/-- Conditioning preserves the indicator-to-payoff order on every retained atom. -/
example (atom : Weighted Bool) (member : atom ∈ fairCoin.atoms) :
    wholeCoinPartition.conditionalExpectation
      coinNumber atom.item ≤
      wholeCoinPartition.conditionalExpectation
        coinPayoff atom.item :=
  wholeCoinPartition.conditionalExpectation_mono_on_atoms
    coinNumber coinPayoff (by
      intro candidate candidateMember
      cases candidate.item <;> decide)
    atom member

/-- The whole-event conditional indicator has essential maximum no larger than the original indicator. -/
example : fairCoin.essentialMaximumMagnitude
      (wholeCoinPartition.conditionalExpectation
        coinNumber) ≤
    fairCoin.essentialMaximumMagnitude coinNumber :=

    Partition.Positive.Coin.Basic.wholeCoinPartition.essentialMaximumMagnitude_conditionalExpectation_le
    coinNumber

/-- The conditioned and original indicator maxima are one half and one. -/
example : fairCoin.essentialMaximumMagnitude
      (wholeCoinPartition.conditionalExpectation
        coinNumber) = 1 / 2 ∧
    fairCoin.essentialMaximumMagnitude coinNumber = 1 :=
      by
  decide

/-- Conditioning both indicators cannot increase their essential maximum distance. -/
example : fairCoin.essentialMaximumDistance
      (wholeCoinPartition.conditionalExpectation
        coinNumber)
      (wholeCoinPartition.conditionalExpectation
        reverseCoinNumber) ≤
    fairCoin.essentialMaximumDistance coinNumber
      reverseCoinNumber :=

    Partition.Positive.Coin.Basic.wholeCoinPartition.essentialMaximumDistance_conditionalExpectation_le
    coinNumber reverseCoinNumber

/-- The conditioned indicator maximum distance is zero while the original distance is one. -/
example : fairCoin.essentialMaximumDistance
      (wholeCoinPartition.conditionalExpectation
        coinNumber)
      (wholeCoinPartition.conditionalExpectation
        reverseCoinNumber) = 0 ∧
    fairCoin.essentialMaximumDistance coinNumber
      reverseCoinNumber = 1 := by
  decide

/-- The coarse payoff variance is zero and the original payoff variance is one. -/
example : fairCoin.variance
  wholeCoinPayoff = 0 ∧
    fairCoin.variance coinPayoff = 1 := by
  decide

/-- Singleton conditional expectation distributes over addition of the original payoff. -/
example (outcome : Bool) :
    positiveCoinPartition.conditionalExpectation
        (fun candidate => coinPayoff candidate +
          coinPayoff candidate) outcome =
      partitionCoinPayoff outcome +
        partitionCoinPayoff outcome :=
  positiveCoinPartition.conditionalExpectation_add
    coinPayoff coinPayoff
    outcome

/-- Singleton conditional expectation preserves the original payoff expectation. -/
example : fairCoin.expectation
  partitionCoinPayoff =
    fairCoin.expectation coinPayoff :=
  positiveCoinPartition.expectation_conditionalExpectation
    coinPayoff

/-- Singleton conditional expectation preserves the original payoff integral on the heads cell. -/
example : fairCoin.eventIntegral (fun outcome => outcome)
      partitionCoinPayoff =
    fairCoin.eventIntegral (fun outcome => outcome)
      coinPayoff := by
  apply positiveCoinPartition.eventIntegral_conditionalExpectation
  change (fun outcome : Bool => outcome) ∈
    [(fun outcome => !outcome), (fun outcome => outcome)]
  exact List.mem_cons_of_mem _ List.mem_cons_self

/-- The singleton partition recovers total payoff variance from conditional variance and mean displacement. -/
example :
    (positiveCoinPartition.events.map fun event =>
        fairCoin.probability event *
          (fairCoin.conditionalVariance event coinPayoff
            +
            (fairCoin.conditionalMean event coinPayoff -
              fairCoin.expectation coinPayoff) ^ 2)).sum
                =
      fairCoin.variance coinPayoff :=
  positiveCoinPartition.total_variance
    coinPayoff

/-- The weighted conditional variances plus variance of conditional means recover the original payoff variance. -/
example :
    (positiveCoinPartition.events.map fun event =>
        fairCoin.probability event *
          fairCoin.conditionalVariance event
            coinPayoff).sum +
      fairCoin.variance
        (positiveCoinPartition.conditionalExpectation
          coinPayoff) =
      fairCoin.variance coinPayoff :=
  positiveCoinPartition.total_variance_decomposition
    coinPayoff

/-- The singleton partition recovers the original payoff second moment from conditional variance and squared means. -/
example :
    (positiveCoinPartition.events.map fun event =>
        fairCoin.probability event *
          (fairCoin.conditionalVariance event coinPayoff
            +
            fairCoin.conditionalMean event coinPayoff ^
              2)).sum =
      fairCoin.expectation (fun outcome => coinPayoff
        outcome ^ 2) :=
  positiveCoinPartition.total_secondMoment
    coinPayoff

/-- The retained total-second-moment sum equals five. -/
example :
    (positiveCoinPartition.events.map fun event =>
        fairCoin.probability event *
          (fairCoin.conditionalVariance event coinPayoff
            +
            fairCoin.conditionalMean event coinPayoff ^
              2)).sum = 5 := by
  decide

/-- The singleton partition recovers the original indicator covariance from conditional covariance and mean
displacements. -/
example :
    (positiveCoinPartition.events.map fun event =>
        fairCoin.probability event *
          (fairCoin.conditionalCovariance event
              coinNumber reverseCoinNumber +
            (fairCoin.conditionalMean event coinNumber -
              fairCoin.expectation coinNumber) *
            (fairCoin.conditionalMean event
              reverseCoinNumber -
              fairCoin.expectation
                reverseCoinNumber))).sum =
      fairCoin.covariance coinNumber
        reverseCoinNumber :=
  positiveCoinPartition.total_covariance
    coinNumber reverseCoinNumber

/-- The weighted conditional covariances plus covariance of conditional means recover the original indicator covariance.
-/
example :
    (positiveCoinPartition.events.map fun event =>
        fairCoin.probability event *
          fairCoin.conditionalCovariance event
            coinNumber reverseCoinNumber).sum +
      fairCoin.covariance
        (positiveCoinPartition.conditionalExpectation
          coinNumber)
        (positiveCoinPartition.conditionalExpectation
          reverseCoinNumber) =
      fairCoin.covariance coinNumber
        reverseCoinNumber :=
  positiveCoinPartition.total_covariance_decomposition
    coinNumber reverseCoinNumber

/-- The two conditional coin indicators have covariance minus one quarter. -/
example : fairCoin.covariance
      (positiveCoinPartition.conditionalExpectation
        coinNumber)
      (positiveCoinPartition.conditionalExpectation
        reverseCoinNumber) =
    -1 / 4 := by
  decide

/-- The retained total-covariance sum equals minus one quarter. -/
example :
    (positiveCoinPartition.events.map fun event =>
        fairCoin.probability event *
          (fairCoin.conditionalCovariance event
              coinNumber reverseCoinNumber +
            (fairCoin.conditionalMean event coinNumber -
              fairCoin.expectation coinNumber) *
            (fairCoin.conditionalMean event
              reverseCoinNumber -
              fairCoin.expectation
                reverseCoinNumber))).sum = -1 / 4 := by
  decide

/-- The retained total-variance sum equals one. -/
example :
    (positiveCoinPartition.events.map fun event =>
        fairCoin.probability event *
          (fairCoin.conditionalVariance event coinPayoff
            +
            (fairCoin.conditionalMean event coinPayoff -
              fairCoin.expectation coinPayoff) ^ 2)).sum
                = 1 := by
  decide

/-- A uniform symmetric error on the original coin atoms bounds both signed expectation differences by the same
tolerance. -/
example (left right : Bool → Fraction.Rational) (epsilon : Fraction.Rational)
    (bounded : Purelib.Measure.SymmetricErrorOn fairCoin.atoms
      (fun _ => epsilon) left right) :
    fairCoin.expectation right - fairCoin.expectation
      left ≤ epsilon ∧
      fairCoin.expectation left - fairCoin.expectation
        right ≤ epsilon :=
  fairCoin.expectation_close_of_uniform epsilon left right bounded

end Purelib.Examples.Measure.Distribution.Partition.Expectation.Projection.Coin.WorkedExamples

end
