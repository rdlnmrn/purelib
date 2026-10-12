module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Distance.Basic
public import Purelib.Examples.Measure.Distribution.Coin.Basic
import Purelib.Examples.Measure.Distribution.Conditioned.Coin.Basic
import Purelib.Examples.Measure.Distribution.Partition.Positive.Coin.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.EssentialMaximum.Lp
import Purelib.Measure.Distribution.Conditioning.EssentialBound
import Purelib.Measure.Distribution.Conditioning.CauchySchwarz
import Purelib.Measure.Distribution.Conditioning.Covariance.Basic
import Purelib.Measure.Distribution.Conditioning.Covariance.Algebra
import Purelib.Measure.Distribution.Conditioning.TailBounds
import Purelib.Measure.Distribution.Partition.CauchySchwarz
import Purelib.Measure.Weighted.Basic
import Purelib.Measure.Distribution.Product.Lp
import Purelib.Measure.Distribution.Product.EssentialMaximum
public import Purelib.Measure.Distribution.Kernel.Basic
import Purelib.Measure.Distribution.Lp.Comparison

@[expose] public section

/-!
# Executable finite measure examples

All numerical examples reduce to finite rational calculations checked by the
kernel.  The final examples exercise the generic CCL area-request interface
without postulating a completed CCL value.
-/

namespace Purelib.Examples.Measure.Distribution.Product.Coin.Basic.WorkedExamples

open Purelib.Data.Rat
open Purelib.Examples
open Purelib.Measure
open Purelib.Examples.Measure.Distribution.Coin.Basic (coinNumber coinPayoff fairCoin reverseCoinNumber)
open Purelib.Examples.Measure.Distribution.Partition.Positive.Coin.Basic (positiveCoinPartition wholeCoinPartition)

/-- The retained product distribution of two independent fair coins. -/
def independentCoinPair : Distribution
  (Bool × Bool) :=
  fairCoin.product fairCoin

/-- The product coin observable has powered L2 equal to the product of the two marginal powered L2 values. -/
example : independentCoinPair.poweredLp 2
      (fun pair => coinNumber pair.1 * coinPayoff
        pair.2) =
    fairCoin.poweredLp 2 coinNumber *
      fairCoin.poweredLp 2 coinPayoff := by
  unfold independentCoinPair
  exact fairCoin.product_poweredLp_mul fairCoin 2
    coinNumber coinPayoff

/-- The product coin observable has powered L2 value five halves. -/
example : independentCoinPair.poweredLp 2
    (fun pair => coinNumber pair.1 * coinPayoff pair.2)
      = 5 / 2 := by
  decide

/-- Adding an independent coordinate preserves the first-coordinate powered L3 distance. -/
example : independentCoinPair.poweredLpDistance 3
      (fun pair => coinNumber pair.1)
      (fun pair => reverseCoinNumber pair.1) =
    fairCoin.poweredLpDistance 3 coinNumber
      reverseCoinNumber := by
  unfold independentCoinPair
  exact fairCoin.product_poweredLpDistance_left fairCoin
    3
    coinNumber reverseCoinNumber

/-- The two complementary first-coordinate indicators have powered L3 distance one. -/
example : independentCoinPair.poweredLpDistance 3
      (fun pair => coinNumber pair.1)
      (fun pair => reverseCoinNumber pair.1) = 1 := by
  decide

/-- The second-coordinate coin payoff retains its marginal powered L2 value. -/
example : independentCoinPair.poweredL2 (fun pair =>
  coinPayoff pair.2) =
    fairCoin.poweredL2 coinPayoff := by
  unfold independentCoinPair
  exact fairCoin.product_poweredL2_right fairCoin
    coinPayoff

/-- The second-coordinate coin payoff has powered L2 value five. -/
example : independentCoinPair.poweredL2
    (fun pair => coinPayoff pair.2) = 5 := by
  decide

/-- The essential maximum magnitude of the product observable factors into its marginal maxima. -/
example : independentCoinPair.essentialMaximumMagnitude
      (fun pair => coinNumber pair.1 * coinPayoff
        pair.2) =
    fairCoin.essentialMaximumMagnitude coinNumber *
      fairCoin.essentialMaximumMagnitude coinPayoff :=
        by
  unfold independentCoinPair
  exact fairCoin.product_essentialMaximumMagnitude_mul
    fairCoin
    coinNumber coinPayoff

/-- The product observable has essential maximum magnitude three. -/
example : independentCoinPair.essentialMaximumMagnitude
    (fun pair => coinNumber pair.1 * coinPayoff pair.2)
      = 3 := by
  decide

/-- Adding an independent coordinate preserves the first-coordinate essential maximum distance. -/
example : independentCoinPair.essentialMaximumDistance
      (fun pair => coinNumber pair.1)
      (fun pair => reverseCoinNumber pair.1) =
    fairCoin.essentialMaximumDistance coinNumber
      reverseCoinNumber := by
  unfold independentCoinPair
  exact fairCoin.product_essentialMaximumDistance_left
    fairCoin
    coinNumber reverseCoinNumber

/-- The separation between the two powered L1 values is bounded by their L1 distance. -/
example : Distance.rationalSeparation (fairCoin.poweredL1
  coinPayoff)
      (fairCoin.poweredL1 coinNumber) ≤
    fairCoin.l1Distance coinPayoff
      coinNumber :=
  fairCoin.poweredL1_separation_le_l1Distance coinPayoff
    coinNumber

/-- The powered L1 separation and L1 distance of payoff and indicator both equal three halves. -/
example : Distance.rationalSeparation (fairCoin.poweredL1
  coinPayoff)
        (fairCoin.poweredL1 coinNumber) = 3 / 2 ∧
    fairCoin.l1Distance coinPayoff
      coinNumber = 3 / 2 := by
  decide

/-- The two coin indicators satisfy the powered L1 triangle bound. -/
example : fairCoin.poweredL1
      (fun outcome => coinNumber outcome +
        reverseCoinNumber outcome) ≤
    fairCoin.poweredL1 coinNumber +
      fairCoin.poweredL1 reverseCoinNumber :=
  fairCoin.poweredL1_add_le coinNumber
    reverseCoinNumber

/-- The complementary indicator sum attains equality one in the powered L1 triangle bound. -/
example : fairCoin.poweredL1
        (fun outcome => coinNumber outcome +
          reverseCoinNumber outcome) = 1 ∧
    fairCoin.poweredL1 coinNumber +
        fairCoin.poweredL1 reverseCoinNumber = 1 := by
  decide

/-- The L1 distance of the displayed products is bounded by the original essential maxima and L1 distances. -/
example : fairCoin.l1Distance
      (fun outcome => coinPayoff outcome * coinNumber
        outcome)
      (fun outcome => coinNumber outcome *
        reverseCoinNumber outcome) ≤
    fairCoin.essentialMaximumMagnitude coinNumber *
        fairCoin.l1Distance coinPayoff
          coinNumber +
      fairCoin.essentialMaximumMagnitude coinNumber *
        fairCoin.l1Distance coinNumber
          reverseCoinNumber :=
  fairCoin.l1Distance_mul_le coinPayoff
    coinNumber
    coinNumber reverseCoinNumber

/-- The displayed product L1 distance is three halves and its comparison bound is five halves. -/
example : fairCoin.l1Distance
        (fun outcome => coinPayoff outcome * coinNumber
          outcome)
        (fun outcome => coinNumber outcome *
          reverseCoinNumber outcome) =
      3 / 2 ∧
    fairCoin.essentialMaximumMagnitude coinNumber *
          fairCoin.l1Distance coinPayoff
            coinNumber +
        fairCoin.essentialMaximumMagnitude coinNumber *
          fairCoin.l1Distance coinNumber
            reverseCoinNumber = 5 / 2 := by
  decide

/-- The zero observable has essential maximum magnitude zero. -/
example : fairCoin.essentialMaximumMagnitude (fun _ => 0) = 0 :=
  fairCoin.essentialMaximumMagnitude_zero

/-- The difference of the two essential maximum magnitudes is bounded by their essential maximum distance. -/
example : Distance.rationalSeparation
      (fairCoin.essentialMaximumMagnitude coinPayoff)
      (fairCoin.essentialMaximumMagnitude coinNumber) ≤
    fairCoin.essentialMaximumDistance coinPayoff
      coinNumber :=
  fairCoin.essentialMaximumMagnitude_separation_le_distance
    coinPayoff coinNumber

/-- The payoff and indicator have essential maximum separation and distance two. -/
example : Distance.rationalSeparation
        (fairCoin.essentialMaximumMagnitude coinPayoff)
        (fairCoin.essentialMaximumMagnitude coinNumber)
          = 2 ∧
    fairCoin.essentialMaximumDistance coinPayoff
      coinNumber = 2 := by
  decide

/-- The constant minus-three observable has essential maximum magnitude three. -/
example : fairCoin.essentialMaximumMagnitude (fun _ => (-3)) = 3 := open Purelib in by
  calc
    fairCoin.essentialMaximumMagnitude (fun _ => (-3)) =
        Data.Rat.Distance.rationalSeparation (-3) 0 :=
      fairCoin.essentialMaximumMagnitude_constant (-3)
    _ = 3 := by decide

/-- Zero essential maximum magnitude is equivalent to almost-everywhere vanishing. -/
example (value : Bool → Fraction.Rational) :
    fairCoin.essentialMaximumMagnitude value = 0 ↔
      fairCoin.EqualAlmostEverywhere value (fun _ => 0) :=
  fairCoin.essentialMaximumMagnitude_eq_zero_iff value

/-- The coin indicator and payoff satisfy the essential maximum triangle bound. -/
example : fairCoin.essentialMaximumMagnitude
      (fun outcome => coinNumber outcome + coinPayoff
        outcome) ≤
    fairCoin.essentialMaximumMagnitude coinNumber +
      fairCoin.essentialMaximumMagnitude coinPayoff :=
  fairCoin.essentialMaximumMagnitude_add_le coinNumber
    coinPayoff

/-- The indicator-plus-payoff maximum and the sum of their maxima both equal four. -/
example : fairCoin.essentialMaximumMagnitude
      (fun outcome => coinNumber outcome + coinPayoff
        outcome) = 4 ∧
    fairCoin.essentialMaximumMagnitude coinNumber +
        fairCoin.essentialMaximumMagnitude coinPayoff =
          4 := by
  decide

/-- Scaling the payoff by minus two scales its essential maximum by two. -/
example : fairCoin.essentialMaximumMagnitude
      (fun outcome => (-2 : Fraction.Rational) * coinPayoff outcome) =
    Distance.rationalSeparation (-2) 0 *
      fairCoin.essentialMaximumMagnitude coinPayoff :=
  fairCoin.essentialMaximumMagnitude_scale (-2)
    coinPayoff

/-- The payoff scaled by minus two has essential maximum magnitude six. -/
example : fairCoin.essentialMaximumMagnitude
      (fun outcome => (-2 : Fraction.Rational) * coinPayoff outcome) =
        6 := by
  decide

/-- Negating the coin payoff preserves its essential maximum magnitude. -/
example : fairCoin.essentialMaximumMagnitude
      (fun outcome => -coinPayoff outcome) =
    fairCoin.essentialMaximumMagnitude coinPayoff :=
  fairCoin.essentialMaximumMagnitude_neg coinPayoff

/-- The maximum magnitude of the payoff-minus-indicator is bounded by the sum of their maxima. -/
example : fairCoin.essentialMaximumMagnitude
      (fun outcome => coinPayoff outcome - coinNumber
        outcome) ≤
    fairCoin.essentialMaximumMagnitude coinPayoff +
      fairCoin.essentialMaximumMagnitude coinNumber :=
  fairCoin.essentialMaximumMagnitude_sub_le coinPayoff
    coinNumber

/-- The essential maximum magnitude of the indicator-payoff product is bounded by the product of their maxima. -/
example : fairCoin.essentialMaximumMagnitude
      (fun outcome => coinNumber outcome * coinPayoff
        outcome) ≤
    fairCoin.essentialMaximumMagnitude coinNumber *
      fairCoin.essentialMaximumMagnitude coinPayoff :=
  fairCoin.essentialMaximumMagnitude_mul_le coinNumber
    coinPayoff

/-- The indicator-payoff product attains equality three in the product maximum bound. -/
example : fairCoin.essentialMaximumMagnitude
      (fun outcome => coinNumber outcome * coinPayoff
        outcome) = 3 ∧
    fairCoin.essentialMaximumMagnitude coinNumber *
        fairCoin.essentialMaximumMagnitude coinPayoff =
          3 := by
  decide

/-- The complementary coin indicators have essential maximum distance one. -/
example : fairCoin.essentialMaximumDistance coinNumber
  reverseCoinNumber = 1 := by
  decide

/-- Essential maximum distance between the indicator and payoff is symmetric. -/
example : fairCoin.essentialMaximumDistance coinNumber
  coinPayoff =
    fairCoin.essentialMaximumDistance coinPayoff
      coinNumber :=
  fairCoin.essentialMaximumDistance_symm coinNumber
    coinPayoff

/-- Every third coin observable gives the essential maximum distance triangle bound. -/
example (third : Bool → Fraction.Rational) :
    fairCoin.essentialMaximumDistance coinNumber
      coinPayoff ≤
      fairCoin.essentialMaximumDistance coinNumber third
        +
        fairCoin.essentialMaximumDistance third
          coinPayoff :=
  fairCoin.essentialMaximumDistance_triangle coinNumber
    third coinPayoff

/-- Zero essential maximum distance is equivalent to almost-everywhere equality of the two coin observables. -/
example (left right : Bool → Fraction.Rational) :
    fairCoin.essentialMaximumDistance left right = 0 ↔
      fairCoin.EqualAlmostEverywhere left right :=
  fairCoin.essentialMaximumDistance_eq_zero_iff left right

/-- The indicator powered L3 distance is bounded by the cube of its essential maximum distance. -/
example : fairCoin.poweredLpDistance 3 coinNumber
  reverseCoinNumber ≤
    fairCoin.essentialMaximumDistance coinNumber
      reverseCoinNumber ^ 3 :=
  fairCoin.poweredLpDistance_le_essentialMaximumDistance
    3 coinNumber reverseCoinNumber

/-- The indicator L1 distance is bounded by its essential maximum distance. -/
example : fairCoin.l1Distance coinNumber
  reverseCoinNumber ≤
    fairCoin.essentialMaximumDistance coinNumber
      reverseCoinNumber :=
  fairCoin.l1Distance_le_essentialMaximumDistance
    coinNumber reverseCoinNumber

/-- The difference of the payoff and indicator expectations is bounded by their L1 distance. -/
example : Distance.rationalSeparation (fairCoin.expectation
  coinPayoff)
      (fairCoin.expectation coinNumber) ≤
    fairCoin.l1Distance coinPayoff
      coinNumber :=
  fairCoin.expectation_separation_le_l1Distance
    coinPayoff coinNumber

/-- The difference of the payoff and indicator expectations is bounded by their essential maximum distance. -/
example : Distance.rationalSeparation (fairCoin.expectation
  coinPayoff)
      (fairCoin.expectation coinNumber) ≤
    fairCoin.essentialMaximumDistance coinPayoff
      coinNumber :=
  fairCoin.expectation_separation_le_essentialMaximumDistance
    coinPayoff coinNumber

/-- The payoff-indicator expectation separation is three halves and their essential maximum distance is two. -/
example : Distance.rationalSeparation (fairCoin.expectation
  coinPayoff)
      (fairCoin.expectation coinNumber) = 3 / 2 ∧
    fairCoin.essentialMaximumDistance coinPayoff
      coinNumber = 2 := by
  decide

/-- The difference of heads-event integrals is bounded by heads probability times the essential maximum distance. -/
example : Distance.rationalSeparation
      (fairCoin.eventIntegral (fun outcome => outcome)
        coinPayoff)
      (fairCoin.eventIntegral (fun outcome => outcome)
        coinNumber) ≤
    fairCoin.probability (fun outcome => outcome) *
      fairCoin.essentialMaximumDistance coinPayoff
        coinNumber :=
  fairCoin.eventIntegral_separation_le_probability_mul_essentialMaximumDistance
    (fun outcome => outcome) coinPayoff coinNumber

/-- The heads-event integral separation and its probability-times-maximum bound both equal one. -/
example : Distance.rationalSeparation
      (fairCoin.eventIntegral (fun outcome => outcome)
        coinPayoff)
      (fairCoin.eventIntegral (fun outcome => outcome)
        coinNumber) = 1 ∧
    fairCoin.probability (fun outcome => outcome) *
        fairCoin.essentialMaximumDistance coinPayoff
          coinNumber = 1 := by
  decide

/-- The difference of the two means conditioned on heads is bounded by the original essential maximum distance. -/
example : Distance.rationalSeparation
      (fairCoin.conditionalMean (fun outcome => outcome)
        coinPayoff)
      (fairCoin.conditionalMean (fun outcome => outcome)
        coinNumber) ≤
    fairCoin.essentialMaximumDistance coinPayoff
      coinNumber :=
  fairCoin.conditionalMean_separation_le_essentialMaximumDistance
    (fun outcome => outcome) Measure.Distribution.Conditioned.Coin.Basic.fairCoin_true_positive
      coinPayoff coinNumber

/-- The heads-conditioned mean separation and the original essential maximum distance both equal two. -/
example : Distance.rationalSeparation
      (fairCoin.conditionalMean (fun outcome => outcome)
        coinPayoff)
      (fairCoin.conditionalMean (fun outcome => outcome)
        coinNumber) = 2 ∧
    fairCoin.essentialMaximumDistance coinPayoff
      coinNumber = 2 := by
  decide

/-- The powered L2 distance is bounded by the squared essential maximum distance. -/
example : fairCoin.poweredL2Distance coinNumber
  reverseCoinNumber ≤
    fairCoin.essentialMaximumDistance coinNumber
      reverseCoinNumber ^ 2 :=
  fairCoin.poweredL2Distance_le_essentialMaximumDistance_sq
    coinNumber reverseCoinNumber

/-- The indicator powered L3 distance and its maximum-cube bound both equal one. -/
example : fairCoin.poweredLpDistance 3 coinNumber
  reverseCoinNumber = 1 ∧
    fairCoin.essentialMaximumDistance coinNumber
      reverseCoinNumber ^ 3 = 1 := by
  decide

/-- The powered L3 payoff is bounded by the squared essential maximum times its powered L1 value. -/
example : fairCoin.poweredLp 3 coinPayoff ≤
    fairCoin.essentialMaximumMagnitude coinPayoff ^ 2 *
      fairCoin.poweredLp 1 coinPayoff := by
  have bound := fairCoin.poweredLp_add_le_essentialMaximum 1 2
    coinPayoff
  simpa only using bound

/-- The powered L3 payoff is fourteen and its maximum-times-L1 bound is eighteen. -/
example : fairCoin.poweredLp 3 coinPayoff = 14 ∧
    fairCoin.essentialMaximumMagnitude coinPayoff ^ 2 *
      fairCoin.poweredLp 1 coinPayoff = 18 := by
  decide

/-- The coin payoff conditioned on heads has mean three. -/
example : fairCoin.conditionalMean (fun outcome => outcome)
  coinPayoff = 3 := by
  decide

/-- The full-event conditional means satisfy the Cauchy–Schwarz product bound. -/
example : fairCoin.conditionalMean (fun _ => true)
        (fun outcome => coinNumber outcome * coinPayoff
          outcome) ^ 2 ≤
      fairCoin.conditionalMean (fun _ => true)
          (fun outcome => coinNumber outcome ^ 2) *
        fairCoin.conditionalMean (fun _ => true)
          (fun outcome => coinPayoff outcome ^ 2) :=
  fairCoin.conditionalMean_mul_sq_le (fun _ => true) (by decide)
    coinNumber coinPayoff

/-- The displayed conditional Cauchy–Schwarz quantities are nine quarters and five halves. -/
example : fairCoin.conditionalMean (fun _ => true)
        (fun outcome => coinNumber outcome * coinPayoff
          outcome) ^ 2 = 9 / 4 ∧
      fairCoin.conditionalMean (fun _ => true)
          (fun outcome => coinNumber outcome ^ 2) *
        fairCoin.conditionalMean (fun _ => true)
          (fun outcome => coinPayoff outcome ^ 2) = 5 / 2 := by
  decide

/-- The squared full-event conditional covariance is bounded by the product of the conditional variances. -/
example : fairCoin.conditionalCovariance (fun _ => true)
        coinNumber coinPayoff ^ 2 ≤
      fairCoin.conditionalVariance (fun _ => true)
        coinNumber *
        fairCoin.conditionalVariance (fun _ => true)
          coinPayoff :=
  fairCoin.conditionalCovariance_sq_le_variance_mul
    (fun _ => true) (by decide) coinNumber coinPayoff

/-- The displayed conditional covariance is one half, with indicator variance one quarter and payoff variance one. -/
example : fairCoin.conditionalCovariance (fun _ => true)
        coinNumber coinPayoff = 1 / 2 ∧
      fairCoin.conditionalVariance (fun _ => true)
        coinNumber = 1 / 4 ∧
        fairCoin.conditionalVariance (fun _ => true)
          coinPayoff = 1 := by
  decide

/-- Adding seven to the indicator preserves its full-event conditional covariance with the payoff. -/
example : fairCoin.conditionalCovariance (fun _ => true)
      (fun outcome => coinNumber outcome + 7) coinPayoff
        =
    fairCoin.conditionalCovariance (fun _ => true)
      coinNumber coinPayoff :=
  fairCoin.conditionalCovariance_add_constant_left
    (fun _ => true) (by decide) coinNumber coinPayoff 7

/-- The full-event conditional covariance is symmetric in indicator and payoff. -/
example : fairCoin.conditionalCovariance (fun _ => true)
      coinNumber coinPayoff =
    fairCoin.conditionalCovariance (fun _ => true)
      coinPayoff coinNumber :=
  fairCoin.conditionalCovariance_symm (fun _ => true)
    coinNumber coinPayoff

/-- The heads probability satisfies the conditional Markov bound at payoff threshold three. -/
example : fairCoin.conditionalProbability (fun outcome => outcome)
        (fun _ => true) (by decide) ≤
      fairCoin.conditionalMean (fun _ => true)
        coinPayoff / 3 :=
  fairCoin.conditionalMarkov_bound (fun outcome => outcome)
    (fun _ => true) (by decide) coinPayoff 3 (by decide)
    (by intro item; cases item <;> decide)
    (by
      intro item selected
      cases item
      · exact Bool.noConfusion selected
      · decide)

/-- The full-event probability satisfies the conditional Chebyshev bound at deviation one. -/
example : fairCoin.conditionalProbability (fun _ => true)
        (fun _ => true) (by decide) ≤
      fairCoin.conditionalVariance (fun _ => true)
        coinPayoff / 1 ^ 2 :=
  fairCoin.conditionalChebyshev_bound (fun _ => true) (fun _ => true)
    (by decide) coinPayoff 1 (by decide) (by
      intro item selected
      cases item <;> decide)

/-- The heads probability satisfies the upper conditional Cantelli bound at deviation one. -/
example : fairCoin.conditionalProbability (fun outcome => outcome)
        (fun _ => true) (by decide) ≤
      fairCoin.conditionalVariance (fun _ => true)
        coinPayoff /
        (fairCoin.conditionalVariance (fun _ => true)
          coinPayoff + 1 ^ 2) :=
  fairCoin.conditionalCantelli_bound (fun outcome => outcome)
    (fun _ => true) (by decide) coinPayoff 1 (by decide) (by
      intro item selected
      cases item
      · exact Bool.noConfusion selected
      · decide)

/-- The tails probability satisfies the lower conditional Cantelli bound at deviation one. -/
example : fairCoin.conditionalProbability (fun outcome => !outcome)
        (fun _ => true) (by decide) ≤
      fairCoin.conditionalVariance (fun _ => true)
        coinPayoff /
        (fairCoin.conditionalVariance (fun _ => true)
          coinPayoff + 1 ^ 2) :=
  fairCoin.conditionalCantelli_lower_bound (fun outcome => !outcome)
    (fun _ => true) (by decide) coinPayoff 1 (by decide) (by
      intro item selected
      cases item
      · decide
      · exact Bool.noConfusion selected)

/-- The displayed conditional probability, Markov bound and Cantelli bound equal one half, two thirds and one half. -/
example : fairCoin.conditionalProbability (fun outcome => outcome)
          (fun _ => true) (by decide) = 1 / 2 ∧
      fairCoin.conditionalMean (fun _ => true)
        coinPayoff / 3 = 2 / 3 ∧
        fairCoin.conditionalVariance (fun _ => true)
          coinPayoff /
          (fairCoin.conditionalVariance (fun _ => true)
            coinPayoff + 1 ^ 2) =
            1 / 2 := by
  decide

/-- The whole-event coin partition satisfies pointwise conditional-expectation Cauchy–Schwarz on retained atoms. -/
example (atom : Purelib.Measure.Weighted Bool) (member : atom ∈ fairCoin.atoms) :
    wholeCoinPartition.conditionalExpectation
          (fun outcome => coinNumber outcome *
            coinPayoff outcome)
          atom.item ^ 2 ≤
      wholeCoinPartition.conditionalExpectation
          (fun outcome => coinNumber outcome ^ 2) atom.item *
        wholeCoinPartition.conditionalExpectation
          (fun outcome => coinPayoff outcome ^ 2) atom.item :=
  wholeCoinPartition.conditionalExpectation_mul_sq_le
    coinNumber coinPayoff atom member

/-- The weighted singleton conditional means recover the original payoff expectation. -/
example :
    (positiveCoinPartition.events.map fun event =>
        fairCoin.probability event *
          fairCoin.conditionalMean event coinPayoff).sum
            =
      fairCoin.expectation coinPayoff :=
  positiveCoinPartition.total_expectation
    coinPayoff

/-- The weighted singleton conditional payoff means sum to two. -/
example :
    (positiveCoinPartition.events.map fun event =>
        fairCoin.probability event *
          fairCoin.conditionalMean event coinPayoff).sum
            = 2 := by
  decide

/-- The retained product distribution of two fair coins for subsequent product-event examples. -/
def twoCoins : Distribution (Bool × Bool)
  :=
  fairCoin.product fairCoin

end Purelib.Examples.Measure.Distribution.Product.Coin.Basic.WorkedExamples

end
