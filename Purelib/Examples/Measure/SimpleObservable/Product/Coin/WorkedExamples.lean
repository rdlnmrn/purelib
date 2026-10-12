module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Conditioning.Independence
import Purelib.Measure.Distribution.Conditioning.Probability
import Purelib.Measure.Distribution.Expectation
import Purelib.Measure.Distribution.Independence.Basic
import Purelib.Measure.Distribution.Independence.Moments
import Purelib.Measure.Distribution.Kernel.Basic
import Purelib.Measure.Distribution.Moments.Basic
import Purelib.Measure.Distribution.Product.Independence
import Purelib.Measure.Distribution.Product.Moments
import Purelib.Measure.EventAlgebra.Bool
import Purelib.Measure.EventAlgebra.Independence
import Purelib.Measure.EventAlgebra.Simple.Basic
import Purelib.Measure.EventAlgebra.Simple.Independence
import Purelib.Measure.Weighted.Integral
import Purelib.Examples.Measure.Distribution.Product.Coin.Basic
import Purelib.Examples.Measure.Distribution.Coin.Basic
import Purelib.Examples.Measure.EventAlgebra.Boolean.WorkedExamples
public import Purelib.Examples.Measure.SimpleObservable.Boolean.WorkedExamples

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Measure.EventAlgebra.Basic

@[expose] public section

/-!
# Executable finite measure examples

All numerical examples reduce to finite rational calculations checked by the
kernel.  The final examples exercise the generic CCL area-request interface
without postulating a completed CCL value.
-/

namespace Purelib.Examples.Measure.SimpleObservable.Product.Coin.WorkedExamples

open Purelib.Data.Rat
open Purelib.Examples
open Purelib.Measure
open Purelib.Examples.Measure.Distribution.Coin.Basic (fairCoin)
open Purelib.Examples.Measure.Distribution.Product.Coin.Basic.WorkedExamples (twoCoins)
open Purelib.Examples.Measure.SimpleObservable.Boolean.WorkedExamples (coinSimpleObservable)

/-- The original one-or-three simple observable pulled back to the first coin coordinate. -/
def firstCoinSimpleObservable :
  SimpleObservable
    (boolEventAlgebra.comap fun outcome : Bool × Bool => outcome.1) :=
  coinSimpleObservable.map fun term =>
    { event := term.event, coefficient := term.coefficient }

/-- The original one-or-three simple observable pulled back to the second coin coordinate. -/
def secondCoinSimpleObservable :
  SimpleObservable
    (boolEventAlgebra.comap fun outcome : Bool × Bool => outcome.2) :=
  coinSimpleObservable.map fun term =>
    { event := term.event, coefficient := term.coefficient }

/-- The event that exactly one of the two coin coordinates is heads. -/
def exactlyOneTrue (outcome : Bool × Bool)
  : Bool :=
  (outcome.1 && !outcome.2) || (!outcome.1 && outcome.2)

/-- Both retained fair coins are heads with probability one quarter. -/
example : twoCoins.probability (fun outcome =>
  outcome.1 && outcome.2) =
    1 / 4 := by
  decide

/-- The two-heads rectangle probability factors into its original marginal probabilities. -/
example : twoCoins.probability (fun outcome =>
  outcome.1 && outcome.2) =
    fairCoin.probability (fun outcome => outcome) *
      fairCoin.probability (fun outcome => outcome) :=
  Distribution.product_probability_rectangle fairCoin
    fairCoin
    (fun outcome => outcome) (fun outcome => outcome)

/-- The two coordinate heads events are independent under the retained product law. -/
example : twoCoins.IndependentEvents
    (fun outcome => outcome.1) (fun outcome => outcome.2) :=
  fairCoin.product_independentEvents_coordinates
    fairCoin
    (fun outcome => outcome) (fun outcome => outcome)

/-- The Boolean event algebras on the two coordinates are independent under the retained product law. -/
example : twoCoins.IndependentEventAlgebras
    (boolEventAlgebra.comap fun outcome : Bool × Bool => outcome.1)
    (boolEventAlgebra.comap fun outcome : Bool × Bool => outcome.2) :=
  fairCoin.product_independentEventAlgebras fairCoin
    boolEventAlgebra boolEventAlgebra

/-- The product of the two coordinate simple observables has expectation equal to the product of their expectations. -/
example : twoCoins.expectation (fun outcome =>
      firstCoinSimpleObservable.evaluate outcome *
        secondCoinSimpleObservable.evaluate outcome) =
    firstCoinSimpleObservable.expectation
      twoCoins *
      secondCoinSimpleObservable.expectation
        twoCoins :=
  SimpleObservable.expectation_mul_eq_mul_expectation_of_independent
    twoCoins
    (fairCoin.product_independentEventAlgebras fairCoin
      boolEventAlgebra boolEventAlgebra)
    firstCoinSimpleObservable
      secondCoinSimpleObservable

/-- The product of the two coordinate simple observables has expectation four. -/
example : twoCoins.expectation (fun outcome =>
      firstCoinSimpleObservable.evaluate outcome *
        secondCoinSimpleObservable.evaluate outcome) = 4 := by
  unfold twoCoins
    firstCoinSimpleObservable
    secondCoinSimpleObservable
    coinSimpleObservable
      Measure.EventAlgebra.Boolean.WorkedExamples.headsEventCode
      Measure.EventAlgebra.Boolean.WorkedExamples.tailsEventCode
  decide

/-- The two coordinate simple observables have covariance zero. -/
example : twoCoins.covariance
  firstCoinSimpleObservable.evaluate
    secondCoinSimpleObservable.evaluate = 0 :=
  SimpleObservable.covariance_eq_zero_of_independent twoCoins
    (fairCoin.product_independentEventAlgebras fairCoin
      boolEventAlgebra boolEventAlgebra)
    firstCoinSimpleObservable
      secondCoinSimpleObservable

/-- The two coordinate tails events are independent under the retained product law. -/
example : twoCoins.IndependentEvents
    (fun outcome => !outcome.1) (fun outcome => !outcome.2) :=
  twoCoins.independentEvents_complements
    (fairCoin.product_independentEvents_coordinates
      fairCoin
      (fun outcome => outcome) (fun outcome => outcome))

/-- Conditioning the first heads event on the independent second heads event gives probability one half. -/
example : twoCoins.conditionalProbability
    (fun outcome => outcome.1) (fun outcome => outcome.2) (by decide) =
      1 / 2 := by
  rw [twoCoins.conditionalProbability_eq_of_independent (by
    decide)
    (fairCoin.product_independentEvents_coordinates
      fairCoin
      (fun outcome => outcome) (fun outcome => outcome))]
  decide

/-- The two coordinate heads indicators have covariance zero. -/
example : twoCoins.covariance
    (Purelib.Measure.Distribution.indicator fun outcome => outcome.1)
    (Purelib.Measure.Distribution.indicator fun outcome => outcome.2) = 0 :=
  twoCoins.covariance_indicators_eq_zero_of_independent
    (fairCoin.product_independentEvents_coordinates
      fairCoin
      (fun outcome => outcome) (fun outcome => outcome))

/-- Exactly one retained coin is heads with probability one half. -/
example : twoCoins.probability
  exactlyOneTrue = 1 / 2 := by
  decide

/-- The exactly-one-head probability equals its iterated original marginal probability. -/
example : twoCoins.probability
  exactlyOneTrue =
    fairCoin.expectation (fun left =>
      fairCoin.probability (fun right =>
        exactlyOneTrue (left, right))) :=
  fairCoin.product_probability_iterated fairCoin
    exactlyOneTrue

/-- The product of the two heads indicators has expectation one quarter. -/
example : twoCoins.expectation
      (fun outcome => Purelib.Measure.Distribution.indicator (fun value => value) outcome.1 *
        Purelib.Measure.Distribution.indicator (fun value => value) outcome.2) = 1 / 4 := by
  unfold twoCoins
  rw [Distribution.product_expectation_mul,
    Distribution.expectation_indicator]
  decide

/-- The exactly-one-head payoff has the same product-law and iterated marginal expectation. -/
example : twoCoins.expectation
      (fun outcome => if exactlyOneTrue outcome then 7 else 1) =
    fairCoin.expectation (fun left =>
      fairCoin.expectation (fun right =>
        if exactlyOneTrue (left, right) then 7 else 1)) :=
  fairCoin.product_expectation_iterated fairCoin
    (fun outcome => if exactlyOneTrue outcome then 7 else 1)

/-- The rational indicator taking zero on tails and one on heads. -/
def coinNumeric (outcome : Bool) :
  Fraction.Rational :=
  if outcome then 1 else 0

/-- The two numeric coin coordinates have covariance zero. -/
example : twoCoins.covariance
    (fun outcome => coinNumeric outcome.1)
    (fun outcome => coinNumeric outcome.2) = 0 :=
  fairCoin.product_covariance_coordinates_zero fairCoin
    coinNumeric
      coinNumeric

/-- The sum of the numeric coin coordinates has variance one half. -/
example : twoCoins.variance
    (fun outcome => coinNumeric outcome.1 +
      coinNumeric outcome.2) = 1 / 2 := by
  decide

/-- The variance of the coordinate sum equals the sum of the two original marginal variances. -/
example : twoCoins.variance
      (fun outcome => coinNumeric outcome.1 +
        coinNumeric outcome.2) =
    fairCoin.variance
      coinNumeric +
      fairCoin.variance
      coinNumeric :=
  fairCoin.product_variance_add_coordinates fairCoin
    coinNumeric
    coinNumeric

end Purelib.Examples.Measure.SimpleObservable.Product.Coin.WorkedExamples

end
