module
public import Purelib.Examples.Measure.Distribution.Coin.Basic
import Purelib.Examples.Measure.Distribution.Expectation.Enclosed.Coin.WorkedExamples
import Purelib.Examples.Measure.Distribution.Mixture.Coin.WorkedExamples

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Kernel.Lp
import Purelib.Measure.Distribution.Kernel.Moments
import Purelib.Measure.Distribution.Kernel.Enclosure
import Purelib.Measure.Distribution.Mixture.Enclosure
import Purelib.Measure.Distribution.Kernel.Iteration
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Measure.Distribution.Expectation
public import Purelib.Measure.Distribution.Kernel.Basic

@[expose] public section

/-!
# Executable finite measure examples

All numerical examples reduce to finite rational calculations checked by the
kernel.  The final examples exercise the generic CCL area-request interface
without postulating a completed CCL value.
-/

namespace Purelib.Examples.Measure.Distribution.Stochastic.Bool.WorkedExamples

open Purelib.Examples
open Purelib.Measure
open Purelib.Examples.Measure.Distribution.Coin.Basic (coinNumber coinPayoff fairCoin reverseCoinNumber)
open Purelib.Examples.Measure.Distribution.Expectation.Enclosed.Coin.WorkedExamples (coarseCoinRange)
open Purelib.Examples.Measure.Distribution.Mixture.Coin.WorkedExamples (mostlyFalseWeight)

/-! ## Bounded finite stochastic processes -/

/-- The deterministic Boolean transition toggling the current state. -/
def toggleTransition (state : Bool) :
  Distribution Bool :=
  Distribution.pure (!state)

/-- The singleton initial law concentrated at false. -/
def startsFalse : Distribution Bool :=
  Distribution.pure false

/-- The deterministic Boolean transition retaining the current state. -/
def stayTransition (state : Bool) :
  Distribution Bool :=
  Distribution.pure state

/-- The transition sending every state to false. -/
def collapseToFalseTransition (_ : Bool) :
  Distribution Bool :=
  Distribution.pure false

/-- The kernel that tosses a fair coin at false and remains at true. -/
def revealOrRandomTransition (state : Bool)
  : Distribution Bool :=
  if state then Distribution.pure true else fairCoin

/-- The kernel's powered L2 payoff is the original expectation of its conditional powered L2 values. -/
example : (fairCoin.bind
  revealOrRandomTransition).poweredL2
  coinPayoff =
    fairCoin.expectation (fun state =>
      (revealOrRandomTransition state).poweredL2
        coinPayoff) :=
  fairCoin.bind_poweredL2
    revealOrRandomTransition
    coinPayoff

/-- Both sides of the kernel powered L2 identity equal seven. -/
example : (fairCoin.bind
  revealOrRandomTransition).poweredL2
  coinPayoff = 7 ∧
    fairCoin.expectation (fun state =>
      (revealOrRandomTransition state).poweredL2
        coinPayoff) = 7 := by
  decide

/-- The kernel's powered L3 distance is the original expectation of its conditional distances. -/
example : (fairCoin.bind
  revealOrRandomTransition).poweredLpDistance 3
      coinNumber reverseCoinNumber =
    fairCoin.expectation (fun state =>
      (revealOrRandomTransition state).poweredLpDistance 3
        coinNumber reverseCoinNumber) :=
  fairCoin.bind_poweredLpDistance
    revealOrRandomTransition 3
    coinNumber reverseCoinNumber

/-- Collapsing to false is superharmonic for the numeric coin indicator. -/
theorem collapseToFalse_superharmonic (state
  : Bool) :
    (collapseToFalseTransition state).expectation
      coinNumber ≤
      coinNumber state := by
  cases state <;> decide

/-- Binding the fair coin with singleton laws preserves its heads probability. -/
example : (fairCoin.bind Distribution.pure).probability
    (fun outcome => outcome) = fairCoin.probability (fun outcome => outcome) :=
  fairCoin.bind_pure_probability (fun outcome => outcome)

/-- Binding a false singleton law with the toggle kernel gives the kernel's original heads probability. -/
example : ((Distribution.pure false).bind
  toggleTransition).probability
    (fun state => state) = (toggleTransition false).probability
      (fun state => state) :=
  Distribution.pure_bind_probability false toggleTransition
    (fun state => state)

/-- Successive finite kernel binds associate at every event probability. -/
example {α β γ : Type} (source : Distribution α)
    (first : α → Distribution β) (second : β → Distribution γ)
    (event : γ → Bool) :
    ((source.bind first).bind second).probability event =
      (source.bind fun item => (first item).bind second).probability event :=
  source.bind_bind_probability first second event

/-- Toggling twice by pushforward gives the same evaluation law as the identity pushforward. -/
example : Distribution.EvaluationEquivalent
    ((fairCoin.map fun outcome => !outcome).map fun outcome => !outcome)
    (fairCoin.map fun outcome => outcome) :=
  fairCoin.map_map_evaluationEquivalent
    (fun outcome => !outcome) (fun outcome => !outcome)

/-- Swapping the two mixture components and their weights preserves the evaluation law. -/
example : Distribution.EvaluationEquivalent
    ((Distribution.pure false).mixture (Distribution.pure true)
      mostlyFalseWeight)
    ((Distribution.pure true).mixture (Distribution.pure false)
      mostlyFalseWeight.swap) :=
  (Distribution.pure false).mixture_swap_evaluationEquivalent
    (Distribution.pure true) mostlyFalseWeight

/-- The kernel variance splits into mean conditional variance and variance of conditional means. -/
example : (fairCoin.bind
  revealOrRandomTransition).variance
  coinNumber =
    fairCoin.expectation (fun state =>
        (revealOrRandomTransition state).variance
          coinNumber) +
      fairCoin.variance (fun state =>
        (revealOrRandomTransition state).expectation
          coinNumber) :=
  fairCoin.bind_variance
    revealOrRandomTransition
    coinNumber

/-- The mean conditional coin variance is one eighth. -/
example : fairCoin.expectation (fun state =>
    (revealOrRandomTransition state).variance
      coinNumber) = 1 / 8 := by
  decide

/-- The variance of the conditional coin means is one sixteenth. -/
example : fairCoin.variance (fun state =>
    (revealOrRandomTransition state).expectation
      coinNumber) = 1 / 16 := by
  decide

/-- The bound kernel coin-number variance is three sixteenths. -/
example : (fairCoin.bind
  revealOrRandomTransition).variance
  coinNumber =
    3 / 16 := by
  decide

/-- The kernel's enclosed expectation equals the iterated enclosed expectation. -/
example : (fairCoin.bind
  revealOrRandomTransition).enclosedExpectation
      coarseCoinRange =
    fairCoin.enclosedExpectation (fun state =>
      (revealOrRandomTransition state).enclosedExpectation
        coarseCoinRange) :=
  fairCoin.enclosedExpectation_bind
    revealOrRandomTransition
    coarseCoinRange

/-- The kernel expectation enclosure width equals the mean of the conditional enclosure widths. -/
example : ((fairCoin.bind
  revealOrRandomTransition).enclosedExpectation
      coarseCoinRange).width =
    fairCoin.expectation (fun state =>
      ((revealOrRandomTransition state).enclosedExpectation
        coarseCoinRange).width) :=
  fairCoin.enclosedExpectation_bind_width
    revealOrRandomTransition
    coarseCoinRange

/-- The mixture expectation enclosure is the sum of the original weighted component enclosures. -/
example : ((Distribution.pure false).mixture
      (Distribution.pure true)
        mostlyFalseWeight).enclosedExpectation
        coarseCoinRange =
    (((Distribution.pure false).enclosedExpectation
      coarseCoinRange).scale
      mostlyFalseWeight.coefficient
        mostlyFalseWeight.nonnegative).add
    (((Distribution.pure true).enclosedExpectation
      coarseCoinRange).scale
      mostlyFalseWeight.complement
      mostlyFalseWeight.complement_nonnegative) :=
  (Distribution.pure false).enclosedExpectation_mixture
    (Distribution.pure true) mostlyFalseWeight
      coarseCoinRange

/-- The kernel covariance splits into mean conditional covariance and covariance of conditional means. -/
example :
    (fairCoin.bind
      revealOrRandomTransition).covariance
        coinNumber reverseCoinNumber =
      fairCoin.expectation (fun state =>
          (revealOrRandomTransition state).covariance
            coinNumber reverseCoinNumber) +
        fairCoin.covariance
          (fun state =>
            (revealOrRandomTransition state).expectation
              coinNumber)
          (fun state =>
            (revealOrRandomTransition state).expectation
              reverseCoinNumber) :=
  fairCoin.bind_covariance
    revealOrRandomTransition
    coinNumber reverseCoinNumber

/-- Three toggles from false give heads probability one. -/
example : (Distribution.iterate toggleTransition 3
  startsFalse).probability
    (fun state => state) = 1 := by
  decide

/-- Four toggles from false give heads probability zero. -/
example : (Distribution.iterate toggleTransition 4
  startsFalse).probability
    (fun state => state) = 0 := by
  decide

/-- Every finite iteration of collapse-to-false keeps coin-number expectation below the original fair-coin expectation.
-/
example (count : Nat) :
    (Distribution.iterate collapseToFalseTransition count
      fairCoin).expectation
        coinNumber ≤ fairCoin.expectation
          coinNumber :=
  Distribution.iterate_expectation_le_of_superharmonic
    collapseToFalseTransition
      coinNumber
      collapseToFalse_superharmonic
      count fairCoin

/-- Every finite iteration of the stay kernel preserves each original fair-coin event probability. -/
example (event : Bool → Bool) (count : Nat) :
    (Distribution.iterate stayTransition count
      fairCoin).probability event =
      fairCoin.probability event := by
  apply Distribution.iterate_probability_of_harmonic_event
  intro item
  exact Distribution.pure_probability item event

end Purelib.Examples.Measure.Distribution.Stochastic.Bool.WorkedExamples

end
