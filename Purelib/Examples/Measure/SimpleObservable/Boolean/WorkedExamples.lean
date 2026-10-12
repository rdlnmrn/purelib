module
public import Purelib.Examples.Measure.EventAlgebra.Boolean.WorkedExamples
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
import Purelib.Measure.EventAlgebra.Distribution
import Purelib.Measure.EventAlgebra.Content
import Purelib.Measure.EventAlgebra.Simple.Content
public import Purelib.Measure.EventAlgebra.Observable
import Purelib.Measure.EventAlgebra.Bool
import Purelib.Measure.EventAlgebra.Simple.Distribution
import Purelib.Measure.EventAlgebra.Basic
import Purelib.Measure.Distribution.Content
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field

@[expose] public section

/-!
# Executable finite measure examples

All numerical examples reduce to finite rational calculations checked by the
kernel.  The final examples exercise the generic CCL area-request interface
without postulating a completed CCL value.
-/

namespace Purelib.Examples.Measure.SimpleObservable.Boolean.WorkedExamples

open Purelib.Examples
open Purelib.Measure
open Purelib.Examples.Measure.Distribution.Coin.Basic (fairCoin)

/-- The simple Boolean observable equal to one on tails and three on heads. -/
def coinSimpleObservable : SimpleObservable
  boolEventAlgebra :=
  [⟨Measure.EventAlgebra.Boolean.WorkedExamples.tailsEventCode, 1⟩,
    ⟨Measure.EventAlgebra.Boolean.WorkedExamples.headsEventCode, 3⟩]

/-- The simple observable evaluates to its displayed two coin values. -/
example : coinSimpleObservable.evaluate false = 1 ∧
    coinSimpleObservable.evaluate true = 3 := by
  decide

/-- The simple observable has fair-coin expectation two. -/
example : coinSimpleObservable.expectation
  fairCoin = 2 := by
  decide

/-- Scaling the simple observable by three gives expectation six. -/
example : (coinSimpleObservable.scale 3).expectation
  fairCoin = 6 := by
  decide

/-- Subtracting the simple observable from itself gives expectation zero. -/
example : (coinSimpleObservable.sub
  coinSimpleObservable).expectation
    fairCoin = 0 := by
  decide

/-- Squaring the simple observable pointwise gives expectation five. -/
example : (coinSimpleObservable.mul
  coinSimpleObservable).expectation
    fairCoin = 5 := by
  decide

/-- The simple-observable expectation equals its finite weighted event-coefficient sum. -/
example : coinSimpleObservable.expectation
  fairCoin =
    (coinSimpleObservable.map fun term =>
      fairCoin.probability (boolEventAlgebra.evaluate term.event) *
        term.coefficient).sum :=
  coinSimpleObservable.expectation_eq_sum
    fairCoin

/-- The simple-observable expectation is preserved by the Boolean signature distribution. -/
example : coinSimpleObservable.expectation
  fairCoin =
    (boolEventAlgebra.signatureDistribution fairCoin).expectation
      coinSimpleObservable.signatureValue :=
  coinSimpleObservable.expectation_eq_signatureDistribution_expectation
    fairCoin

/-- The simple-observable expectation is preserved by the Boolean atom distribution. -/
example : coinSimpleObservable.expectation
  fairCoin =
    (boolEventAlgebra.atomDistribution fairCoin).expectation
      coinSimpleObservable.signatureValue :=
  coinSimpleObservable.expectation_eq_atomDistribution_expectation
    fairCoin

/-- The algebra observable retaining the original two-term coin simple observable. -/
def coinAlgebraObservable : AlgebraObservable
  boolEventAlgebra :=
  AlgebraObservable.ofSimple coinSimpleObservable

/-- The algebra-observable integral is preserved by passage to Boolean atom content. -/
example : fairCoin.toContent.integral
  coinAlgebraObservable.evaluate =
    (boolEventAlgebra.atomContent fairCoin.toContent).integral
      coinAlgebraObservable.signatureValue :=
  coinAlgebraObservable.integral_eq_atomContent_integral
    fairCoin.toContent

/-- The algebra observable retains the original values one and three. -/
example : coinAlgebraObservable.evaluate false = 1 ∧
    coinAlgebraObservable.evaluate true = 3 := by
  decide

/-- The simple-observable integral is preserved by passage to Boolean atom content. -/
example : fairCoin.toContent.integral
  coinSimpleObservable.evaluate =
    (boolEventAlgebra.atomContent fairCoin.toContent).integral
      coinSimpleObservable.signatureValue :=
  boolEventAlgebra.simpleObservable_integral_eq_atomContent_integral
    fairCoin.toContent
      coinSimpleObservable

end Purelib.Examples.Measure.SimpleObservable.Boolean.WorkedExamples

end
