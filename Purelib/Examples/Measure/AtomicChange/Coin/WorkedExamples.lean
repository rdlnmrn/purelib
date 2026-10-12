module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Content.AbsoluteContinuity.Basic
import Purelib.Measure.Content.Density.AbsoluteContinuity
public import Purelib.Measure.Content.Density.Aligned
import Purelib.Measure.Content.Density.Composition
import Purelib.Measure.Content.Density.Witness
import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Distribution.Density
import Purelib.Measure.Distribution.Expectation
import Purelib.Measure.Distribution.Lp.AlmostEverywhere
import Purelib.Measure.Weighted.Integral
public import Purelib.Examples.Measure.Distribution.Coin.Basic

import Purelib.Tactic.QuotientFreeOmega
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
import Purelib.Measure.Weighted.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

@[expose] public section

/-!
# Executable finite measure examples

All numerical examples reduce to finite rational calculations checked by the
kernel.  The final examples exercise the generic CCL area-request interface
without postulating a completed CCL value.
-/

namespace Purelib.Examples.Measure.AtomicChange.Coin.WorkedExamples

open Purelib.Data.Rat
open Purelib.Examples
open Purelib.Measure
open Purelib.Examples.Measure.Distribution.Coin.Basic (coinNumber fairCoin)

/-- The coin density taking values one half on tails and three halves on heads. -/
def coinDensity (outcome : Bool) : Fraction.Rational :=
  if outcome then 3 / 2 else 1 / 2

/-- The displayed coin density is nonnegative. -/
theorem coinDensity_nonnegative (outcome : Bool) :
    0 ≤ coinDensity outcome := by
  cases outcome <;> decide

/-- The displayed density has fair-coin expectation one. -/
theorem coinDensity_normalizes :
  fairCoin.expectation coinDensity = 1 := by
  decide

/-- The coin law obtained by reweighting the original fair coin with the retained density. -/
def biasedCoin : Distribution Bool :=
  fairCoin.reweight coinDensity
    coinDensity_nonnegative
    coinDensity_normalizes

/-- The reweighted coin assigns heads probability three quarters. -/
example : biasedCoin.probability (fun outcome => outcome) = 3 / 4 := by
  decide

/-- The reweighted heads probability equals the original expectation of density times its indicator. -/
example : biasedCoin.probability (fun outcome => outcome) =
    fairCoin.expectation (fun outcome =>
      coinDensity outcome * Purelib.Measure.Distribution.indicator (fun value
        => value) outcome) :=
  Distribution.reweight_probability fairCoin
    coinDensity
    coinDensity_nonnegative
      coinDensity_normalizes (fun outcome => outcome)

/-- The atomic change from weights `(1/4, 3/4)` to the fair coin.

Both original Boolean rows retain their nonnegative source and target weights and the implication from source nullity to
target nullity. -/
def coinAtomicChange : AtomicChange Bool where
  rows :=
    [{ item := false
       sourceWeight := 1 / 4
       targetWeight := 1 / 2
       source_nonnegative := by decide
       target_nonnegative := by decide
       target_zero_of_source_zero := by decide },
     { item := true
       sourceWeight := 3 / 4
       targetWeight := 1 / 2
       source_nonnegative := by decide
       target_nonnegative := by decide
       target_zero_of_source_zero := by decide }]
  noRepeated := by
    simp only [-eq_self, -iff_self, NoRepeatedAtomicRows, AtomicRowPayloadAbsent]
    exact ⟨⟨Bool.noConfusion, trivial⟩, ⟨trivial, trivial⟩⟩

/-- The reverse atomic change from the fair coin to weights `(1/4, 3/4)`. -/
def coinAtomicReverseChange : AtomicChange Bool where
  rows :=
    [{ item := false
       sourceWeight := 1 / 2
       targetWeight := 1 / 4
       source_nonnegative := by decide
       target_nonnegative := by decide
       target_zero_of_source_zero := by decide },
     { item := true
       sourceWeight := 1 / 2
       targetWeight := 3 / 4
       source_nonnegative := by decide
       target_nonnegative := by decide
       target_zero_of_source_zero := by decide }]
  noRepeated := by
    simp only [-eq_self, -iff_self, NoRepeatedAtomicRows, AtomicRowPayloadAbsent]
    exact ⟨⟨Bool.noConfusion, trivial⟩, ⟨trivial, trivial⟩⟩

/-- The forward atomic density on tails is two. -/
example : coinAtomicChange.density false = 2 := by
  decide

/-- The forward atomic density on heads is two thirds. -/
example : coinAtomicChange.density true = 2 / 3 := by
  decide

/-- The reverse density is one half on tails and three halves on heads. -/
example : coinAtomicReverseChange.density false = 1 / 2 ∧
    coinAtomicReverseChange.density true = 3 / 2 := by
  decide

/-- The forward and reverse retained densities multiply to one almost everywhere for the original source content. -/
example : coinAtomicChange.source.EqualAlmostEverywhere
    (fun outcome => coinAtomicChange.witness.density outcome *
      coinAtomicReverseChange.witness.density outcome)
    (fun _ => 1) :=
  Purelib.Measure.Content.DensityWitness.density_mul_reverse_eq_one_almostEverywhere
    coinAtomicChange.witness
    coinAtomicReverseChange.witness

/-- The target coin content is absolutely continuous with respect to the source content. -/
example : coinAtomicChange.target.AbsolutelyContinuous
    coinAtomicChange.source :=
  coinAtomicChange.target_absolutelyContinuous_source

/-- The two retained coin contents have the same null events. -/
example : coinAtomicChange.target.SameNullEvents
  coinAtomicChange.source :=
  Content.DensityWitness.sameNullEvents_of_reverse coinAtomicChange.witness
    coinAtomicReverseChange.witness

/-- The atomic source assigns heads weight three quarters. -/
example : coinAtomicChange.source.measure (fun outcome => outcome) =
    3 / 4 := by
  decide

/-- The atomic target assigns heads weight one half. -/
example : coinAtomicChange.target.measure (fun outcome => outcome) =
    1 / 2 := by
  decide

/-- The target coin integral equals the source integral weighted by the retained density. -/
example : coinAtomicChange.target.integral
  coinNumber =
    coinAtomicChange.source.integral (fun outcome =>
      coinAtomicChange.density outcome *
        coinNumber outcome) :=
  coinAtomicChange.witness.integral_eq
    coinNumber

/-- Every density witness between these contents agrees at the positive heads atom. -/
example (other : Purelib.Measure.AtomicChange.Witness coinAtomicChange.source
    coinAtomicChange.target) :
    coinAtomicChange.witness.density true = other.density true :=
  Content.DensityWitness.density_eq_of_positive_atom coinAtomicChange.witness
    other true (by decide)

/-- Reweighting the original source by the retained density reproduces the target heads measure. -/
example :
    (coinAtomicChange.source.reweight
      coinAtomicChange.density
      coinAtomicChange.density_nonnegative).measure
        (fun outcome => outcome) =
      coinAtomicChange.target.measure (fun outcome => outcome) :=
  coinAtomicChange.reweight_measure_eq_target (fun outcome => outcome)

/-- The atomic change retaining a zero-weight tails row and unit-weight heads row. -/
def zeroRowAtomicChange : AtomicChange Bool where
  rows :=
    [{ item := false
       sourceWeight := 0
       targetWeight := 0
       source_nonnegative := by decide
       target_nonnegative := by decide
       target_zero_of_source_zero := by decide },
     { item := true
       sourceWeight := 1
       targetWeight := 1
       source_nonnegative := by decide
       target_nonnegative := by decide
       target_zero_of_source_zero := by decide }]
  noRepeated := by
    simp only [-eq_self, -iff_self, NoRepeatedAtomicRows, AtomicRowPayloadAbsent]
    exact ⟨⟨Bool.noConfusion, trivial⟩, ⟨trivial, trivial⟩⟩

/-- The retained zero-weight row has density zero. -/
example : zeroRowAtomicChange.density false = 0 := by
  decide

/-- The zero-weight tails event remains null under the atomic change. -/
example : zeroRowAtomicChange.target.measure (fun outcome => !outcome) = 0 :=
  zeroRowAtomicChange.target_measure_eq_zero_of_source_measure_eq_zero
    (fun outcome => !outcome) (by decide)

end Purelib.Examples.Measure.AtomicChange.Coin.WorkedExamples

end
