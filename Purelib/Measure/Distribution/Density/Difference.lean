module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Distribution.Density
import Purelib.Measure.Distribution.Expectation
import Purelib.Measure.Distribution.Stability
public import Purelib.Measure.Event.RationalOrder
import Purelib.Measure.Weighted.Integral
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Data.Rat.PositiveNegativePart
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic

section
@[expose] public section

/-!
# Finite Scheffé identities

Two nonnegative rational densities of expectation one define finite
reweighted probability laws.  The executable event where the first density
dominates the second attains their event-probability discrepancy.  Its mass is
the integral of the positive density difference, which equals the negative
part because both densities normalise.  Consequently atomic total variation
is exactly half the original-law L1 density separation.
-/

namespace Purelib.Measure
namespace Distribution

open Purelib.Data.Rat in
/-- The probability difference between two normalized reweightings is the original expectation of their density
difference times the event indicator. -/
private theorem reweight_probability_sub
    {α : Type} (source : Distribution α)
    (first second : α → Fraction.Rational)
    (firstNonnegative : ∀ item, 0 ≤ first item)
    (secondNonnegative : ∀ item, 0 ≤ second item)
    (firstNormalizes : source.expectation first = 1)
    (secondNormalizes : source.expectation second = 1)
    (event : α → Bool) :
    (source.reweight first firstNonnegative firstNormalizes).probability event -
        (source.reweight second secondNonnegative secondNormalizes).probability
          event =
      source.expectation (fun item =>
        (first item - second item) * indicator event item) := by
  rw [source.reweight_probability first firstNonnegative firstNormalizes,
    source.reweight_probability second secondNonnegative secondNormalizes,
    ← source.expectation_sub]
  exact source.expectation_congr _ _ (fun item => by ring1)

open Purelib
open Purelib.Data.Rat
/-- Every reweighted event-probability difference is bounded by the original expectation of the densities' positive
difference part. -/
theorem reweight_probability_sub_le_positivePart
    {α : Type} (source : Distribution α)
    (first second : α → Fraction.Rational)
    (firstNonnegative : ∀ item, 0 ≤ first item)
    (secondNonnegative : ∀ item, 0 ≤ second item)
    (firstNormalizes : source.expectation first = 1)
    (secondNormalizes : source.expectation second = 1)
    (event : α → Bool) :
    (source.reweight first firstNonnegative firstNormalizes).probability event -
        (source.reweight second secondNonnegative secondNormalizes).probability
          event ≤
      source.expectation (fun item =>
        Data.Rat.positiveWeight (first item - second item)) := by
  rw [source.reweight_probability_sub first second firstNonnegative
    secondNonnegative firstNormalizes secondNormalizes event]
  apply source.expectation_mono
  intro atom member
  cases selected : event atom.item
  · simp only [indicator, selected, mul_zero]
    exact Data.Rat.positiveWeight_nonneg _
  · simp only [indicator, selected, mul_one]
    exact Fraction.Order.Basic.le_max_left _ _

/-- The density-dominance event attains the positive-part expectation bound for the exact two normalized reweightings.
-/
theorem reweight_probability_sub_densityDominanceEvent
    {α : Type} (source : Distribution α)
    (first second : α → Fraction.Rational)
    (firstNonnegative : ∀ item, 0 ≤ first item)
    (secondNonnegative : ∀ item, 0 ≤ second item)
    (firstNormalizes : source.expectation first = 1)
    (secondNormalizes : source.expectation second = 1) :
    (source.reweight first firstNonnegative firstNormalizes).probability
          (densityDominanceEvent first second) -
        (source.reweight second secondNonnegative secondNormalizes).probability
          (densityDominanceEvent first second) =
      source.expectation (fun item =>
        Data.Rat.positiveWeight (first item - second item)) := by
  rw [source.reweight_probability_sub first second firstNonnegative
    secondNonnegative firstNormalizes secondNormalizes]
  exact source.expectation_congr _ _ (fun item => by
    by_cases order : second item ≤ first item
    · have selected : densityDominanceEvent first second item = true := by
        rewrite [densityDominanceEvent]
        exact decide_eq_true order
      change (first item - second item) *
        (match densityDominanceEvent first second item with | true => 1 | false => 0) = _
      rw [selected]
      change (first item - second item) * 1 = _
      rw [Data.Rat.positiveWeight_eq_self_of_nonneg
        (Fraction.Order.Arithmetic.sub_nonneg_direct order)]
      ring1
    · have reverse : first item ≤ second item :=
        (Fraction.Order.Arithmetic.lt_of_not_ge_direct order).le
      have selected : densityDominanceEvent first second item = false := by
        rewrite [densityDominanceEvent]
        exact decide_eq_false order
      change (first item - second item) *
        (match densityDominanceEvent first second item with | true => 1 | false => 0) = _
      rw [selected]
      change (first item - second item) * 0 = _
      have nonpositive : first item - second item ≤ 0 := by
        calc
          first item - second item ≤ second item - second item :=
            Fraction.Order.Arithmetic.sub_le_sub_right_direct reverse (second item)
          _ = 0 := by ring1
      rw [Data.Rat.positiveWeight_eq_zero_of_nonpos nonpositive]
      ring1)

/-- Two densities of unit original expectation have equal expected positive and negative difference parts. -/
theorem expectation_positivePart_eq_negativePart_of_normalized
    {α : Type} (source : Distribution α)
    (first second : α → Fraction.Rational)
    (firstNormalizes : source.expectation first = 1)
    (secondNormalizes : source.expectation second = 1) :
    source.expectation (fun item =>
        Data.Rat.positiveWeight (first item - second item)) =
      source.expectation (fun item =>
        Data.Rat.negativeWeight (first item - second item)) := by
  have differenceZero : source.expectation
      (fun item => first item - second item) = 0 := by
    rw [source.expectation_sub, firstNormalizes, secondNormalizes]
    ring1
  have decomposition : source.expectation
      (fun item => first item - second item) =
      source.expectation (fun item => Data.Rat.positiveWeight (first item - second item) -
        Data.Rat.negativeWeight (first item - second item)) :=
    source.expectation_congr _ _ (fun item =>
      (Data.Rat.positiveWeight_sub_negativeWeight
        (first item - second item)).symm)
  rw [decomposition, source.expectation_sub] at differenceZero
  calc
    source.expectation (fun item => Data.Rat.positiveWeight (first item - second item)) =
        (source.expectation (fun item => Data.Rat.positiveWeight (first item - second item)) -
          source.expectation (fun item => Data.Rat.negativeWeight (first item - second item))) +
            source.expectation (fun item => Data.Rat.negativeWeight (first item - second item)) := by ring1
    _ = source.expectation (fun item => Data.Rat.negativeWeight (first item - second item)) := by
      rw [differenceZero]
      ring1
end Distribution

end Purelib.Measure

end
