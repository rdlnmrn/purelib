module
import Purelib.Measure.Weighted.Integral
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
import Purelib.Measure.Content.Basic
public import Purelib.Measure.Content.Integral
public import Purelib.Measure.Weighted.Density
import Purelib.Measure.Weighted.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic

section
@[expose] public section

/-!
# Finite rational change of measure

A rational density reweights a displayed finite atom list by multiplication.
The resulting change-of-measure identities are exact finite sums.  There is
no almost-everywhere quotient, measurable function space, or Radon--Nikodym
existence theorem.
-/

namespace Purelib.Measure
namespace Content

open Purelib.Data.Rat
/-- Multiply each exact retained content weight by the supplied pointwise nonnegative rational density. -/
def reweight {α : Type} (content : Content α)
    (density : α → Fraction.Rational) (nonnegative : ∀ item, 0 ≤ density item) :
    Content α :=
  ⟨densityAtoms density nonnegative content.atoms⟩

/-- The reweighted total equals the original weighted integral of the density. -/
theorem reweight_total {α : Type} (content : Content α)
    (density : α → Fraction.Rational) (nonnegative : ∀ item, 0 ≤ density item) :
    (content.reweight density nonnegative).total =
      Distribution.expectationWeight content.atoms density :=
  totalWeight_densityAtoms content.atoms density nonnegative

/-- Reweighted event measurement equals the original integral of density times its indicator. -/
theorem reweight_measure {α : Type} (content : Content α)
    (density : α → Fraction.Rational) (nonnegative : ∀ item, 0 ≤ density item)
    (event : α → Bool) :
    (content.reweight density nonnegative).measure event =
      Distribution.expectationWeight content.atoms
        (fun item => density item * Distribution.indicator event item) :=
  eventWeight_densityAtoms content.atoms density nonnegative event

/-- An integral after reweighting equals the original integral of the density-observable product. -/
theorem reweight_integral {α : Type} (content : Content α)
    (density : α → Fraction.Rational) (nonnegative : ∀ item, 0 ≤ density item)
    (value : α → Fraction.Rational) :
    (content.reweight density nonnegative).integral value =
      content.integral (fun item => density item * value item) :=
  expectationWeight_densityAtoms content.atoms density value nonnegative

/-- A density ceiling on retained occurrences bounds reweighted event content by that ceiling times original content. -/
theorem reweight_measure_le {α : Type} (content : Content α)
    (density : α → Fraction.Rational) (nonnegative : ∀ item, 0 ≤ density item)
    (ceiling : Fraction.Rational)
    (bounded : ∀ atom, atom ∈ content.atoms → density atom.item ≤ ceiling)
    (event : α → Bool) :
    (content.reweight density nonnegative).measure event ≤
      ceiling * content.measure event :=
  eventWeight_densityAtoms_le content.atoms density nonnegative ceiling
    bounded event

/-- Pointwise nonnegative reweighting preserves every zero-content event. -/
theorem reweight_measure_zero {α : Type} (content : Content α)
    (density : α → Fraction.Rational) (nonnegative : ∀ item, 0 ≤ density item)
    (event : α → Bool) (zero : content.measure event = 0) :
    (content.reweight density nonnegative).measure event = 0 :=
  eventWeight_densityAtoms_eq_zero_of_eventWeight_eq_zero density nonnegative
    event content.atoms zero

/-- Successive density reweightings have the same integrals as one reweighting by their pointwise product. -/
theorem reweight_reweight_integral {α : Type}
    (content : Content α)
    (first second : α → Fraction.Rational)
    (firstNonnegative : ∀ item, 0 ≤ first item)
    (secondNonnegative : ∀ item, 0 ≤ second item)
    (value : α → Fraction.Rational) :
    ((content.reweight first firstNonnegative).reweight
        second secondNonnegative).integral value =
      (content.reweight (fun item => first item * second item)
        (fun item => Fraction.Order.Arithmetic.mul_nonneg_direct
          (firstNonnegative item) (secondNonnegative item))).integral value := by
  calc
    ((content.reweight first firstNonnegative).reweight
          second secondNonnegative).integral value =
        (content.reweight first firstNonnegative).integral
          (fun item => second item * value item) :=
      (content.reweight first firstNonnegative).reweight_integral
        second secondNonnegative value
    _ = content.integral
          (fun item => first item * (second item * value item)) :=
      content.reweight_integral first firstNonnegative
        (fun item => second item * value item)
    _ = content.integral
          (fun item => (first item * second item) * value item) := by
      exact content.integral_congr _ _ (fun item => by ring1)
    _ = (content.reweight (fun item => first item * second item)
          (fun item => Fraction.Order.Arithmetic.mul_nonneg_direct
            (firstNonnegative item) (secondNonnegative item))).integral value :=
      (content.reweight_integral (fun item => first item * second item)
        (fun item => Fraction.Order.Arithmetic.mul_nonneg_direct
          (firstNonnegative item) (secondNonnegative item)) value).symm

/-- Successive density reweightings have the same event measurements as their pointwise product reweighting. -/
theorem reweight_reweight_measure {α : Type}
    (content : Content α)
    (first second : α → Fraction.Rational)
    (firstNonnegative : ∀ item, 0 ≤ first item)
    (secondNonnegative : ∀ item, 0 ≤ second item)
    (event : α → Bool) :
    ((content.reweight first firstNonnegative).reweight
        second secondNonnegative).measure event =
      (content.reweight (fun item => first item * second item)
        (fun item => Fraction.Order.Arithmetic.mul_nonneg_direct
          (firstNonnegative item) (secondNonnegative item))).measure event := by
  rw [← (content.reweight first firstNonnegative).reweight
      second secondNonnegative |>.integral_indicator event]
  rw [content.reweight_reweight_integral first second firstNonnegative
    secondNonnegative (Distribution.indicator event)]
  exact (content.reweight (fun item => first item * second item)
    (fun item => Fraction.Order.Arithmetic.mul_nonneg_direct
      (firstNonnegative item) (secondNonnegative item))).integral_indicator event

end Content

namespace Distribution
end Distribution

end Purelib.Measure

end
