module
import Purelib.Measure.Content.Density.AbsoluteContinuity
public import Purelib.Measure.Content.Density.Witness
import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Distribution.Conditioning.Basic
import Purelib.Measure.Distribution.Conditioning.Probability
public import Purelib.Measure.Distribution.Content
import Purelib.Measure.Weighted.Integral
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
public import Purelib.Measure.Content.AbsoluteContinuity.Basic
import Purelib.Measure.Content.Density.Basic
import Purelib.Measure.Content.Integral
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic

/-!
# Conditioning as a finite change of measure

Conditioning on an explicitly positive event is an executable
Radon--Nikodym change.  Its rational density is zero off the event and the
reciprocal of the event probability on it.  All claims are identities and
bounds over the displayed finite atom table.
-/

@[expose] public section

namespace Purelib.Measure

namespace Distribution

/-- At a selected payload, the retained conditioning density is the reciprocal of the conditioning event's probability.

The original strictly positive probability supplies the same reciprocal factor; the selected Boolean indicator
contributes exactly one. -/
theorem conditioningDensity_eq_inverse_of_selected {α : Type}
    (distribution : Distribution α) (condition : α → Bool)
    (positive : 0 < distribution.probability condition) (item : α)
    (selected : condition item = true) :
    distribution.conditioningDensity condition positive item =
      (distribution.probability condition)⁻¹ := by
  simp only [conditioningDensity, indicator, selected, one_mul, -eq_self, -iff_self]
  rfl

/-- At a rejected payload, the retained conditioning density is zero.

The original Boolean condition contributes a zero indicator at this payload, independently of the retained
positive-probability factor. -/
theorem conditioningDensity_eq_zero_of_unselected {α : Type}
    (distribution : Distribution α) (condition : α → Bool)
    (positive : 0 < distribution.probability condition) (item : α)
    (unselected : condition item = false) :
    distribution.conditioningDensity condition positive item = 0 := by
  simp only [conditioningDensity, indicator, unselected, zero_mul, -eq_self, -iff_self]
  rfl

open Purelib.Data.Rat in
/-- The conditioning density is everywhere bounded by the reciprocal of the positive conditioning probability. -/
theorem conditioningDensity_le_inverse {α : Type}
    (distribution : Distribution α) (condition : α → Bool)
    (positive : 0 < distribution.probability condition) (item : α) :
    distribution.conditioningDensity condition positive item ≤
      (distribution.probability condition)⁻¹ := by
  cases selected : condition item
  · rw [distribution.conditioningDensity_eq_zero_of_unselected condition
      positive item selected]
    exact Fraction.Order.Arithmetic.le_of_lt_direct
      (Fraction.Order.Field.inv_pos_direct positive)
  · rw [distribution.conditioningDensity_eq_inverse_of_selected condition
      positive item selected]

/-- Certify the exact conditioning density as a density witness from the original content to its retained conditioned
content.

The stored nonnegativity proof and integral identity use the same original law, Boolean condition and positivity
certificate. -/
def conditionedWitness {α : Type} (distribution : Distribution α)
    (condition : α → Bool)
    (positive : 0 < distribution.probability condition) :
    AtomicChange.Witness distribution.toContent
      (distribution.conditioned condition positive).toContent where
  density := distribution.conditioningDensity condition positive
  nonnegative := distribution.conditioningDensity_nonnegative condition
    positive
  integral_eq value :=
    distribution.conditioned_expectation condition positive value

open Purelib.Measure in
/-- Positive-event conditioning gives content absolutely continuous with respect to the original content. -/
theorem conditioned_absolutelyContinuous {α : Type}
    (distribution : Distribution α) (condition : α → Bool)
    (positive : 0 < distribution.probability condition) :
    Content.AbsolutelyContinuous
      (distribution.conditioned condition positive).toContent
        distribution.toContent :=
  Content.DensityWitness.absolutelyContinuous (distribution.conditionedWitness condition positive)

/-- Conditioned event probability is bounded by original event probability times the reciprocal conditioning
probability. -/
theorem conditioned_probability_le_inverse_mul {α : Type}
    (distribution : Distribution α) (condition event : α → Bool)
    (positive : 0 < distribution.probability condition) :
    (distribution.conditioned condition positive).probability event ≤
      (distribution.probability condition)⁻¹ *
        distribution.probability event := by
  exact distribution.toContent.reweight_measure_le
    (distribution.conditioningDensity condition positive)
    (distribution.conditioningDensity_nonnegative condition positive)
    (distribution.probability condition)⁻¹
    (fun atom member =>
      distribution.conditioningDensity_le_inverse condition positive
        atom.item)
    event

open Purelib.Measure in
/-- Conditional probability equals the original content integral of the retained conditioning density times the event
indicator. -/
theorem conditionalProbability_eq_density_integral {α : Type}
    (distribution : Distribution α) (condition event : α → Bool)
    (positive : 0 < distribution.probability condition) :
    distribution.conditionalProbability event condition positive =
      distribution.toContent.integral (fun item =>
        distribution.conditioningDensity condition positive item *
          indicator event item) := by
  rw [← distribution.conditioned_probability condition event positive]
  exact Content.DensityWitness.measure_eq (distribution.conditionedWitness condition positive) event

end Distribution

end Purelib.Measure
