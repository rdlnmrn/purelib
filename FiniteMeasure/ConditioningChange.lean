import FiniteMeasure.Conditioning
import FiniteMeasure.AbsoluteContinuity

/-!
# Conditioning as a finite change of measure

Conditioning on an explicitly positive event is an executable
Radon--Nikodym change.  Its rational density is zero off the event and the
reciprocal of the event probability on it.  All claims are identities and
bounds over the displayed finite atom table.
-/

namespace FiniteMeasure

namespace Distribution

/-- The conditioning density is exactly the reciprocal probability on the
conditioning event. -/
theorem conditioningDensity_eq_inverse_of_selected {α : Type}
    (distribution : Distribution α) (condition : α → Bool)
    (positive : 0 < distribution.probability condition) (item : α)
    (selected : condition item = true) :
    distribution.conditioningDensity condition positive item =
      (distribution.probability condition)⁻¹ := by
  simp only [conditioningDensity, indicator, selected, one_mul]

/-- The conditioning density vanishes off the conditioning event. -/
theorem conditioningDensity_eq_zero_of_unselected {α : Type}
    (distribution : Distribution α) (condition : α → Bool)
    (positive : 0 < distribution.probability condition) (item : α)
    (unselected : condition item = false) :
    distribution.conditioningDensity condition positive item = 0 := by
  simp only [conditioningDensity, indicator, unselected, zero_mul]

/-- The conditioning density has the explicit reciprocal upper bound. -/
theorem conditioningDensity_le_inverse {α : Type}
    (distribution : Distribution α) (condition : α → Bool)
    (positive : 0 < distribution.probability condition) (item : α) :
    distribution.conditioningDensity condition positive item ≤
      (distribution.probability condition)⁻¹ := by
  cases selected : condition item
  · rw [distribution.conditioningDensity_eq_zero_of_unselected condition
      positive item selected]
    exact RFAP.ConstructiveFraction.le_of_lt_direct
      (RFAP.ConstructiveFraction.inv_pos_direct positive)
  · rw [distribution.conditioningDensity_eq_inverse_of_selected condition
      positive item selected]

/-- Conditioning supplies its own finite Radon--Nikodym witness. -/
def conditionedWitness {α : Type} (distribution : Distribution α)
    (condition : α → Bool)
    (positive : 0 < distribution.probability condition) :
    AtomicChange.Witness distribution.toFiniteContent
      (distribution.conditioned condition positive).toFiniteContent where
  density := distribution.conditioningDensity condition positive
  nonnegative := distribution.conditioningDensity_nonnegative condition
    positive
  integral_eq value :=
    distribution.conditioned_expectation condition positive value

/-- A conditioned finite distribution is absolutely continuous with respect
to its original finite content. -/
theorem conditioned_absolutelyContinuous {α : Type}
    (distribution : Distribution α) (condition : α → Bool)
    (positive : 0 < distribution.probability condition) :
    FiniteContent.AbsolutelyContinuous
      (distribution.conditioned condition positive).toFiniteContent
        distribution.toFiniteContent :=
  (distribution.conditionedWitness condition positive).absolutelyContinuous

/-- Quantitative finite absolute continuity: conditioning can enlarge an
event by at most the reciprocal probability of the condition. -/
theorem conditioned_probability_le_inverse_mul {α : Type}
    (distribution : Distribution α) (condition event : α → Bool)
    (positive : 0 < distribution.probability condition) :
    (distribution.conditioned condition positive).probability event ≤
      (distribution.probability condition)⁻¹ *
        distribution.probability event := by
  exact distribution.toFiniteContent.reweight_measure_le
    (distribution.conditioningDensity condition positive)
    (distribution.conditioningDensity_nonnegative condition positive)
    (distribution.probability condition)⁻¹
    (fun atom member =>
      distribution.conditioningDensity_le_inverse condition positive
        atom.item)
    event

/-- The witness measure identity is the usual conditional-probability
formula, expressed entirely as a finite rational integral. -/
theorem conditionalProbability_eq_density_integral {α : Type}
    (distribution : Distribution α) (condition event : α → Bool)
    (positive : 0 < distribution.probability condition) :
    distribution.conditionalProbability event condition positive =
      distribution.toFiniteContent.integral (fun item =>
        distribution.conditioningDensity condition positive item *
          indicator event item) := by
  rw [← distribution.conditioned_probability condition event positive]
  exact (distribution.conditionedWitness condition positive).measure_eq event

end Distribution

end FiniteMeasure
