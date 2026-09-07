import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.EssentialMaximumOperations
import FiniteMeasure.Mixture

/-!
# Essential maxima of explicit finite mixtures

A mixture concatenates two atom tables after scaling their weights.  Positive
scaling preserves nonzero support, while a zero coefficient discards that
component.  This gives an exact, executable `L∞` mixture formula, including
the endpoint cases, without a supremum or a selected maximizing atom.
-/

namespace FiniteMeasure

namespace Distribution

/-- Exact support-sensitive essential-maximum formula for a rational
two-component mixture. -/
theorem mixture_essentialMaximumMagnitude {α : Type}
    (left right : Distribution α) (weight : MixingWeight)
    (value : α → Coordinate) :
    (left.mixture right weight).essentialMaximumMagnitude value =
      max
        (if weight.coefficient = 0 then 0
          else left.essentialMaximumMagnitude value)
        (if weight.complement = 0 then 0
          else right.essentialMaximumMagnitude value) := by
  change
    ((left.toFiniteContent.scale weight.coefficient weight.nonnegative).append
      (right.toFiniteContent.scale weight.complement
        weight.complement_nonnegative)).essentialMaximumMagnitude value =
      max
        (if weight.coefficient = 0 then 0
          else left.toFiniteContent.essentialMaximumMagnitude value)
        (if weight.complement = 0 then 0
          else right.toFiniteContent.essentialMaximumMagnitude value)
  rw [FiniteContent.append_essentialMaximumMagnitude]
  by_cases leftZero : weight.coefficient = 0
  · rw [left.toFiniteContent.scale_essentialMaximumMagnitude_of_eq_zero
      weight.coefficient weight.nonnegative leftZero value]
    by_cases rightZero : weight.complement = 0
    · rw [right.toFiniteContent.scale_essentialMaximumMagnitude_of_eq_zero
        weight.complement weight.complement_nonnegative rightZero value]
      simp only [leftZero, rightZero, ↓reduceIte]
    · rw [right.toFiniteContent.scale_essentialMaximumMagnitude_of_ne
        weight.complement weight.complement_nonnegative rightZero value]
      simp only [leftZero, rightZero, ↓reduceIte]
  · rw [left.toFiniteContent.scale_essentialMaximumMagnitude_of_ne
      weight.coefficient weight.nonnegative leftZero value]
    by_cases rightZero : weight.complement = 0
    · rw [right.toFiniteContent.scale_essentialMaximumMagnitude_of_eq_zero
        weight.complement weight.complement_nonnegative rightZero value]
      simp only [leftZero, rightZero, ↓reduceIte]
    · rw [right.toFiniteContent.scale_essentialMaximumMagnitude_of_ne
        weight.complement weight.complement_nonnegative rightZero value]
      simp only [leftZero, rightZero, ↓reduceIte]

/-- A finite mixture cannot exceed the larger component essential maximum. -/
theorem mixture_essentialMaximumMagnitude_le {α : Type}
    (left right : Distribution α) (weight : MixingWeight)
    (value : α → Coordinate) :
    (left.mixture right weight).essentialMaximumMagnitude value ≤
      max (left.essentialMaximumMagnitude value)
        (right.essentialMaximumMagnitude value) := by
  rw [left.mixture_essentialMaximumMagnitude right weight value]
  apply max_le
  · by_cases zero : weight.coefficient = 0
    · simp only [zero, ↓reduceIte]
      exact (left.essentialMaximumMagnitude_nonnegative value).trans
        (le_max_left _ _)
    · simp only [zero, ↓reduceIte]
      exact le_max_left _ _
  · by_cases zero : weight.complement = 0
    · simp only [zero, ↓reduceIte]
      exact (right.essentialMaximumMagnitude_nonnegative value).trans
        (le_max_right _ _)
    · simp only [zero, ↓reduceIte]
      exact le_max_right _ _

/-- With both displayed component weights positive, both supports survive and
the mixture essential maximum is exactly their maximum. -/
theorem mixture_essentialMaximumMagnitude_eq_max {α : Type}
    (left right : Distribution α) (weight : MixingWeight)
    (coefficientPositive : 0 < weight.coefficient)
    (complementPositive : 0 < weight.complement)
    (value : α → Coordinate) :
    (left.mixture right weight).essentialMaximumMagnitude value =
      max (left.essentialMaximumMagnitude value)
        (right.essentialMaximumMagnitude value) := by
  rw [left.mixture_essentialMaximumMagnitude right weight value]
  simp only [coefficientPositive.ne', complementPositive.ne', ↓reduceIte]

/-- At the left endpoint, the mixture has exactly the right component's
essential maximum. -/
theorem mixture_essentialMaximumMagnitude_of_coefficient_eq_zero
    {α : Type} (left right : Distribution α) (weight : MixingWeight)
    (coefficientZero : weight.coefficient = 0)
    (value : α → Coordinate) :
    (left.mixture right weight).essentialMaximumMagnitude value =
      right.essentialMaximumMagnitude value := by
  have complementNonzero : weight.complement ≠ 0 := by
    rw [MixingWeight.complement, coefficientZero]
    decide
  rw [left.mixture_essentialMaximumMagnitude right weight value]
  simp only [coefficientZero, complementNonzero, ↓reduceIte]
  exact max_eq_right (right.essentialMaximumMagnitude_nonnegative value)

/-- At the right endpoint, the mixture has exactly the left component's
essential maximum. -/
theorem mixture_essentialMaximumMagnitude_of_coefficient_eq_one
    {α : Type} (left right : Distribution α) (weight : MixingWeight)
    (coefficientOne : weight.coefficient = 1)
    (value : α → Coordinate) :
    (left.mixture right weight).essentialMaximumMagnitude value =
      left.essentialMaximumMagnitude value := by
  have coefficientNonzero : weight.coefficient ≠ 0 := by
    rw [coefficientOne]
    decide
  have complementZero : weight.complement = 0 := by
    rw [MixingWeight.complement, coefficientOne]
    ring1
  rw [left.mixture_essentialMaximumMagnitude right weight value]
  simp only [coefficientNonzero, complementZero, ↓reduceIte]
  exact max_eq_left (left.essentialMaximumMagnitude_nonnegative value)

theorem mixture_essentialMaximumDistance_le {α : Type}
    (left right : Distribution α) (weight : MixingWeight)
    (first second : α → Coordinate) :
    (left.mixture right weight).essentialMaximumDistance first second ≤
      max (left.essentialMaximumDistance first second)
        (right.essentialMaximumDistance first second) := by
  unfold essentialMaximumDistance
  exact left.mixture_essentialMaximumMagnitude_le right weight
    (fun item => first item - second item)

theorem mixture_essentialMaximumDistance_eq_max {α : Type}
    (left right : Distribution α) (weight : MixingWeight)
    (coefficientPositive : 0 < weight.coefficient)
    (complementPositive : 0 < weight.complement)
    (first second : α → Coordinate) :
    (left.mixture right weight).essentialMaximumDistance first second =
      max (left.essentialMaximumDistance first second)
        (right.essentialMaximumDistance first second) := by
  unfold essentialMaximumDistance
  exact left.mixture_essentialMaximumMagnitude_eq_max right weight
    coefficientPositive complementPositive
    (fun item => first item - second item)

end Distribution

end FiniteMeasure
