import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.ConditionalCauchySchwarz
import FiniteMeasure.CovarianceAlgebra

/-!
# Algebra of finite conditional covariance

On an explicitly positive event, conditional covariance is ordinary
covariance under the displayed conditioned finite distribution.  The exact
rational symmetry, bilinearity, scaling, and translation laws therefore
follow without any limiting conditional-expectation object.
-/

namespace FiniteMeasure

namespace Distribution

/-- Conditional covariance is symmetric even before a positivity hypothesis
is used. -/
theorem conditionalCovariance_symm {α : Type}
    (distribution : Distribution α) (event : α → Bool)
    (left right : α → Coordinate) :
    distribution.conditionalCovariance event left right =
      distribution.conditionalCovariance event right left := by
  unfold conditionalCovariance
  exact distribution.conditionalMean_congr event _ _ (fun item => by ring1)

/-- Conditional covariance of an observable with itself is conditional
variance. -/
theorem conditionalCovariance_self {α : Type}
    (distribution : Distribution α) (event : α → Bool)
    (value : α → Coordinate) :
    distribution.conditionalCovariance event value value =
      distribution.conditionalVariance event value := by
  unfold conditionalCovariance conditionalVariance
  exact distribution.conditionalMean_congr event _ _ (fun item => by ring1)

/-- Covariance under the explicitly conditioned finite distribution is
exactly conditional covariance on the source table. -/
theorem conditioned_covariance_eq_conditionalCovariance {α : Type}
    (distribution : Distribution α) (event : α → Bool)
    (positive : 0 < distribution.probability event)
    (left right : α → Coordinate) :
    (distribution.conditioned event positive).covariance left right =
      distribution.conditionalCovariance event left right := by
  unfold covariance conditionalCovariance
  rw [distribution.conditioned_expectation_eq_conditionalMean
      event positive left,
    distribution.conditioned_expectation_eq_conditionalMean
      event positive right,
    distribution.conditioned_expectation_eq_conditionalMean
      event positive]

/-- Conditional covariance is additive in its left observable. -/
theorem conditionalCovariance_add_left {α : Type}
    (distribution : Distribution α) (event : α → Bool)
    (positive : 0 < distribution.probability event)
    (left middle right : α → Coordinate) :
    distribution.conditionalCovariance event
        (fun item => left item + middle item) right =
      distribution.conditionalCovariance event left right +
        distribution.conditionalCovariance event middle right := by
  rw [← distribution.conditioned_covariance_eq_conditionalCovariance
      event positive,
    ← distribution.conditioned_covariance_eq_conditionalCovariance
      event positive,
    ← distribution.conditioned_covariance_eq_conditionalCovariance
      event positive]
  exact (distribution.conditioned event positive).covariance_add_left
    left middle right

/-- Conditional covariance is additive in its right observable. -/
theorem conditionalCovariance_add_right {α : Type}
    (distribution : Distribution α) (event : α → Bool)
    (positive : 0 < distribution.probability event)
    (left right final : α → Coordinate) :
    distribution.conditionalCovariance event left
        (fun item => right item + final item) =
      distribution.conditionalCovariance event left right +
        distribution.conditionalCovariance event left final := by
  rw [← distribution.conditioned_covariance_eq_conditionalCovariance
      event positive,
    ← distribution.conditioned_covariance_eq_conditionalCovariance
      event positive,
    ← distribution.conditioned_covariance_eq_conditionalCovariance
      event positive]
  exact (distribution.conditioned event positive).covariance_add_right
    left right final

/-- Conditional covariance distributes over subtraction on the left. -/
theorem conditionalCovariance_sub_left {α : Type}
    (distribution : Distribution α) (event : α → Bool)
    (positive : 0 < distribution.probability event)
    (left middle right : α → Coordinate) :
    distribution.conditionalCovariance event
        (fun item => left item - middle item) right =
      distribution.conditionalCovariance event left right -
        distribution.conditionalCovariance event middle right := by
  rw [← distribution.conditioned_covariance_eq_conditionalCovariance
      event positive,
    ← distribution.conditioned_covariance_eq_conditionalCovariance
      event positive,
    ← distribution.conditioned_covariance_eq_conditionalCovariance
      event positive]
  exact (distribution.conditioned event positive).covariance_sub_left
    left middle right

/-- Conditional covariance distributes over subtraction on the right. -/
theorem conditionalCovariance_sub_right {α : Type}
    (distribution : Distribution α) (event : α → Bool)
    (positive : 0 < distribution.probability event)
    (left right final : α → Coordinate) :
    distribution.conditionalCovariance event left
        (fun item => right item - final item) =
      distribution.conditionalCovariance event left right -
        distribution.conditionalCovariance event left final := by
  rw [← distribution.conditioned_covariance_eq_conditionalCovariance
      event positive,
    ← distribution.conditioned_covariance_eq_conditionalCovariance
      event positive,
    ← distribution.conditioned_covariance_eq_conditionalCovariance
      event positive]
  exact (distribution.conditioned event positive).covariance_sub_right
    left right final

/-- Conditional covariance is homogeneous in its left observable. -/
theorem conditionalCovariance_scale_left {α : Type}
    (distribution : Distribution α) (event : α → Bool)
    (positive : 0 < distribution.probability event)
    (factor : Coordinate) (left right : α → Coordinate) :
    distribution.conditionalCovariance event
        (fun item => factor * left item) right =
      factor * distribution.conditionalCovariance event left right := by
  rw [← distribution.conditioned_covariance_eq_conditionalCovariance
      event positive,
    ← distribution.conditioned_covariance_eq_conditionalCovariance
      event positive]
  exact (distribution.conditioned event positive).covariance_scale_left
    factor left right

/-- Conditional covariance is homogeneous in its right observable. -/
theorem conditionalCovariance_scale_right {α : Type}
    (distribution : Distribution α) (event : α → Bool)
    (positive : 0 < distribution.probability event)
    (factor : Coordinate) (left right : α → Coordinate) :
    distribution.conditionalCovariance event left
        (fun item => factor * right item) =
      factor * distribution.conditionalCovariance event left right := by
  rw [← distribution.conditioned_covariance_eq_conditionalCovariance
      event positive,
    ← distribution.conditioned_covariance_eq_conditionalCovariance
      event positive]
  exact (distribution.conditioned event positive).covariance_scale_right
    factor left right

/-- A constant left observable has zero conditional covariance. -/
theorem conditionalCovariance_constant_left {α : Type}
    (distribution : Distribution α) (event : α → Bool)
    (positive : 0 < distribution.probability event)
    (constant : Coordinate) (value : α → Coordinate) :
    distribution.conditionalCovariance event (fun _ => constant) value = 0 := by
  rw [← distribution.conditioned_covariance_eq_conditionalCovariance
    event positive]
  exact (distribution.conditioned event positive).covariance_constant_left
    constant value

/-- A constant right observable has zero conditional covariance. -/
theorem conditionalCovariance_constant_right {α : Type}
    (distribution : Distribution α) (event : α → Bool)
    (positive : 0 < distribution.probability event)
    (value : α → Coordinate) (constant : Coordinate) :
    distribution.conditionalCovariance event value (fun _ => constant) = 0 := by
  rw [distribution.conditionalCovariance_symm]
  exact distribution.conditionalCovariance_constant_left
    event positive constant value

/-- Translating the left observable preserves conditional covariance. -/
theorem conditionalCovariance_add_constant_left {α : Type}
    (distribution : Distribution α) (event : α → Bool)
    (positive : 0 < distribution.probability event)
    (left right : α → Coordinate) (constant : Coordinate) :
    distribution.conditionalCovariance event
        (fun item => left item + constant) right =
      distribution.conditionalCovariance event left right := by
  rw [distribution.conditionalCovariance_add_left event positive left
      (fun _ => constant) right,
    distribution.conditionalCovariance_constant_left event positive,
    add_zero]

/-- Translating the right observable preserves conditional covariance. -/
theorem conditionalCovariance_add_constant_right {α : Type}
    (distribution : Distribution α) (event : α → Bool)
    (positive : 0 < distribution.probability event)
    (left right : α → Coordinate) (constant : Coordinate) :
    distribution.conditionalCovariance event left
        (fun item => right item + constant) =
      distribution.conditionalCovariance event left right := by
  rw [distribution.conditionalCovariance_add_right event positive left right
      (fun _ => constant),
    distribution.conditionalCovariance_constant_right event positive,
    add_zero]

end Distribution

end FiniteMeasure
