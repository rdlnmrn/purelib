module
import Purelib.Data.Rat.Fraction
public import Purelib.Measure.Distribution.Conditioning.Covariance.Basic

import Purelib.Measure.Distribution.Moments.Covariance
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
public import Purelib.Measure.Distribution.Conditioning.Moments
import Purelib.Measure.Distribution.Conditioning.Basic
import Purelib.Measure.EventAlgebra.Basic
import Purelib.Measure.Distribution.Conditioning.Mean
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

@[expose] public section

/-!
# Algebra of finite conditional covariance

On an explicitly positive event, conditional covariance is ordinary
covariance under the displayed conditioned finite distribution.  The exact
rational symmetry, bilinearity, scaling, and translation laws therefore
follow without any limiting conditional-expectation object.
-/

namespace Purelib.Measure

namespace Distribution

section
open Purelib
open Purelib.Data.Rat
/-- Conditional covariance is unchanged by reversing the two observables. -/
theorem conditionalCovariance_symm {α : Type}
    (distribution : Measure.Distribution α) (event : α → Bool)
    (left right : α → Fraction.Rational) :
    distribution.conditionalCovariance event left right =
      distribution.conditionalCovariance event right left := by
  unfold conditionalCovariance
  exact distribution.conditionalMean_congr event _ _ (fun item => by ring1)

open Purelib.Measure in
/-- Conditional covariance of an observable with itself equals its conditional variance. -/
theorem conditionalCovariance_self {α : Type}
    (distribution : Measure.Distribution α) (event : α → Bool)
    (value : α → Fraction.Rational) :
    distribution.conditionalCovariance event value value =
      distribution.conditionalVariance event value := by
  unfold conditionalCovariance Distribution.conditionalVariance
  exact distribution.conditionalMean_congr event _ _ (fun item => by ring1)

/-- Covariance under positive-event conditioning equals the original law's conditional covariance. -/
theorem conditioned_covariance_eq_conditionalCovariance {α : Type}
    (distribution : Measure.Distribution α) (event : α → Bool)
    (positive : 0 < distribution.probability event)
    (left right : α → Fraction.Rational) :
    (distribution.conditioned event positive).covariance left right =
      distribution.conditionalCovariance event left right := by
  unfold covariance conditionalCovariance
  rw [distribution.conditioned_expectation_eq_conditionalMean
      event positive left,
    distribution.conditioned_expectation_eq_conditionalMean
      event positive right,
    distribution.conditioned_expectation_eq_conditionalMean
      event positive]

/-- On a positive-probability event, conditional covariance is additive in its left observable. -/
theorem conditionalCovariance_add_left {α : Type}
    (distribution : Measure.Distribution α) (event : α → Bool)
    (positive : 0 < distribution.probability event)
    (left middle right : α → Fraction.Rational) :
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

/-- On a positive-probability event, conditional covariance is additive in its right observable. -/
theorem conditionalCovariance_add_right {α : Type}
    (distribution : Measure.Distribution α) (event : α → Bool)
    (positive : 0 < distribution.probability event)
    (left right final : α → Fraction.Rational) :
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

/-- On a positive-probability event, conditional covariance preserves subtraction in its left observable. -/
theorem conditionalCovariance_sub_left {α : Type}
    (distribution : Measure.Distribution α) (event : α → Bool)
    (positive : 0 < distribution.probability event)
    (left middle right : α → Fraction.Rational) :
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

/-- On a positive-probability event, conditional covariance preserves subtraction in its right observable. -/
theorem conditionalCovariance_sub_right {α : Type}
    (distribution : Measure.Distribution α) (event : α → Bool)
    (positive : 0 < distribution.probability event)
    (left right final : α → Fraction.Rational) :
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

/-- On a positive-probability event, scaling the left observable scales conditional covariance by the same factor. -/
theorem conditionalCovariance_scale_left {α : Type}
    (distribution : Measure.Distribution α) (event : α → Bool)
    (positive : 0 < distribution.probability event)
    (factor : Fraction.Rational) (left right : α → Fraction.Rational) :
    distribution.conditionalCovariance event
        (fun item => factor * left item) right =
      factor * distribution.conditionalCovariance event left right := by
  rw [← distribution.conditioned_covariance_eq_conditionalCovariance
      event positive,
    ← distribution.conditioned_covariance_eq_conditionalCovariance
      event positive]
  exact (distribution.conditioned event positive).covariance_scale_left
    factor left right

/-- On a positive-probability event, scaling the right observable scales conditional covariance by the same factor. -/
theorem conditionalCovariance_scale_right {α : Type}
    (distribution : Measure.Distribution α) (event : α → Bool)
    (positive : 0 < distribution.probability event)
    (factor : Fraction.Rational) (left right : α → Fraction.Rational) :
    distribution.conditionalCovariance event left
        (fun item => factor * right item) =
      factor * distribution.conditionalCovariance event left right := by
  rw [← distribution.conditioned_covariance_eq_conditionalCovariance
      event positive,
    ← distribution.conditioned_covariance_eq_conditionalCovariance
      event positive]
  exact (distribution.conditioned event positive).covariance_scale_right
    factor left right

/-- On a positive-probability event, a constant left observable has zero conditional covariance. -/
theorem conditionalCovariance_constant_left {α : Type}
    (distribution : Measure.Distribution α) (event : α → Bool)
    (positive : 0 < distribution.probability event)
    (constant : Fraction.Rational) (value : α → Fraction.Rational) :
    distribution.conditionalCovariance event (fun _ => constant) value = 0 := by
  rw [← distribution.conditioned_covariance_eq_conditionalCovariance
    event positive]
  exact (distribution.conditioned event positive).covariance_constant_left
    constant value

/-- On a positive-probability event, a constant right observable has zero conditional covariance. -/
theorem conditionalCovariance_constant_right {α : Type}
    (distribution : Measure.Distribution α) (event : α → Bool)
    (positive : 0 < distribution.probability event)
    (value : α → Fraction.Rational) (constant : Fraction.Rational) :
    distribution.conditionalCovariance event value (fun _ => constant) = 0 := by
  rw [distribution.conditionalCovariance_symm]
  exact distribution.conditionalCovariance_constant_left
    event positive constant value

/-- On a positive-probability event, adding a constant to the left observable preserves conditional covariance. -/
theorem conditionalCovariance_add_constant_left {α : Type}
    (distribution : Measure.Distribution α) (event : α → Bool)
    (positive : 0 < distribution.probability event)
    (left right : α → Fraction.Rational) (constant : Fraction.Rational) :
    distribution.conditionalCovariance event
        (fun item => left item + constant) right =
      distribution.conditionalCovariance event left right := by
  rw [distribution.conditionalCovariance_add_left event positive left
      (fun _ => constant) right,
    distribution.conditionalCovariance_constant_left event positive,
    add_zero]

/-- On a positive-probability event, adding a constant to the right observable preserves conditional covariance. -/
theorem conditionalCovariance_add_constant_right {α : Type}
    (distribution : Measure.Distribution α) (event : α → Bool)
    (positive : 0 < distribution.probability event)
    (left right : α → Fraction.Rational) (constant : Fraction.Rational) :
    distribution.conditionalCovariance event left
        (fun item => right item + constant) =
      distribution.conditionalCovariance event left right := by
  rw [distribution.conditionalCovariance_add_right event positive left right
      (fun _ => constant),
    distribution.conditionalCovariance_constant_right event positive,
    add_zero]

end

end Distribution

end Purelib.Measure
