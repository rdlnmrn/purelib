module
import Purelib.Data.Rat.Fraction
import Purelib.Measure.Content.AbsoluteContinuity.Basic
import Purelib.Measure.Content.Basic
import Purelib.Measure.Content.Operations

public import Purelib.Measure.Distribution.Mixture.Basic
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Content
import Purelib.Measure.Content.EssentialMaximum.Operations
import Purelib.Measure.Classified.Basic
import Purelib.Measure.Filtration.Basic
import Purelib.Measure.Distribution.Partition.Basic
import Purelib.Measure.Distribution.Partition.Positive
import Purelib.Measure.EventAlgebra.Simple.Basic
import Purelib.Measure.Event.Chain
import Purelib.Approximation.OneSided.Basic
import Purelib.Measure.Classified.FixedLawProcess
import Purelib.Approximation.OneSided.Located
public import Purelib.Measure.Distribution.EssentialMaximum.Basic
import Purelib.Measure.EventAlgebra.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

/-!
# Essential maxima of explicit finite mixtures

A mixture concatenates two atom tables after scaling their weights.  Positive
scaling preserves nonzero support, while a zero coefficient discards that
component.  This gives an exact, executable `L∞` mixture formula, including
the endpoint cases, without a supremum or a selected maximizing atom.
-/

public section

namespace Purelib.Measure

namespace Distribution

section
open Purelib
open Purelib.Data.Rat
/-- Compute a mixture's essential maximum as the maximum of its two component maxima, replacing zero-weight components
by zero. -/
theorem mixture_essentialMaximumMagnitude {α : Type}
    (left right : Measure.Distribution α) (weight : Measure.MixingWeight)
    (value : α → Fraction.Rational) :
    (left.mixture right weight).essentialMaximumMagnitude value =
      max
        (if weight.coefficient = 0 then 0
          else left.essentialMaximumMagnitude value)
        (if weight.complement = 0 then 0
          else right.essentialMaximumMagnitude value) := by
  change
    ((left.toContent.scale weight.coefficient weight.nonnegative).append
      (right.toContent.scale weight.complement
        weight.complement_nonnegative)).essentialMaximumMagnitude value =
      max
        (if weight.coefficient = 0 then 0
          else left.toContent.essentialMaximumMagnitude value)
        (if weight.complement = 0 then 0
          else right.toContent.essentialMaximumMagnitude value)
  rw [Content.append_essentialMaximumMagnitude]
  by_cases leftZero : weight.coefficient = 0
  · rw [left.toContent.scale_essentialMaximumMagnitude_of_eq_zero
      weight.coefficient weight.nonnegative leftZero value]
    by_cases rightZero : weight.complement = 0
    · rw [right.toContent.scale_essentialMaximumMagnitude_of_eq_zero
        weight.complement weight.complement_nonnegative rightZero value]
      simp only [-eq_self, -iff_self, if_pos leftZero, if_pos rightZero]
      rfl
    · rw [right.toContent.scale_essentialMaximumMagnitude_of_ne
        weight.complement weight.complement_nonnegative rightZero value]
      simp only [-eq_self, -iff_self, if_pos leftZero, if_neg rightZero]
      rfl
  · rw [left.toContent.scale_essentialMaximumMagnitude_of_ne
      weight.coefficient weight.nonnegative leftZero value]
    by_cases rightZero : weight.complement = 0
    · rw [right.toContent.scale_essentialMaximumMagnitude_of_eq_zero
        weight.complement weight.complement_nonnegative rightZero value]
      simp only [-eq_self, -iff_self, if_neg leftZero, if_pos rightZero]
      rfl
    · rw [right.toContent.scale_essentialMaximumMagnitude_of_ne
        weight.complement weight.complement_nonnegative rightZero value]
      simp only [-eq_self, -iff_self, if_neg leftZero, if_neg rightZero]
      rfl

/-- A mixture's essential maximum is bounded by the maximum of the two original component maxima. -/
theorem mixture_essentialMaximumMagnitude_le {α : Type}
    (left right : Measure.Distribution α) (weight : Measure.MixingWeight)
    (value : α → Fraction.Rational) :
    (left.mixture right weight).essentialMaximumMagnitude value ≤
      max (left.essentialMaximumMagnitude value)
        (right.essentialMaximumMagnitude value) := by
  rw [left.mixture_essentialMaximumMagnitude right weight value]
  apply Fraction.Order.Basic.max_le
  · by_cases zero : weight.coefficient = 0
    · simp only [-eq_self, -iff_self, if_pos zero]
      exact (left.essentialMaximumMagnitude_nonnegative value).trans
        (Fraction.Order.Basic.le_max_left _ _)
    · simp only [-eq_self, -iff_self, if_neg zero]
      exact Fraction.Order.Basic.le_max_left _ _
  · by_cases zero : weight.complement = 0
    · simp only [-eq_self, -iff_self, if_pos zero]
      exact (right.essentialMaximumMagnitude_nonnegative value).trans
        (Fraction.Order.Basic.le_max_right _ _)
    · simp only [-eq_self, -iff_self, if_neg zero]
      exact Fraction.Order.Basic.le_max_right _ _

/-- When both mixing coefficients are positive, the mixture's essential maximum equals the maximum of the original
component maxima. -/
theorem mixture_essentialMaximumMagnitude_eq_max {α : Type}
    (left right : Measure.Distribution α) (weight : Measure.MixingWeight)
    (coefficientPositive : 0 < weight.coefficient)
    (complementPositive : 0 < weight.complement)
    (value : α → Fraction.Rational) :
    (left.mixture right weight).essentialMaximumMagnitude value =
      max (left.essentialMaximumMagnitude value)
        (right.essentialMaximumMagnitude value) := by
  rw [left.mixture_essentialMaximumMagnitude right weight value]
  simp only [-eq_self, -iff_self, if_neg coefficientPositive.ne', if_neg complementPositive.ne']
  rfl

/-- A zero left mixing coefficient leaves the original right-law essential maximum. -/
theorem mixture_essentialMaximumMagnitude_of_coefficient_eq_zero
    {α : Type} (left right : Measure.Distribution α) (weight : Measure.MixingWeight)
    (coefficientZero : weight.coefficient = 0)
    (value : α → Fraction.Rational) :
    (left.mixture right weight).essentialMaximumMagnitude value =
      right.essentialMaximumMagnitude value := by
  have complementNonzero : weight.complement ≠ 0 := by
    rw [MixingWeight.complement, coefficientZero]
    decide
  rw [left.mixture_essentialMaximumMagnitude right weight value]
  simp only [-eq_self, -iff_self, if_pos coefficientZero, if_neg complementNonzero]
  exact Fraction.Order.Basic.max_eq_right (right.essentialMaximumMagnitude_nonnegative value)

/-- A unit left mixing coefficient leaves the original left-law essential maximum. -/
theorem mixture_essentialMaximumMagnitude_of_coefficient_eq_one
    {α : Type} (left right : Measure.Distribution α) (weight : Measure.MixingWeight)
    (coefficientOne : weight.coefficient = 1)
    (value : α → Fraction.Rational) :
    (left.mixture right weight).essentialMaximumMagnitude value =
      left.essentialMaximumMagnitude value := by
  have coefficientNonzero : weight.coefficient ≠ 0 := by
    rw [coefficientOne]
    decide
  have complementZero : weight.complement = 0 := by
    rw [MixingWeight.complement, coefficientOne]
    ring1
  rw [left.mixture_essentialMaximumMagnitude right weight value]
  simp only [-eq_self, -iff_self, if_neg coefficientNonzero, if_pos complementZero]
  exact Fraction.Order.Basic.max_eq_left (left.essentialMaximumMagnitude_nonnegative value)

/-- A mixture's essential distance is bounded by the maximum of the two original component essential distances. -/
theorem mixture_essentialMaximumDistance_le {α : Type}
    (left right : Measure.Distribution α) (weight : Measure.MixingWeight)
    (first second : α → Fraction.Rational) :
    (left.mixture right weight).essentialMaximumDistance first second ≤
      max (left.essentialMaximumDistance first second)
        (right.essentialMaximumDistance first second) := by
  unfold essentialMaximumDistance
  exact left.mixture_essentialMaximumMagnitude_le right weight
    (fun item => first item - second item)

/-- With both mixing coefficients positive, the mixture's essential distance equals the maximum of the original
component essential distances. -/
theorem mixture_essentialMaximumDistance_eq_max {α : Type}
    (left right : Measure.Distribution α) (weight : Measure.MixingWeight)
    (coefficientPositive : 0 < weight.coefficient)
    (complementPositive : 0 < weight.complement)
    (first second : α → Fraction.Rational) :
    (left.mixture right weight).essentialMaximumDistance first second =
      max (left.essentialMaximumDistance first second)
        (right.essentialMaximumDistance first second) := by
  unfold essentialMaximumDistance
  exact left.mixture_essentialMaximumMagnitude_eq_max right weight
    coefficientPositive complementPositive
    (fun item => first item - second item)

end

end Distribution

end Purelib.Measure
