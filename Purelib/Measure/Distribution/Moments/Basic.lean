module
import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Distribution.Expectation
import Purelib.Measure.Weighted.Integral
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Data.Rat.Fraction.Compatibility
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
import Purelib.Measure.Distribution.Stability
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Measure.Weighted.Basic

section
@[expose] public section

/-!
# Finite rational probability

A probability distribution is a displayed finite weighted list whose total is
exactly one.  Events are executable Boolean tests, so their probabilities and
expectations are exact rational calculations.
-/

namespace Purelib.Measure
namespace Distribution

/-! ## Exact finite dispersion -/

open Purelib.Data.Rat
/-- Take the expectation of squared deviation from the supplied rational center. -/
def varianceAround {α : Type} (distribution : Distribution α)
    (value : α → Fraction.Rational) (center : Fraction.Rational) : Fraction.Rational :=
  distribution.expectation (fun item => (value item - center) ^ 2)

/-- Pointwise equal observables have equal mean squared deviations from the same center. -/
theorem varianceAround_congr {α : Type} (distribution : Distribution α)
    (left right : α → Fraction.Rational) (center : Fraction.Rational)
    (pointwise : ∀ item, left item = right item) :
    distribution.varianceAround left center =
      distribution.varianceAround right center := by
  unfold varianceAround
  exact distribution.expectation_congr _ _ (fun item =>
    congrArg (fun value => (value - center) ^ 2) (pointwise item))

/-- Take the mean squared deviation from the observable's expectation under the exact retained distribution. -/
def variance {α : Type} (distribution : Distribution α)
    (value : α → Fraction.Rational) : Fraction.Rational :=
  distribution.varianceAround value (distribution.expectation value)

/-- Pointwise equal observables have equal variance in the same retained distribution. -/
theorem variance_congr {α : Type} (distribution : Distribution α)
    (left right : α → Fraction.Rational)
    (pointwise : ∀ item, left item = right item) :
    distribution.variance left = distribution.variance right := by
  have meanEqual := distribution.expectation_congr left right pointwise
  unfold variance
  rw [meanEqual]
  exact distribution.varianceAround_congr left right
    (distribution.expectation right) pointwise

/-- Mean squared deviation from any rational center is nonnegative. -/
theorem varianceAround_nonneg {α : Type} (distribution : Distribution α)
    (value : α → Fraction.Rational) (center : Fraction.Rational) :
    0 ≤ distribution.varianceAround value center := by
  apply distribution.expectation_nonneg
  intro atom member
  exact Fraction.Order.Arithmetic.sq_nonneg_direct
    (value atom.item - center)

/-- Variance in the retained finite distribution is nonnegative. -/
theorem variance_nonneg {α : Type} (distribution : Distribution α)
    (value : α → Fraction.Rational) : 0 ≤ distribution.variance value :=
  distribution.varianceAround_nonneg value (distribution.expectation value)

/-- An event whose selected squared deviations exceed a positive threshold squared has probability at most variance
divided by that square.

The deviation condition is checked only at retained distribution occurrences selected by the same event. -/
theorem chebyshev_bound {α : Type} (distribution : Distribution α)
    (event : α → Bool) (value : α → Fraction.Rational)
    (threshold : Fraction.Rational) (positive : 0 < threshold)
    (selectedDeviation : ∀ atom, atom ∈ distribution.atoms →
      event atom.item = true →
        threshold ^ 2 ≤
          (value atom.item - distribution.expectation value) ^ 2) :
    distribution.probability event ≤
      distribution.variance value / threshold ^ 2 := by
  apply distribution.markov_bound event
    (fun item => (value item - distribution.expectation value) ^ 2)
    (threshold ^ 2)
    (Fraction.Order.Arithmetic.pow_pos_direct positive 2)
  · intro atom member
    exact Fraction.Order.Arithmetic.sq_nonneg_direct
      (value atom.item - distribution.expectation value)
  · exact selectedDeviation
end Distribution

end Purelib.Measure

end

section
section
@[expose] public section

/-!
# Finite rational moment identities

Variance and covariance are exact rational weighted sums on displayed finite
distributions.  Their algebraic identities need only finite linearity and
direct polynomial calculations.
-/

namespace Purelib.Measure

namespace Distribution

open Purelib.Data.Rat in
/-- Variance equals the second moment minus the square of the expectation. -/
theorem variance_eq_secondMoment_sub_sq {α : Type}
    (distribution : Distribution α) (value : α → Fraction.Rational) :
    distribution.variance value =
      distribution.expectation (fun item => value item ^ 2) -
        distribution.expectation value ^ 2 := by
  unfold variance varianceAround
  calc
    distribution.expectation (fun item =>
        (value item - distribution.expectation value) ^ 2) =
        distribution.expectation (fun item =>
          (value item ^ 2 -
            (2 * distribution.expectation value) * value item) +
            distribution.expectation value ^ 2) :=
      distribution.expectation_congr _ _ (fun item => by ring1)
    _ = distribution.expectation (fun item => value item ^ 2) -
          distribution.expectation value ^ 2 := by
      rw [distribution.expectation_add,
        distribution.expectation_sub, distribution.expectation_scale,
        distribution.expectation_constant]
      ring1

/-- An event indicator has variance equal to its probability times one minus that probability. -/
theorem variance_indicator {α : Type}
    (distribution : Distribution α) (event : α → Bool) :
    distribution.variance (indicator event) =
      distribution.probability event *
        (1 - distribution.probability event) := by
  rw [distribution.variance_eq_secondMoment_sub_sq,
    distribution.expectation_indicator]
  have indicatorSquare : distribution.expectation
        (fun item => indicator event item ^ 2) =
      distribution.expectation (indicator event) :=
    distribution.expectation_congr _ _ (fun item => by
      cases selected : event item <;>
        simp only [indicator, selected] <;> ring1)
  rw [indicatorSquare, distribution.expectation_indicator]
  ring1

section
open Purelib.Data.Rat
/-- Every Boolean event indicator has variance at most one quarter. -/
theorem variance_indicator_le_quarter {α : Type}
    (distribution : Distribution α) (event : α → Bool) :
    distribution.variance (indicator event) ≤ 1 / 4 := by
  rw [distribution.variance_indicator]
  apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
  calc
    0 ≤ (distribution.probability event - 1 / 2) ^ 2 :=
      Fraction.Order.Arithmetic.sq_nonneg_direct _
    _ = (1 / 2) ^ 2 - distribution.probability event *
        (2 * (1 / 2) - distribution.probability event) := by ring1
    _ = (1 / 2) ^ 2 - distribution.probability event *
        (1 - distribution.probability event) := by
      rw [show (2 : Fraction.Rational) * (1 / 2) = 1 by decide]
    _ = 1 / 4 - distribution.probability event *
        (1 - distribution.probability event) := by
      rw [show ((1 / 2 : Fraction.Rational) ^ 2) = 1 / 4 by decide]

/-- A constant observable has zero variance. -/
theorem variance_constant {α : Type}
    (distribution : Distribution α) (constant : Fraction.Rational) :
    distribution.variance (fun _ => constant) = 0 := by
  rw [distribution.variance_eq_secondMoment_sub_sq,
    distribution.expectation_constant, distribution.expectation_constant]
  ring1

/-- The square of an observable's expectation is at most its second moment. -/
theorem expectation_sq_le_secondMoment {α : Type}
    (distribution : Distribution α) (value : α → Fraction.Rational) :
    distribution.expectation value ^ 2 ≤
      distribution.expectation (fun item => value item ^ 2) := by
  have nonnegative := distribution.variance_nonneg value
  rw [distribution.variance_eq_secondMoment_sub_sq] at nonnegative
  exact Fraction.Order.Arithmetic.le_of_sub_nonneg_direct nonnegative

/-- Mean squared deviation around a center equals variance plus squared displacement of the mean from that center. -/
theorem varianceAround_eq_variance_add_mean_sub_sq {α : Type}
    (distribution : Distribution α) (value : α → Fraction.Rational)
    (center : Fraction.Rational) :
    distribution.varianceAround value center =
      distribution.variance value +
        (distribution.expectation value - center) ^ 2 := by
  rw [distribution.variance_eq_secondMoment_sub_sq]
  unfold varianceAround
  calc
    distribution.expectation (fun item => (value item - center) ^ 2) =
        distribution.expectation (fun item =>
          value item ^ 2 - (2 * center) * value item + center ^ 2) :=
      distribution.expectation_congr _ _ (fun item => by ring1)
    _ = distribution.expectation (fun item => value item ^ 2) -
          distribution.expectation value ^ 2 +
            (distribution.expectation value - center) ^ 2 := by
      rw [distribution.expectation_add,
        distribution.expectation_sub, distribution.expectation_scale,
        distribution.expectation_constant]
      ring1

/-- Centering at the expectation minimizes mean squared deviation among rational centers. -/
theorem variance_le_varianceAround {α : Type}
    (distribution : Distribution α) (value : α → Fraction.Rational)
    (center : Fraction.Rational) :
    distribution.variance value ≤
      distribution.varianceAround value center := by
  rw [distribution.varianceAround_eq_variance_add_mean_sub_sq]
  calc
    distribution.variance value = distribution.variance value + 0 := by
      ring1
    _ ≤ distribution.variance value +
        (distribution.expectation value - center) ^ 2 :=
      Fraction.Order.Arithmetic.add_le_add_direct le_rfl
        (Fraction.Order.Arithmetic.sq_nonneg_direct _)

/-- A center attains the variance as its mean squared deviation exactly when it equals the expectation. -/
theorem varianceAround_eq_variance_iff_center_eq_expectation {α : Type}
    (distribution : Distribution α) (value : α → Fraction.Rational)
    (center : Fraction.Rational) :
    distribution.varianceAround value center = distribution.variance value ↔
      center = distribution.expectation value := by
  constructor
  · intro equality
    rw [distribution.varianceAround_eq_variance_add_mean_sub_sq]
      at equality
    have squareZero :
        (distribution.expectation value - center) ^ 2 = 0 := by
      calc
        (distribution.expectation value - center) ^ 2 =
            (distribution.variance value +
              (distribution.expectation value - center) ^ 2) -
                distribution.variance value := by ring1
        _ = distribution.variance value - distribution.variance value :=
          congrArg (fun amount => amount - distribution.variance value) equality
        _ = 0 := by ring1
    have differenceZero : distribution.expectation value - center = 0 :=
      (Fraction.Order.Arithmetic.sq_eq_zero_direct _).mp squareZero
    calc
      center = distribution.expectation value -
          (distribution.expectation value - center) := by ring1
      _ = distribution.expectation value := by
        rewrite [differenceZero]
        ring1
  · intro centerEqual
    rw [distribution.varianceAround_eq_variance_add_mean_sub_sq,
      centerEqual, sub_self]
    ring1

/-- An observable's variance is at most its second moment. -/
theorem variance_le_secondMoment {α : Type}
    (distribution : Distribution α) (value : α → Fraction.Rational) :
    distribution.variance value ≤
      distribution.expectation (fun item => value item ^ 2) := by
  rw [distribution.variance_eq_secondMoment_sub_sq]
  have meanSquareNonnegative :=
    Fraction.Order.Arithmetic.sq_nonneg_direct
      (distribution.expectation value)
  have negativeMeanSquareNonpositive :
      -(distribution.expectation value ^ 2) ≤ 0 := by
    simpa only [neg_zero] using
      Fraction.Order.Arithmetic.neg_le_neg_direct meanSquareNonnegative
  calc
    distribution.expectation (fun item => value item ^ 2) -
          distribution.expectation value ^ 2 ≤
        distribution.expectation (fun item => value item ^ 2) + 0 := by
      change distribution.expectation (fun item => value item ^ 2) +
          -(distribution.expectation value ^ 2) ≤
        distribution.expectation (fun item => value item ^ 2) + 0
      exact Fraction.Order.Arithmetic.add_le_add_direct le_rfl
        negativeMeanSquareNonpositive
    _ = distribution.expectation (fun item => value item ^ 2) := by ring1

/-- Adding a constant to an observable preserves its variance. -/
theorem variance_add_constant {α : Type}
    (distribution : Distribution α) (value : α → Fraction.Rational)
    (constant : Fraction.Rational) :
    distribution.variance (fun item => value item + constant) =
      distribution.variance value := by
  have mean :
      distribution.expectation (fun item => value item + constant) =
        distribution.expectation value + constant := by
    rw [distribution.expectation_add,
      distribution.expectation_constant]
  unfold variance varianceAround
  rw [mean]
  exact distribution.expectation_congr _ _ (fun item => by ring1)

/-- Scaling an observable scales its variance by the square of the factor. -/
theorem variance_scale {α : Type}
    (distribution : Distribution α) (factor : Fraction.Rational)
    (value : α → Fraction.Rational) :
    distribution.variance (fun item => factor * value item) =
      factor ^ 2 * distribution.variance value := by
  have mean :
      distribution.expectation (fun item => factor * value item) =
        factor * distribution.expectation value :=
    distribution.expectation_scale factor value
  unfold variance varianceAround
  rw [mean]
  calc
    distribution.expectation (fun item =>
        (factor * value item - factor * distribution.expectation value) ^ 2) =
        distribution.expectation (fun item => factor ^ 2 *
          (value item - distribution.expectation value) ^ 2) :=
      distribution.expectation_congr _ _ (fun item => by ring1)
    _ = factor ^ 2 * distribution.expectation (fun item =>
          (value item - distribution.expectation value) ^ 2) :=
      distribution.expectation_scale _ _
end

end Distribution

end Purelib.Measure

end

end

