module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Measure.Content.Integral
import Purelib.Measure.Content.SignedDifference
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Content
import Purelib.Measure.Distribution.Expectation
import Purelib.Measure.Distribution.Stability
public import Purelib.Measure.Distribution.TotalVariation.Basic
import Purelib.Measure.SignedContent.Basic
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

section
@[expose] public section

/-!
# Total variation distance between finite rational laws

The duplicate-free union of two displayed atom catalogues supports their
signed difference.  A decidable comparison of the two singleton masses gives
an executable Hahn event.  For probability distributions this event attains
the largest possible event-probability discrepancy, because the positive and
negative Jordan masses agree.

Thus total variation is an exact rational computation here.  The development
proves its sharp event bound, half-L1 formula, metric laws modulo evaluation
equivalence, contraction under pushforward, and the coupling inequality.
-/

namespace Purelib.Measure

namespace Distribution

open Purelib.Data.Rat
/-- A nonnegative observable with a global nonnegative ceiling has expectation separation bounded by that ceiling times
total variation. -/
theorem expectation_separation_le_bound_mul_totalVariationDistance
    {α : Type} [DecidableEq α] (left right : Distribution α)
    (value : α → Fraction.Rational) (bound : Fraction.Rational)
    (_boundNonnegative : 0 ≤ bound)
    (nonnegative : ∀ item, 0 ≤ value item)
    (bounded : ∀ item, value item ≤ bound) :
    Distance.rationalSeparation (left.expectation value) (right.expectation value) ≤
      bound * left.totalVariationDistance right := by
  let difference := left.signedDifference right
  have measured : difference.integral value =
      left.expectation value - right.expectation value :=
    left.toContent.signedDifference_integral
      right.toContent value
  have positiveNonnegative :
      0 ≤ difference.positiveContent.integral value := by
    apply difference.positiveContent.integral_nonneg
    intro atom member
    exact nonnegative atom.item
  have negativeNonnegative :
      0 ≤ difference.negativeContent.integral value := by
    apply difference.negativeContent.integral_nonneg
    intro atom member
    exact nonnegative atom.item
  have positiveBound : difference.positiveContent.integral value ≤
      difference.positiveContent.total * bound := by
    calc
      difference.positiveContent.integral value ≤
          difference.positiveContent.integral (fun _ => bound) := by
        apply difference.positiveContent.integral_mono
        intro atom member
        exact bounded atom.item
      _ = difference.positiveContent.total * bound :=
        difference.positiveContent.integral_constant bound
  have negativeBound : difference.negativeContent.integral value ≤
      difference.negativeContent.total * bound := by
    calc
      difference.negativeContent.integral value ≤
          difference.negativeContent.integral (fun _ => bound) := by
        apply difference.negativeContent.integral_mono
        intro atom member
        exact bounded atom.item
      _ = difference.negativeContent.total * bound :=
        difference.negativeContent.integral_constant bound
  have upper : difference.integral value ≤
      bound * difference.positiveContent.total := by
    rw [difference.integral_eq_positive_sub_negative]
    calc
      difference.positiveContent.integral value -
            difference.negativeContent.integral value ≤
          difference.positiveContent.integral value :=
        (Fraction.Order.Arithmetic.sub_le_iff_le_add_direct).mpr (by
          have translated := Fraction.Order.Arithmetic.add_le_add_direct
            (Fraction.Order.Basic.le_refl (difference.positiveContent.integral value)) negativeNonnegative
          simpa only [-eq_self, -iff_self, add_zero] using translated)
      _ ≤ difference.positiveContent.total * bound := positiveBound
      _ = bound * difference.positiveContent.total := by ring1
  have negativeUpper : -difference.integral value ≤
      bound * difference.positiveContent.total := by
    rw [difference.integral_eq_positive_sub_negative]
    calc
      -(difference.positiveContent.integral value -
            difference.negativeContent.integral value) =
          difference.negativeContent.integral value -
            difference.positiveContent.integral value := by ring1
      _ ≤ difference.negativeContent.integral value :=
        (Fraction.Order.Arithmetic.sub_le_iff_le_add_direct).mpr (by
          have translated := Fraction.Order.Arithmetic.add_le_add_direct
            (Fraction.Order.Basic.le_refl (difference.negativeContent.integral value)) positiveNonnegative
          simpa only [-eq_self, -iff_self, add_zero] using translated)
      _ ≤ difference.negativeContent.total * bound := negativeBound
      _ = bound * difference.positiveContent.total := by
        rw [← left.signedDifference_positiveTotal_eq_negativeTotal right]
        ring1
  unfold Distance.rationalSeparation totalVariationDistance
  apply Fraction.Order.Basic.max_le
  · rw [← measured]
    exact upper
  · calc
      right.expectation value - left.expectation value =
          -(left.expectation value - right.expectation value) := by ring1
      _ = -difference.integral value := by rw [measured]
      _ ≤ bound * difference.positiveContent.total := negativeUpper

/-- A globally unit-interval-valued observable has expectation separation bounded by total variation. -/
theorem expectation_separation_le_totalVariationDistance_of_unitInterval
    {α : Type} [DecidableEq α] (left right : Distribution α)
    (value : α → Fraction.Rational)
    (nonnegative : ∀ item, 0 ≤ value item)
    (atMostOne : ∀ item, value item ≤ 1) :
    Distance.rationalSeparation (left.expectation value) (right.expectation value) ≤
      left.totalVariationDistance right := by
  have bounded :=
    left.expectation_separation_le_bound_mul_totalVariationDistance right
      value 1 (by decide) nonnegative atMostOne
  simpa only [-eq_self, -iff_self, one_mul] using bounded

/-- An observable globally between ordered endpoints has expectation separation bounded by interval width times total
variation. -/
theorem expectation_separation_le_oscillation_mul_totalVariationDistance
    {α : Type} [DecidableEq α] (left right : Distribution α)
    (value : α → Fraction.Rational) (lower upper : Fraction.Rational)
    (order : lower ≤ upper)
    (lowerBound : ∀ item, lower ≤ value item)
    (upperBound : ∀ item, value item ≤ upper) :
    Distance.rationalSeparation (left.expectation value) (right.expectation value) ≤
      (upper - lower) * left.totalVariationDistance right := by
  let shifted := fun item => value item - lower
  have shiftedNonnegative : ∀ item, 0 ≤ shifted item :=
    fun item => Fraction.Order.Arithmetic.sub_nonneg_direct (lowerBound item)
  have shiftedBounded : ∀ item, shifted item ≤ upper - lower :=
    fun item => Fraction.Order.Arithmetic.sub_le_sub_right_direct (upperBound item) lower
  have estimate :=
    left.expectation_separation_le_bound_mul_totalVariationDistance right
      shifted (upper - lower) (Fraction.Order.Arithmetic.sub_nonneg_direct order)
      shiftedNonnegative shiftedBounded
  have leftShift : left.expectation shifted =
      left.expectation value - lower := by
    unfold shifted
    rw [left.expectation_sub, left.expectation_constant]
  have rightShift : right.expectation shifted =
      right.expectation value - lower := by
    unfold shifted
    rw [right.expectation_sub, right.expectation_constant]
  rw [leftShift, rightShift] at estimate
  have separationShift : Distance.rationalSeparation
      (left.expectation value - lower) (right.expectation value - lower) =
      Distance.rationalSeparation (left.expectation value)
        (right.expectation value) := by
    unfold Distance.rationalSeparation
    congr 1 <;> ring1
  rw [separationShift] at estimate
  exact estimate
end Distribution

end Purelib.Measure

end
