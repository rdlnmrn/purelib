module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Distance.Basic
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Content.Basic
public import Purelib.Measure.Content.EssentialMaximum.Basic
import Purelib.Measure.Content.Lp.L1
import Purelib.Measure.Content.EssentialBound.Lp
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Measure.Weighted.Integral
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Measure.Content.Integral
import Purelib.Measure.Content.Lp.Natural
import Purelib.Measure.Content.Lp.L2
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

section
/-!
# Executable finite essential maxima

On a displayed finite atom table, every rational observable has a computed
least essential magnitude bound: recursively ignore zero-weight rows and
take the rational maximum on the rest.  Thus no supremum, infimum, or
completed line is needed.  The construction also gives an explicit uniform
absolute-continuity bound for restricted integrals.
-/

@[expose] public section

namespace Purelib.Measure
namespace Content

section
open Purelib.Data.Rat
/-- The magnitude integral of an event indicator equals the original event measurement. -/
private theorem poweredL1_indicator {α : Type}
    (content : Content α) (event : α → Bool) :
    content.poweredL1 (Distribution.indicator event) =
      content.measure event := by
  unfold poweredL1
  calc
    content.integral (fun item =>
        Distance.rationalSeparation (Distribution.indicator event item) 0) =
        content.integral (Distribution.indicator event) :=
      content.integral_congr _ _ (fun item => by
        cases selected : event item
        · simp only [-eq_self, -iff_self, Distribution.indicator, selected]
          rfl
        · simp only [-eq_self, -iff_self, Distribution.indicator, selected]
          decide)
    _ = content.measure event := content.integral_indicator event

/-- The magnitude integral restricted by an event indicator is bounded by essential maximum magnitude times that exact
event mass. -/
theorem poweredL1_indicator_mul_le_essentialMaximum_mul_measure {α : Type}
    (content : Content α) (event : α → Bool)
    (value : α → Fraction.Rational) :
    content.poweredL1 (fun item =>
        Distribution.indicator event item * value item) ≤
      content.essentialMaximumMagnitude value * content.measure event := by
  have bound := content.poweredL1_mul_le_of_right_essentialBound
    (Distribution.indicator event) value
    (content.essentialMaximumMagnitude value)
    (content.essentiallyBoundedBy_essentialMaximumMagnitude value)
  rw [content.poweredL1_indicator event] at bound
  exact bound

/-- The product's magnitude integral is bounded by the right essential maximum times the left magnitude integral. -/
theorem poweredL1_mul_le_essentialMaximum_right {α : Type}
    (content : Content α) (left right : α → Fraction.Rational) :
    content.poweredL1 (fun item => left item * right item) ≤
      content.essentialMaximumMagnitude right * content.poweredL1 left :=
  content.poweredL1_mul_le_of_right_essentialBound left right
    (content.essentialMaximumMagnitude right)
    (content.essentiallyBoundedBy_essentialMaximumMagnitude right)

/-- The product's magnitude integral is bounded by the left essential maximum times the right magnitude integral. -/
theorem poweredL1_mul_le_essentialMaximum_left {α : Type}
    (content : Content α) (left right : α → Fraction.Rational) :
    content.poweredL1 (fun item => left item * right item) ≤
      content.essentialMaximumMagnitude left * content.poweredL1 right := by
  have bound := content.poweredL1_mul_le_essentialMaximum_right right left
  have commuted : content.poweredL1 (fun item => right item * left item) =
      content.poweredL1 (fun item => left item * right item) :=
    content.poweredL1_congr _ _ (fun item => by ring1)
  rw [commuted] at bound
  exact bound

/-- The integrated distance of two products is bounded by the two factor distances weighted by the retained
opposite-factor essential maxima.

The decomposition uses the first product's right factor and the second product's left factor, preserving their distinct
coefficients. -/
theorem l1Distance_mul_le {α : Type} (content : Content α)
    (leftFirst leftSecond rightFirst rightSecond : α → Fraction.Rational) :
    content.l1Distance
        (fun item => leftFirst item * rightFirst item)
        (fun item => leftSecond item * rightSecond item) ≤
      content.essentialMaximumMagnitude rightFirst *
          content.l1Distance leftFirst leftSecond +
        content.essentialMaximumMagnitude leftSecond *
          content.l1Distance rightFirst rightSecond := by
  calc
    content.l1Distance
          (fun item => leftFirst item * rightFirst item)
          (fun item => leftSecond item * rightSecond item) =
        content.poweredL1 (fun item =>
          leftFirst item * rightFirst item -
            leftSecond item * rightSecond item) :=
      (content.poweredL1_sub_eq_l1Distance
        (fun item => leftFirst item * rightFirst item)
        (fun item => leftSecond item * rightSecond item)).symm
    _ = content.poweredL1 (fun item =>
          (leftFirst item - leftSecond item) * rightFirst item +
            leftSecond item *
              (rightFirst item - rightSecond item)) :=
      content.poweredL1_congr _ _ (fun item => by ring1)
    _ ≤ content.poweredL1 (fun item =>
          (leftFirst item - leftSecond item) * rightFirst item) +
        content.poweredL1 (fun item =>
          leftSecond item * (rightFirst item - rightSecond item)) :=
      content.poweredL1_add_le _ _
    _ ≤ content.essentialMaximumMagnitude rightFirst *
          content.poweredL1 (fun item =>
            leftFirst item - leftSecond item) +
        content.essentialMaximumMagnitude leftSecond *
          content.poweredL1 (fun item =>
            rightFirst item - rightSecond item) :=
      add_le_add
        (content.poweredL1_mul_le_essentialMaximum_right _ rightFirst)
        (content.poweredL1_mul_le_essentialMaximum_left leftSecond _)
    _ = content.essentialMaximumMagnitude rightFirst *
          content.l1Distance leftFirst leftSecond +
        content.essentialMaximumMagnitude leftSecond *
          content.l1Distance rightFirst rightSecond := by
      rw [content.poweredL1_sub_eq_l1Distance,
        content.poweredL1_sub_eq_l1Distance]

/-- Multiplication by the same right observable scales integrated distance by at most its essential maximum magnitude.
-/
theorem l1Distance_mul_right_le {α : Type} (content : Content α)
    (leftFirst leftSecond right : α → Fraction.Rational) :
    content.l1Distance
        (fun item => leftFirst item * right item)
        (fun item => leftSecond item * right item) ≤
      content.essentialMaximumMagnitude right *
        content.l1Distance leftFirst leftSecond := by
  have bound := content.l1Distance_mul_le
    leftFirst leftSecond right right
  rw [content.l1Distance_refl, mul_zero, add_zero] at bound
  exact bound

/-- Multiplication by the same left observable scales integrated distance by at most its essential maximum magnitude. -/
theorem l1Distance_mul_left_le {α : Type} (content : Content α)
    (left rightFirst rightSecond : α → Fraction.Rational) :
    content.l1Distance
        (fun item => left item * rightFirst item)
        (fun item => left item * rightSecond item) ≤
      content.essentialMaximumMagnitude left *
        content.l1Distance rightFirst rightSecond := by
  have bound := content.l1Distance_mul_le
    left left rightFirst rightSecond
  rw [content.l1Distance_refl, mul_zero, zero_add] at bound
  exact bound

/-- Every powered magnitude integral is bounded by total mass times the same power of essential maximum magnitude. -/
theorem poweredLp_le_essentialMaximum {α : Type}
    (content : Content α) (exponent : Nat)
    (value : α → Fraction.Rational) :
    content.poweredLp exponent value ≤
      content.total * content.essentialMaximumMagnitude value ^ exponent :=
  content.poweredLp_le_of_essentialBound exponent value
    (content.essentialMaximumMagnitude value)
    (content.essentiallyBoundedBy_essentialMaximumMagnitude value)

/-- Every powered distance integral is bounded by total mass times the same power of essential maximum distance. -/
theorem poweredLpDistance_le_essentialMaximumDistance {α : Type}
    (content : Content α) (exponent : Nat)
    (left right : α → Fraction.Rational) :
    content.poweredLpDistance exponent left right ≤
      content.total *
        content.essentialMaximumDistance left right ^ exponent := by
  have bound := content.poweredLp_le_essentialMaximum exponent
    (fun item => left item - right item)
  rw [content.poweredLp_sub_eq_poweredLpDistance exponent left right]
    at bound
  exact bound

/-- Integrated distance is bounded by total mass times essential maximum distance. -/
theorem l1Distance_le_total_mul_essentialMaximumDistance {α : Type}
    (content : Content α) (left right : α → Fraction.Rational) :
    content.l1Distance left right ≤
      content.total * content.essentialMaximumDistance left right := by
  have bound := content.poweredLpDistance_le_essentialMaximumDistance
    1 left right
  rw [content.poweredLpDistance_one, pow_one] at bound
  exact bound

/-- The separation of two integrals is bounded by total mass times their observables' essential maximum distance. -/
theorem integral_separation_le_total_mul_essentialMaximumDistance {α : Type}
    (content : Content α) (left right : α → Fraction.Rational) :
    Distance.rationalSeparation (content.integral left) (content.integral right) ≤
      content.total * content.essentialMaximumDistance left right :=
  (content.integral_separation_le_l1Distance left right).trans
    (content.l1Distance_le_total_mul_essentialMaximumDistance left right)

/-- Squared integrated distance is bounded by total mass times squared essential maximum distance. -/
theorem poweredL2Distance_le_total_mul_essentialMaximumDistance_sq
    {α : Type} (content : Content α)
    (left right : α → Fraction.Rational) :
    content.poweredL2Distance left right ≤
      content.total * content.essentialMaximumDistance left right ^ 2 := by
  have bound := content.poweredLpDistance_le_essentialMaximumDistance
    2 left right
  rw [content.poweredLpDistance_two] at bound
  exact bound

end

end Content

end Purelib.Measure

end
