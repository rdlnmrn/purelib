module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
import Purelib.Measure.Content.Basic
import Purelib.Measure.Content.Integral
import Purelib.Measure.Content.Operations
import Purelib.Measure.Distribution.Basic
import Purelib.Data.List.Event
public import Purelib.Measure.Content.Lp.Natural
import Purelib.Measure.Content.Lp.L2
import Purelib.Measure.Content.Lp.L1
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Measure.Weighted.Integral

section
/-!
# Powered Lp under finite restriction and conditioning

Restricting a displayed finite content multiplies the powered integrand by
an executable indicator and therefore cannot increase a nonnegative powered
quantity.  Normalized conditioning evaluates the same powered integrands by
the existing rational conditional mean.
-/

@[expose] public section

namespace Purelib.Measure

namespace Content

section
open Purelib
open Purelib.Data.Rat
/-- Powered integration on the event restriction equals original integration of its indicator times the powered
magnitude. -/
theorem restrict_poweredLp {α : Type} (content : Measure.Content α)
    (event : α → Bool) (exponent : Nat) (value : α → Fraction.Rational) :
    (content.restrict event).poweredLp exponent value =
      content.integral (fun item => Distribution.indicator event item *
        Distance.rationalSeparation (value item) 0 ^ exponent) := by
  change (content.restrict event).integral (fun item =>
      Distance.rationalSeparation (value item) 0 ^ exponent) = _
  exact content.restrict_integral event _

/-- Powered distance on the event restriction equals original integration of its indicator times powered separation. -/
theorem restrict_poweredLpDistance {α : Type}
    (content : Measure.Content α) (event : α → Bool)
    (exponent : Nat) (left right : α → Fraction.Rational) :
    (content.restrict event).poweredLpDistance exponent left right =
      content.integral (fun item => Distribution.indicator event item *
        Distance.rationalSeparation (left item) (right item) ^ exponent) := by
  change (content.restrict event).integral (fun item =>
      Distance.rationalSeparation (left item) (right item) ^ exponent) = _
  exact content.restrict_integral event _

/-- Restricting content to an event cannot increase a natural-powered magnitude integral. -/
theorem restrict_poweredLp_le {α : Type} (content : Measure.Content α)
    (event : α → Bool) (exponent : Nat) (value : α → Fraction.Rational) :
    (content.restrict event).poweredLp exponent value ≤
      content.poweredLp exponent value := by
  rw [content.restrict_poweredLp]
  apply content.integral_mono
  intro atom member
  cases selected : event atom.item
  · simp only [Distribution.indicator, selected, zero_mul]
    exact Fraction.Order.Arithmetic.pow_nonneg_direct
      (Distance.rationalSeparation_nonneg _ _) exponent
  · simp only [Distribution.indicator, selected, one_mul]
    exact le_rfl

/-- Restricting content to an event cannot increase a natural-powered distance. -/
theorem restrict_poweredLpDistance_le {α : Type}
    (content : Measure.Content α) (event : α → Bool)
    (exponent : Nat) (left right : α → Fraction.Rational) :
    (content.restrict event).poweredLpDistance exponent left right ≤
      content.poweredLpDistance exponent left right := by
  rw [content.restrict_poweredLpDistance]
  apply content.integral_mono
  intro atom member
  cases selected : event atom.item
  · simp only [Distribution.indicator, selected, zero_mul]
    exact Fraction.Order.Arithmetic.pow_nonneg_direct
      (Distance.rationalSeparation_nonneg _ _) exponent
  · simp only [Distribution.indicator, selected, one_mul]
    exact le_rfl

/-- Restricting content to an event cannot increase the magnitude integral. -/
theorem restrict_poweredL1_le {α : Type} (content : Measure.Content α)
    (event : α → Bool) (value : α → Fraction.Rational) :
    (content.restrict event).poweredL1 value ≤ content.poweredL1 value := by
  have bound := content.restrict_poweredLp_le event 1 value
  rw [(content.restrict event).poweredLp_one,
    content.poweredLp_one] at bound
  exact bound

/-- Restricting content to an event cannot increase integrated separation. -/
theorem restrict_l1Distance_le {α : Type} (content : Measure.Content α)
    (event : α → Bool) (left right : α → Fraction.Rational) :
    (content.restrict event).l1Distance left right ≤
      content.l1Distance left right := by
  have bound := content.restrict_poweredLpDistance_le event 1 left right
  rw [(content.restrict event).poweredLpDistance_one,
    content.poweredLpDistance_one] at bound
  exact bound

/-- Restricting content to an event cannot increase the square integral. -/
theorem restrict_poweredL2_le {α : Type} (content : Measure.Content α)
    (event : α → Bool) (value : α → Fraction.Rational) :
    (content.restrict event).poweredL2 value ≤ content.poweredL2 value := by
  have bound := content.restrict_poweredLp_le event 2 value
  rw [(content.restrict event).poweredLp_two,
    content.poweredLp_two] at bound
  exact bound

/-- Restricting content to an event cannot increase squared integrated distance. -/
theorem restrict_poweredL2Distance_le {α : Type}
    (content : Measure.Content α) (event : α → Bool)
    (left right : α → Fraction.Rational) :
    (content.restrict event).poweredL2Distance left right ≤
      content.poweredL2Distance left right := by
  have bound := content.restrict_poweredLpDistance_le event 2 left right
  rw [(content.restrict event).poweredLpDistance_two,
    content.poweredLpDistance_two] at bound
  exact bound

end

end Content

namespace Distribution
end Distribution

end Purelib.Measure

end
