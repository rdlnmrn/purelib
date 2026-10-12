module
public import Purelib.Measure.Distribution.EssentialMaximum.Basic
import Purelib.Measure.Content.EssentialMaximum.Lp
import Purelib.Measure.Distribution.Lp.Natural
import Purelib.Measure.Distribution.Lp.L2
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Distance.Basic
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Content.Basic
import Purelib.Measure.Distribution.Content
import Purelib.Measure.Distribution.Lp.L1
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Measure.Distribution.Expectation
import Purelib.Data.Rat.Fraction.Field
import Mathlib.Order.Basic

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

namespace Distribution

section
open Purelib.Data.Rat
/-- The product's magnitude expectation is bounded by the right essential maximum times the left magnitude expectation.
-/
theorem poweredL1_mul_le_essentialMaximum_right {α : Type}
    (distribution : Distribution α) (left right : α → Fraction.Rational) :
    distribution.poweredL1 (fun item => left item * right item) ≤
      distribution.essentialMaximumMagnitude right *
        distribution.poweredL1 left :=
  distribution.toContent
    |>.poweredL1_mul_le_essentialMaximum_right left right

/-- The product's magnitude expectation is bounded by the left essential maximum times the right magnitude expectation.
-/
theorem poweredL1_mul_le_essentialMaximum_left {α : Type}
    (distribution : Distribution α) (left right : α → Fraction.Rational) :
    distribution.poweredL1 (fun item => left item * right item) ≤
      distribution.essentialMaximumMagnitude left *
        distribution.poweredL1 right :=
  distribution.toContent
    |>.poweredL1_mul_le_essentialMaximum_left left right

/-- Bound the distance between two products by their factor distances weighted by opposite-factor essential maxima.

The retained coefficients are the first product's right-factor maximum and the second product's left-factor maximum. -/
theorem l1Distance_mul_le {α : Type} (distribution : Distribution α)
    (leftFirst leftSecond rightFirst rightSecond : α → Fraction.Rational) :
    distribution.l1Distance
        (fun item => leftFirst item * rightFirst item)
        (fun item => leftSecond item * rightSecond item) ≤
      distribution.essentialMaximumMagnitude rightFirst *
          distribution.l1Distance leftFirst leftSecond +
        distribution.essentialMaximumMagnitude leftSecond *
          distribution.l1Distance rightFirst rightSecond :=
  distribution.toContent
    |>.l1Distance_mul_le leftFirst leftSecond rightFirst rightSecond

/-- Multiplication by the same right observable scales integrated distance by at most its essential maximum magnitude.
-/
theorem l1Distance_mul_right_le {α : Type}
    (distribution : Distribution α)
    (leftFirst leftSecond right : α → Fraction.Rational) :
    distribution.l1Distance
        (fun item => leftFirst item * right item)
        (fun item => leftSecond item * right item) ≤
      distribution.essentialMaximumMagnitude right *
        distribution.l1Distance leftFirst leftSecond :=
  distribution.toContent
    |>.l1Distance_mul_right_le leftFirst leftSecond right

/-- Multiplication by the same left observable scales integrated distance by at most its essential maximum magnitude. -/
theorem l1Distance_mul_left_le {α : Type}
    (distribution : Distribution α)
    (left rightFirst rightSecond : α → Fraction.Rational) :
    distribution.l1Distance
        (fun item => left item * rightFirst item)
        (fun item => left item * rightSecond item) ≤
      distribution.essentialMaximumMagnitude left *
        distribution.l1Distance rightFirst rightSecond :=
  distribution.toContent
    |>.l1Distance_mul_left_le left rightFirst rightSecond

/-- Every natural-powered magnitude expectation is bounded by the matching power of the essential maximum magnitude. -/
theorem poweredLp_le_essentialMaximum {α : Type}
    (distribution : Distribution α) (exponent : Nat)
    (value : α → Fraction.Rational) :
    distribution.poweredLp exponent value ≤
      distribution.essentialMaximumMagnitude value ^ exponent := by
  have bound := distribution.toContent.poweredLp_le_essentialMaximum
    exponent value
  rw [distribution.toContent_total, one_mul] at bound
  exact bound

/-- Every natural-powered distance expectation is bounded by the matching power of the essential maximum distance. -/
theorem poweredLpDistance_le_essentialMaximumDistance {α : Type}
    (distribution : Distribution α) (exponent : Nat)
    (left right : α → Fraction.Rational) :
    distribution.poweredLpDistance exponent left right ≤
      distribution.essentialMaximumDistance left right ^ exponent := by
  have bound :=
    distribution.toContent.poweredLpDistance_le_essentialMaximumDistance
      exponent left right
  rw [distribution.toContent_total, one_mul] at bound
  exact bound

/-- Integrated distance is at most essential maximum distance under the same normalized law. -/
theorem l1Distance_le_essentialMaximumDistance {α : Type}
    (distribution : Distribution α) (left right : α → Fraction.Rational) :
    distribution.l1Distance left right ≤
      distribution.essentialMaximumDistance left right := by
  have bound := distribution.poweredLpDistance_le_essentialMaximumDistance
    1 left right
  rw [distribution.poweredLpDistance_one, pow_one] at bound
  exact bound

/-- The separation of the two expectations is at most their observables' essential maximum distance. -/
theorem expectation_separation_le_essentialMaximumDistance {α : Type}
    (distribution : Distribution α) (left right : α → Fraction.Rational) :
    Distance.rationalSeparation (distribution.expectation left)
        (distribution.expectation right) ≤
      distribution.essentialMaximumDistance left right :=
  (distribution.expectation_separation_le_l1Distance left right).trans
    (distribution.l1Distance_le_essentialMaximumDistance left right)

/-- Squared-distance expectation is at most squared essential maximum distance. -/
theorem poweredL2Distance_le_essentialMaximumDistance_sq {α : Type}
    (distribution : Distribution α) (left right : α → Fraction.Rational) :
    distribution.poweredL2Distance left right ≤
      distribution.essentialMaximumDistance left right ^ 2 := by
  have bound := distribution.poweredLpDistance_le_essentialMaximumDistance
    2 left right
  rw [distribution.poweredLpDistance_two] at bound
  exact bound

end

end Distribution

end Purelib.Measure

end
