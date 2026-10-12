module
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Distribution.Kernel.Basic
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Distance.Power
import Purelib.Data.Rat.Fraction

import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Measure.Distribution.Basic
import Purelib.Data.List.Event
import Purelib.Measure.Distribution.Lp.L2
public import Purelib.Measure.Distribution.Lp.Natural
import Purelib.Measure.Distribution.Lp.L1
import Purelib.Measure.Distribution.Expectation
import Purelib.Data.Rat.Fraction.Arithmetic

section
/-!
# Lp quantities of one-point finite distributions

The one-point distribution is the base constructor for finite bind and
sampling.  All powered and essential-maximum quantities reduce exactly to
the displayed rational value at that point.
-/

@[expose] public section

namespace Purelib.Measure

namespace Distribution

open Purelib.Data.Rat
/-- A pure distribution's powered magnitude expectation is the matching power of its sole observable magnitude. -/
@[simp] theorem pure_poweredLp {α : Type} (item : α)
    (exponent : Nat) (value : α → Fraction.Rational) :
    (Distribution.pure item).poweredLp exponent value =
      Distance.rationalSeparation (value item) 0 ^ exponent := by
  change (Distribution.pure item).expectation (fun point =>
    Distance.rationalSeparation (value point) 0 ^ exponent) = _
  rw [Distribution.pure_expectation]

/-- A pure distribution's powered distance expectation is the matching power of its sole observable separation. -/
@[simp] theorem pure_poweredLpDistance {α : Type} (item : α)
    (exponent : Nat) (left right : α → Fraction.Rational) :
    (Distribution.pure item).poweredLpDistance exponent left right =
      Distance.rationalSeparation (left item) (right item) ^ exponent := by
  change (Distribution.pure item).expectation (fun point =>
    Distance.rationalSeparation (left point) (right point) ^ exponent) = _
  rw [Distribution.pure_expectation]

/-- A pure distribution's magnitude expectation is the observable magnitude at its sole payload. -/
@[simp] theorem pure_poweredL1 {α : Type} (item : α)
    (value : α → Fraction.Rational) :
    (Distribution.pure item).poweredL1 value =
      Distance.rationalSeparation (value item) 0 := by
  rw [← (Distribution.pure item).poweredLp_one value,
    Distribution.pure_poweredLp, pow_one]

/-- A pure distribution's integrated distance is the observable separation at its sole payload. -/
@[simp] theorem pure_l1Distance {α : Type} (item : α)
    (left right : α → Fraction.Rational) :
    (Distribution.pure item).l1Distance left right =
      Distance.rationalSeparation (left item) (right item) := by
  rw [← (Distribution.pure item).poweredLpDistance_one left right,
    Distribution.pure_poweredLpDistance, pow_one]

/-- A pure distribution's squared-observable expectation is its sole observable value squared. -/
@[simp] theorem pure_poweredL2 {α : Type} (item : α)
    (value : α → Fraction.Rational) :
    (Distribution.pure item).poweredL2 value = value item ^ 2 := by
  rw [← (Distribution.pure item).poweredLp_two value,
    Distribution.pure_poweredLp, Distance.NaturalLp.rationalSeparation_sq]
  ring1

/-- A pure distribution's squared-distance expectation is its sole observable difference squared. -/
@[simp] theorem pure_poweredL2Distance {α : Type} (item : α)
    (left right : α → Fraction.Rational) :
    (Distribution.pure item).poweredL2Distance left right =
      (left item - right item) ^ 2 := by
  rw [← (Distribution.pure item).poweredLpDistance_two left right,
    Distribution.pure_poweredLpDistance, Distance.NaturalLp.rationalSeparation_sq]
end Distribution

end Purelib.Measure

end
