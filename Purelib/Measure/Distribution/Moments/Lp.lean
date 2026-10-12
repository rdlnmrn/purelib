module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Expectation
public import Purelib.Measure.Distribution.Lp.AlmostEverywhere
import Purelib.Measure.Distribution.Lp.L2
public import Purelib.Measure.Distribution.Moments.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

@[expose] public section

/-!
# Variance as finite powered-L2 distance

Variance is exactly the rational powered-L2 distance from a displayed
observable to its rational mean.  This identifies its zero set and relates
the moment and finite-almost-everywhere APIs without constructing an `L2`
completion.
-/

namespace Purelib.Measure

namespace Distribution

open Purelib.Data.Rat
/-- Variance around a supplied center is exactly the powered-L2 distance to that constant observable. -/
theorem varianceAround_eq_poweredL2Distance_constant {α : Type}
    (distribution : Distribution α) (value : α → Fraction.Rational)
    (center : Fraction.Rational) :
    distribution.varianceAround value center =
      distribution.poweredL2Distance value (fun _ => center) := rfl

/-- Variance is exactly the powered-L2 distance to the original expectation constant. -/
theorem variance_eq_poweredL2Distance_expectation {α : Type}
    (distribution : Distribution α) (value : α → Fraction.Rational) :
    distribution.variance value =
      distribution.poweredL2Distance value
        (fun _ => distribution.expectation value) := rfl

/-- The original variance is at most the original second moment. -/
theorem variance_le_poweredL2 {α : Type}
    (distribution : Distribution α) (value : α → Fraction.Rational) :
    distribution.variance value ≤ distribution.poweredL2 value := by
  change distribution.variance value ≤
    distribution.expectation (fun item => value item ^ 2)
  exact distribution.variance_le_secondMoment value

/-- Variance vanishes exactly when the observable equals its original mean almost everywhere for the retained
distribution. -/
theorem variance_eq_zero_iff_equalAlmostEverywhere_expectation {α : Type}
    (distribution : Distribution α) (value : α → Fraction.Rational) :
    distribution.variance value = 0 ↔
      distribution.EqualAlmostEverywhere value
        (fun _ => distribution.expectation value) := by
  constructor
  · intro zero
    exact (distribution.poweredL2Distance_eq_zero_iff _ _).mp
      ((distribution.variance_eq_poweredL2Distance_expectation value).symm.trans zero)
  · intro equal
    exact (distribution.variance_eq_poweredL2Distance_expectation value).trans
      ((distribution.poweredL2Distance_eq_zero_iff _ _).mpr equal)

end Distribution

end Purelib.Measure
