module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
public import Purelib.Data.Rat.Interval.Basic
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Event.RationalDistance
public import Purelib.Measure.Distribution.Lp.Natural
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic

section
@[expose] public section

/-!
# Finite tail bounds from CCL prefix moments

A CCL-derived enclosure of a natural-powered probe moment gives an explicit
Markov bound for the finite probability that the probe magnitude crosses a
positive rational threshold.  Progressive requests additionally make the
displayed moment upper endpoint arbitrarily close to every explicitly
supplied realization family's exact powered moment.
-/

namespace Purelib.Measure.Distribution

open Purelib
open Purelib.Data.Rat
/-- An interval enclosing powered distance expectation bounds the positive-threshold separation tail by its upper
endpoint divided by that threshold's power. -/
public theorem tailProbability_le_upper_div_of_poweredLpDistance_mem
    {α : Type} (distribution : Measure.Distribution α)
    (bound : Data.Rat.Interval)
    (exponent : Nat) (threshold : Fraction.Rational)
    (thresholdPositive : 0 < threshold) (left right : α → Fraction.Rational)
    (inside : bound.Contains
      (distribution.poweredLpDistance exponent left right)) :
    distribution.probability
        (Measure.separationAtLeast threshold left right) ≤
      bound.upper / threshold ^ exponent := by
  have markov :=
    distribution.probability_separationAtLeast_le_poweredLpDistance
      exponent threshold thresholdPositive left right
  have denominatorPositive : 0 < threshold ^ exponent :=
    Fraction.Order.Arithmetic.pow_pos_direct thresholdPositive exponent
  have divided : distribution.poweredLpDistance exponent left right /
        threshold ^ exponent ≤
      bound.upper / threshold ^ exponent := by
    apply (Fraction.Order.Field.div_le_iff_pos denominatorPositive).2
    calc
      distribution.poweredLpDistance exponent left right ≤ bound.upper :=
        inside.2
      _ = (bound.upper / threshold ^ exponent) * threshold ^ exponent :=
        (Fraction.Field.div_mul_cancel_of_ne bound.upper
          (threshold ^ exponent) denominatorPositive.ne').symm
  exact markov.trans divided

/-- An interval enclosing powered magnitude expectation bounds the positive-threshold magnitude tail by its upper
endpoint divided by that threshold's power. -/
public theorem tailProbability_le_upper_div_of_poweredLp_mem
    {α : Type} (distribution : Measure.Distribution α)
    (bound : Data.Rat.Interval)
    (exponent : Nat) (threshold : Fraction.Rational)
    (thresholdPositive : 0 < threshold) (value : α → Fraction.Rational)
    (inside : bound.Contains (distribution.poweredLp exponent value)) :
    distribution.probability
        (Measure.separationAtLeast threshold value
          (fun _ => 0)) ≤
      bound.upper / threshold ^ exponent := by
  have markov :=
    distribution.probability_separationAtLeast_le_poweredLpDistance
      exponent threshold thresholdPositive value (fun _ => 0)
  have poweredDistance :
      distribution.poweredLpDistance exponent value (fun _ => 0) =
        distribution.poweredLp exponent value := rfl
  rw [poweredDistance] at markov
  have denominatorPositive : 0 < threshold ^ exponent :=
    Fraction.Order.Arithmetic.pow_pos_direct thresholdPositive exponent
  have divided : distribution.poweredLp exponent value /
        threshold ^ exponent ≤
      bound.upper / threshold ^ exponent := by
    apply (Fraction.Order.Field.div_le_iff_pos denominatorPositive).2
    calc
      distribution.poweredLp exponent value ≤ bound.upper := inside.2
      _ = (bound.upper / threshold ^ exponent) * threshold ^ exponent :=
        (Fraction.Field.div_mul_cancel_of_ne bound.upper
          (threshold ^ exponent) denominatorPositive.ne').symm
  exact markov.trans divided

end Purelib.Measure.Distribution

end
