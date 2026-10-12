module
import Purelib.Data.Rat.Distance.Power
import Purelib.Data.Rat.Fraction

import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Content.Basic
import Purelib.Data.List.Event
import Purelib.Measure.Distribution.Lp.L2
public import Purelib.Measure.Distribution.Lp.Natural
import Purelib.Measure.Distribution.Lp.L1
import Purelib.Measure.Distribution.Expectation
public import Purelib.Measure.Distribution.Conditioning.Mean
import Purelib.Measure.Distribution.Conditioning.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

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
end Content

namespace Distribution

section
open Purelib
open Purelib.Data.Rat
/-- A conditioned natural-powered magnitude expectation equals the original conditional mean of that magnitude power. -/
theorem conditioned_poweredLp_eq_conditionalMean {α : Type}
    (distribution : Measure.Distribution α) (event : α → Bool)
    (positive : 0 < distribution.probability event)
    (exponent : Nat) (value : α → Fraction.Rational) :
    (distribution.conditioned event positive).poweredLp exponent value =
      distribution.conditionalMean event (fun item =>
        Distance.rationalSeparation (value item) 0 ^ exponent) := by
  change (distribution.conditioned event positive).expectation (fun item =>
      Distance.rationalSeparation (value item) 0 ^ exponent) = _
  exact distribution.conditioned_expectation_eq_conditionalMean
    event positive _

/-- A conditioned natural-powered distance expectation equals the original conditional mean of that separation power. -/
theorem conditioned_poweredLpDistance_eq_conditionalMean {α : Type}
    (distribution : Measure.Distribution α) (event : α → Bool)
    (positive : 0 < distribution.probability event)
    (exponent : Nat) (left right : α → Fraction.Rational) :
    (distribution.conditioned event positive).poweredLpDistance
        exponent left right =
      distribution.conditionalMean event (fun item =>
        Distance.rationalSeparation (left item) (right item) ^ exponent) := by
  change (distribution.conditioned event positive).expectation (fun item =>
      Distance.rationalSeparation (left item) (right item) ^ exponent) = _
  exact distribution.conditioned_expectation_eq_conditionalMean
    event positive _

/-- A conditioned magnitude expectation equals the original conditional magnitude mean. -/
theorem conditioned_poweredL1_eq_conditionalMean {α : Type}
    (distribution : Measure.Distribution α) (event : α → Bool)
    (positive : 0 < distribution.probability event)
    (value : α → Fraction.Rational) :
    (distribution.conditioned event positive).poweredL1 value =
      distribution.conditionalMean event (fun item =>
        Distance.rationalSeparation (value item) 0) := by
  have identity := distribution.conditioned_poweredLp_eq_conditionalMean
    event positive 1 value
  rw [(distribution.conditioned event positive).poweredLp_one] at identity
  calc
    (distribution.conditioned event positive).poweredL1 value =
        distribution.conditionalMean event (fun item =>
          Distance.rationalSeparation (value item) 0 ^ 1) := identity
    _ = distribution.conditionalMean event (fun item =>
          Distance.rationalSeparation (value item) 0) :=
      distribution.conditionalMean_congr event _ _ (fun item => pow_one _)

/-- Conditioned integrated distance equals the original conditional separation mean. -/
theorem conditioned_l1Distance_eq_conditionalMean {α : Type}
    (distribution : Measure.Distribution α) (event : α → Bool)
    (positive : 0 < distribution.probability event)
    (left right : α → Fraction.Rational) :
    (distribution.conditioned event positive).l1Distance left right =
      distribution.conditionalMean event (fun item =>
        Distance.rationalSeparation (left item) (right item)) := by
  have identity :=
    distribution.conditioned_poweredLpDistance_eq_conditionalMean
      event positive 1 left right
  rw [(distribution.conditioned event positive).poweredLpDistance_one]
    at identity
  calc
    (distribution.conditioned event positive).l1Distance left right =
        distribution.conditionalMean event (fun item =>
          Distance.rationalSeparation (left item) (right item) ^ 1) := identity
    _ = distribution.conditionalMean event (fun item =>
          Distance.rationalSeparation (left item) (right item)) :=
      distribution.conditionalMean_congr event _ _ (fun item => pow_one _)

/-- A conditioned squared-observable expectation equals the original conditional square mean. -/
theorem conditioned_poweredL2_eq_conditionalMean {α : Type}
    (distribution : Measure.Distribution α) (event : α → Bool)
    (positive : 0 < distribution.probability event)
    (value : α → Fraction.Rational) :
    (distribution.conditioned event positive).poweredL2 value =
      distribution.conditionalMean event (fun item => value item ^ 2) := by
  have identity := distribution.conditioned_poweredLp_eq_conditionalMean
    event positive 2 value
  rw [(distribution.conditioned event positive).poweredLp_two] at identity
  calc
    (distribution.conditioned event positive).poweredL2 value =
        distribution.conditionalMean event (fun item =>
          Distance.rationalSeparation (value item) 0 ^ 2) := identity
    _ = distribution.conditionalMean event (fun item => value item ^ 2) :=
      distribution.conditionalMean_congr event _ _ (fun item => by
        exact (Distance.NaturalLp.rationalSeparation_sq (value item) 0).trans
          (congrArg (fun base : Fraction.Rational => base ^ 2)
            (show value item - 0 = value item by
              change value item + 0 = value item
              exact (Fraction.Field.add_comm _ _).trans (Fraction.Field.zero_add _))))

/-- Conditioned squared-distance expectation equals the original conditional squared-difference mean. -/
theorem conditioned_poweredL2Distance_eq_conditionalMean {α : Type}
    (distribution : Measure.Distribution α) (event : α → Bool)
    (positive : 0 < distribution.probability event)
    (left right : α → Fraction.Rational) :
    (distribution.conditioned event positive).poweredL2Distance left right =
      distribution.conditionalMean event (fun item =>
        (left item - right item) ^ 2) := by
  have identity :=
    distribution.conditioned_poweredLpDistance_eq_conditionalMean
      event positive 2 left right
  rw [(distribution.conditioned event positive).poweredLpDistance_two]
    at identity
  calc
    (distribution.conditioned event positive).poweredL2Distance left right =
        distribution.conditionalMean event (fun item =>
          Distance.rationalSeparation (left item) (right item) ^ 2) := identity
    _ = distribution.conditionalMean event (fun item =>
          (left item - right item) ^ 2) :=
      distribution.conditionalMean_congr event _ _ (fun item =>
        Distance.NaturalLp.rationalSeparation_sq (left item) (right item))

end

end Distribution

end Purelib.Measure

end
