module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Distance.Basic
public import Purelib.Measure.Distribution.Mixture.Basic
import Purelib.Measure.Distribution.Basic
import Purelib.Data.List.Event
import Purelib.Measure.Distribution.Lp.L2
public import Purelib.Measure.Distribution.Lp.Natural
import Purelib.Measure.Distribution.Lp.L1
import Purelib.Measure.Distribution.Expectation
import Purelib.Data.Rat.Fraction.Arithmetic

@[expose] public section

/-!
# Powered Lp quantities of explicit finite mixtures

Natural-powered magnitudes and distances are expectations of explicit
rational observables, so a displayed two-way mixture evaluates them as the
same rational convex combination of the component quantities.
-/

namespace Purelib.Measure

namespace Distribution

section
open Purelib
open Purelib.Data.Rat
/-- A mixture's natural-powered magnitude expectation is the retained weighted sum of the two original powered
expectations. -/
theorem mixture_poweredLp {α : Type}
    (left right : Measure.Distribution α) (weight : Measure.MixingWeight)
    (exponent : Nat) (value : α → Fraction.Rational) :
    (left.mixture right weight).poweredLp exponent value =
      weight.coefficient * left.poweredLp exponent value +
        weight.complement * right.poweredLp exponent value := by
  change (left.mixture right weight).expectation (fun item =>
      Distance.rationalSeparation (value item) 0 ^ exponent) = _
  exact left.mixture_expectation right weight _

/-- A mixture's natural-powered distance expectation is the retained weighted sum of the original powered distances. -/
theorem mixture_poweredLpDistance {α : Type}
    (left right : Measure.Distribution α) (weight : Measure.MixingWeight)
    (exponent : Nat) (first second : α → Fraction.Rational) :
    (left.mixture right weight).poweredLpDistance exponent first second =
      weight.coefficient * left.poweredLpDistance exponent first second +
        weight.complement *
          right.poweredLpDistance exponent first second := by
  change (left.mixture right weight).expectation (fun item =>
      Distance.rationalSeparation (first item) (second item) ^ exponent) = _
  exact left.mixture_expectation right weight _

/-- A mixture's magnitude expectation is the retained weighted sum of the original magnitude expectations. -/
theorem mixture_poweredL1 {α : Type}
    (left right : Measure.Distribution α) (weight : Measure.MixingWeight)
    (value : α → Fraction.Rational) :
    (left.mixture right weight).poweredL1 value =
      weight.coefficient * left.poweredL1 value +
        weight.complement * right.poweredL1 value := by
  have identity := left.mixture_poweredLp right weight 1 value
  rw [(left.mixture right weight).poweredLp_one,
    left.poweredLp_one, right.poweredLp_one] at identity
  exact identity

/-- A mixture's integrated distance is the retained weighted sum of the original integrated distances. -/
theorem mixture_l1Distance {α : Type}
    (left right : Measure.Distribution α) (weight : Measure.MixingWeight)
    (first second : α → Fraction.Rational) :
    (left.mixture right weight).l1Distance first second =
      weight.coefficient * left.l1Distance first second +
        weight.complement * right.l1Distance first second := by
  have identity := left.mixture_poweredLpDistance right weight 1 first second
  rw [(left.mixture right weight).poweredLpDistance_one,
    left.poweredLpDistance_one, right.poweredLpDistance_one] at identity
  exact identity

/-- A mixture's squared expectation is the retained weighted sum of the original squared expectations. -/
theorem mixture_poweredL2 {α : Type}
    (left right : Measure.Distribution α) (weight : Measure.MixingWeight)
    (value : α → Fraction.Rational) :
    (left.mixture right weight).poweredL2 value =
      weight.coefficient * left.poweredL2 value +
        weight.complement * right.poweredL2 value := by
  have identity := left.mixture_poweredLp right weight 2 value
  rw [(left.mixture right weight).poweredLp_two,
    left.poweredLp_two, right.poweredLp_two] at identity
  exact identity

/-- A mixture's squared-distance expectation is the retained weighted sum of the original squared distances. -/
theorem mixture_poweredL2Distance {α : Type}
    (left right : Measure.Distribution α) (weight : Measure.MixingWeight)
    (first second : α → Fraction.Rational) :
    (left.mixture right weight).poweredL2Distance first second =
      weight.coefficient * left.poweredL2Distance first second +
        weight.complement *
          right.poweredL2Distance first second := by
  have identity := left.mixture_poweredLpDistance right weight 2 first second
  rw [(left.mixture right weight).poweredLpDistance_two,
    left.poweredLpDistance_two, right.poweredLpDistance_two] at identity
  exact identity

end

end Distribution

end Purelib.Measure
