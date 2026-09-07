import FiniteMeasure.Mixture
import FiniteMeasure.NaturalLp

/-!
# Powered Lp quantities of explicit finite mixtures

Natural-powered magnitudes and distances are expectations of explicit
rational observables, so a displayed two-way mixture evaluates them as the
same rational convex combination of the component quantities.
-/

namespace FiniteMeasure

namespace Distribution

theorem mixture_poweredLp {α : Type}
    (left right : Distribution α) (weight : MixingWeight)
    (exponent : Nat) (value : α → Coordinate) :
    (left.mixture right weight).poweredLp exponent value =
      weight.coefficient * left.poweredLp exponent value +
        weight.complement * right.poweredLp exponent value := by
  change (left.mixture right weight).expectation (fun item =>
      rationalSeparation (value item) 0 ^ exponent) = _
  exact left.mixture_expectation right weight _

theorem mixture_poweredLpDistance {α : Type}
    (left right : Distribution α) (weight : MixingWeight)
    (exponent : Nat) (first second : α → Coordinate) :
    (left.mixture right weight).poweredLpDistance exponent first second =
      weight.coefficient * left.poweredLpDistance exponent first second +
        weight.complement *
          right.poweredLpDistance exponent first second := by
  change (left.mixture right weight).expectation (fun item =>
      rationalSeparation (first item) (second item) ^ exponent) = _
  exact left.mixture_expectation right weight _

theorem mixture_poweredL1 {α : Type}
    (left right : Distribution α) (weight : MixingWeight)
    (value : α → Coordinate) :
    (left.mixture right weight).poweredL1 value =
      weight.coefficient * left.poweredL1 value +
        weight.complement * right.poweredL1 value := by
  have identity := left.mixture_poweredLp right weight 1 value
  rw [(left.mixture right weight).poweredLp_one,
    left.poweredLp_one, right.poweredLp_one] at identity
  exact identity

theorem mixture_l1Distance {α : Type}
    (left right : Distribution α) (weight : MixingWeight)
    (first second : α → Coordinate) :
    (left.mixture right weight).l1Distance first second =
      weight.coefficient * left.l1Distance first second +
        weight.complement * right.l1Distance first second := by
  have identity := left.mixture_poweredLpDistance right weight 1 first second
  rw [(left.mixture right weight).poweredLpDistance_one,
    left.poweredLpDistance_one, right.poweredLpDistance_one] at identity
  exact identity

theorem mixture_poweredL2 {α : Type}
    (left right : Distribution α) (weight : MixingWeight)
    (value : α → Coordinate) :
    (left.mixture right weight).poweredL2 value =
      weight.coefficient * left.poweredL2 value +
        weight.complement * right.poweredL2 value := by
  have identity := left.mixture_poweredLp right weight 2 value
  rw [(left.mixture right weight).poweredLp_two,
    left.poweredLp_two, right.poweredLp_two] at identity
  exact identity

theorem mixture_poweredL2Distance {α : Type}
    (left right : Distribution α) (weight : MixingWeight)
    (first second : α → Coordinate) :
    (left.mixture right weight).poweredL2Distance first second =
      weight.coefficient * left.poweredL2Distance first second +
        weight.complement *
          right.poweredL2Distance first second := by
  have identity := left.mixture_poweredLpDistance right weight 2 first second
  rw [(left.mixture right weight).poweredLpDistance_two,
    left.poweredLpDistance_two, right.poweredLpDistance_two] at identity
  exact identity

end Distribution

end FiniteMeasure
