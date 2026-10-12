module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Distance.Basic
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Expectation
import Purelib.Measure.Distribution.Kernel.Basic
import Purelib.Data.List.Event
import Purelib.Measure.Distribution.Lp.L2
public import Purelib.Measure.Distribution.Lp.Natural
import Purelib.Measure.Distribution.Lp.L1

@[expose] public section

/-!
# Powered Lp quantities through explicit finite kernels

Finite bind evaluates natural-powered magnitudes and distances by averaging
the corresponding quantities in each displayed transition table.  These are
exact rational tower identities over finite lists, with no function-space
completion or limiting construction.
-/

namespace Purelib.Measure

namespace Distribution

section
open Purelib
open Purelib.Data.Rat
/-- Powered-Lp magnitude after the exact kernel bind is the original expectation of transition powered-Lp magnitudes. -/
theorem bind_poweredLp {α β : Type}
    (source : Measure.Distribution α) (transition : α → Measure.Distribution β)
    (exponent : Nat) (value : β → Fraction.Rational) :
    (source.bind transition).poweredLp exponent value =
      source.expectation (fun item =>
        (transition item).poweredLp exponent value) := by
  change (source.bind transition).expectation (fun result =>
      Distance.rationalSeparation (value result) 0 ^ exponent) =
    source.expectation (fun item =>
      (transition item).expectation (fun result =>
        Distance.rationalSeparation (value result) 0 ^ exponent))
  exact source.bind_expectation transition _

/-- Powered-Lp distance after the exact kernel bind is the original expectation of transition powered-Lp distances. -/
theorem bind_poweredLpDistance {α β : Type}
    (source : Measure.Distribution α) (transition : α → Measure.Distribution β)
    (exponent : Nat) (left right : β → Fraction.Rational) :
    (source.bind transition).poweredLpDistance exponent left right =
      source.expectation (fun item =>
        (transition item).poweredLpDistance exponent left right) := by
  change (source.bind transition).expectation (fun result =>
      Distance.rationalSeparation (left result) (right result) ^ exponent) =
    source.expectation (fun item =>
      (transition item).expectation (fun result =>
        Distance.rationalSeparation (left result) (right result) ^ exponent))
  exact source.bind_expectation transition _

/-- L1 magnitude after the exact kernel bind is the original expectation of transition L1 magnitudes. -/
theorem bind_poweredL1 {α β : Type}
    (source : Measure.Distribution α) (transition : α → Measure.Distribution β)
    (value : β → Fraction.Rational) :
    (source.bind transition).poweredL1 value =
      source.expectation (fun item => (transition item).poweredL1 value) := by
  calc
    (source.bind transition).poweredL1 value =
        (source.bind transition).poweredLp 1 value :=
      ((source.bind transition).poweredLp_one value).symm
    _ = source.expectation (fun item =>
        (transition item).poweredLp 1 value) :=
      source.bind_poweredLp transition 1 value
    _ = source.expectation (fun item =>
        (transition item).poweredL1 value) :=
      source.expectation_congr _ _ (fun item =>
        (transition item).poweredLp_one value)

/-- L1 distance after the exact kernel bind is the original expectation of transition L1 distances. -/
theorem bind_l1Distance {α β : Type}
    (source : Measure.Distribution α) (transition : α → Measure.Distribution β)
    (left right : β → Fraction.Rational) :
    (source.bind transition).l1Distance left right =
      source.expectation (fun item =>
        (transition item).l1Distance left right) := by
  calc
    (source.bind transition).l1Distance left right =
        (source.bind transition).poweredLpDistance 1 left right :=
      ((source.bind transition).poweredLpDistance_one left right).symm
    _ = source.expectation (fun item =>
        (transition item).poweredLpDistance 1 left right) :=
      source.bind_poweredLpDistance transition 1 left right
    _ = source.expectation (fun item =>
        (transition item).l1Distance left right) :=
      source.expectation_congr _ _ (fun item =>
        (transition item).poweredLpDistance_one left right)

/-- Second moment after the exact kernel bind is the original expectation of transition second moments. -/
theorem bind_poweredL2 {α β : Type}
    (source : Measure.Distribution α) (transition : α → Measure.Distribution β)
    (value : β → Fraction.Rational) :
    (source.bind transition).poweredL2 value =
      source.expectation (fun item => (transition item).poweredL2 value) := by
  calc
    (source.bind transition).poweredL2 value =
        (source.bind transition).poweredLp 2 value :=
      ((source.bind transition).poweredLp_two value).symm
    _ = source.expectation (fun item =>
        (transition item).poweredLp 2 value) :=
      source.bind_poweredLp transition 2 value
    _ = source.expectation (fun item =>
        (transition item).poweredL2 value) :=
      source.expectation_congr _ _ (fun item =>
        (transition item).poweredLp_two value)

/-- Squared-L2 distance after the exact kernel bind is the original expectation of transition squared-L2 distances. -/
theorem bind_poweredL2Distance {α β : Type}
    (source : Measure.Distribution α) (transition : α → Measure.Distribution β)
    (left right : β → Fraction.Rational) :
    (source.bind transition).poweredL2Distance left right =
      source.expectation (fun item =>
        (transition item).poweredL2Distance left right) := by
  calc
    (source.bind transition).poweredL2Distance left right =
        (source.bind transition).poweredLpDistance 2 left right :=
      ((source.bind transition).poweredLpDistance_two left right).symm
    _ = source.expectation (fun item =>
        (transition item).poweredLpDistance 2 left right) :=
      source.bind_poweredLpDistance transition 2 left right
    _ = source.expectation (fun item =>
        (transition item).poweredL2Distance left right) :=
      source.expectation_congr _ _ (fun item =>
        (transition item).poweredLpDistance_two left right)

end

end Distribution

end Purelib.Measure
