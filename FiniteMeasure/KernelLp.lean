import FiniteMeasure.NaturalLp
import FiniteMeasure.Stochastic

/-!
# Powered Lp quantities through explicit finite kernels

Finite bind evaluates natural-powered magnitudes and distances by averaging
the corresponding quantities in each displayed transition table.  These are
exact rational tower identities over finite lists, with no function-space
completion or limiting construction.
-/

namespace FiniteMeasure

namespace Distribution

/-- Exact finite tower law for natural-powered magnitudes. -/
theorem bind_poweredLp {α β : Type}
    (source : Distribution α) (transition : α → Distribution β)
    (exponent : Nat) (value : β → Coordinate) :
    (source.bind transition).poweredLp exponent value =
      source.expectation (fun item =>
        (transition item).poweredLp exponent value) := by
  change (source.bind transition).expectation (fun result =>
      rationalSeparation (value result) 0 ^ exponent) =
    source.expectation (fun item =>
      (transition item).expectation (fun result =>
        rationalSeparation (value result) 0 ^ exponent))
  exact source.bind_expectation transition _

/-- Exact finite tower law for natural-powered distances. -/
theorem bind_poweredLpDistance {α β : Type}
    (source : Distribution α) (transition : α → Distribution β)
    (exponent : Nat) (left right : β → Coordinate) :
    (source.bind transition).poweredLpDistance exponent left right =
      source.expectation (fun item =>
        (transition item).poweredLpDistance exponent left right) := by
  change (source.bind transition).expectation (fun result =>
      rationalSeparation (left result) (right result) ^ exponent) =
    source.expectation (fun item =>
      (transition item).expectation (fun result =>
        rationalSeparation (left result) (right result) ^ exponent))
  exact source.bind_expectation transition _

theorem bind_poweredL1 {α β : Type}
    (source : Distribution α) (transition : α → Distribution β)
    (value : β → Coordinate) :
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

theorem bind_l1Distance {α β : Type}
    (source : Distribution α) (transition : α → Distribution β)
    (left right : β → Coordinate) :
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

theorem bind_poweredL2 {α β : Type}
    (source : Distribution α) (transition : α → Distribution β)
    (value : β → Coordinate) :
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

theorem bind_poweredL2Distance {α β : Type}
    (source : Distribution α) (transition : α → Distribution β)
    (left right : β → Coordinate) :
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

end Distribution

end FiniteMeasure
