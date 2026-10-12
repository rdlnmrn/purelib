module
import Purelib.Data.Rat.Fraction

import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction.Field
public import Purelib.Measure.Distribution.Equivalence
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Content.Basic
import Purelib.Data.List.Event
import Purelib.Measure.Distribution.Lp.L2
import Purelib.Measure.Distribution.Lp.Natural
public import Purelib.Measure.Distribution.Lp.AlmostEverywhere
import Purelib.Measure.Distribution.Lp.L1
import Purelib.Measure.Distribution.Expectation

section
@[expose] public section

/-!
# Lp invariance under finite evaluation equivalence

Every rational powered-Lp quantity is an exact expectation of an explicit
observable.  It therefore depends only on finite evaluations, not on row
order, duplicated payloads, or another choice of displayed atom table.
-/

namespace Purelib.Measure

namespace Content.EvaluationEquivalent
end Content.EvaluationEquivalent

namespace Distribution.EvaluationEquivalent

section
open Purelib
open Purelib.Data.Rat
/-- Evaluation-equivalent distributions have equal natural-powered magnitude expectations. -/
theorem poweredLp_eq {α : Type} {left right : Measure.Distribution α}
    (equivalent : Distribution.EvaluationEquivalent left right)
    (exponent : Nat) (value : α → Fraction.Rational) :
    left.poweredLp exponent value = right.poweredLp exponent value := by
  change left.expectation (fun item =>
      Distance.rationalSeparation (value item) 0 ^ exponent) =
    right.expectation (fun item =>
      Distance.rationalSeparation (value item) 0 ^ exponent)
  exact equivalent.expectation_eq _

/-- Evaluation-equivalent distributions have equal natural-powered distance expectations. -/
theorem poweredLpDistance_eq {α : Type} {left right : Measure.Distribution α}
    (equivalent : Distribution.EvaluationEquivalent left right)
    (exponent : Nat) (first second : α → Fraction.Rational) :
    left.poweredLpDistance exponent first second =
      right.poweredLpDistance exponent first second := by
  change left.expectation (fun item =>
      Distance.rationalSeparation (first item) (second item) ^ exponent) =
    right.expectation (fun item =>
      Distance.rationalSeparation (first item) (second item) ^ exponent)
  exact equivalent.expectation_eq _

/-- Evaluation-equivalent distributions have equal magnitude expectations. -/
theorem poweredL1_eq {α : Type} {left right : Measure.Distribution α}
    (equivalent : Distribution.EvaluationEquivalent left right)
    (value : α → Fraction.Rational) :
    left.poweredL1 value = right.poweredL1 value := by
  change left.expectation (fun item => Distance.rationalSeparation (value item) 0) =
    right.expectation (fun item => Distance.rationalSeparation (value item) 0)
  exact equivalent.expectation_eq _

/-- Evaluation-equivalent distributions have equal integrated distances between observables. -/
theorem l1Distance_eq {α : Type} {left right : Measure.Distribution α}
    (equivalent : Distribution.EvaluationEquivalent left right)
    (first second : α → Fraction.Rational) :
    left.l1Distance first second = right.l1Distance first second :=
  equivalent.expectation_eq fun item =>
    Distance.rationalSeparation (first item) (second item)

/-- Evaluation-equivalent distributions have equal squared-observable expectations. -/
theorem poweredL2_eq {α : Type} {left right : Measure.Distribution α}
    (equivalent : Distribution.EvaluationEquivalent left right)
    (value : α → Fraction.Rational) :
    left.poweredL2 value = right.poweredL2 value := by
  change left.expectation (fun item => value item ^ 2) =
    right.expectation (fun item => value item ^ 2)
  exact equivalent.expectation_eq _

/-- Evaluation-equivalent distributions have equal squared-distance expectations. -/
theorem poweredL2Distance_eq {α : Type}
    {left right : Measure.Distribution α}
    (equivalent : Distribution.EvaluationEquivalent left right)
    (first second : α → Fraction.Rational) :
    left.poweredL2Distance first second =
      right.poweredL2Distance first second := by
  change left.expectation (fun item => (first item - second item) ^ 2) =
    right.expectation (fun item => (first item - second item) ^ 2)
  exact equivalent.expectation_eq _

/-- Evaluation-equivalent distributions give the same almost-everywhere equality relation on rational observables. -/
theorem equalAlmostEverywhere_iff {α : Type}
    {left right : Measure.Distribution α}
    (equivalent : Distribution.EvaluationEquivalent left right)
    (first second : α → Fraction.Rational) :
    left.EqualAlmostEverywhere first second ↔
      right.EqualAlmostEverywhere first second := by
  constructor
  · intro equal
    apply (right.l1Distance_eq_zero_iff first second).mp
    rw [← equivalent.l1Distance_eq first second]
    exact (left.l1Distance_eq_zero_iff first second).mpr equal
  · intro equal
    apply (left.l1Distance_eq_zero_iff first second).mp
    rw [equivalent.l1Distance_eq first second]
    exact (right.l1Distance_eq_zero_iff first second).mpr equal

end

end Distribution.EvaluationEquivalent

end Purelib.Measure

end
