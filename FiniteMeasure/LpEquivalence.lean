import FiniteMeasure.DistributionEquivalence
import FiniteMeasure.ContentEquivalence
import FiniteMeasure.NaturalLp
import FiniteMeasure.AlmostEverywhere

/-!
# Lp invariance under finite evaluation equivalence

Every rational powered-Lp quantity is an exact expectation of an explicit
observable.  It therefore depends only on finite evaluations, not on row
order, duplicated payloads, or another choice of displayed atom table.
-/

namespace FiniteMeasure

namespace FiniteContent.EvaluationEquivalent

theorem poweredLp_eq {α : Type} {left right : FiniteContent α}
    (equivalent : FiniteContent.EvaluationEquivalent left right)
    (exponent : Nat) (value : α → Coordinate) :
    left.poweredLp exponent value = right.poweredLp exponent value :=
  equivalent.integral_eq fun item =>
    rationalSeparation (value item) 0 ^ exponent

theorem poweredLpDistance_eq {α : Type}
    {left right : FiniteContent α}
    (equivalent : FiniteContent.EvaluationEquivalent left right)
    (exponent : Nat) (first second : α → Coordinate) :
    left.poweredLpDistance exponent first second =
      right.poweredLpDistance exponent first second :=
  equivalent.integral_eq fun item =>
    rationalSeparation (first item) (second item) ^ exponent

theorem poweredL1_eq {α : Type} {left right : FiniteContent α}
    (equivalent : FiniteContent.EvaluationEquivalent left right)
    (value : α → Coordinate) :
    left.poweredL1 value = right.poweredL1 value :=
  equivalent.integral_eq fun item => rationalSeparation (value item) 0

theorem l1Distance_eq {α : Type} {left right : FiniteContent α}
    (equivalent : FiniteContent.EvaluationEquivalent left right)
    (first second : α → Coordinate) :
    left.l1Distance first second = right.l1Distance first second :=
  equivalent.integral_eq fun item =>
    rationalSeparation (first item) (second item)

theorem poweredL2_eq {α : Type} {left right : FiniteContent α}
    (equivalent : FiniteContent.EvaluationEquivalent left right)
    (value : α → Coordinate) :
    left.poweredL2 value = right.poweredL2 value :=
  equivalent.integral_eq fun item => value item ^ 2

theorem poweredL2Distance_eq {α : Type}
    {left right : FiniteContent α}
    (equivalent : FiniteContent.EvaluationEquivalent left right)
    (first second : α → Coordinate) :
    left.poweredL2Distance first second =
      right.poweredL2Distance first second :=
  equivalent.integral_eq fun item => (first item - second item) ^ 2

end FiniteContent.EvaluationEquivalent

namespace Distribution.EvaluationEquivalent

theorem poweredLp_eq {α : Type} {left right : Distribution α}
    (equivalent : Distribution.EvaluationEquivalent left right)
    (exponent : Nat) (value : α → Coordinate) :
    left.poweredLp exponent value = right.poweredLp exponent value := by
  change left.expectation (fun item =>
      rationalSeparation (value item) 0 ^ exponent) =
    right.expectation (fun item =>
      rationalSeparation (value item) 0 ^ exponent)
  exact equivalent.expectation_eq _

theorem poweredLpDistance_eq {α : Type} {left right : Distribution α}
    (equivalent : Distribution.EvaluationEquivalent left right)
    (exponent : Nat) (first second : α → Coordinate) :
    left.poweredLpDistance exponent first second =
      right.poweredLpDistance exponent first second := by
  change left.expectation (fun item =>
      rationalSeparation (first item) (second item) ^ exponent) =
    right.expectation (fun item =>
      rationalSeparation (first item) (second item) ^ exponent)
  exact equivalent.expectation_eq _

theorem poweredL1_eq {α : Type} {left right : Distribution α}
    (equivalent : Distribution.EvaluationEquivalent left right)
    (value : α → Coordinate) :
    left.poweredL1 value = right.poweredL1 value := by
  change left.expectation (fun item => rationalSeparation (value item) 0) =
    right.expectation (fun item => rationalSeparation (value item) 0)
  exact equivalent.expectation_eq _

theorem l1Distance_eq {α : Type} {left right : Distribution α}
    (equivalent : Distribution.EvaluationEquivalent left right)
    (first second : α → Coordinate) :
    left.l1Distance first second = right.l1Distance first second :=
  equivalent.expectation_eq fun item =>
    rationalSeparation (first item) (second item)

theorem poweredL2_eq {α : Type} {left right : Distribution α}
    (equivalent : Distribution.EvaluationEquivalent left right)
    (value : α → Coordinate) :
    left.poweredL2 value = right.poweredL2 value := by
  change left.expectation (fun item => value item ^ 2) =
    right.expectation (fun item => value item ^ 2)
  exact equivalent.expectation_eq _

theorem poweredL2Distance_eq {α : Type}
    {left right : Distribution α}
    (equivalent : Distribution.EvaluationEquivalent left right)
    (first second : α → Coordinate) :
    left.poweredL2Distance first second =
      right.poweredL2Distance first second := by
  change left.expectation (fun item => (first item - second item) ^ 2) =
    right.expectation (fun item => (first item - second item) ^ 2)
  exact equivalent.expectation_eq _

/-- Evaluation-equivalent distributions have exactly the same finite null
discrepancies for rational observables. -/
theorem equalAlmostEverywhere_iff {α : Type}
    {left right : Distribution α}
    (equivalent : Distribution.EvaluationEquivalent left right)
    (first second : α → Coordinate) :
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

end Distribution.EvaluationEquivalent

end FiniteMeasure
