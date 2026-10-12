module
import Purelib.Data.Rat.Fraction

import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Measure.Content.Basic
public import Purelib.Measure.Content.Equivalence
import Purelib.Measure.Distribution.Basic
import Purelib.Data.List.Event
import Purelib.Measure.Content.Lp.L2
public import Purelib.Measure.Content.Lp.Natural
import Purelib.Measure.Content.Lp.L1

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

section
open Purelib
open Purelib.Data.Rat
/-- Evaluation-equivalent contents give the same natural-powered magnitude integral. -/
theorem poweredLp_eq {α : Type} {left right : Measure.Content α}
    (equivalent : Content.EvaluationEquivalent left right)
    (exponent : Nat) (value : α → Fraction.Rational) :
    left.poweredLp exponent value = right.poweredLp exponent value :=
  equivalent.integral_eq fun item =>
    Distance.rationalSeparation (value item) 0 ^ exponent

/-- Evaluation-equivalent contents give the same natural-powered separation integral. -/
theorem poweredLpDistance_eq {α : Type}
    {left right : Measure.Content α}
    (equivalent : Content.EvaluationEquivalent left right)
    (exponent : Nat) (first second : α → Fraction.Rational) :
    left.poweredLpDistance exponent first second =
      right.poweredLpDistance exponent first second :=
  equivalent.integral_eq fun item =>
    Distance.rationalSeparation (first item) (second item) ^ exponent

/-- Evaluation-equivalent contents give the same magnitude integral. -/
theorem poweredL1_eq {α : Type} {left right : Measure.Content α}
    (equivalent : Content.EvaluationEquivalent left right)
    (value : α → Fraction.Rational) :
    left.poweredL1 value = right.poweredL1 value :=
  equivalent.integral_eq fun item => Distance.rationalSeparation (value item) 0

/-- Evaluation-equivalent contents give the same integrated separation. -/
theorem l1Distance_eq {α : Type} {left right : Measure.Content α}
    (equivalent : Content.EvaluationEquivalent left right)
    (first second : α → Fraction.Rational) :
    left.l1Distance first second = right.l1Distance first second :=
  equivalent.integral_eq fun item =>
    Distance.rationalSeparation (first item) (second item)

/-- Evaluation-equivalent contents give the same square integral. -/
theorem poweredL2_eq {α : Type} {left right : Measure.Content α}
    (equivalent : Content.EvaluationEquivalent left right)
    (value : α → Fraction.Rational) :
    left.poweredL2 value = right.poweredL2 value :=
  equivalent.integral_eq fun item => value item ^ 2

/-- Evaluation-equivalent contents give the same squared integrated distance. -/
theorem poweredL2Distance_eq {α : Type}
    {left right : Measure.Content α}
    (equivalent : Content.EvaluationEquivalent left right)
    (first second : α → Fraction.Rational) :
    left.poweredL2Distance first second =
      right.poweredL2Distance first second :=
  equivalent.integral_eq fun item => (first item - second item) ^ 2

end

end Content.EvaluationEquivalent

namespace Distribution.EvaluationEquivalent
end Distribution.EvaluationEquivalent

end Purelib.Measure

end
