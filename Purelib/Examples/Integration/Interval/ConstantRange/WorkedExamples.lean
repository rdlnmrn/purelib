module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Examples.Approximation.Bound.Process.WorkedExamples
import Purelib.Integration.Cell.Basic

import Purelib.Tactic.QuotientFreeOmega
public import Purelib.Measure.IntervalIntegration
import Purelib.Approximation.Bound.Observation
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

@[expose] public section

/-!
# Executable finite measure examples

All numerical examples reduce to finite rational calculations checked by the
kernel.  The final examples exercise the generic CCL area-request interface
without postulating a completed CCL value.
-/

namespace Purelib.Examples.Integration.Interval.ConstantRange.WorkedExamples

open Purelib.Data.Rat.Fraction (Rational)

open Purelib.Data.Rat
open Purelib
open Purelib.Measure
open Purelib.Examples

/-- The exact rational interval [0,1]. -/
def unitInterval : Data.Rat.Interval :=
  ⟨0, 1, by decide⟩

/-- The unit integration interval with retained value bounds two and five. -/
def unitIntervalRange :
  IntervalIntegrationCell where
  interval := unitInterval
  lower := 2
  upper := 5
  range_valid := by decide

/-- Cutting the unit interval at one half while retaining the same range refines its integral enclosure. -/
example : Purelib.Data.Rat.Interval.Refines
    (Purelib.Integration.integralBound
      (Purelib.Measure.intervalCutSameRangeSplit unitIntervalRange (1
        / 2) (by decide)).children)
    (Purelib.Integration.integralBound
      [unitIntervalRange.toIntegrationCell]) :=
  intervalCutSameRange_integralBound_refines
    unitIntervalRange (1 / 2) (by decide)

/-- Adding the two exact-one processes gives the exact interval [2,2]. -/
example : ((Purelib.Examples.Approximation.Bound.Process.WorkedExamples.exactOneProcess.add
  Purelib.Examples.Approximation.Bound.Process.WorkedExamples.exactOneProcess).bound ((), ())).lower = 2 ∧
    ((Purelib.Examples.Approximation.Bound.Process.WorkedExamples.exactOneProcess.add
      Purelib.Examples.Approximation.Bound.Process.WorkedExamples.exactOneProcess).bound ((), ())).upper = 2 := by
  decide

/-- Positive scaling of the exact-one process by three gives the exact interval [3,3]. -/
example : ((Purelib.Examples.Approximation.Bound.Process.WorkedExamples.exactOneProcess.scalePositive 3 (by
  decide)).bound ()).lower = 3 ∧
    ((Purelib.Examples.Approximation.Bound.Process.WorkedExamples.exactOneProcess.scalePositive 3 (by decide)).bound
      ()).upper = 3 := by
  decide

/-- Subtracting the exact-one process from itself gives the exact interval [0,0]. -/
example : ((Purelib.Examples.Approximation.Bound.Process.WorkedExamples.exactOneProcess.sub
  Purelib.Examples.Approximation.Bound.Process.WorkedExamples.exactOneProcess).bound ((), ())).lower = 0 ∧
    ((Purelib.Examples.Approximation.Bound.Process.WorkedExamples.exactOneProcess.sub
      Purelib.Examples.Approximation.Bound.Process.WorkedExamples.exactOneProcess).bound ((), ())).upper = 0 := by
  decide

/-- Two readings inside the requested exact-one enclosure have separation below the positive requested tolerance. -/
example (epsilon : Rational) (positive : 0 < epsilon)
    {left right : Rational}
    (leftInside :
      (Purelib.Examples.Approximation.Bound.Process.WorkedExamples.exactOneProcess.bound
        (Purelib.Examples.Approximation.Bound.Process.WorkedExamples.exactOneProcess.request () epsilon
          positive)).Contains left)
    (rightInside :
      (Purelib.Examples.Approximation.Bound.Process.WorkedExamples.exactOneProcess.bound
        (Purelib.Examples.Approximation.Bound.Process.WorkedExamples.exactOneProcess.request () epsilon
          positive)).Contains right) :
    Purelib.Data.Rat.Distance.rationalSeparation left right < epsilon :=
  open Purelib.Examples in Approximation.Bound.Process.WorkedExamples.exactOneProcess.request_rationalSeparation_lt ()
    epsilon positive
    leftInside rightInside

end Purelib.Examples.Integration.Interval.ConstantRange.WorkedExamples

end
