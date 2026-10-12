module
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Measure.Content.Counting
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Examples.Measure.Content.Counting.WorkedExamples

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Content.Basic
import Purelib.Measure.Classified.Basic
import Purelib.Measure.Filtration.Basic
import Purelib.Measure.Distribution.Partition.Basic
import Purelib.Measure.Distribution.Partition.Positive
import Purelib.Measure.EventAlgebra.Simple.Basic
import Purelib.Measure.Event.Chain
import Purelib.Approximation.OneSided.Basic
import Purelib.Measure.Classified.FixedLawProcess
import Purelib.Approximation.OneSided.Located
import Purelib.Measure.Content.Density.Basic
import Purelib.Measure.EventAlgebra.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Basic

@[expose] public section

/-!
# Executable finite measure examples

All numerical examples reduce to finite rational calculations checked by the
kernel.  The final examples exercise the generic CCL area-request interface
without postulating a completed CCL value.
-/

namespace Purelib.Examples.Measure.Content.Density.Constant.WorkedExamples

open Purelib.Data.Rat
open Purelib.Measure
open Purelib.Examples
open Purelib.Examples.Measure.Content.Counting.WorkedExamples (observedEven observedRolls)

/-- The constant density two on natural-number observations. -/
def doubleDensity (_ : Nat) : Fraction.Rational
  := 2

/-- The constant density two is nonnegative. -/
theorem doubleDensity_nonnegative (item : Nat) :
    0 ≤ doubleDensity item := by
  unfold doubleDensity
  decide

/-- The constant density one half on natural-number observations. -/
def halfDensity (_ : Nat) : Fraction.Rational :=
  1 / 2

/-- The constant density one half is nonnegative. -/
theorem halfDensity_nonnegative (item : Nat) :
    0 ≤ halfDensity item := by
  unfold halfDensity
  decide

/-- Successive reweighting by two and one half agrees with reweighting by their pointwise product. -/
example :
    (((Purelib.Measure.countingContent observedRolls).reweight
      doubleDensity
        doubleDensity_nonnegative).reweight
          halfDensity
          halfDensity_nonnegative).measure
            observedEven =
      ((Purelib.Measure.countingContent observedRolls).reweight
        (fun item => doubleDensity item *
          halfDensity item)
        (fun item => Purelib.Data.Rat.Fraction.Order.Arithmetic.mul_nonneg_direct
          (doubleDensity_nonnegative item)
          (halfDensity_nonnegative item))).measure
            observedEven :=
  (Purelib.Measure.countingContent
    observedRolls).reweight_reweight_measure
    doubleDensity
      halfDensity
      doubleDensity_nonnegative
      halfDensity_nonnegative
        observedEven

/-- The two successive reweightings retain even-observation measure three. -/
example :
    (((Purelib.Measure.countingContent observedRolls).reweight
      doubleDensity
        doubleDensity_nonnegative).reweight
          halfDensity
          halfDensity_nonnegative).measure
            observedEven = 3 := by
  decide

end Purelib.Examples.Measure.Content.Density.Constant.WorkedExamples

end
