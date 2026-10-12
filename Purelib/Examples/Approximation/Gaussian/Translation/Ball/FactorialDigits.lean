module
public import Purelib.Approximation.Gaussian.Translation.Enclosure
public import Purelib.Examples.Approximation.Gaussian.Process.OneSided.LiouvilleDigits
import Purelib.Examples.Approximation.Rational.Radix.FactorialPosition.WorkedExamples
import Purelib.Approximation.Gaussian.Translation.Realizer
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Approximation.OneSided.Located
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Translation.Schedule
import Purelib.Approximation.Gaussian.Representation.Basic
import Purelib.Approximation.Gaussian.Process.OneSided
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Approximation.Gaussian.Translation.Request
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Approximation.Gaussian.Representation.Ball
import Purelib.Approximation.Gaussian.Representation.Process

@[expose] public section

/-!
# Worked finite-translation examples

These four examples exercise different parts of the protocol: algebraic
bisection, a Liouville-style nonalgebraic digit process, sequential raw CCL
output for a finite exponential program, and a redundant signed-digit
translation of that same non-rational process.
-/

namespace Purelib.Examples.Approximation.Gaussian.Translation.Ball.FactorialDigits

open Purelib.Examples.Approximation.Rational.Radix

open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Process
open Purelib.Examples.Approximation
open Purelib.Examples.Approximation.Gaussian

/-! ## 2. Liouville factorial-position digits to a rational ball -/

/-- The positive factorial-digit ball-translation target one ninth. -/
def request :
  Approximation.Gaussian.Translation.Request :=
  ⟨1 / 9, by decide⟩

/-- Translate the original factorial-position Gaussian process to a certified ball.

Retains the exact located-process initial state, requested refinement, output enclosure and unit translation cost. -/
def result :=
  (Translation.Enclosure.processToBall
    (OneSided.LocatedPair.toProcess FactorialPosition.WorkedExamples.located)).translate
      FactorialPosition.WorkedExamples.located.initial request

/-- The translation retains the original selected index two. -/
theorem refined_state :
    result.source' =
      Process.OneSided.LiouvilleDigits.refinedState := by
  change
    (OneSided.LocatedPair.toProcess FactorialPosition.WorkedExamples.located).refine
      FactorialPosition.WorkedExamples.located.initial
        (1 / 9) request.positive = _
  exact
    Process.OneSided.LiouvilleDigits.process_refine_eq_refinedState

/-- The actual translated ball is centered at (5/16,0) with squared radius (1/16)^2. -/
theorem translated_ball_data :
    result.output.center.re = 5 / 16 ∧
      result.output.center.im = 0 ∧
      result.output.radiusSq = (1 / 16) ^ 2 := by
  change
    ((OneSided.LocatedPair.toProcess FactorialPosition.WorkedExamples.located).ball
      result.source').center.re = 5 / 16 ∧
    ((OneSided.LocatedPair.toProcess FactorialPosition.WorkedExamples.located).ball
      result.source').center.im = 0 ∧
    ((OneSided.LocatedPair.toProcess FactorialPosition.WorkedExamples.located).ball
      result.source').radiusSq = (1 / 16) ^ 2
  rw [refined_state]
  exact
    Process.OneSided.LiouvilleDigits.refined_ball_data

/-- The original ball translation records unit scheduled work and unit cost bound. -/
theorem translation_cost :
    result.schedule.work = 1 ∧ result.costBound = 1 :=
      by
  exact ⟨rfl, rfl⟩

/-! ## A shared finite exponential process for Examples 3 and 4 -/

/-! ## 3. Finite exponential approximation to a persistent CCL prefix -/

/-! ## 4. The same finite exponential process in redundant signed digits -/

end Purelib.Examples.Approximation.Gaussian.Translation.Ball.FactorialDigits

end
