module
import Purelib.Approximation.Gaussian.Process.Basic
public import Purelib.Approximation.Gaussian.Process.OneSided
import Purelib.Data.Gaussian.Field

import Purelib.Approximation.OneSided.Located
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
public import Purelib.Examples.Measure.Probability.Classification.FirstArrival.WorkedExamples
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Gaussian.Basic

@[expose] public section

/-!
# CCL conversion examples for one-sided rational pairs

The four finite-measure examples are converted here to the ordinary CCL
process interface.  The computations expose exact Gaussian-rational balls
returned by finite squared-error requests.
-/

namespace Purelib.Examples.Approximation.Gaussian.Process.OneSided.FirstArrivalProbability

open Purelib.Examples.Measure.Probability.Classification

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Approximation.Gaussian.Process
open Purelib.Examples

/-- The Gaussian process induced by the retained first-arrival probability bounds.

Uses the original located lower/upper pair and its exact finite stage states. -/
def process :
    Approximation.Gaussian.Process :=
  (OneSided.LocatedPair.toProcess FirstArrival.WorkedExamples.located)

/-- The complete retained first-arrival classification stage. -/
def refinedState :
    FirstArrival.WorkedExamples.Stage :=
  .complete

/-- A one-tenth Gaussian accuracy request reaches the original complete stage. -/
theorem
  process_refine_eq_refinedState
  :
    (OneSided.LocatedPair.toProcess FirstArrival.WorkedExamples.located).refine
      FirstArrival.WorkedExamples.located.initial
      (1 / 10) (by decide) = refinedState := by
  rfl

/-- The complete stage gives the exact Gaussian point (3/5,0).

The retained ball's real center is the original first-arrival probability and its imaginary center and squared radius
are zero. -/
theorem refined_ball_data :
    ((OneSided.LocatedPair.toProcess FirstArrival.WorkedExamples.located).ball
        refinedState).center.re = 3 / 5 ∧
      ((OneSided.LocatedPair.toProcess FirstArrival.WorkedExamples.located).ball
        refinedState).center.im = 0 ∧
      ((OneSided.LocatedPair.toProcess FirstArrival.WorkedExamples.located).ball
        refinedState).radiusSq = 0 := by
  decide

/-- The original one-tenth refinement has squared radius below one tenth. -/
theorem requested_ball_accurate
  :
    ((OneSided.LocatedPair.toProcess FirstArrival.WorkedExamples.located).ball
      ((OneSided.LocatedPair.toProcess FirstArrival.WorkedExamples.located).refine
        FirstArrival.WorkedExamples.located.initial
        (1 / 10) (by decide))).radiusSq < 1 / 10 :=
  (OneSided.LocatedPair.toProcess FirstArrival.WorkedExamples.located).accurate
    FirstArrival.WorkedExamples.located.initial
    (1 / 10) (by decide)

end Purelib.Examples.Approximation.Gaussian.Process.OneSided.FirstArrivalProbability

end
