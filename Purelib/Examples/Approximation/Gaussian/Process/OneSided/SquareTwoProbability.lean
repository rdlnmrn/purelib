module
import Purelib.Approximation.Gaussian.Process.Basic
public import Purelib.Approximation.Gaussian.Process.OneSided
import Purelib.Data.Gaussian.Field

import Purelib.Approximation.OneSided.Located
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
public import Purelib.Examples.Measure.Probability.Classification.SquareTwo.WorkedExamples
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction

@[expose] public section

/-!
# CCL conversion examples for one-sided rational pairs

The four finite-measure examples are converted here to the ordinary CCL
process interface.  The computations expose exact Gaussian-rational balls
returned by finite squared-error requests.
-/

namespace Purelib.Examples.Approximation.Gaussian.Process.OneSided.SquareTwoProbability

open Purelib.Examples.Measure.Probability.Classification

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Approximation.Gaussian.Process
open Purelib.Examples

/-- The Gaussian process induced by the retained square-threshold probability bounds. -/
def process :
    Approximation.Gaussian.Process :=
  (OneSided.LocatedPair.toProcess SquareTwo.WorkedExamples.located)

/-- The original complete square-threshold classification stage. -/
def refinedState :
    SquareTwo.WorkedExamples.Stage :=
  .complete

/-- A one-tenth Gaussian request reaches the retained complete stage. -/
theorem
  process_refine_eq_refinedState :
    (OneSided.LocatedPair.toProcess SquareTwo.WorkedExamples.located).refine
      SquareTwo.WorkedExamples.located.initial
      (1 / 10) (by decide) = refinedState := by
  rfl

/-- The retained complete-stage Gaussian ball is the exact point (4/5,0). -/
theorem refined_ball_data :
    ((OneSided.LocatedPair.toProcess SquareTwo.WorkedExamples.located).ball
        refinedState).center.re = 4 / 5 ∧
      ((OneSided.LocatedPair.toProcess SquareTwo.WorkedExamples.located).ball
        refinedState).center.im = 0 ∧
      ((OneSided.LocatedPair.toProcess SquareTwo.WorkedExamples.located).ball
        refinedState).radiusSq = 0 := by
  decide

/-- The original one-tenth Gaussian request has squared radius below its target. -/
theorem requested_ball_accurate :
    ((OneSided.LocatedPair.toProcess SquareTwo.WorkedExamples.located).ball
      ((OneSided.LocatedPair.toProcess SquareTwo.WorkedExamples.located).refine
        SquareTwo.WorkedExamples.located.initial
        (1 / 10) (by decide))).radiusSq < 1 / 10 :=
  (OneSided.LocatedPair.toProcess SquareTwo.WorkedExamples.located).accurate
    SquareTwo.WorkedExamples.located.initial
    (1 / 10) (by decide)

end Purelib.Examples.Approximation.Gaussian.Process.OneSided.SquareTwoProbability

end
