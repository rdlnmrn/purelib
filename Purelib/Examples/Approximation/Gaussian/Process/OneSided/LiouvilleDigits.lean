module
public import Purelib.Approximation.Gaussian.Process.OneSided
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Approximation.Rational.Request.Square

import Purelib.Approximation.OneSided.Located
import Purelib.Approximation.Rational.Budget.Geometric
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
public import Purelib.Examples.Approximation.Rational.Radix.FactorialPosition.WorkedExamples
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic

@[expose] public section

/-!
# CCL conversion examples for one-sided rational pairs

The four finite-measure examples are converted here to the ordinary CCL
process interface.  The computations expose exact Gaussian-rational balls
returned by finite squared-error requests.
-/

namespace Purelib.Examples.Approximation.Gaussian.Process.OneSided.LiouvilleDigits

open Purelib.Examples.Approximation.Rational.Radix

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Approximation.Gaussian.Process
open Purelib.Examples.Approximation
open Purelib
open Purelib.Approximation.Rational

/-- The Gaussian process induced by the retained factorial-position radix-four bounds.

Uses the original located pair and its natural-number prefix indices. -/
def process :
    Approximation.Gaussian.Process :=
  (OneSided.LocatedPair.toProcess FactorialPosition.WorkedExamples.located)

/-- The retained Gaussian refinement index two. -/
def refinedState : Nat := 2

/-- A one-ninth squared-radius request reaches the original index two.

Uses the exact conversion to a one-tenth gap target and the retained quarter-geometric search result. -/
theorem process_refine_eq_refinedState :
    (OneSided.LocatedPair.toProcess FactorialPosition.WorkedExamples.located).refine
      FactorialPosition.WorkedExamples.located.initial
      (1 / 9) (by decide) = refinedState := by
  rw [OneSided.LocatedPair.toProcess_refine]
  change Approximation.Geometric.firstQuarterBelow
    1 0 (Request.Square.gapTarget (1 / 9)) = refinedState
  have gapIdentity :
      Request.Square.gapTarget (1 / 9) = 1 / 10 := by
    decide
  rw [gapIdentity]
  exact FactorialPosition.WorkedExamples.tenth_request_index

/-- At index two the retained Gaussian ball is centered at (5/16,0).

Its squared radius is exactly the square of one sixteenth, preserving the original paired prefix-gap readback. -/
theorem refined_ball_data :
    ((OneSided.LocatedPair.toProcess FactorialPosition.WorkedExamples.located).ball
        refinedState).center.re = 5 / 16 ∧
      ((OneSided.LocatedPair.toProcess FactorialPosition.WorkedExamples.located).ball
        refinedState).center.im = 0 ∧
      ((OneSided.LocatedPair.toProcess FactorialPosition.WorkedExamples.located).ball
        refinedState).radiusSq = (1 / 16) ^ 2 := by
  constructor
  · decide
  constructor
  · decide
  · decide

/-- The original one-ninth refinement has squared radius below one ninth. -/
theorem requested_ball_accurate :
    ((OneSided.LocatedPair.toProcess FactorialPosition.WorkedExamples.located).ball
      ((OneSided.LocatedPair.toProcess FactorialPosition.WorkedExamples.located).refine
        FactorialPosition.WorkedExamples.located.initial
        (1 / 9) (by decide))).radiusSq < 1 / 9 :=
  (OneSided.LocatedPair.toProcess FactorialPosition.WorkedExamples.located).accurate
    FactorialPosition.WorkedExamples.located.initial
    (1 / 9) (by decide)

end Purelib.Examples.Approximation.Gaussian.Process.OneSided.LiouvilleDigits

end
