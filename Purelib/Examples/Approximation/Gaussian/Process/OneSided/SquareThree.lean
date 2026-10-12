module
public import Purelib.Approximation.Gaussian.Process.OneSided
import Purelib.Approximation.Gaussian.Enclosure.Ball.RationalInterval
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Approximation.Rational.Request.Square
import Purelib.Data.Rat.Interval.Basic

import Purelib.Approximation.OneSided.Basic
import Purelib.Approximation.OneSided.Located
import Purelib.Approximation.RationalGap.SqrtThree
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
public import Purelib.Examples.Approximation.Rational.Algebraic.SquareThree.OneSided
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Bound.Process
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

namespace Purelib.Examples.Approximation.Gaussian.Process.OneSided.SquareThree

open Purelib.Approximation
open Purelib.Examples.Approximation.Rational.Algebraic

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Approximation.Gaussian.Process
open Purelib.Examples.Approximation
open Purelib
open Purelib.Approximation.Rational
open Purelib.Approximation.Gaussian
open Purelib.Data.Rat

/-- The Gaussian process induced by the original square-root-of-three located pair. -/
def process : Approximation.Gaussian.Process
    :=
  (OneSided.LocatedPair.toProcess SquareThree.OneSided.located)

/-- The retained initial-bracket request at tolerance one eighth. -/
def refinedState :
  SqrtThree.State :=
  SqrtThree.request SqrtThree.initialState
    (1 / 8)

/-- A one-seventh squared-radius request retains the one-eighth bracket state.

Uses the original exact conversion from Gaussian squared-radius tolerance to a rational gap request. -/
theorem process_refine_eq_refinedState :
    (OneSided.LocatedPair.toProcess SquareThree.OneSided.located).refine
      SquareThree.OneSided.located.initial
      (1 / 7) (by decide) = refinedState := by
  rw [OneSided.LocatedPair.toProcess_refine]
  change SqrtThree.request SqrtThree.initialState
    (Request.Square.gapTarget (1 / 7)) = refinedState
  have gapIdentity :
      Request.Square.gapTarget (1 / 7) = 1 / 8 := by
    decide
  rw [gapIdentity]
  rfl

/-- The retained refined Gaussian ball is centered at (27/16,0). -/
theorem refined_ball_center :
    ((OneSided.LocatedPair.toProcess SquareThree.OneSided.located).ball
        refinedState).center.re = 27 / 16 ∧
      ((OneSided.LocatedPair.toProcess SquareThree.OneSided.located).ball
        refinedState).center.im = 0 := by
  simp only [OneSided.LocatedPair.toProcess_ball,
    Enclosure.Ball.RationalInterval.ballOfBound_center_re,
    Enclosure.Ball.RationalInterval.ballOfBound_center_im,
    SquareThree.OneSided.located,
    SquareThree.OneSided.observation, refinedState,
    -eq_self, -iff_self]
  have data :=
    SquareThree.OneSided.eighth_request_data
  exact ⟨by simpa only [Interval.sample,
    Approximation.PairedObservation.bound] using data.1, rfl⟩

/-- The original one-seventh Gaussian request has squared radius below its target. -/
theorem requested_ball_accurate :
    ((OneSided.LocatedPair.toProcess SquareThree.OneSided.located).ball
      ((OneSided.LocatedPair.toProcess SquareThree.OneSided.located).refine
        SquareThree.OneSided.located.initial
        (1 / 7) (by decide))).radiusSq < 1 / 7 :=
  (OneSided.LocatedPair.toProcess SquareThree.OneSided.located).accurate
    SquareThree.OneSided.located.initial
    (1 / 7) (by decide)

end Purelib.Examples.Approximation.Gaussian.Process.OneSided.SquareThree

end
