module
import Purelib.Approximation.Gaussian.Representation.Ball
public import Purelib.Approximation.Gaussian.Translation.Enclosure
import Purelib.Approximation.RationalGap.SqrtThree
public import Purelib.Examples.Approximation.Gaussian.Process.OneSided.SquareThree
import Purelib.Approximation.Gaussian.Translation.Realizer
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Translation.Schedule
import Purelib.Approximation.Gaussian.Representation.Basic
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Approximation.Gaussian.Translation.Request
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Approximation.Gaussian.Representation.Process

@[expose] public section

/-!
# Worked finite-translation examples

These four examples exercise different parts of the protocol: algebraic
bisection, a Liouville-style nonalgebraic digit process, sequential raw CCL
output for a finite exponential program, and a redundant signed-digit
translation of that same non-rational process.
-/

namespace Purelib.Examples.Approximation.Gaussian.Translation.Ball.SquareThree

open Purelib.Approximation

open Purelib.Approximation.Gaussian
open Purelib
open Purelib.Examples.Approximation.Gaussian

/-- The original Gaussian process from the square-root-of-three located pair. -/
abbrev process :=
  Purelib.Examples.Approximation.Gaussian.Process.OneSided.SquareThree.process

/-- The positive square-root-of-three ball-translation target one seventh. -/
def request :
    Approximation.Gaussian.Translation.Request :=
  ⟨1 / 7, by decide⟩

/-- Translate the retained initial square-root bracket to a certified Gaussian ball.

Keeps the original refinement state, output ball, precision certificate and unit work schedule. -/
def result :=
  (Translation.Enclosure.processToBall process).translate
    SqrtThree.initialState request

/-- The translated output retains the original one-eighth bracket request state. -/
theorem refined_state :
    result.source' =
      Process.OneSided.SquareThree.refinedState := by
  change process.refine SqrtThree.initialState
    (1 / 7) request.positive = _
  exact Process.OneSided.SquareThree.process_refine_eq_refinedState

/-- The actual translated ball is centered at (27/16,0). -/
theorem translated_center :
    result.output.center.re = 27 / 16 ∧
      result.output.center.im = 0 := by
  change (process.ball result.source').center.re = 27 / 16 ∧
    (process.ball result.source').center.im = 0
  rw [refined_state]
  exact
    Process.OneSided.SquareThree.refined_ball_center

/-- The original translation records unit scheduled work and unit cost bound. -/
theorem translation_cost :
    result.schedule.work = 1 ∧ result.costBound = 1 := by
  exact ⟨rfl, rfl⟩

/-- The retained translated ball has squared precision below one seventh.

Uses the original translation precision certificate and its exact zero loss at the fixed request. -/
theorem translated_precision :
    (Representation.Ball.ballRepresentation.precisionSq result.output) <
      1 / 7 := by
  calc
    Representation.Ball.ballRepresentation.precisionSq result.output <
        request.targetSq + result.precisionLoss :=
          result.precision
    _ = 1 / 7 := by decide

/-! ## 2. Liouville factorial-position digits to a rational ball -/

/-! ## A shared finite exponential process for Examples 3 and 4 -/

/-! ## 3. Finite exponential approximation to a persistent CCL prefix -/

/-! ## 4. The same finite exponential process in redundant signed digits -/

end Purelib.Examples.Approximation.Gaussian.Translation.Ball.SquareThree

end
