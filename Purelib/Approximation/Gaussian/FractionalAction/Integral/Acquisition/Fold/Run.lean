module
public import Purelib.Control.FiniteRunner.Basic
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Fold.State
public import Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Fold.Step
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Words.Fold.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.LinearAlgebra.Matrix.Basic
import Init.Prelude

open Purelib.LinearAlgebra.Matrix.Basic (IntegralMatrix)

open Purelib

open Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Fold

open Purelib.Approximation.Gaussian.FractionalAction.Integral.Words

open Purelib.Approximation.Gaussian.Name

open Purelib.Control.FiniteRunner

open Purelib.LinearAlgebra.Matrix

section
@[expose] public section

/-!
# Resumable automatic acquisition for stepwise dual words

Each cursor retains completed head and suffix preparations, plus the exact
current denominator search state. Exhausting a budget preserves the cursor;
resumption neither reconstructs earlier outputs nor starts their searches
again. The final preparation is consumed directly by the existing arbitrary
finite-word period theorem.
-/

namespace Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Fold.Run

/-- A completed fractional-word preparation or its exact resumable acquisition cursor.

Exhaustion retains all cached work in the dependent cursor and makes no claim that a denominator cannot be prepared. -/
def Result (tau :
  Coherent.CoherentNamed) (matrices : List IntegralMatrix) :=
  LegendreFold.ResultPayload (Fold.Basic.FoldPreparations tau matrices) (State.Cursor tau matrices)

/-- Fuel bounds the total work across the entire dependent word, not a separate unbounded search at each intermediate
denominator. -/
def attempt (tau :
  Coherent.CoherentNamed) (matrices : List IntegralMatrix)
    (cursor : State.Cursor tau matrices) : Nat →
      Result tau matrices
  | 0 => match State.finished? tau matrices cursor with
      | some preparations => .ready preparations
      | none => .exhausted cursor
  | fuel + 1 => match State.finished? tau matrices cursor with
      | some preparations => .ready preparations
      | none => attempt tau matrices
        (Step.step tau matrices cursor) fuel

/-- A cursor already containing finished preparations returns them for every finite fuel budget.

The same successful finite observation is returned directly, independently of the supplied budget and without advancing
the retained cursor. -/
theorem attempt_of_finished (tau :
  Coherent.CoherentNamed) (matrices : List IntegralMatrix)
    (cursor : State.Cursor tau matrices) (preparations : Fold.Basic.FoldPreparations tau matrices)
    (finished : State.finished? tau matrices cursor = some preparations) (fuel : Nat) :
    attempt tau matrices cursor fuel = .ready
      preparations := by
  cases fuel <;>
    (simp only [attempt, finished, -eq_self,
      -iff_self]
     rfl)

/-- Splitting a budget and resuming the retained cursor is exactly the same finite computation as running the combined
budget in one call.

An exhausted first run retains the actual cursor for the second budget, while a completed first run returns its existing
preparations without further work. -/
theorem attempt_add (tau :
  Coherent.CoherentNamed) (matrices : List IntegralMatrix)
    (cursor : State.Cursor tau matrices) (first second : Nat) :
    attempt tau matrices cursor (first + second) =
      match attempt tau matrices cursor first with
      | .ready preparations => .ready preparations
      | .exhausted retained => attempt tau
        matrices retained second := by
  induction first generalizing cursor with
  | zero =>
      cases finished : State.finished? tau matrices cursor with
      | none =>
          simp only [Nat.zero_add, attempt,
            finished, -eq_self, -iff_self]
          rfl
      | some preparations =>
          simp only [Nat.zero_add, attempt,
            finished]
          exact attempt_of_finished tau matrices
            cursor preparations finished second
  | succ first inductionHypothesis =>
      cases finished : State.finished? tau matrices cursor with
      | none =>
          simp only [Nat.succ_add, attempt,
            finished]
          exact inductionHypothesis (Step.step tau matrices cursor)
      | some preparations =>
          simp only [Nat.succ_add, attempt,
            finished, -eq_self, -iff_self]
          rfl
end Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Fold.Run

end
