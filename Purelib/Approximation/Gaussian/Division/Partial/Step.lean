module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Approximation.Gaussian.Division.Partial.Preparation
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Approximation.Gaussian.Division.Partial.Ready
public import Purelib.Approximation.Gaussian.Division.Partial.Requirement
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Process.Apart.Possible
import Purelib.Approximation.Gaussian.Process.Based
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib

open Purelib.Approximation.Gaussian.Division.Partial

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent.Refinement

section
@[expose] public section

/-!
# Retryable finite preflight for constructive division

An ordinary progressive division is total only after its denominator carries
uniform whole-ball apartness.  This module searches for that certificate one
explicit finite refinement at a time.  It keeps the existing total `Process`
and productive transducer unchanged: a caller receives an ordinary
`CoherentNamed` only in the `ready` case.

Failure of the current rational separation test is represented solely by a
certified progress step.  It is neither evidence that the denominator is zero
nor evidence that zero lies in the current ball.  Manual resumption accepts an
apartness witness indexed by the exact retained denominator state.
-/

namespace Purelib.Approximation.Gaussian.Division.Partial.Step

set_option genInjectivity false in
/-- One automatic inspection either finishes or performs exactly one certified refinement. There is deliberately no
exclusion constructor. -/
inductive StepResult (numerator denominator :
  Coherent.CoherentNamed)
    (state : Approximation.Gaussian.Name.Coherent.Refinement.State denominator) : Type 2
  /-- Retain the computed ordinary quotient and its readiness certificate indexed by the exact denominator state. -/ |
    ready (output : Coherent.CoherentNamed) (valid : Approximation.Gaussian.Division.Partial.Ready numerator denominator
        state output)
  /-- Retain the next denominator state and the certificate of one actual refinement step. -/ | progressed (next :
    Approximation.Gaussian.Name.Coherent.Refinement.State denominator) (progress : State.Progress state next)

constructive_injectivity StepResult

/-- Inspect one displayed rational ball. A failed test performs exactly the canonical refinement selected by
`nextIndex`; it never reports zero or domain exclusion. -/
def step (numerator denominator : Coherent.CoherentNamed)
    (state : Approximation.Gaussian.Name.Coherent.Refinement.State denominator) :
        StepResult numerator denominator
      state :=
  if separated :
      2 * (denominator.name.process.ball state.source).radiusSq <
        Data.Gaussian.Norm.Basic.normSq (denominator.name.process.ball state.source).center then
    let evidence := Preparation.evidenceOfSeparation state separated
    .ready (Ready.readyName numerator denominator state evidence)
      { evidence := evidence, output_eq := rfl }
  else
    .progressed state.advance (.refined state)

/-- A successful rational separation test makes the automatic step ready. -/
theorem step_is_ready_of_separated (numerator denominator :
  Coherent.CoherentNamed)
    (state : Approximation.Gaussian.Name.Coherent.Refinement.State denominator)
    (separated :
      2 * (denominator.name.process.ball state.source).radiusSq <
        Data.Gaussian.Norm.Basic.normSq (denominator.name.process.ball state.source).center) :
    ∃ output : Coherent.CoherentNamed, ∃ valid :
        Approximation.Gaussian.Division.Partial.Ready numerator denominator state output,
      step numerator denominator state = .ready output valid := by
  rw [step, dif_pos separated]
  exact ⟨_, _, rfl⟩

/-- Failure of the sufficient separation test has exactly one meaning: one canonical certified refinement is returned.
-/
theorem step_eq_progressed_of_not_separated
    (numerator denominator : Coherent.CoherentNamed) (state : Approximation.Gaussian.Name.Coherent.Refinement.State
        denominator)
    (notSeparated : ¬
      2 * (denominator.name.process.ball state.source).radiusSq <
        Data.Gaussian.Norm.Basic.normSq (denominator.name.process.ball state.source).center) :
    step numerator denominator state =
      .progressed state.advance (.refined state) := by
  rw [step, dif_neg notSeparated]

/-- Satisfy the exact typed requirement explicitly, bypassing further automatic search. -/
def resume (numerator denominator : Coherent.CoherentNamed)
    (state : Approximation.Gaussian.Name.Coherent.Refinement.State denominator) (requirement :
        Approximation.Gaussian.Division.Partial.Requirement state)
    (evidence : Requirement.Evidence requirement) :
    StepResult numerator denominator state :=
  match requirement with
  | .candidateApartness =>
      .ready (Ready.readyName numerator denominator state evidence)
        { evidence := evidence, output_eq := rfl }

/-- Supplying evidence for the exact indexed requirement always returns an ordinary ready quotient in one finite call.
-/
theorem resume_is_ready (numerator denominator :
  Coherent.CoherentNamed)
    (state : Approximation.Gaussian.Name.Coherent.Refinement.State denominator) (requirement :
        Approximation.Gaussian.Division.Partial.Requirement state)
    (evidence : Requirement.Evidence requirement) :
    ∃ output : Coherent.CoherentNamed, ∃ valid :
        Approximation.Gaussian.Division.Partial.Ready numerator denominator state output,
      resume numerator denominator state requirement evidence =
        .ready output valid := by
  cases requirement
  exact ⟨_, _, rfl⟩
end Purelib.Approximation.Gaussian.Division.Partial.Step

end
