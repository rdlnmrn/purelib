module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored
import Purelib.Approximation.Gaussian.Logarithm.Chart.Partial.Ready
import Purelib.Approximation.Gaussian.Logarithm.Chart.Partial.Requirement
public import Purelib.Approximation.Gaussian.Logarithm.Chart.Partial.Step
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.LogarithmState
import Init.Prelude

open Purelib

open Purelib.Approximation.Gaussian.Logarithm.Chart

open Purelib.Approximation.Gaussian.Logarithm.Chart.Partial

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent.Refinement

section
public section

/-!
# Retryable finite preflight for one anchored logarithm branch

The source anchor fixes the logarithm branch.  Automatic work refines one
target coherent name until an executable rational chart-safety certificate is
visible.  Generic finite refinement cannot construct semantic overlap between
two unrelated `Possible` predicates, so success of the safety test returns a
typed `blocked` requirement for an overlap witness at the exact prepared target
state.  Supplying that witness resumes directly into the existing
`SafeOverlapExtension.transport` operation.

No output name is exposed before readiness.  Failure of a safety test performs
one certified refinement and never proves that the input is zero or outside a
logarithm domain.
-/

namespace Purelib.Approximation.Gaussian.Logarithm.Chart.Partial.Run

/-- Small non-dependent observation of why a finite run stopped. -/
inductive ResultKind
  /-- The run has a certified anchored output. -/ | ready
  /-- The run requires typed evidence at its retained state. -/ | blocked
  /-- The supplied finite refinement budget is exhausted. -/ | exhausted
  deriving DecidableEq

set_option genInjectivity false in
/-- The payload which is specific to one terminal kind and exact retained state. Only this field is dependent; ordinary
scheduling observations remain cheap projections. -/
inductive RunPayload
    (sourceInput targetInput : Coherent.CoherentNamed)
    (source : Anchored.AnchoredChart sourceInput)
    (state : LogarithmState.State targetInput) : ResultKind → Type 2
  /-- Retain the anchored output and its readiness certificate at the terminal state. -/ | ready (output :
    Anchored.AnchoredChart (LogarithmState.preparedTarget state))
      (valid : Approximation.Gaussian.Logarithm.Chart.Partial.Ready sourceInput targetInput source state output) :
      RunPayload sourceInput targetInput source state .ready
  /-- Retain the exact requirement blocking the terminal state. -/
  | blocked (requirement : Approximation.Gaussian.Logarithm.Chart.Partial.Requirement
    sourceInput targetInput source state) :
      RunPayload sourceInput targetInput source state
        .blocked
  /-- Record exhaustion without asserting an exclusion or a ready output. -/ | exhausted :
      RunPayload sourceInput targetInput source state
        .exhausted

constructive_injectivity RunPayload

set_option genInjectivity false in
/-- Terminal result of a caller-bounded automatic run. Kind and state are first-class fields; the exact branch or
requirement remains indexed by both. -/
structure RunResult
    (sourceInput targetInput : Coherent.CoherentNamed)
    (source : Anchored.AnchoredChart sourceInput)
    (start : LogarithmState.State targetInput) : Type 2 where
  /-- The retained reason that the bounded run stopped. -/ kind :
    ResultKind
  /-- The exact target state retained when the bounded run stopped. -/ state : LogarithmState.State targetInput
  /-- The retained state is reached from the original start by genuine refinement steps. -/ reachable :
    LogarithmState.Reachable start state
  /-- The terminal certificate or requirement indexed by the retained state and stop kind. -/ payload :
    RunPayload sourceInput targetInput source state kind

constructive_injectivity RunResult

/-- Exhaustion at an unchanged retained state. -/
@[expose] def exhaustedResult
    (sourceInput targetInput : Coherent.CoherentNamed)
    (source : Anchored.AnchoredChart sourceInput)
    (state : LogarithmState.State targetInput) :
    RunResult sourceInput targetInput source state where
  kind := .exhausted
  state := state
  reachable := .refl state
  payload := .exhausted

/-- Immediate ready result at one retained state. -/
@[expose] def readyResult
    (sourceInput targetInput : Coherent.CoherentNamed)
    (source : Anchored.AnchoredChart sourceInput)
    (state : LogarithmState.State targetInput)
    (output : Anchored.AnchoredChart (LogarithmState.preparedTarget state))
    (valid : Approximation.Gaussian.Logarithm.Chart.Partial.Ready sourceInput targetInput source state output) :
    RunResult sourceInput targetInput source state where
  kind := .ready
  state := state
  reachable := .refl state
  payload := .ready output valid

/-- Immediate typed evidence request at one retained state. -/
@[expose] def blockedResult
    (sourceInput targetInput : Coherent.CoherentNamed)
    (source : Anchored.AnchoredChart sourceInput)
    (state : LogarithmState.State targetInput)
    (requirement : Approximation.Gaussian.Logarithm.Chart.Partial.Requirement sourceInput targetInput source state) :
    RunResult sourceInput targetInput source state where
  kind := .blocked
  state := state
  reachable := .refl state
  payload := .blocked requirement

/-- Prefix one genuine progress step to a recursive terminal result. -/
@[expose] def prefixResult
    {sourceInput targetInput : Coherent.CoherentNamed}
    {source : Anchored.AnchoredChart sourceInput}
    {start next : LogarithmState.State targetInput}
    (progress : LogarithmState.Progress start next)
    (later : RunResult sourceInput targetInput source next) :
    RunResult sourceInput targetInput source start where
  kind := later.kind
  state := later.state
  reachable := .tail progress later.reachable
  payload := later.payload

/-- Structurally recursive finite runner. Fuel is consumed only by a genuine `progressed` transition. -/
@[expose] def attempt
    (sourceInput targetInput : Coherent.CoherentNamed)
    (source : Anchored.AnchoredChart sourceInput)
    (state : LogarithmState.State targetInput) :
    Nat → RunResult sourceInput targetInput source state
  | 0 => exhaustedResult sourceInput targetInput source state
  | fuel + 1 =>
      match Step.step sourceInput targetInput source state with
      | .ready output valid =>
          readyResult sourceInput targetInput source state output
            valid
      | .blocked requirement =>
          blockedResult sourceInput targetInput source state
            requirement
      | .progressed next progress =>
          prefixResult progress
            (attempt sourceInput targetInput source next
              fuel)

/-- A zero-fuel attempt immediately retains the original state with an exhausted result. -/
@[simp] theorem attempt_zero
    (sourceInput targetInput : Coherent.CoherentNamed)
    (source : Anchored.AnchoredChart sourceInput)
    (state : LogarithmState.State targetInput) :
    attempt sourceInput targetInput source state 0 =
      exhaustedResult sourceInput targetInput source state := rfl
end Purelib.Approximation.Gaussian.Logarithm.Chart.Partial.Run

end
