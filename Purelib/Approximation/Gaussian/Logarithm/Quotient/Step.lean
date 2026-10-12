module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Approximation.Gaussian.Division.Partial.Preparation
import Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored
import Purelib.Approximation.Gaussian.Logarithm.Chart.Partial.Ready
import Purelib.Approximation.Gaussian.Logarithm.Chart.Partial.Step
import Purelib.Approximation.Gaussian.Logarithm.Quotient.Client
public import Purelib.Approximation.Gaussian.Logarithm.Quotient.Ready
public import Purelib.Approximation.Gaussian.Logarithm.Quotient.Requirement
import Purelib.Approximation.Gaussian.Logarithm.Quotient.State
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.LogarithmState
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
import Purelib.Approximation.Gaussian.Process.Apart.Possible
import Purelib.Approximation.Gaussian.Process.Based
import Init.Prelude
import Purelib.Approximation.Gaussian.Logarithm.Chart.Partial.Requirement
import Purelib.Approximation.Gaussian.Name.Basic

open Purelib.Approximation.Gaussian.Logarithm.Quotient (Client)

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Division.Partial

open Purelib.Approximation.Gaussian.Logarithm.Chart

open Purelib.Approximation.Gaussian.Logarithm.Chart.Partial

open Purelib.Approximation.Gaussian.Logarithm.Quotient

open Purelib.Approximation.Gaussian.Logarithm.Quotient.State

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent.Refinement

open Purelib.Approximation.Gaussian.Process.Apart

section
public section

/-!
# A finite dependency scheduler for `log(1 + z) / z`

This is the first composition client for retryable partial operations.  It
coordinates one fixed anchored-logarithm branch with denominator-only
apartness preparation.  A scheduler tick performs at most one child action,
and a blocked result retains the exact child state and typed requirement.

The client deliberately stays at the coherent-name level.  It neither fills
the removable value at zero nor claims a global logarithm branch.
-/

namespace Purelib.Approximation.Gaussian.Logarithm.Quotient.Step

set_option genInjectivity false in
/-- One certified scheduler transition. Readiness acquisition is progress: it replaces one pending child by retained
evidence and never recomputes it. -/
inductive Progress (client :
    Client) : Purelib.Approximation.Gaussian.Logarithm.Quotient.State
  client → Purelib.Approximation.Gaussian.Logarithm.Quotient.State client → Type 2
  /-- Advance only the logarithm search by its certified refinement and toggle scheduling priority. -/ | logRefined
    (logState next : LogarithmState.State client.argument)
      (progress : LogarithmState.Progress logState next)
      (denominatorSlot : State.DenominatorSlot client) (cursor : Bool) :
      Progress client
        (Approximation.Gaussian.Logarithm.Quotient.State.withLogSearching logState denominatorSlot cursor)
        (Approximation.Gaussian.Logarithm.Quotient.State.withLogSearching next denominatorSlot (!cursor))
  /-- Replace only the pending logarithm child with its cached ready chart and toggle scheduling priority. -/ |
    logPrepared (logState : LogarithmState.State client.argument)
      (output : Anchored.AnchoredChart (LogarithmState.preparedTarget logState))
      (valid : Purelib.Approximation.Gaussian.Logarithm.Chart.Partial.Ready client.sourceInput client.argument
        client.source
        logState output)
      (denominatorSlot : State.DenominatorSlot client) (cursor : Bool) :
      Progress client
        (Approximation.Gaussian.Logarithm.Quotient.State.withLogSearching logState denominatorSlot cursor)
        (Approximation.Gaussian.Logarithm.Quotient.State.withLogReady logState output valid denominatorSlot (!cursor))
  /-- Advance only the denominator search by its certified refinement and toggle scheduling priority. -/ |
    denominatorRefined (logSlot : State.LogSlot client)
      (denominatorState next : Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State client.denominator)
      (progress : State.Progress denominatorState next) (cursor : Bool) :
      Progress client
        (Approximation.Gaussian.Logarithm.Quotient.State.withDenominatorSearching logSlot denominatorState cursor)
        (Approximation.Gaussian.Logarithm.Quotient.State.withDenominatorSearching logSlot next (!cursor))
  /-- Replace only the pending denominator child with its cached apartness certificate and toggle scheduling priority.
  -/
  | denominatorPrepared (logSlot : State.LogSlot client)
      (denominatorState : Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State client.denominator)
      (evidence : Possible.PossibleApart
        (Gaussian.Process.Based.based client.denominator.name.process
          denominatorState.source))
      (cursor : Bool) :
      Progress client
        (Approximation.Gaussian.Logarithm.Quotient.State.withDenominatorSearching logSlot denominatorState cursor)
        (Approximation.Gaussian.Logarithm.Quotient.State.withDenominatorReady logSlot denominatorState evidence
            (!cursor))

constructive_injectivity Progress

set_option genInjectivity false in
/-- Finite reachability contains only the current dependency-tree states, not an unbounded execution log. -/
inductive Reachable {client :
    Client} : Purelib.Approximation.Gaussian.Logarithm.Quotient.State
  client → Purelib.Approximation.Gaussian.Logarithm.Quotient.State client → Type 2
  /-- The current scheduler state is reachable from itself. -/ | refl (state :
    Purelib.Approximation.Gaussian.Logarithm.Quotient.State client) :
    Reachable state state
  /-- Prepend one certified scheduler transition to a finite reachability witness. -/ | tail {start middle finish :
    Purelib.Approximation.Gaussian.Logarithm.Quotient.State client} :
      Progress client start middle →
        Reachable middle finish →
        Reachable start finish

constructive_injectivity Reachable

set_option genInjectivity false in
/-- One global scheduler tick. -/
inductive StepResult (client :
    Client) (current :
  Purelib.Approximation.Gaussian.Logarithm.Quotient.State client) : Type 2
  /-- Return the ordinary quotient output and its certificate retaining both ready child results. -/ | ready (output :
    Coherent.CoherentNamed) (valid : Purelib.Approximation.Gaussian.Logarithm.Quotient.Ready client output)
  /-- Retain the next scheduler state and the certified transition from the current state. -/ | progressed (next :
    Purelib.Approximation.Gaussian.Logarithm.Quotient.State client) (progress :
      Progress client current next)
  /-- Retain the typed child requirement together with equality to the unchanged current scheduler state. -/ | blocked
    (request : Requirement.Blocked client) (retained : request.state = current)

constructive_injectivity StepResult

/-- Advance the logarithm child by exactly one operation-specific action. -/
@[expose] def advanceLog (client :
    Client)
    (logState : LogarithmState.State client.argument)
    (denominatorSlot : State.DenominatorSlot client) (cursor : Bool) :
    StepResult client
        (Approximation.Gaussian.Logarithm.Quotient.State.withLogSearching logState denominatorSlot
      cursor) :=
  match Chart.Partial.Step.step client.sourceInput client.argument client.source logState with
  | .ready output valid =>
      .progressed
        (Approximation.Gaussian.Logarithm.Quotient.State.withLogReady logState output valid denominatorSlot (!cursor))
        (.logPrepared logState output valid denominatorSlot cursor)
  | .progressed next progress =>
      .progressed
        (Approximation.Gaussian.Logarithm.Quotient.State.withLogSearching next denominatorSlot (!cursor))
        (.logRefined logState next progress denominatorSlot cursor)
  | .blocked requirement =>
      .blocked (.logarithm logState requirement denominatorSlot cursor) rfl

/-- Advance denominator-only preparation by exactly one operation-specific action. It is independent of the
not-yet-ready logarithm numerator. -/
@[expose] def advanceDenominator (client :
    Client)
  (logSlot : State.LogSlot client)
    (denominatorState : Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State client.denominator) (cursor :
      Bool) :
    StepResult client
      (Approximation.Gaussian.Logarithm.Quotient.State.withDenominatorSearching logSlot denominatorState cursor) :=
  match Preparation.prepare client.denominator denominatorState with
  | .prepared evidence =>
      .progressed
        (Approximation.Gaussian.Logarithm.Quotient.State.withDenominatorReady logSlot denominatorState evidence
            (!cursor))
        (.denominatorPrepared logSlot denominatorState evidence cursor)
  | .progressed next progress =>
      .progressed
        (Approximation.Gaussian.Logarithm.Quotient.State.withDenominatorSearching logSlot next (!cursor))
        (.denominatorRefined logSlot denominatorState next progress cursor)

/-- Deterministic round-robin scheduler. If only one child is pending it is selected directly; if both are pending,
`cursor` selects the next child. -/
@[expose] def step (client :
    Client) : (state :
  Purelib.Approximation.Gaussian.Logarithm.Quotient.State client) →
    StepResult client state
  | ⟨.ready logState logOutput logValid,
      .ready denominatorState denominatorEvidence, _cursor⟩ =>
      let output := Ready.readyName client logState logOutput denominatorState
        denominatorEvidence
      .ready output
        { logState := logState
          logOutput := logOutput
          logValid := logValid
          denominatorState := denominatorState
          denominatorEvidence := denominatorEvidence
          output_eq := rfl }
  | ⟨.ready logState logOutput logValid,
      .searching denominatorState, cursor⟩ =>
      advanceDenominator client (.ready logState logOutput logValid)
        denominatorState cursor
  | ⟨.searching logState,
      .ready denominatorState denominatorEvidence, cursor⟩ =>
      advanceLog client logState
        (.ready denominatorState denominatorEvidence) cursor
  | ⟨.searching logState, .searching denominatorState, cursor⟩ =>
      if cursor then
        advanceDenominator client (.searching logState) denominatorState
          cursor
      else
        advanceLog client logState (.searching denominatorState) cursor
end Purelib.Approximation.Gaussian.Logarithm.Quotient.Step

end
