module
meta import Purelib.Elab.ConstructiveInjectivity
public import Purelib.Approximation.Gaussian.Division.Partial.Requirement
import Purelib.Approximation.Gaussian.Logarithm.Chart.Partial.Requirement
public import Purelib.Approximation.Gaussian.Logarithm.Chart.Partial.Step
import Purelib.Approximation.Gaussian.Logarithm.Quotient.Client
public import Purelib.Approximation.Gaussian.Logarithm.Quotient.State
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.LogarithmState
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
import Init.Prelude

open Purelib.Approximation.Gaussian.Logarithm.Quotient (Client)

open Purelib

open Purelib.Approximation.Gaussian.Logarithm.Chart.Partial

open Purelib.Approximation.Gaussian.Logarithm.Quotient

open Purelib.Approximation.Gaussian.Logarithm.Quotient.State

open Purelib.Approximation.Gaussian.Name.Coherent.Refinement

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

namespace Purelib.Approximation.Gaussian.Logarithm.Quotient.Requirement

set_option genInjectivity false in
/-- One exact typed request together with the other retained child. The request itself determines the scheduler state to
which evidence may resume. -/
inductive Blocked (client :
    Client) : Type 2
  /-- Retain the logarithm child's exact state and requirement together with the unchanged denominator slot and
    priority. -/ | logarithm (logState : LogarithmState.State client.argument)
      (requirement : Approximation.Gaussian.Logarithm.Chart.Partial.Requirement client.sourceInput client.argument
        client.source logState)
      (denominator : State.DenominatorSlot client) (cursor : Bool)
  /-- Retain the denominator child's exact state and requirement together with the unchanged logarithm slot and
    priority. -/ | denominator (denominatorState : Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
      client.denominator)
      (requirement : Approximation.Gaussian.Division.Partial.Requirement denominatorState)
      (log : State.LogSlot client) (cursor : Bool)

constructive_injectivity Blocked

namespace Blocked

/-- Recover the exact scheduler state retained by the blocked child requirement. -/
@[expose] def state {client :
  Client} : Approximation.Gaussian.Logarithm.Quotient.Requirement.Blocked
      client → Purelib.Approximation.Gaussian.Logarithm.Quotient.State client
  | .logarithm logState _ denominatorSlot cursor =>
      Approximation.Gaussian.Logarithm.Quotient.State.withLogSearching logState denominatorSlot cursor
  | .denominator denominatorState _ log cursor =>
      Approximation.Gaussian.Logarithm.Quotient.State.withDenominatorSearching log denominatorState cursor

/-- Read which child owns the retained blocked requirement. -/
@[expose] def path {client :
    Client}
  : Approximation.Gaussian.Logarithm.Quotient.Requirement.Blocked client → State.NodePath
  | .logarithm .. => .logarithm
  | .denominator .. => .denominator

/-- Evidence is indexed by the complete blocked request, including its exact node path and retained child state. -/
@[expose] def Evidence {client :
  Client} : Approximation.Gaussian.Logarithm.Quotient.Requirement.Blocked
      client → Type
  | .logarithm _ requirement _ _ => Requirement.Evidence requirement
  | .denominator _ requirement _ _ => Approximation.Gaussian.Division.Partial.Requirement.Evidence requirement

/-- Resume only the child named by the blocked request. The other child is retained definitionally and the round-robin
cursor advances once. -/
@[expose] def resume {client :
  Client} (blocked :
      Approximation.Gaussian.Logarithm.Quotient.Requirement.Blocked client)
    (evidence : Approximation.Gaussian.Logarithm.Quotient.Requirement.Blocked.Evidence blocked) :
      Purelib.Approximation.Gaussian.Logarithm.Quotient.State client :=
  match blocked with
  | .logarithm logState requirement denominatorSlot cursor =>
      let satisfied := Step.satisfy client.sourceInput client.argument
        client.source logState requirement evidence
      Approximation.Gaussian.Logarithm.Quotient.State.withLogReady logState satisfied.output satisfied.valid
          denominatorSlot
        (!cursor)
  | .denominator denominatorState requirement log cursor =>
      match requirement with
      | .candidateApartness =>
          Approximation.Gaussian.Logarithm.Quotient.State.withDenominatorReady log denominatorState evidence (!cursor)

end Blocked

/-- Construct an explicit manual denominator-apartness request at the current retained denominator state. Automatic
scheduling never fabricates this evidence and may instead keep refining. -/
@[expose] def requestDenominator {client :
  Client} (log : State.LogSlot client)
    (denominatorState : Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State client.denominator) (cursor :
      Bool) :
    Blocked client :=
  .denominator denominatorState .candidateApartness log cursor

/-- Resuming a logarithm request retains the denominator child exactly. -/
theorem resume_logarithm_preserves_denominator
  {client : Client}
    (logState : LogarithmState.State client.argument)
    (requirement : Approximation.Gaussian.Logarithm.Chart.Partial.Requirement client.sourceInput client.argument
      client.source logState)
    (denominatorSlot : State.DenominatorSlot client) (cursor : Bool)
    (evidence : Blocked.Evidence
      (.logarithm logState requirement denominatorSlot cursor)) :
    (Blocked.resume (.logarithm logState requirement
      denominatorSlot cursor)
      evidence).denominator = denominatorSlot := by
  cases requirement <;> rfl

/-- Resuming a denominator request retains the logarithm child exactly. -/
theorem resume_denominator_preserves_log {client :
  Client}
    (denominatorState : Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State client.denominator)
    (requirement : Approximation.Gaussian.Division.Partial.Requirement denominatorState)
    (logSlot : State.LogSlot client) (cursor : Bool)
    (evidence : Blocked.Evidence
      (.denominator denominatorState requirement logSlot cursor)) :
    (Blocked.resume (.denominator denominatorState requirement
      logSlot cursor)
      evidence).log = logSlot := by
  cases requirement
  rfl
end Purelib.Approximation.Gaussian.Logarithm.Quotient.Requirement

end
