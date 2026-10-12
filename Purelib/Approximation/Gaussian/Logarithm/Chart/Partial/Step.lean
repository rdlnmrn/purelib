module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored
public import Purelib.Approximation.Gaussian.Logarithm.Chart.Partial.Ready
public import Purelib.Approximation.Gaussian.Logarithm.Chart.Partial.Requirement
import Purelib.Approximation.Gaussian.Logarithm.Chart.Safety
import Purelib.Approximation.Gaussian.Logarithm.Chart.Transport
public import Purelib.Approximation.Gaussian.Logarithm.Chart.Transport.Safety
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.LogarithmState
import Init.Prelude
import Purelib.Approximation.Gaussian.Logarithm.Chart.Basic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent.Based
import Purelib.Approximation.Gaussian.Process.Basic

open Purelib.Approximation.Gaussian.Logarithm.Chart.Partial (Ready)

open Purelib

open Purelib.Approximation.Gaussian.Logarithm.Chart

open Purelib.Approximation.Gaussian.Logarithm.Chart.Partial

open Purelib.Approximation.Gaussian.Logarithm.Chart.Transport

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

namespace Purelib.Approximation.Gaussian.Logarithm.Chart.Partial.Step

set_option genInjectivity false in
/-- One operation-specific finite step. `blocked` exposes an exact typed requirement at the unchanged state. -/
inductive StepResult
    (sourceInput targetInput : Coherent.CoherentNamed)
    (source : Anchored.AnchoredChart sourceInput)
    (state : LogarithmState.State targetInput) : Type 2
  /-- Return the anchored output together with its readiness certificate at the exact retained state. -/ | ready (output
    : Anchored.AnchoredChart (LogarithmState.preparedTarget state))
      (valid : Ready sourceInput targetInput source state output)
  /-- Retain the next state and the genuine canonical refinement that reaches it. -/ | progressed (next :
    LogarithmState.State targetInput) (progress : LogarithmState.Progress state next)
  /-- Retain the exact typed requirement that must be supplied before readiness. -/ | blocked (requirement :
    Approximation.Gaussian.Logarithm.Chart.Partial.Requirement sourceInput targetInput source state)

constructive_injectivity StepResult

/-- Assemble a ready result from a complete safe overlap extension. -/
@[expose] def readyOfExtension
    {sourceInput targetInput : Coherent.CoherentNamed}
    {source : Anchored.AnchoredChart sourceInput}
    {state : LogarithmState.State targetInput}
    (extension : Transport.SafeOverlapExtension sourceInput (LogarithmState.preparedTarget state) source) :
    StepResult sourceInput targetInput source state :=
  .ready (extension.transport source)
    { extension := extension, output_eq := rfl }

set_option genInjectivity false in
/-- The ordinary ready branch computed by satisfying one exact requirement. This package is convenient for a parent
dependency scheduler: it contains no spurious progressed or blocked alternatives. -/
structure Satisfied
    (sourceInput targetInput : Coherent.CoherentNamed)
    (source : Anchored.AnchoredChart sourceInput)
    (state : LogarithmState.State targetInput) : Type 2 where
  /-- The anchored output indexed by the exact prepared target state. -/ output : Anchored.AnchoredChart
    (LogarithmState.preparedTarget state)
  /-- The output is exactly the safe transport certified at the retained state. -/
  valid : Ready sourceInput
    targetInput source state output

constructive_injectivity Satisfied

/-- Satisfy one exact typed requirement and return the resulting branch directly. -/
@[expose] def satisfy
    (sourceInput targetInput : Coherent.CoherentNamed)
    (source : Anchored.AnchoredChart sourceInput)
    (state : LogarithmState.State targetInput)
    (requirement : Approximation.Gaussian.Logarithm.Chart.Partial.Requirement sourceInput targetInput source state)
    (evidence : Requirement.Evidence requirement) :
    Satisfied sourceInput targetInput source state :=
  match requirement with
  | .overlap certificate =>
      let extension :=
        Safety.extensionOfBased sourceInput targetInput source
          state.source certificate evidence
      { output := extension.transport source
        valid := { extension := extension, output_eq := rfl } }
  | .completeExtension =>
      { output := evidence.transport source
        valid := { extension := evidence, output_eq := rfl } }

/-- Inspect one target ball. Failure performs exactly one canonical refinement. Success exposes the semantic overlap
evidence which rational ball arithmetic cannot manufacture for unrelated `Possible` predicates. -/
@[expose] def step
    (sourceInput targetInput : Coherent.CoherentNamed)
    (source : Anchored.AnchoredChart sourceInput)
    (state : LogarithmState.State targetInput) :
    StepResult sourceInput targetInput source state :=
  if certificate : Safety.Certificate source.chart.factor
      (targetInput.name.process.ball state.source) state.nextIndex then
    .blocked (.overlap certificate)
  else
    .progressed state.advance (.refined state)

/-- A successful finite chart-safety check returns an overlap requirement retaining that safety certificate. -/
theorem step_is_blocked_of_safe
    (sourceInput targetInput : Coherent.CoherentNamed)
    (source : Anchored.AnchoredChart sourceInput)
    (state : LogarithmState.State targetInput)
    (certificate : Safety.Certificate source.chart.factor
      (targetInput.name.process.ball state.source) state.nextIndex) :
    ∃ discovered : Safety.Certificate source.chart.factor
        (targetInput.name.process.ball state.source) state.nextIndex,
      step sourceInput targetInput source state =
        .blocked (.overlap discovered) := by
  rw [step, dif_pos certificate]
  exact ⟨certificate, rfl⟩

/-- Failure of the finite chart-safety predicate performs exactly the canonical refinement step. -/
theorem step_eq_progressed_of_not_safe
    (sourceInput targetInput : Coherent.CoherentNamed)
    (source : Anchored.AnchoredChart sourceInput)
    (state : LogarithmState.State targetInput)
    (notSafe : ¬ Safety.Certificate source.chart.factor
      (targetInput.name.process.ball state.source) state.nextIndex) :
    step sourceInput targetInput source state =
      .progressed state.advance (.refined state) := by
  rw [step, dif_neg notSafe]

/-- Satisfy one exact typed requirement. An overlap witness is combined with the retained safety proof; a complete
extension is used directly. -/
@[expose] def resume
    (sourceInput targetInput : Coherent.CoherentNamed)
    (source : Anchored.AnchoredChart sourceInput)
    (state : LogarithmState.State targetInput)
    (requirement : Approximation.Gaussian.Logarithm.Chart.Partial.Requirement sourceInput targetInput source state)
    (evidence : Requirement.Evidence requirement) :
    StepResult sourceInput targetInput source state :=
  let satisfied := satisfy sourceInput targetInput source state
    requirement evidence
  .ready satisfied.output satisfied.valid

/-- Supplying evidence for the retained requirement produces a certified ready anchored output. -/
theorem resume_is_ready
    (sourceInput targetInput : Coherent.CoherentNamed)
    (source : Anchored.AnchoredChart sourceInput)
    (state : LogarithmState.State targetInput)
    (requirement : Approximation.Gaussian.Logarithm.Chart.Partial.Requirement sourceInput targetInput source state)
    (evidence : Requirement.Evidence requirement) :
    ∃ output : Anchored.AnchoredChart (LogarithmState.preparedTarget state),
      ∃ valid : Ready sourceInput targetInput source state output,
        resume sourceInput targetInput source state requirement
          evidence =
          .ready output valid := by
  cases requirement with
  | overlap certificate => exact ⟨_, _, rfl⟩
  | completeExtension => exact ⟨_, _, rfl⟩
end Purelib.Approximation.Gaussian.Logarithm.Chart.Partial.Step

end
