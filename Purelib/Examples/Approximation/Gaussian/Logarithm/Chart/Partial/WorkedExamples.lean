module
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored.Output
import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Approximation.Gaussian.Logarithm.Chart.Anchor.Unit
import Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored
public import Purelib.Approximation.Gaussian.Logarithm.Chart.Partial.Equivalence
import Purelib.Approximation.Gaussian.Logarithm.Chart.Partial.Ready
import Purelib.Approximation.Gaussian.Logarithm.Chart.Partial.Requirement
public import Purelib.Approximation.Gaussian.Logarithm.Chart.Partial.Run
import Purelib.Approximation.Gaussian.Logarithm.Chart.Partial.Step
import Purelib.Approximation.Gaussian.Logarithm.Chart.Safety
import Purelib.Approximation.Gaussian.Logarithm.Chart.Transport
import Purelib.Approximation.Gaussian.Logarithm.Chart.Transport.Safety
import Purelib.Approximation.Gaussian.Name.Coherent.Overlap
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.LogarithmState
public import Purelib.Examples.Approximation.Gaussian.Division.Partial.DelayedOne
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Logarithm.Chart.Basic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Process.Basic

@[expose] public section

/-!
# Executable examples for retryable anchored-logarithm preflight

The target reuses the deliberately delayed exact-one process from division
preflight.  Its initial ball is too coarse for complex-log chart safety.  One
finite refinement exposes an exact safe ball, after which the generic builder
blocks on the precise semantic overlap witness.  Supplying that witness
transports the separately packaged exact-one anchor to a genuinely different
based process state type.
-/

namespace Purelib.Examples.Approximation.Gaussian.Logarithm.Chart.Partial.WorkedExamples

open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)

open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name
open Purelib.Examples.Approximation.Gaussian
open Purelib.Examples.Approximation.Gaussian.Division
open Purelib.Approximation.Gaussian.Name.Coherent.Refinement

/-- The exact coherent name of one used as logarithm anchor input. -/
def sourceInput :
  CoherentNamed := Logarithm.Chart.Anchor.Unit.exactOneInput

/-- The original anchored logarithm chart at exact one. -/
def sourceAnchor :
  Logarithm.Chart.Anchored.AnchoredChart sourceInput :=
  Logarithm.Chart.Anchor.Unit.exactOneAnchor

/-- The delayed coherent name of one used as logarithm transport target. -/
def targetInput :
  CoherentNamed :=
  Partial.DelayedOne.delayedOne

/-- The original initial logarithm-refinement state of the delayed target. -/
def initial : LogarithmState.State
  targetInput := LogarithmState.State.initial
  targetInput

/-- The delayed target's state after one retained refinement. -/
def refined : LogarithmState.State
  targetInput := initial.advance

/-- The delayed target's state after two retained refinements. -/
def refinedAgain :
  LogarithmState.State targetInput :=
  refined.advance

/-- The initial target ball fails the original logarithm chart-safety predicate. -/
theorem initial_not_safe :
    ¬ Logarithm.Chart.Safety.Certificate sourceAnchor.chart.factor
      (targetInput.name.process.ball
        initial.source) initial.nextIndex
        := by
  decide

/-- The first partial logarithm step retains a refinement transition. -/
theorem first_step_progresses :
    Logarithm.Chart.Partial.Step.step sourceInput
      targetInput sourceAnchor
      initial =
      .progressed refined (.refined
        initial) := by
  exact Logarithm.Chart.Partial.Step.step_eq_progressed_of_not_safe sourceInput
    targetInput sourceAnchor
    initial initial_not_safe

/-- The once-refined target satisfies the original chart-safety certificate. -/
theorem refinedSafety :
    Logarithm.Chart.Safety.Certificate sourceAnchor.chart.factor
      (targetInput.name.process.ball
        refined.source) refined.nextIndex
        := by
  decide

/-- After refinement the partial logarithm step requests an overlap witness.

Safety alone yields the exact retained overlap requirement rather than a ready chart transport. -/
theorem
  second_step_blocks_for_overlap :
    Logarithm.Chart.Partial.Step.step sourceInput
      targetInput sourceAnchor
      refined =
      .blocked (.overlap refinedSafety) := by
  rw [Logarithm.Chart.Partial.Step.step, dif_pos refinedSafety]

/-- The common possible value one witnesses overlap with the once-refined target. -/
def refinedOverlap :
    Coherent.Overlap.OverlapWitness sourceInput (LogarithmState.preparedTarget
      refined) where
  point := 1
  left_possible := rfl
  right_possible := rfl

/-- The overlap requirement retaining the once-refined safety certificate. -/
def refinedRequirement :
    Approximation.Gaussian.Logarithm.Chart.Partial.Requirement sourceInput
      targetInput sourceAnchor
      refined :=
  .overlap refinedSafety

/-- The safe original-chart extension to the once-refined target.

Uses the retained refined source state and the actual common-point overlap witness. -/
def refinedExtension :
    Logarithm.Chart.Transport.SafeOverlapExtension sourceInput
      (LogarithmState.preparedTarget refined)
      sourceAnchor :=
  Logarithm.Chart.Transport.Safety.extensionOfBased sourceInput
    targetInput sourceAnchor
    refined.source refinedSafety
      refinedOverlap

/-- The anchored chart transported through the once-refined safe extension. -/
def refinedOutput :
  Logarithm.Chart.Anchored.AnchoredChart (LogarithmState.preparedTarget refined)
  :=
  refinedExtension.transport sourceAnchor

/-- Readiness certificate retaining the once-refined extension and its exact output. -/
def refinedReady :
    Approximation.Gaussian.Logarithm.Chart.Partial.Ready sourceInput
      targetInput sourceAnchor
      refined refinedOutput where
  extension := refinedExtension
  output_eq := rfl

/-- Supplying the retained overlap witness resumes to the exact ready chart. -/
theorem resume_overlap_is_ready :
    Logarithm.Chart.Partial.Step.resume sourceInput
      targetInput sourceAnchor
      refined refinedRequirement
      refinedOverlap = .ready
        refinedOutput refinedReady := by
  rfl

/-- The expected one-step result: refinement followed by budget exhaustion. -/
def oneFuelExpected :
    Logarithm.Chart.Partial.Run.RunResult sourceInput
      targetInput sourceAnchor
      initial :=
  Logarithm.Chart.Partial.Run.prefixResult (.refined initial)
    (Logarithm.Chart.Partial.Run.exhaustedResult sourceInput
      targetInput sourceAnchor
      refined)

/-- The original one-step partial logarithm attempt. -/
def oneFuelRun :
    Logarithm.Chart.Partial.Run.RunResult sourceInput
      targetInput sourceAnchor
      initial :=
  Logarithm.Chart.Partial.Run.attempt sourceInput
    targetInput sourceAnchor
    initial 1

/-- The expected two-step result: refinement followed by an overlap requirement. -/
def twoFuelExpected :
    Logarithm.Chart.Partial.Run.RunResult sourceInput
      targetInput sourceAnchor
      initial :=
  Logarithm.Chart.Partial.Run.prefixResult (.refined initial)
    (Logarithm.Chart.Partial.Run.blockedResult sourceInput
      targetInput sourceAnchor
      refined
      (.overlap refinedSafety))

/-- The original two-step partial logarithm attempt. -/
def twoFuelRun :
    Logarithm.Chart.Partial.Run.RunResult sourceInput
      targetInput sourceAnchor
      initial :=
  Logarithm.Chart.Partial.Run.attempt sourceInput
    targetInput sourceAnchor
    initial 2

/-- The twice-refined target retains the chart-safety certificate. -/
theorem refinedAgainSafety :
    Logarithm.Chart.Safety.Certificate sourceAnchor.chart.factor
      (targetInput.name.process.ball
        refinedAgain.source)
      refinedAgain.nextIndex := by
  decide

/-- The common possible value one witnesses overlap after two refinements. -/
def refinedAgainOverlap :
    Coherent.Overlap.OverlapWitness sourceInput (LogarithmState.preparedTarget
      refinedAgain) where
  point := 1
  left_possible := rfl
  right_possible := rfl

/-- The safe original-chart extension to the twice-refined target.

Keeps its exact second source state, safety certificate and common-point overlap witness. -/
def refinedAgainExtension :
    Logarithm.Chart.Transport.SafeOverlapExtension sourceInput
      (LogarithmState.preparedTarget refinedAgain)
      sourceAnchor :=
  Logarithm.Chart.Transport.Safety.extensionOfBased sourceInput
    targetInput sourceAnchor
    refinedAgain.source refinedAgainSafety
      refinedAgainOverlap

/-- The anchored chart transported through the twice-refined safe extension. -/
def refinedAgainOutput :
  Logarithm.Chart.Anchored.AnchoredChart (LogarithmState.preparedTarget
  refinedAgain) :=
  refinedAgainExtension.transport
    sourceAnchor

/-- Readiness certificate for the exact twice-refined transported chart. -/
def refinedAgainReady :
    Approximation.Gaussian.Logarithm.Chart.Partial.Ready sourceInput
      targetInput sourceAnchor
      refinedAgain
      refinedAgainOutput where
  extension := refinedAgainExtension
  output_eq := rfl

/-- The one- and two-refinement logarithm outputs are operationally equivalent.

Compares the two original ready transports without replacing either retained output name. -/
def different_schedules_equivalent
  :
    Equivalence.NamedEquivalent refinedOutput.output.name
      refinedAgainOutput.output.name :=
  Logarithm.Chart.Partial.Equivalence.ready_respects refinedReady
    refinedAgainReady

end Purelib.Examples.Approximation.Gaussian.Logarithm.Chart.Partial.WorkedExamples

end
