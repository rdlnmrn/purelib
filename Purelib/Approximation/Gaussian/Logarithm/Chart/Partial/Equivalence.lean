module
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Exponential.Progressive.Range.Name
import Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored
public import Purelib.Approximation.Gaussian.Logarithm.Chart.Partial.Ready
public import Purelib.Approximation.Gaussian.Logarithm.Chart.Transport.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.LogarithmState
import Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored.Inverse
import Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored.Output
import Purelib.Approximation.Gaussian.Logarithm.Chart.Transport

open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Logarithm.Chart.Partial (Ready)

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian

open Purelib.Approximation.Gaussian.Logarithm.Chart

open Purelib.Approximation.Gaussian.Logarithm.Chart.Partial

open Purelib.Approximation.Gaussian.Logarithm.Chart.Transport

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent.Refinement

section
@[expose] public section

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

namespace Purelib.Approximation.Gaussian.Logarithm.Chart.Partial.Equivalence

/-! ## Operational laws of readiness -/

/-- Any two ready branches obtained from the fixed source anchor are operationally equivalent, independently of their
finite safety and overlap schedules. -/
def ready_respects
    {sourceInput targetInput : Coherent.CoherentNamed}
    {source : Anchored.AnchoredChart sourceInput}
    {firstState secondState : LogarithmState.State targetInput}
    {firstOutput : Anchored.AnchoredChart (LogarithmState.preparedTarget firstState)}
    {secondOutput : Anchored.AnchoredChart (LogarithmState.preparedTarget secondState)}
    (firstReady : Ready sourceInput targetInput source firstState
        firstOutput)
    (secondReady : Ready sourceInput targetInput source secondState
        secondOutput) :
    NamedEquivalent firstOutput.output.name secondOutput.output.name := by
  rcases firstReady with ⟨firstExtension, rfl⟩
  rcases secondReady with ⟨secondExtension, rfl⟩
  exact Congruence.transportedOutput_respects source
    firstExtension secondExtension
    (LogarithmState.preparedTargetsEquivalent firstState secondState)

/-- Reachability documents the execution relationship; the stronger schedule-free theorem supplies semantic stability.
-/
def ready_stable_after_progress
    {sourceInput targetInput : Coherent.CoherentNamed}
    {source : Anchored.AnchoredChart sourceInput}
    {firstState laterState : LogarithmState.State targetInput}
    (_reachable : LogarithmState.Reachable firstState laterState)
    {firstOutput : Anchored.AnchoredChart (LogarithmState.preparedTarget firstState)}
    {laterOutput : Anchored.AnchoredChart (LogarithmState.preparedTarget laterState)}
    (firstReady : Ready sourceInput targetInput source firstState
        firstOutput)
    (laterReady : Ready sourceInput targetInput source laterState
        laterOutput) :
    NamedEquivalent firstOutput.output.name laterOutput.output.name :=
  ready_respects firstReady laterReady

/-- Every ready branch has the existing finite exponential inverse. -/
def ready_exponential_inverse
    {sourceInput targetInput : Coherent.CoherentNamed}
    {source : Anchored.AnchoredChart sourceInput}
    {state : LogarithmState.State targetInput}
    {output : Anchored.AnchoredChart (LogarithmState.preparedTarget state)}
    (_ready : Ready sourceInput targetInput source state output) :
    NamedEquivalent
      (Exponential.Progressive.Range.Name.named output.output.name)
      (LogarithmState.preparedTarget state).name :=
  output.exponential_inverse
end Purelib.Approximation.Gaussian.Logarithm.Chart.Partial.Equivalence

end
