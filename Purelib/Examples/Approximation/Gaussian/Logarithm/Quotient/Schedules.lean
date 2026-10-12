module
import Purelib.Approximation.Gaussian.Equivalence
public import Purelib.Approximation.Gaussian.Logarithm.Quotient.Equivalence
import Purelib.Approximation.Gaussian.Logarithm.Quotient.Ready
import Purelib.Approximation.Gaussian.Logarithm.Quotient.Requirement
import Purelib.Approximation.Gaussian.Logarithm.Quotient.State
import Purelib.Approximation.Gaussian.Logarithm.Quotient.Step
import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Examples.Approximation.Gaussian.Logarithm.Quotient.WorkedExamples

@[expose] public section

/-!
# Executable schedules for `log(1 + z) / z`

The concrete input is the exact rational `z = 1/2`, while the logarithm source
anchor is built independently at `3/2`.  One schedule acquires logarithm
overlap first and denominator apartness second; another supplies denominator
apartness first.  Both finish with ordinary operationally equivalent quotient
CCLs.
-/

namespace Purelib.Examples.Approximation.Gaussian.Logarithm.Quotient.Schedules

open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Examples.Approximation.Gaussian.Logarithm

open Purelib.Approximation.Gaussian
open Purelib.Examples.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name

/-! ## A different evidence schedule -/

/-- A retained denominator requirement with logarithm search still pending. -/
def denominatorBlockedFirst :
  Logarithm.Quotient.Requirement.Blocked Quotient.WorkedExamples.client :=
  Logarithm.Quotient.Requirement.requestDenominator (.searching Quotient.WorkedExamples.logState)
    Quotient.WorkedExamples.denominatorState false

/-- The original apartness witness satisfies the denominator-first requirement. -/
def denominatorEvidenceFirst :
  Logarithm.Quotient.Requirement.Blocked.Evidence denominatorBlockedFirst :=
  Quotient.WorkedExamples.denominatorEvidence

/-- The joint state resumed with denominator evidence before logarithm overlap. -/
def afterDenominatorFirst :
  Approximation.Gaussian.Logarithm.Quotient.State Quotient.WorkedExamples.client :=
  denominatorBlockedFirst.resume denominatorEvidenceFirst

/-- The retained logarithm-overlap requirement with the denominator already ready. -/
def logBlockedSecond :
  Logarithm.Quotient.Requirement.Blocked Quotient.WorkedExamples.client :=
  .logarithm Quotient.WorkedExamples.logState Quotient.WorkedExamples.logRequirement (.ready
    Quotient.WorkedExamples.denominatorState
    Quotient.WorkedExamples.denominatorEvidence) true

/-- The denominator-first schedule resumed with the original logarithm overlap. -/
def afterBothSecond :
  Approximation.Gaussian.Logarithm.Quotient.State Quotient.WorkedExamples.client :=
  logBlockedSecond.resume Quotient.WorkedExamples.logOverlap

/-- The actual joint-search step after denominator-first resumption. -/
def denominatorFirstStep :
  Logarithm.Quotient.Step.StepResult Quotient.WorkedExamples.client
  afterDenominatorFirst :=
  Logarithm.Quotient.Step.step Quotient.WorkedExamples.client
    afterDenominatorFirst

/-- The expected logarithm-overlap obstruction after preparing the denominator. -/
def denominatorFirstStepExpected :
  Logarithm.Quotient.Step.StepResult Quotient.WorkedExamples.client
  afterDenominatorFirst :=
  .blocked logBlockedSecond rfl

/-- The denominator-first schedule reaches an actual ready quotient output.

Uses the exact retained overlap and denominator witnesses without replacing either search state. -/
theorem denominator_first_finishes :
    ∃ output : CoherentNamed, ∃ valid : Approximation.Gaussian.Logarithm.Quotient.Ready
        Quotient.WorkedExamples.client
      output,
      Logarithm.Quotient.Step.step Quotient.WorkedExamples.client afterBothSecond
        = .ready output valid := by
  simp only [afterBothSecond, logBlockedSecond,
    Logarithm.Quotient.Requirement.Blocked.resume]
  exact ⟨_, _, rfl⟩

/-- Ready outputs of the same retained client are operationally equivalent.

Compares the original names from any two completed schedules using their exact readiness certificates. -/
def schedules_equivalent
    {firstOutput secondOutput : CoherentNamed}
    (firstReady : Approximation.Gaussian.Logarithm.Quotient.Ready Quotient.WorkedExamples.client firstOutput)
    (secondReady : Approximation.Gaussian.Logarithm.Quotient.Ready Quotient.WorkedExamples.client
        secondOutput) :
    Equivalence.NamedEquivalent
      firstOutput.name secondOutput.name :=
  Logarithm.Quotient.Equivalence.ready_respects firstReady secondReady

end Purelib.Examples.Approximation.Gaussian.Logarithm.Quotient.Schedules

end
