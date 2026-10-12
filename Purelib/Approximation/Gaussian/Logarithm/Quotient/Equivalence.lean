module
public import Purelib.Approximation.Gaussian.Division.Partial.Equivalence
import Purelib.Approximation.Gaussian.Division.Partial.Preparation
import Purelib.Approximation.Gaussian.Division.Partial.Ready
import Purelib.Approximation.Gaussian.Equivalence
public import Purelib.Approximation.Gaussian.Logarithm.Chart.Partial.Equivalence
import Purelib.Approximation.Gaussian.Logarithm.Quotient.Client
public import Purelib.Approximation.Gaussian.Logarithm.Quotient.Ready
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Division.Equivalence
import Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored
import Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored.Output
import Purelib.Approximation.Gaussian.Logarithm.Chart.Partial.Ready
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.LogarithmState
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
import Purelib.Approximation.Gaussian.Process.Apart.Possible
import Purelib.Approximation.Gaussian.Process.Based

open Purelib.Approximation.Gaussian.Logarithm.Quotient (Ready)

open Purelib.Approximation

open Purelib.Approximation.Gaussian

open Purelib.Approximation.Gaussian.Equivalence

open Purelib.Approximation.Gaussian.Logarithm.Chart.Partial

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent.Division

section
@[expose] public section

/-!
# A finite dependency scheduler for `log(1 + z) / z`

This is the first composition client for retryable partial operations.  It
coordinates one fixed anchored-logarithm branch with denominator-only
apartness preparation.  A scheduler tick performs at most one child action,
and a blocked result retains the exact child state and typed requirement.

The client deliberately stays at the coherent-name level.  It neither fills
the removable value at zero nor claims a global logarithm branch.
-/

namespace Purelib.Approximation.Gaussian.Logarithm.Quotient.Equivalence

/-! ## Ready-output laws -/

/-- Any two successful schedules for the same fixed source anchor and input produce operationally equivalent quotient
names. -/
def ready_respects {client :
  Approximation.Gaussian.Logarithm.Quotient.Client} {firstOutput secondOutput : Coherent.CoherentNamed}
    (first : Ready client firstOutput) (second :
        Ready client
      secondOutput) :
    Gaussian.Equivalence.NamedEquivalent firstOutput.name secondOutput.name := by
  rcases first with
    ⟨firstLogState, firstLogOutput, firstLogValid,
      firstDenominatorState, firstEvidence, rfl⟩
  rcases second with
    ⟨secondLogState, secondLogOutput, secondLogValid,
      secondDenominatorState, secondEvidence, rfl⟩
  let firstDenominator :=
    Division.Partial.Preparation.preparedDenominator
      firstDenominatorState firstEvidence
  let secondDenominator :=
    Division.Partial.Preparation.preparedDenominator
      secondDenominatorState secondEvidence
  have numeratorEquivalent : Gaussian.Equivalence.NamedEquivalent
      firstLogOutput.output.name secondLogOutput.output.name :=
    Chart.Partial.Equivalence.ready_respects
      firstLogValid secondLogValid
  have denominatorEquivalent : Gaussian.Equivalence.NamedEquivalent
      firstDenominator.name secondDenominator.name :=
    NamedEquivalent.trans
      (NamedEquivalent.symm
        (Division.Partial.Equivalence.preparedDenominatorEquivalent
          firstDenominatorState firstEvidence))
      (Division.Partial.Equivalence.preparedDenominatorEquivalent
        secondDenominatorState secondEvidence)
  simpa only [Ready.readyName, Division.Partial.Ready.readyName,
    firstDenominator, secondDenominator,
    Coherent.CoherentNamed.div] using
    Equivalence.coherentDiv_respects
      firstLogOutput.output secondLogOutput.output
      firstDenominator secondDenominator
      (Division.Partial.Preparation.preparedApart
        firstDenominatorState firstEvidence)
      (Division.Partial.Preparation.preparedApart
        secondDenominatorState secondEvidence)
      numeratorEquivalent denominatorEquivalent
end Purelib.Approximation.Gaussian.Logarithm.Quotient.Equivalence

end
