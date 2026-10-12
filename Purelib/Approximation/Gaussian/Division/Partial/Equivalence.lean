module
import Purelib.Approximation.Gaussian.Division.Partial.Preparation
public import Purelib.Approximation.Gaussian.Division.Partial.Ready
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Apart
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Based
public import Purelib.Approximation.Gaussian.Name.Coherent.Division.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
import Purelib.Approximation.Gaussian.Process.Apart.Possible
import Purelib.Approximation.Gaussian.Process.Based
import Purelib.Approximation.Gaussian.Name.Apart
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Process.Coherence.Division

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Division.Partial

open Purelib.Approximation.Gaussian.Equivalence

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent

open Purelib.Approximation.Gaussian.Name.Coherent.Division

open Purelib.Approximation.Gaussian.Name.Coherent.Refinement

open Purelib.Approximation.Gaussian.Process.Apart

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

namespace Purelib.Approximation.Gaussian.Division.Partial.Equivalence

/-! ## Operational laws of readiness -/

/-- The based and apartified denominator returned by preflight has the same finite operational value as the original
coherent denominator. -/
def preparedDenominatorEquivalent {denominator :
  Coherent.CoherentNamed}
    (state : Approximation.Gaussian.Name.Coherent.Refinement.State denominator)
    (evidence : Possible.PossibleApart
      (Gaussian.Process.Based.based denominator.name.process state.source)) :
    Gaussian.Equivalence.NamedEquivalent denominator.name (Preparation.preparedDenominator state evidence).name :=
  NamedEquivalent.trans
    (CoherentNamed.basedEquivalent
      denominator state.source)
    (CoherentNamed.apartifyEquivalent
      (Preparation.basedDenominator state) evidence)

/-- Any two ready quotients of the fixed inputs are operationally equivalent, regardless of the finite states or
evidence schedules at which readiness was obtained. -/
def ready_respects {numerator denominator :
  Coherent.CoherentNamed}
    {firstState secondState : Approximation.Gaussian.Name.Coherent.Refinement.State denominator}
    {firstOutput secondOutput : Coherent.CoherentNamed}
    (firstReady : Approximation.Gaussian.Division.Partial.Ready numerator denominator firstState firstOutput)
    (secondReady : Approximation.Gaussian.Division.Partial.Ready numerator denominator secondState secondOutput) :
    Gaussian.Equivalence.NamedEquivalent firstOutput.name secondOutput.name := by
  rcases firstReady with ⟨firstEvidence, rfl⟩
  rcases secondReady with ⟨secondEvidence, rfl⟩
  let firstDenominator := Preparation.preparedDenominator firstState firstEvidence
  let secondDenominator := Preparation.preparedDenominator secondState secondEvidence
  have denominatorEquivalent : Gaussian.Equivalence.NamedEquivalent
      firstDenominator.name secondDenominator.name :=
    NamedEquivalent.trans
      (NamedEquivalent.symm
        (preparedDenominatorEquivalent firstState firstEvidence))
      (preparedDenominatorEquivalent secondState secondEvidence)
  simpa only [Ready.readyName, firstDenominator, secondDenominator,
    CoherentNamed.div] using
    Equivalence.coherentDiv_respects
      numerator numerator firstDenominator secondDenominator
      (Preparation.preparedApart firstState firstEvidence)
      (Preparation.preparedApart secondState secondEvidence)
      (NamedEquivalent.refl numerator.name)
      denominatorEquivalent

/-- In particular, a ready output remains semantically stable against any later reachable success. Reachability is
retained to document the execution relationship; operational stability follows from the stronger schedule-free ready
congruence above. -/
def ready_stable_after_progress {numerator
  denominator : Coherent.CoherentNamed}
    {firstState laterState : Approximation.Gaussian.Name.Coherent.Refinement.State denominator}
    (_reachable : State.Reachable firstState laterState)
    {firstOutput laterOutput : Coherent.CoherentNamed}
    (firstReady : Approximation.Gaussian.Division.Partial.Ready numerator denominator firstState firstOutput)
    (laterReady : Approximation.Gaussian.Division.Partial.Ready numerator denominator laterState laterOutput) :
    Gaussian.Equivalence.NamedEquivalent firstOutput.name laterOutput.name :=
  ready_respects firstReady laterReady
end Purelib.Approximation.Gaussian.Division.Partial.Equivalence

end
