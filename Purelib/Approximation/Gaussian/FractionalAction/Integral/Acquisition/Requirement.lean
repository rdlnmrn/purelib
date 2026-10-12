module
public import Purelib.Approximation.Gaussian.Division.Partial.Requirement
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.State
public import Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Step
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation.FromSearch
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
import Purelib.Control.FiniteRunner.Progress
import Purelib.Riemann.Integration.LegendreModularMonodromy
meta import Mathlib.Tactic.Linter.Lint

open Purelib.LinearAlgebra.Matrix.Basic (IntegralMatrix)

open Purelib

open Purelib.Approximation.Gaussian.Division.Partial

open Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition

open Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation

open Purelib.Approximation.Gaussian.Name

open Purelib.LinearAlgebra.Matrix

section
@[expose] public section

/-!
# Retryable acquisition of Legendre fractional denominators

The generic division preflight is reused at the exact transformed denominator.
A successful retained-state search is converted to the generalized modular
preparation by carrying its based denominator, whole-ball apartness, and
operational equivalence to the original process.
-/

namespace Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition

/-- The exact manually satisfiable requirement at a retained search state. -/
abbrev Requirement {matrix :
  IntegralMatrix} {tau : Coherent.CoherentNamed}
    (state : State matrix tau) :=
  Approximation.Gaussian.Division.Partial.Requirement state

namespace Requirement

/-- Evidence remains indexed by that exact retained state. -/
abbrev Evidence {matrix :
  IntegralMatrix} {tau : Coherent.CoherentNamed}
    {state : State matrix tau} (requirement :
      Requirement state) :=
  Approximation.Gaussian.Division.Partial.Requirement.Evidence requirement

/-- Expose the unique candidate-apartness requirement without performing another refinement. -/
def currentRequirement {matrix :
  IntegralMatrix} {tau : Coherent.CoherentNamed}
    (state : State matrix tau) :
      Requirement state :=
  .candidateApartness

/-- Resume at exactly the state which requested the supplied based apartness. -/
def resume (matrix :
  IntegralMatrix) (tau : Coherent.CoherentNamed)
    (state : State matrix tau) (requirement :
      Requirement state)
    (evidence : Approximation.Gaussian.FractionalAction.Integral.Acquisition.Requirement.Evidence requirement) :
      Step.StepResult matrix tau state :=
  match requirement with
  | .candidateApartness => .ready (FromSearch.preparationAt matrix tau state evidence)

/-- The adapter inherits the generic preflight's empty exclusion family. -/
abbrev Exclusion {matrix :
  IntegralMatrix} {tau : Coherent.CoherentNamed}
    (state : State matrix tau) :=
  Approximation.Gaussian.Division.Partial.Requirement.Exclusion state

/-- The fractional-denominator preflight has no exclusion constructor. -/
theorem exclusion_impossible
  {matrix : IntegralMatrix} {tau : Coherent.CoherentNamed}
    {state : State matrix tau} (excluded :
      Approximation.Gaussian.FractionalAction.Integral.Acquisition.Requirement.Exclusion state) : False := by
  exact nomatch excluded

/-- Supplying the current apartness requirement returns the corresponding prepared denominator immediately. -/
@[simp] theorem resume_is_ready
  (matrix : IntegralMatrix)
    (tau : Coherent.CoherentNamed) (state : State matrix tau)
    (evidence : Approximation.Gaussian.FractionalAction.Integral.Acquisition.Requirement.Evidence
      (Approximation.Gaussian.FractionalAction.Integral.Acquisition.Requirement.currentRequirement state)) :
    Approximation.Gaussian.FractionalAction.Integral.Acquisition.Requirement.resume matrix tau state
      (Approximation.Gaussian.FractionalAction.Integral.Acquisition.Requirement.currentRequirement state) evidence =
      .ready (FromSearch.preparationAt matrix tau state evidence) := rfl

end Requirement

end Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition

end
