module
public import Purelib.Control.FiniteRunner.Progress
import Purelib.Riemann.Integration.LegendreModularMonodromy
import Purelib.Approximation.Gaussian.Division.Partial.Preparation
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.State
public import Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation.FromSearch
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Process.Apart.Possible
import Purelib.Approximation.Gaussian.Process.Based
import Purelib.Approximation.Gaussian.Division.Prepared.Denominator

open Purelib

open Purelib.Approximation.Gaussian.Division.Partial

open Purelib.Approximation.Gaussian.Division

open Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition

open Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent.Refinement

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

namespace Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Step
open Purelib.Control.FiniteRunner.Progress (StepResultPayload)
open Purelib.Riemann.Integration.LegendreModularMonodromy (fractionalDenominator)

/-- One finite inspection either returns a directly consumable modular preparation or performs the canonical
generic-division refinement. -/
def StepResult (matrix :
  LinearAlgebra.Matrix.Basic.IntegralMatrix) (tau : Coherent.CoherentNamed)
    (state :
      Approximation.Gaussian.FractionalAction.Integral.Acquisition.State matrix tau) : Type 1 :=
  StepResultPayload
    (Approximation.Gaussian.Division.Prepared.DenominatorPreparation (fractionalDenominator matrix tau))
    (Approximation.Gaussian.FractionalAction.Integral.Acquisition.State matrix tau)
    (fun next => State.Progress state next)

/-- Inspect one retained fractional-denominator state and either prepare it or advance it.

A successful generic division preflight is transported to the exact fractional denominator. Otherwise the result retains
the next search state and its certified progress relation. -/
def step (matrix :
  LinearAlgebra.Matrix.Basic.IntegralMatrix) (tau : Coherent.CoherentNamed)
    (state :
      Approximation.Gaussian.FractionalAction.Integral.Acquisition.State matrix tau) :
      StepResult
        matrix tau state :=
  match Preparation.prepare
      (fractionalDenominator matrix tau) state with
  | .prepared evidence => .ready (FromSearch.preparationAt matrix tau state evidence)
  | .progressed next progress => .progressed next progress
end Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Step

end
