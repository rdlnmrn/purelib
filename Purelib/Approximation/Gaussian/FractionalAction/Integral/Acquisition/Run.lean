module
public import Purelib.Control.FiniteRunner.Reachable
import Purelib.Riemann.Integration.LegendreModularMonodromy
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.State
public import Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Step
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.LinearAlgebra.Matrix.Basic
import Init.Prelude
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
import Purelib.Control.FiniteRunner.Progress
import Purelib.Approximation.Gaussian.Division.Prepared.Denominator

open Purelib.LinearAlgebra.Matrix.Basic (IntegralMatrix)

open Purelib

open Purelib.Approximation.Gaussian.Division

open Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition

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

namespace Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Run
open Purelib.Control.FiniteRunner.Reachable (RunResultPayload)
open Purelib.Riemann.Integration.LegendreModularMonodromy (fractionalDenominator)

/-- Result of a caller-bounded preparation run. Exhaustion retains the exact state and means only that the finite fuel
ended. -/
def RunResult (matrix :
  IntegralMatrix) (tau : Coherent.CoherentNamed)
    (start : Approximation.Gaussian.FractionalAction.Integral.Acquisition.State matrix tau) (fuel : Nat) : Type 1 :=
  RunResultPayload
    (Approximation.Gaussian.Division.Prepared.DenominatorPreparation (fractionalDenominator matrix tau))
    (Approximation.Gaussian.FractionalAction.Integral.Acquisition.State matrix tau) (fun final => State.Reachable start
        final) fuel

/-- Structurally recursive bounded acquisition. Exactly one unit of fuel is consumed by each certified progress step. -/
def attempt (matrix :
  IntegralMatrix) (tau : Coherent.CoherentNamed)
    (start : Approximation.Gaussian.FractionalAction.Integral.Acquisition.State matrix tau) :
    (fuel : Nat) -> RunResult matrix tau start fuel
  | 0 => .exhausted start (.refl start)
  | fuel + 1 =>
      match Step.step matrix tau start with
      | .ready preparation => .ready start (.refl start) preparation
      | .progressed next progress =>
          match attempt matrix tau next fuel
            with
          | .ready final reachable preparation =>
              .ready final (.tail progress reachable) preparation
          | .exhausted final reachable =>
              .exhausted final (.tail progress reachable)

/-- Zero acquisition fuel preserves the exact initial state and its reflexive reachability witness. -/
@[simp] theorem attempt_zero (matrix :
  IntegralMatrix) (tau : Coherent.CoherentNamed)
    (state : Approximation.Gaussian.FractionalAction.Integral.Acquisition.State matrix tau) :
    attempt matrix tau state 0 = .exhausted state
      (.refl state) := rfl
end Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Run

end
