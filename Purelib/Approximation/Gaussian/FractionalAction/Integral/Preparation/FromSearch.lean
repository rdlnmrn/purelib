module
import Purelib.Approximation.Gaussian.Division.Partial.Equivalence
import Purelib.Approximation.Gaussian.Division.Partial.Preparation
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
public import Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.State
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Process.Apart.Possible
import Purelib.Approximation.Gaussian.Process.Based
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.Riemann.Integration.LegendreModularMonodromy
import Purelib.Approximation.Gaussian.Division.Prepared.Denominator
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Division.Partial

open Purelib.Approximation.Gaussian.Division

open Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Process.Apart

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

namespace Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation.FromSearch
open Purelib.Riemann.Integration.LegendreModularMonodromy

/-- Convert retained-state apartness into a modular preparation. The based denominator is not confused with the original
process: their operational equivalence is retained explicitly. -/
def preparationAt (matrix :
  LinearAlgebra.Matrix.Basic.IntegralMatrix) (tau : Coherent.CoherentNamed)
    (state : Approximation.Gaussian.FractionalAction.Integral.Acquisition.State matrix tau)
    (evidence : Possible.PossibleApart
      (Gaussian.Process.Based.based
        (fractionalDenominator matrix tau).name.process state.source)) :
    Gaussian.Division.Prepared.DenominatorPreparation (fractionalDenominator matrix tau) where
  prepared := Preparation.preparedDenominator state evidence
  apart := Preparation.preparedApart state evidence
  equivalent :=
    Equivalence.preparedDenominatorEquivalent state evidence
end Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation.FromSearch

end
