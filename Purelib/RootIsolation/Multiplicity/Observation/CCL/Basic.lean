module
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Context.Basic
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side
import Purelib.RootIsolation.FTA.Squarefree.Basic
public import Purelib.RootIsolation.Multiplicity.Observation.Basic
import Purelib.RootIsolation.Roots.CCL.Terminal.Basic
public import Purelib.RootIsolation.Roots.CCL.Terminal.Build
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Positive
import Purelib.Polynomial.Dense.Gaussian.Roots.Certificate
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Part

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# CCL-2 data for the rational-function argument principle

Paper I returns exact rational sites or independently shrinking zero/pole
tracks after finite cancellation.  This module adds CCL observations to those
existing results without duplicating any RFAP isolation or winding proof.
-/

namespace Purelib.RootIsolation.Multiplicity.Observation.CCL.Basic

/-- CCL data attached to one already-proved RFAP factor observation. -/
def ObservationCCL
    {source opposite : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {input : Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput source opposite}
    {context : Dense.Gaussian.Multiplicity.Basis.Context.Basic.PositiveContext input.entries} :
    Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput.FactorObservation input context → Type
  | .exact _ _ _ =>
      RootIsolation.Roots.CCL.Terminal context.focus.part.polynomial
  | .higher _ _ =>
      FTA.Squarefree.AdapterResult context.focus.part.polynomial

/-- Construct the CCL attachment by reusing the exact terminal constructor or
the exact same higher-degree box result stored by RFAP. -/
def observationCCL
    {source opposite : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {input : Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput source opposite}
    {context : Dense.Gaussian.Multiplicity.Basis.Context.Basic.PositiveContext input.entries}
    (observation :
      Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput.FactorObservation input context) :
    ObservationCCL observation := by
  cases observation with
  | exact root degree oppositeAtRoot =>
      exact Roots.CCL.Terminal.Build.terminalOfExactRoot root
  | higher boxes degree =>
      exact ⟨boxes⟩
end Purelib.RootIsolation.Multiplicity.Observation.CCL.Basic

end
