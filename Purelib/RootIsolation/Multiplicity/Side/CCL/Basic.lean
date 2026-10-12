module
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.RootIsolation.Multiplicity.Observation.CCL.Basic
public import Purelib.RootIsolation.Multiplicity.Side.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Context.Basic
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side
import Purelib.RootIsolation.Multiplicity.Family.Basic

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

namespace Purelib.RootIsolation.Multiplicity.Side.CCL.Basic

/-- CCL attachments for every factor group on one reduced cofactor side.
Constants contribute no site and therefore need no encoding data. -/
def SideCCL
    {source opposite : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} :
    Multiplicity.Side.Basic.SideResult source opposite → Type
  | .constant _ _ _ => Unit
  | .positive input family =>
      (index : Fin input.contexts.length) →
        Multiplicity.Observation.CCL.Basic.ObservationCCL (family.observationAt index)

/-- Construct the CCL attachments for the retained sites of the original reduced cofactor side.

Constant sides have unit attachment data; positive sides retain the original observation attachment at every context
index. -/
def sideCCL
    {source opposite : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (side : Multiplicity.Side.Basic.SideResult source opposite) :
    SideCCL side := by
  cases side with
  | constant => exact Unit.unit
  | positive input family =>
      exact fun index => Multiplicity.Observation.CCL.Basic.observationCCL (family.observationAt index)
end Purelib.RootIsolation.Multiplicity.Side.CCL.Basic

end
