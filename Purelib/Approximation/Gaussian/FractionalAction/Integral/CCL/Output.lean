module
import Purelib.Riemann.Integration.LegendreModularMonodromy
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
public import Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Output
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Data.CCL.Transducer.Machine.Advance
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.Approximation.Gaussian.Name.CCL.Output
import Purelib.Data.CCL.Transducer.Machine.Basic
import Purelib.Approximation.Gaussian.Division.Prepared.Denominator

open Purelib.Approximation.Gaussian.Division

open Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition

open Purelib.Approximation.Gaussian.Name

open Purelib.Data.CCL.Transducer.Machine

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

namespace Purelib.Approximation.Gaussian.FractionalAction.Integral.CCL.Output
open Purelib.Riemann.Integration.LegendreModularMonodromy (fractionalDenominator)

/-- A ready transformed output retains the unchanged finite productivity contract. -/
theorem ready_productive (matrix :
  LinearAlgebra.Matrix.Basic.IntegralMatrix) (tau : Coherent.CoherentNamed)
    (preparation : Approximation.Gaussian.Division.Prepared.DenominatorPreparation
      (fractionalDenominator matrix tau)) (count : Nat) :
    (Output.readyOutput matrix tau preparation).name.machine.emitted.IsPrefix
        (Advance.advance
          (Output.readyOutput matrix tau preparation).name.machine count).emitted ∧
      (Advance.advance
        (Output.readyOutput matrix tau preparation).name.machine count).emitted.length =
        count :=
  (Output.readyOutput matrix tau preparation).name.productive count
end Purelib.Approximation.Gaussian.FractionalAction.Integral.CCL.Output

end
