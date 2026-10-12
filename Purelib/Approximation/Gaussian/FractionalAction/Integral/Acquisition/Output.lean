module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Riemann.Integration.LegendreModularMonodromy
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Equivalence
public import Purelib.Approximation.Gaussian.FractionalAction.Integral.Comparison
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.Data.Vector.Basic
import Purelib.Approximation.Gaussian.Division.Prepared.Denominator

section

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Division

open Purelib.Approximation.Gaussian.FractionalAction.Integral

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

namespace Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Output
open Purelib.Riemann.Integration.LegendreModularMonodromy (fractionalDenominator fractionalLinear)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)

/-! ## Ready output and schedule independence -/

/-- The ordinary productive fractional output returned after readiness. -/
def readyOutput (matrix : LinearAlgebra.Matrix.Basic.IntegralMatrix) (tau : Coherent.CoherentNamed)
    (preparation : Division.Prepared.DenominatorPreparation
      (fractionalDenominator matrix tau)) : CoherentNamed :=
  fractionalLinear matrix tau preparation

/-- Different finite schedules which prepare the same exact transformed denominator produce operationally equivalent
outputs. -/
def ready_respects (matrix : LinearAlgebra.Matrix.Basic.IntegralMatrix) (tau : Coherent.CoherentNamed)
    (first second : Division.Prepared.DenominatorPreparation
      (fractionalDenominator matrix tau)) :
    Gaussian.Equivalence.NamedEquivalent
      (Approximation.Gaussian.FractionalAction.Integral.Acquisition.Output.readyOutput matrix tau first).name
      (Approximation.Gaussian.FractionalAction.Integral.Acquisition.Output.readyOutput matrix tau second).name := by
  simpa only [Approximation.Gaussian.FractionalAction.Integral.Acquisition.Output.readyOutput] using
    Comparison.fractionalLinear_preparation_independent matrix tau first second
end Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Output

end

section
@[expose] public section

/-!
# Automatic finite-word dual period outputs

The public result caches the exact word matrix, its denominator preparation,
and the productive output. A positive enclosure constructs it directly;
bounded acquisition returns either this same result or an exact resumable
state. The transport proof is shared by both construction routes.
-/

namespace Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Output

set_option genInjectivity false in
/-- A cached integral matrix, its dependent preparation and the corresponding coherent output.

The matrix satisfies the supplied specification; the output equality identifies the cached executable value with
evaluation using that exact matrix and preparation. -/
structure ReadyPayload (specification : LinearAlgebra.Matrix.Basic.IntegralMatrix → Prop)
    (preparationType : LinearAlgebra.Matrix.Basic.IntegralMatrix → Type 1)
    (evaluate :
      (matrix : LinearAlgebra.Matrix.Basic.IntegralMatrix) → preparationType matrix → Coherent.CoherentNamed) where
  /-- The cached integral matrix used by the prepared action. -/ matrix : LinearAlgebra.Matrix.Basic.IntegralMatrix
  /-- The cached matrix satisfies the requested matrix specification. -/ matrix_eq : specification matrix
  /-- The retained preparation indexed by the cached matrix. -/ preparation : preparationType matrix
  /-- The cached coherent result of the prepared action. -/ output : Coherent.CoherentNamed
  /-- The cached output equals evaluation of the retained matrix and preparation. -/ output_eq : output = evaluate
    matrix preparation

constructive_injectivity ReadyPayload

end Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Output

end

end
