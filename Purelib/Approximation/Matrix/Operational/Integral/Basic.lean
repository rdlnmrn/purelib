module
import Purelib.Approximation.Gaussian.Geometric
public import Purelib.Approximation.Matrix.Operational.Types
import Purelib.Approximation.Matrix
public import Purelib.Data.Gaussian.Cast
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Vector.Basic

open Purelib.LinearAlgebra.Matrix.Basic (IntegralMatrix)

open Purelib

open Purelib.Approximation.Gaussian.Geometric

open Purelib.Approximation.Matrix.Operational.Types

open Purelib.Data.Gaussian

open Purelib.LinearAlgebra.Matrix

open Purelib.Riemann.Periods

open Purelib.Riemann.Periods.PeriodMatrix

section
@[expose] public section

/-!
# Finite Gauss--Manin continuation for the Legendre family

Finite root and homology continuation along an open parameter path produces
endpoint periods by the *dual* (transposed) homology action on actual
target-fibre programs.  It does not equate periods on different Legendre
curves.  Shrinking comparisons remain available below as a generic way to
prove that two refinement programs name the same value, without attaching
that stronger statement to changing-fibre continuation.
-/

namespace Purelib.Approximation.Matrix.Operational.Integral.Basic

/-- Exact synchronized geometric matrix underlying an integral homology matrix. -/
def integralGeometricMatrix (matrix :
  IntegralMatrix) : PeriodMatrix.GeometricMatrix 2 :=
  LinearAlgebra.Matrix.matrixOfFn fun row column =>
    GeometricApproximation.exact
      (Cast.integralGaussian (matrix row column))

/-- Productive exact CCL matrix carrying the same integral coefficients. -/
def integralNamedMatrix (matrix :
  IntegralMatrix) : NamedMatrix2 :=
  ScaledInverseCertificate.geometricNamedMatrix
    (integralGeometricMatrix matrix)

/-- An entry of the productive integral matrix is exactly the coherent geometric name of its integer coefficient. -/
@[simp] theorem integralNamedMatrix_apply (matrix :
  IntegralMatrix)
    (row column : Fin 2) :
    integralNamedMatrix matrix row column =
      PeriodMatrix.geometricNamed
        (GeometricApproximation.exact
          (Cast.integralGaussian (matrix row column))) := by
  rw [integralNamedMatrix,
    ScaledInverseCertificate.geometricNamedMatrix_apply,
    integralGeometricMatrix,
    LinearAlgebra.Matrix.matrixOfFn_apply]

/-- Every finite sample of the integral geometric matrix is exactly the original embedded integer coefficient. -/
theorem sample_integralGeometricMatrix_apply
    (matrix : IntegralMatrix) (index : Nat) (row column : Fin 2) :
    Approximation.Matrix.sampleMatrix
        (integralGeometricMatrix matrix) index row column =
      Cast.integralGaussian (matrix row column) := by
  rw [Approximation.Matrix.sampleMatrix_apply,
    integralGeometricMatrix,
    LinearAlgebra.Matrix.matrixOfFn_apply]
  exact GeometricApproximation.exact_sample
    _ _
end Purelib.Approximation.Matrix.Operational.Integral.Basic

end
