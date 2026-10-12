module
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Matrix.Basic

import Purelib.LinearAlgebra.Gaussian.QuadraticForm

open Purelib

open Purelib.Algebra

open Purelib.Data.Rat

/-!
# Retained Gaussian matrix carrier observations

Kernel proofs check indexed vector and matrix carriers, supplied nonzero witness
fields and the explicit finite double-sum formula against the quadratic-form API.
-/

namespace Test.LinearAlgebra.Gaussian.QuadraticForms

open Purelib.LinearAlgebra.Gaussian.QuadraticForm

/-- The reference Stokes scalar alias is the canonical Gaussian-rational carrier. -/
private abbrev retainedStokesGaussian := Data.Gaussian.Basic.Canonical
/-- The reference indexed Stokes Gaussian matrix carrier. -/
private abbrev retainedStokesGaussianMatrix (size : Nat) :=
  LinearAlgebra.Matrix retainedStokesGaussian size

/-- The reference period-coordinate alias is the canonical rational carrier. -/
private abbrev retainedPeriodCoordinate :=
  Fraction.Rational
/-- The reference period scalar alias is the canonical Gaussian-rational carrier. -/
private abbrev retainedPeriodGaussian := Data.Gaussian.Basic.Canonical
/-- The reference period rational vector retains its exact supplied finite dimension. -/
private abbrev retainedPeriodRationalVector (size : Nat) :=
  Data.Vector retainedPeriodCoordinate size
/-- The reference period Gaussian matrix retains its exact supplied finite dimension. -/
private abbrev retainedPeriodGaussianMatrix (size : Nat) :=
  LinearAlgebra.Matrix retainedPeriodGaussian size

/-- The reference Stokes scalar alias is exactly the canonical Gaussian-rational type. -/
example : retainedStokesGaussian = Data.Gaussian.Basic.Canonical := rfl

/-- The reference Stokes matrix carrier is exactly the Gaussian matrix type at the same dimension. -/
example (size : Nat) :
    retainedStokesGaussianMatrix size = GaussianMatrix size := rfl

/-- The reference period rational vector is exactly the canonical vector at the same dimension. -/
example (size : Nat) :
    retainedPeriodRationalVector size = RationalVector size := rfl

/-- The reference period Gaussian matrix is exactly the canonical matrix at the same dimension. -/
example (size : Nat) :
    retainedPeriodGaussianMatrix size = GaussianMatrix size := rfl

-- The mapped nominal carrier retains its supplied index and exact proof.
/-- The nonzero-vector certificate retains the supplied reference finite index. -/
example {size : Nat} {vector : RationalVector size}
    (index : Fin size) (nonzero : vector index ≠ 0) :
    (⟨index, nonzero⟩ : NonzeroVector vector).index = index := rfl

/-- The nonzero-vector certificate retains the exact supplied nonzero proof. -/
example {size : Nat} {vector : RationalVector size}
    (index : Fin size) (nonzero : vector index ≠ 0) :
    (⟨index, nonzero⟩ : NonzeroVector vector).coefficient_nonzero = nonzero := rfl

/-- Reconstructing the nonzero-vector certificate from its reference index and proof preserves the entire witness. -/
example {size : Nat} {vector : RationalVector size}
    (witness : NonzeroVector vector) :
    (⟨witness.index, witness.coefficient_nonzero⟩ : NonzeroVector vector) =
      witness := by
  cases witness
  rfl

/-- The reference finite double sum of rational coefficients against imaginary Gaussian matrix entries. -/
private def retainedImaginaryQuadraticForm {size : Nat}
    (vector : retainedPeriodRationalVector size)
    (matrix : retainedPeriodGaussianMatrix size) : retainedPeriodCoordinate :=
  FiniteSum.Fin.sumFin fun row =>
    FiniteSum.Fin.sumFin fun column =>
      vector row * (matrix row column).im * vector column

/-- The retained reference finite double sum equals the canonical imaginary quadratic form exactly. -/
example {size : Nat} (vector : RationalVector size)
    (matrix : GaussianMatrix size) :
    retainedImaginaryQuadraticForm vector matrix =
      imaginaryQuadraticForm vector matrix := rfl

end Test.LinearAlgebra.Gaussian.QuadraticForms
