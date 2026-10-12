module
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Geometric
import Purelib.Approximation.Matrix
public import Purelib.Approximation.Matrix.Operational.Integral.Basic
import Purelib.Data.Gaussian.Cast
import Purelib.LinearAlgebra.Matrix.Basic
public import Purelib.LinearAlgebra.Matrix.Integral.Gaussian
import Purelib.LinearAlgebra.Matrix.Multiplication
import Purelib.Riemann.Periods.PeriodMatrix
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Int.Defs
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Vector.Basic

namespace Purelib.Approximation.Matrix.Operational.Integral.Multiplication

open Purelib
open Purelib.Algebra
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Geometric
open Purelib.Approximation.Matrix.Operational
open Purelib.Data.Gaussian
open Purelib.LinearAlgebra.Matrix
open Purelib.Riemann.Periods
open Purelib.Riemann.Periods.PeriodMatrix

public section

/-!
# Finite Gauss--Manin continuation for the Legendre family

Finite root and homology continuation along an open parameter path produces
endpoint periods by the *dual* (transposed) homology action on actual
target-fibre programs.  It does not equate periods on different Legendre
curves.  Shrinking comparisons remain available below as a generic way to
prove that two refinement programs name the same value, without attaching
that stronger statement to changing-fibre continuation.
-/

/-- Productive exact integral matrices multiply like their finite integer matrices, entry by entry, at the operational
layer. -/
@[expose] def integralNamedMatrix_mul (left right : LinearAlgebra.Matrix.Basic.IntegralMatrix) :
    PeriodMatrix.MatrixEquivalent
      (PeriodMatrix.matrixMul
        (Integral.Basic.integralNamedMatrix left) (Integral.Basic.integralNamedMatrix right))
      (Integral.Basic.integralNamedMatrix
        (Multiplication.mul left right)) := by
  let leftGeometric := Integral.Basic.integralGeometricMatrix left
  let rightGeometric := Integral.Basic.integralGeometricMatrix right
  let productGeometric :=
    ScaledInverseCertificate.geometricProductMatrix
      leftGeometric rightGeometric
  have normalize : PeriodMatrix.MatrixEquivalent
      (PeriodMatrix.matrixMul
        (Integral.Basic.integralNamedMatrix left) (Integral.Basic.integralNamedMatrix right))
      (ScaledInverseCertificate.geometricNamedMatrix
        productGeometric) :=
    ScaledInverseCertificate.matrixMul_equivalent_geometricProductMatrix
      (Integral.Basic.integralNamedMatrix left) (Integral.Basic.integralNamedMatrix right)
      leftGeometric rightGeometric
      (fun row column => by
        dsimp only [leftGeometric]
        rw [Integral.Basic.integralNamedMatrix_apply, Integral.Basic.integralGeometricMatrix,
          LinearAlgebra.Matrix.matrixOfFn_apply]
        exact NamedEquivalent.refl _)
      (fun row column => by
        dsimp only [rightGeometric]
        rw [Integral.Basic.integralNamedMatrix_apply, Integral.Basic.integralGeometricMatrix,
          LinearAlgebra.Matrix.matrixOfFn_apply]
        exact NamedEquivalent.refl _)
  apply MatrixEquivalent.trans normalize
  intro row column
  rw [ScaledInverseCertificate.geometricNamedMatrix_apply,
    Integral.Basic.integralNamedMatrix_apply]
  apply ScaledInverseCertificate.geometricNamed_equivalent_of_samples
  intro index
  rw [show (productGeometric row column).sample index =
      Multiplication.mul
        (Approximation.Matrix.sampleMatrix
          leftGeometric index)
        (Approximation.Matrix.sampleMatrix
          rightGeometric index) row column by
    dsimp only [productGeometric]
    rw [ScaledInverseCertificate.geometricProductMatrix_apply]
    exact ScaledInverseCertificate.geometricProductEntry_sample
      leftGeometric rightGeometric row column index]
  rw [Multiplication.mul_apply]
  rw [FiniteSum.Fin.sumFin_congr
    (right := fun middle =>
      Cast.integralGaussian (left row middle) *
        Cast.integralGaussian (right middle column))
    (fun middle => by
      rw [Integral.Basic.sample_integralGeometricMatrix_apply,
        Integral.Basic.sample_integralGeometricMatrix_apply])]
  rw [GeometricApproximation.exact_sample]
  rw [Multiplication.mul_apply]
  exact Integral.Gaussian.integralGaussian_sumFin_two left right row column

end

end Purelib.Approximation.Matrix.Operational.Integral.Multiplication
