module
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Geometric
public import Purelib.Approximation.Gaussian.Geometric.Coherent.Comparison
import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Approximation.Matrix.Operational.Integral.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Cast
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.LinearAlgebra.Matrix.Multiplication
import Purelib.Riemann.Periods.PeriodMatrix
import Init.Core
import Init.Data.Int.Basic
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.Int.Cast.Defs
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Vector.Basic

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Equivalence

open Purelib.Approximation.Gaussian.Geometric

open Purelib.Approximation.Gaussian.Geometric.Coherent

open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed

open Purelib.Approximation.Matrix.Operational

open Purelib.Data.Gaussian

open Purelib.LinearAlgebra.Matrix

open Purelib.Riemann.Periods

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

namespace Purelib.Approximation.Matrix.Operational.Integral.Identity

/-- The exact integral identity matrix is operationally equivalent to the coherent unit-scaled identity.

The comparison retains the same row and column indices. Its diagonal entries are exact one readings and its other
entries are exact zero readings. -/
public def integralNamedMatrix_identity_scaleIdentity
  :
    PeriodMatrix.MatrixEquivalent
      (Integral.Basic.integralNamedMatrix Purelib.LinearAlgebra.Matrix.Multiplication.identity)
      (PeriodMatrix.scaleIdentity
        (Coherence.exact 1)) := by
  intro row column
  rw [Integral.Basic.integralNamedMatrix_apply,
    PeriodMatrix.scaleIdentity_apply]
  by_cases equal : row = column
  · subst column
    rw [if_pos rfl]
    change Gaussian.Equivalence.NamedEquivalent
      (PeriodMatrix.geometricNamed
        (GeometricApproximation.exact
          (Cast.integralGaussian
            (Purelib.LinearAlgebra.Matrix.Multiplication.identity row row)))).name
      (Coherence.exact 1).name
    have diagonal :
        (Purelib.LinearAlgebra.Matrix.Multiplication.identity :
          LinearAlgebra.Matrix.Basic.IntegralMatrix) row row =
          (1 : Int) := by
      unfold Purelib.LinearAlgebra.Matrix.Multiplication.identity
      rw [LinearAlgebra.Matrix.matrixOfFn_apply, if_pos rfl]
    rw [diagonal]
    have oneEqual : Cast.integralGaussian 1 = (1 : Data.Gaussian.Basic.Canonical) := by
      apply Data.Gaussian.Basic.ext <;>
        simp only [Cast.integralGaussian, Int.cast_one,
          Purelib.Data.Gaussian.Basic.one_re,
          Purelib.Data.Gaussian.Basic.one_im, -eq_self, -iff_self] <;> rfl
    rw [oneEqual]
    exact Comparison.geometricExact_equivalent_exact
      (1 : Data.Gaussian.Basic.Canonical)
  · rw [if_neg equal]
    have offDiagonal :
        (Purelib.LinearAlgebra.Matrix.Multiplication.identity :
          LinearAlgebra.Matrix.Basic.IntegralMatrix) row column =
          (0 : Int) := by
      unfold Purelib.LinearAlgebra.Matrix.Multiplication.identity
      rw [LinearAlgebra.Matrix.matrixOfFn_apply, if_neg equal]
    rw [offDiagonal]
    exact NamedEquivalent.refl _

end Purelib.Approximation.Matrix.Operational.Integral.Identity

end
