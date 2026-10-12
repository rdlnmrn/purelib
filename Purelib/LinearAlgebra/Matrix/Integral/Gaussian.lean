module
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Gaussian.Field
import Purelib.Algebra.FiniteSum.Gaussian
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Cast
import Purelib.Data.Rat.Fraction.Cast
import Purelib.LinearAlgebra.Matrix.Basic
public import Purelib.LinearAlgebra.Matrix.Multiplication
import Mathlib.Algebra.Ring.Int.Defs
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Vector.Basic
import Purelib.Tactic.Ring

open Purelib.Algebra

open Purelib

open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix

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

namespace Purelib.LinearAlgebra.Matrix.Integral.Gaussian

/-- Casting a two-term integral dot product into exact Gaussian rationals
commutes with the displayed finite sum. -/
theorem integralGaussian_sumFin_two
    (left right : LinearAlgebra.Matrix.Basic.IntegralMatrix) (row column : Fin 2) :
    FiniteSum.Fin.sumFin (fun middle =>
        Data.Gaussian.Cast.integralGaussian (left row middle) *
          Data.Gaussian.Cast.integralGaussian (right middle column)) =
      Data.Gaussian.Cast.integralGaussian
        (FiniteSum.Fin.sumFin fun middle =>
          left row middle * right middle column) := open Purelib.Data.Rat in by
  have sumTwo (values : Fin 2 → Data.Gaussian.Basic.Canonical) :
      FiniteSum.Fin.sumFin values = values 0 + values 1 := by
    rw [FiniteSum.Fin.sumFin_succ,
      FiniteSum.Fin.sumFin_succ]
    have empty : FiniteSum.Fin.sumFin
        (fun index : Fin 0 => values index.succ.succ) = 0 := by
      calc
        _ = FiniteSum.Fin.sumFin
            (fun _ : Fin 0 => (0 : Data.Gaussian.Basic.Canonical)) :=
          FiniteSum.Fin.sumFin_congr (fun index => Fin.elim0 index)
        _ = 0 := FiniteSum.Fin.sumFin_zero
    rw [empty, Data.Gaussian.Basic.add_zero]
    rfl
  rw [sumTwo, FiniteSum.Fin.sumFin_two_int]
  apply Data.Gaussian.Basic.ext
  · simp only [Data.Gaussian.Cast.integralGaussian,
      Data.Gaussian.Basic.add_re,
      Data.Gaussian.Basic.mul_re,
      Fraction.Cast.intCast_add_direct,
      Fraction.Cast.intCast_mul_direct]
    ring1
  · simp only [Data.Gaussian.Cast.integralGaussian,
      Data.Gaussian.Basic.add_im,
      Data.Gaussian.Basic.mul_im]
    ring1

/-- Entrywise casting commutes with exact two-by-two integer matrix
multiplication. -/
theorem integralGaussian_matrix_mul_entry
    (left right : LinearAlgebra.Matrix.Basic.IntegralMatrix) (row column : Fin 2) :
    SquareMatrix.Multiplication.mul
        (SquareMatrix.matrixOfFn fun row column =>
          Data.Gaussian.Cast.integralGaussian (left row column))
        (SquareMatrix.matrixOfFn fun row column =>
          Data.Gaussian.Cast.integralGaussian (right row column)) row column =
      Data.Gaussian.Cast.integralGaussian
        (SquareMatrix.Multiplication.mul left right row column) := by
  rw [SquareMatrix.Multiplication.mul_apply]
  rw [FiniteSum.Fin.sumFin_congr
    (right := fun middle =>
      Data.Gaussian.Cast.integralGaussian (left row middle) *
        Data.Gaussian.Cast.integralGaussian (right middle column))
    (fun middle => by
      rw [SquareMatrix.matrixOfFn_apply,
        SquareMatrix.matrixOfFn_apply])]
  rw [SquareMatrix.Multiplication.mul_apply]
  exact SquareMatrix.Integral.Gaussian.integralGaussian_sumFin_two left right row column
end Purelib.LinearAlgebra.Matrix.Integral.Gaussian

end
