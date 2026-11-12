module
import Purelib.Data.Gaussian.Basic
import Purelib.Algebra.FiniteSum.Fin
public import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
public import Purelib.LinearAlgebra.Matrix.Inverse.Scaled.Basic
import Purelib.LinearAlgebra.Matrix.Multiplication
import Purelib.LinearAlgebra.Matrix.Basic

open Purelib

open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix

section
/-!
Checked finite witnesses for the original separated-Sylvester clearances.
An untrusted column solves the evaluated matrix equation. The original scaled
inverse proves uniqueness, so the saved column supplies the original normalized
cofactors, rather than merely some valid Bezout coefficients. Equality of the
resulting rational polynomials uses the existing explicit finite-grid theorem.
-/

@[expose] public section

namespace Purelib.LinearAlgebra.Matrix.Inverse.Scaled.GaussianColumn

/-- A structural vector over the supplied coefficient type with retained finite length. -/
abbrev Vector (K : Type*) (n :
  Nat) := Data.Vector K n

/-- Materialize the coordinate unit column at the supplied bounded index. -/
def unitColumn {n : Nat} (column :
  Fin n) : GaussianColumn.Vector Data.Gaussian.Basic.Canonical n :=
  Data.Vector.Basic.vectorOfFn fun row => if row = column then 1 else 0

section
/-- Multiplying a Gaussian matrix by a unit column reads the corresponding matrix column.

The original finite sum has one nonzero entry, determined by the supplied column index; its coefficient is one. -/
theorem matrixVector_unit
  {n : Nat} (matrix : SquareMatrix Data.Gaussian.Basic.Canonical n)
    (column row : Fin n) : Multiplication.matrixVector matrix
      (unitColumn column) row = matrix row column := open Purelib.Algebra in
      by
  rw [Multiplication.matrixVector_apply]
  calc
    _ = FiniteSum.Fin.sumFin (fun middle => if middle = column then matrix row middle else 0) := by
      apply FiniteSum.Fin.sumFin_congr
      intro middle
      simp only [unitColumn, Data.Vector.Basic.vectorOfFn_apply]
      split <;>
        (simp only [mul_one, mul_zero, -eq_self, -iff_self]
         rfl)
    _ = _ := FiniteSum.Fin.sumFin_ite_eq column (fun middle => matrix row middle)
end

/-- The original symbolic inverse appears only in this uniqueness proof.
Checking a saved solution does not construct it at runtime. -/
theorem solution_eq_column {n :
  Nat} (matrix : SquareMatrix Data.Gaussian.Basic.Canonical n)
    (inverse : Basic.ScaledInverse matrix) (nonzero : inverse.scalar ≠ 0)
    (column : Fin n) (values : GaussianColumn.Vector Data.Gaussian.Basic.Canonical n)
    (solves : Multiplication.matrixVector matrix values =
      unitColumn column) (row : Fin n) :
    values row = inverse.scalar⁻¹ * inverse.inverse row column := by
  have product : inverse.scalar * values row = inverse.inverse row column := by
    calc
      _ = Multiplication.matrixVector (Multiplication.scaleIdentity inverse.scalar) values row
        := by
        rw [Multiplication.matrixVector_scaleIdentity, Data.Vector.Basic.vectorOfFn_apply]
      _ = Multiplication.matrixVector (Multiplication.mul inverse.inverse matrix) values row
        := by
        rw [inverse.left_identity]
      _ = Multiplication.matrixVector inverse.inverse (Multiplication.matrixVector matrix
        values) row := by
        rw [Multiplication.matrixVector_mul]
      _ = Multiplication.matrixVector inverse.inverse
        (unitColumn column) row := by
        rw [solves]
      _ = _ :=
        matrixVector_unit
        _ _ _
  calc
    values row = (inverse.scalar⁻¹ * inverse.scalar) * values row := by
      rw [Data.Gaussian.Basic.Canonical.inv_mul_cancel _ nonzero, one_mul]
    _ = inverse.scalar⁻¹ * (inverse.scalar * values row) := _root_.mul_assoc _ _ _
    _ = _ := by rw [product]
end Purelib.LinearAlgebra.Matrix.Inverse.Scaled.GaussianColumn

end
