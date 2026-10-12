module
-- The exposed block formula retains the finite coordinate splitter.
public import Purelib.Data.Fin
import Purelib.Algebra.Field.ExplicitField
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.LinearAlgebra.PolynomialMatrix.Basic
public import Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Basic
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Multiplication

/-!
# Polynomial-valued fraction-free matrix inversion

The block recursion is run symbolically over dense coordinate polynomials.
Evaluation at any coordinate commutes with every finite sum and block
operation, so the resulting scalar and matrix specialize to the constructive
scaled inverse from `Purelib.LinearAlgebra`.
-/

namespace Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Block

open Purelib
open Purelib.Algebra.Field
open Purelib.LinearAlgebra
open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix

public section
variable {K : Type*} [ExplicitField K] [DecidableEq K]

/-- Extend smaller polynomial inverse data by the fraction-free block formula.

The leading pivot, cached row and column products, and retained smaller scalar determine all four output blocks. -/
@[expose] def blockInverse {n : Nat} (matrix : PolynomialMatrix.Basic.Matrix K (n + 1))
    (smaller : PolynomialMatrix.Inverse.Scaled.Basic.ScaledInverseData K n) : PolynomialMatrix.Basic.Matrix K (n + 1) :=
  let a := PolynomialMatrix.Basic.head matrix
  let row := PolynomialMatrix.Basic.topRow matrix
  let column := PolynomialMatrix.Basic.leftColumn matrix
  let inverse := smaller.inverse
  let inverseColumn := PolynomialMatrix.Basic.matrixVector inverse column
  let rowInverse := PolynomialMatrix.Basic.vectorMatrix row inverse
  let corner := smaller.scalar + PolynomialMatrix.Basic.dot row inverseColumn
  SquareMatrix.matrixOfFn fun i j => Data.Fin.cases
    (Data.Fin.cases corner (fun columnIndex => -a * rowInverse columnIndex) j)
    (fun rowIndex => Data.Fin.cases
      (-a * inverseColumn rowIndex)
      (fun columnIndex => (a * a) * inverse rowIndex columnIndex) j) i

/-- Read one finite entry of the symbolic division-free block inverse.

The original row and column choose one of the four retained block values.
The entry readback uses the same first-position splitter as the construction. -/
theorem blockInverse_apply {n : Nat} (matrix : PolynomialMatrix.Basic.Matrix K (n + 1))
    (smaller : PolynomialMatrix.Inverse.Scaled.Basic.ScaledInverseData K n) (row column : Fin (n + 1)) :
    PolynomialMatrix.Inverse.Scaled.Block.blockInverse matrix smaller row column =
      Data.Fin.cases
        (Data.Fin.cases
          (smaller.scalar + PolynomialMatrix.Basic.dot (PolynomialMatrix.Basic.topRow matrix)
            (PolynomialMatrix.Basic.matrixVector smaller.inverse (PolynomialMatrix.Basic.leftColumn matrix)))
          (fun columnIndex =>
            -PolynomialMatrix.Basic.head matrix * PolynomialMatrix.Basic.vectorMatrix (PolynomialMatrix.Basic.topRow
              matrix) smaller.inverse
              columnIndex) column)
        (fun rowIndex => Data.Fin.cases
          (-PolynomialMatrix.Basic.head matrix * PolynomialMatrix.Basic.matrixVector smaller.inverse
            (PolynomialMatrix.Basic.leftColumn matrix)
            rowIndex)
          (fun columnIndex =>
            (PolynomialMatrix.Basic.head matrix * PolynomialMatrix.Basic.head matrix) *
              smaller.inverse rowIndex columnIndex) column) row := by
  unfold PolynomialMatrix.Inverse.Scaled.Block.blockInverse
  rewrite [SquareMatrix.matrixOfFn_apply]
  exact Eq.refl _
end

end Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Block
