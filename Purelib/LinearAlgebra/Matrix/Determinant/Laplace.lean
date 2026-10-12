module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Group.Negation
import Purelib.Data.Fin
import Purelib.Data.List.OfFn.Basic
import Purelib.LinearAlgebra.Matrix.Basic
public import Purelib.LinearAlgebra.Matrix.Minor
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Vector.Basic

open Purelib.Algebra.Field

open Purelib.Algebra.Group in
attribute [local instance high] Negation.subNegZeroMonoid

attribute [local instance high] SubNegMonoid.toNeg

open Purelib

open Purelib.LinearAlgebra.Matrix.Bivariate renaming Square -> BivariateMatrix

open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix

public section

/-!
# Finite bivariate coordinate polynomials and determinants

Both variables are represented by finite high-to-low coefficient lists.  The
determinant is an explicit Laplace recursion over `Fin n`; it does not use a
sparse polynomial, a generic matrix determinant, or any infinite carrier.
-/

namespace Purelib.LinearAlgebra.Matrix.Determinant.Laplace
variable {K : Type*} [ExplicitField K] [DecidableEq K]

/-- Compute a finite scalar determinant by first-column Laplace recursion.

The original bounded rows, signed entry products and retained minor indices
produce a finite table whose sum uses the same left fold and zero accumulator. -/
@[expose] def scalarDeterminant : (n : Nat) →
    BivariateMatrix K n → K
  | 0, _ => 1
  | n + 1, matrix =>
      (List.ofFn fun row : Fin (n + 1) =>
        (-1 : K) ^ (row : Nat) * matrix row 0 *
          Purelib.LinearAlgebra.Matrix.Determinant.Laplace.scalarDeterminant n
            (SquareMatrix.Minor.scalarFirstColumnMinor matrix row)).foldl
        (fun a b => a + b) 0

omit [DecidableEq K] in
/-- Entrywise equal finite matrices have equal scalar Laplace determinants.

The original minor indices and finite summand table retain each bounded entry
comparison through the recursive determinants and the same addition fold. -/
theorem scalarDeterminant_congr : ∀ {n : Nat} (left right : BivariateMatrix K n),
    (∀ row column, left row column = right row column) →
      SquareMatrix.Determinant.Laplace.scalarDeterminant n left = SquareMatrix.Determinant.Laplace.scalarDeterminant n
        right
  | 0, left, right, equal => rfl
  | n + 1, left, right, equal => by
      rw [SquareMatrix.Determinant.Laplace.scalarDeterminant, SquareMatrix.Determinant.Laplace.scalarDeterminant]
      apply congrArg (fun values : List K =>
        values.foldl (fun a b => a + b) 0)
      apply Purelib.Data.List.OfFn.Basic.ofFn_congr
      intro row
      have minorEqual :
          SquareMatrix.Determinant.Laplace.scalarDeterminant n (SquareMatrix.Minor.scalarFirstColumnMinor left row) =
            SquareMatrix.Determinant.Laplace.scalarDeterminant n (SquareMatrix.Minor.scalarFirstColumnMinor right row)
              :=
        Purelib.LinearAlgebra.Matrix.Determinant.Laplace.scalarDeterminant_congr _ _ (fun minorRow
          column => by
          simp only [SquareMatrix.Minor.scalarFirstColumnMinor,
            SquareMatrix.matrixOfFn_apply]
          exact equal (Data.Fin.skipIndex row minorRow) column.succ)
      calc
        (-1 : K) ^ (row : Nat) * left row 0 *
              SquareMatrix.Determinant.Laplace.scalarDeterminant n (SquareMatrix.Minor.scalarFirstColumnMinor left row)
                =
            (-1 : K) ^ (row : Nat) * right row 0 *
              SquareMatrix.Determinant.Laplace.scalarDeterminant n (SquareMatrix.Minor.scalarFirstColumnMinor left row)
                :=
          congrArg (fun value =>
            (-1 : K) ^ (row : Nat) * value *
              SquareMatrix.Determinant.Laplace.scalarDeterminant n (SquareMatrix.Minor.scalarFirstColumnMinor left row))
            (equal row 0)
        _ = (-1 : K) ^ (row : Nat) * right row 0 *
              SquareMatrix.Determinant.Laplace.scalarDeterminant n (SquareMatrix.Minor.scalarFirstColumnMinor right row)
                :=
          congrArg (fun value =>
            (-1 : K) ^ (row : Nat) * right row 0 * value) minorEqual
end Purelib.LinearAlgebra.Matrix.Determinant.Laplace

end
