module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Group.Negation
import Purelib.Data.Fin
import Purelib.Data.List.OfFn.Basic
import Purelib.LinearAlgebra.Matrix.Basic
public import Purelib.LinearAlgebra.Matrix.Determinant.Laplace
import Purelib.LinearAlgebra.Matrix.Minor
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
public import Purelib.Polynomial.Dense.Multiplication
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Vector.Basic

open Purelib.Polynomial.Dense.Basic

open Purelib.Algebra.Field

open Purelib.Algebra.Group in
attribute [local instance high] Negation.subNegZeroMonoid

attribute [local instance high] SubNegMonoid.toNeg

open Purelib

open Purelib.LinearAlgebra.Matrix.Bivariate renaming Square -> BivariateMatrix

open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix

open Purelib.Polynomial

public section

/-!
# Finite bivariate coordinate polynomials and determinants

Both variables are represented by finite high-to-low coefficient lists.  The
determinant is an explicit Laplace recursion over `Fin n`; it does not use a
sparse polynomial, a generic matrix determinant, or any infinite carrier.
-/

namespace Purelib.LinearAlgebra.PolynomialMatrix.Determinant
variable {K : Type*} [ExplicitField K] [DecidableEq K]

/-- Delete the first column and the supplied bounded row of a polynomial matrix.

The smaller structural matrix reads original rows through the retained skip-index map. -/
@[expose] def firstColumnMinor {n : Nat}
    (matrix : BivariateMatrix (CoefficientPolynomial K) (n + 1))
    (row : Fin (n + 1)) : BivariateMatrix (CoefficientPolynomial K) n :=
  SquareMatrix.matrixOfFn fun minorRow column =>
    matrix (Data.Fin.skipIndex row minorRow) column.succ

open Purelib.LinearAlgebra in
/-- Compute a finite determinant over dense coordinate polynomials.

Each first-column term retains its signed scalar, original polynomial entry
and bounded minor. The same finite left fold sums the resulting polynomials. -/
@[expose] def determinant : (n : Nat) →
    BivariateMatrix (CoefficientPolynomial K) n → CoefficientPolynomial K
  | 0, _ => DensePolynomial.constant 1
  | n + 1, matrix =>
      (List.ofFn fun row : Fin (n + 1) =>
        DensePolynomial.scale ((-1 : K) ^ (row : Nat))
          (matrix row 0 * Determinant.determinant n
            (firstColumnMinor matrix row))).foldl
        (fun a b => a + b) 0

/-- Evaluating a polynomial addition fold gives the corresponding scalar addition fold.

The polynomial accumulator is evaluated at the same supplied point. -/
private theorem eval_foldl_add (t : K)
    (polynomials : List (CoefficientPolynomial K))
    (accumulator : CoefficientPolynomial K) :
    (polynomials.foldl (fun a b => a + b) accumulator).eval t =
      (polynomials.map (fun p => p.eval t)).foldl
        (fun a b => a + b) (accumulator.eval t) := by
  induction polynomials generalizing accumulator with
  | nil => rfl
  | cons p remaining inductionHypothesis =>
      simp only [List.foldl_cons, List.map_cons]
      rw [inductionHypothesis,
        DensePolynomial.eval_add]

open Purelib.LinearAlgebra in
/-- Evaluating the finite polynomial determinant gives the determinant of the evaluated entries.

Both determinants use the same first-column Laplace recursion and retained minor indices. -/
theorem eval_determinant (t : K) : ∀ (n : Nat)
    (matrix : BivariateMatrix (CoefficientPolynomial K) n),
    (determinant n matrix).eval t =
      SquareMatrix.Determinant.Laplace.scalarDeterminant n
        (SquareMatrix.matrixOfFn fun row column =>
          (matrix row column).eval t)
  | 0, _ => by
      change (DensePolynomial.constant 1).eval t = 1
      exact DensePolynomial.eval_constant 1 t
  | n + 1, matrix => by
      rw [determinant, SquareMatrix.Determinant.Laplace.scalarDeterminant,
        eval_foldl_add,
        DensePolynomial.eval_zero,
        Data.List.OfFn.Basic.map_ofFn]
      apply congrArg (fun values : List K =>
        values.foldl (fun a b => a + b) 0)
      apply Data.List.OfFn.Basic.ofFn_congr
      intro row
      simp only [Function.comp_apply,
        SquareMatrix.matrixOfFn_apply]
      change
        (DensePolynomial.scale ((-1 : K) ^ (row : Nat))
            (matrix row 0 * determinant n
              (firstColumnMinor matrix row))).eval t =
          (-1 : K) ^ (row : Nat) * (matrix row 0).eval t *
            SquareMatrix.Determinant.Laplace.scalarDeterminant n
              (SquareMatrix.Minor.scalarFirstColumnMinor
                (SquareMatrix.matrixOfFn
                  fun matrixRow column =>
                    (matrix matrixRow column).eval t) row)
      rw [DensePolynomial.eval_scale,
        DensePolynomial.eval_mul]
      rw [Determinant.eval_determinant t n
        (firstColumnMinor matrix row)]
      have minorDeterminantEqual := SquareMatrix.Determinant.Laplace.scalarDeterminant_congr
        (SquareMatrix.matrixOfFn fun minorRow column =>
          (firstColumnMinor matrix row minorRow column).eval t)
        (SquareMatrix.Minor.scalarFirstColumnMinor
          (SquareMatrix.matrixOfFn fun matrixRow column =>
            (matrix matrixRow column).eval t) row)
        (fun minorRow column => by
          rw [SquareMatrix.matrixOfFn_apply,
            firstColumnMinor, SquareMatrix.Minor.scalarFirstColumnMinor,
            SquareMatrix.matrixOfFn_apply,
            SquareMatrix.matrixOfFn_apply,
            SquareMatrix.matrixOfFn_apply])
      rw [minorDeterminantEqual]
      exact (mul_assoc _ _ _).symm
end Purelib.LinearAlgebra.PolynomialMatrix.Determinant

end
