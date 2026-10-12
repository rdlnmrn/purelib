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
    (matrix : BivariateMatrix (Polynomial.Dense.Basic.CoefficientPolynomial K) (n + 1))
    (row : Fin (n + 1)) : BivariateMatrix (Polynomial.Dense.Basic.CoefficientPolynomial K) n :=
  SquareMatrix.matrixOfFn fun minorRow column =>
    matrix (Data.Fin.skipIndex row minorRow) column.succ

open Purelib.LinearAlgebra in
/-- Compute a finite determinant over dense coordinate polynomials.

Each first-column term retains its signed scalar, original polynomial entry
and bounded minor. The same finite left fold sums the resulting polynomials. -/
@[expose] def determinant : (n : Nat) →
    BivariateMatrix (Polynomial.Dense.Basic.CoefficientPolynomial K) n → Polynomial.Dense.Basic.CoefficientPolynomial K
  | 0, _ => Dense.Basic.DensePolynomial.constant 1
  | n + 1, matrix =>
      (List.ofFn fun row : Fin (n + 1) =>
        Dense.Basic.DensePolynomial.scale ((-1 : K) ^ (row : Nat))
          (matrix row 0 * Purelib.LinearAlgebra.PolynomialMatrix.Determinant.determinant n
            (PolynomialMatrix.Determinant.firstColumnMinor matrix row))).foldl
        (fun a b => a + b) 0

/-- Evaluating a polynomial addition fold gives the corresponding scalar addition fold.

The polynomial accumulator is evaluated at the same supplied point. -/
private theorem eval_foldl_add (t : K)
    (polynomials : List (Polynomial.Dense.Basic.CoefficientPolynomial K))
    (accumulator : Polynomial.Dense.Basic.CoefficientPolynomial K) :
    (polynomials.foldl (fun a b => a + b) accumulator).eval t =
      (polynomials.map (fun p => p.eval t)).foldl
        (fun a b => a + b) (accumulator.eval t) := by
  induction polynomials generalizing accumulator with
  | nil => rfl
  | cons p remaining inductionHypothesis =>
      simp only [List.foldl_cons, List.map_cons]
      rw [inductionHypothesis,
        Dense.Basic.DensePolynomial.eval_add]

open Purelib.LinearAlgebra in
/-- Evaluating the finite polynomial determinant gives the determinant of the evaluated entries.

Both determinants use the same first-column Laplace recursion and retained minor indices. -/
theorem eval_determinant (t : K) : ∀ (n : Nat)
    (matrix : BivariateMatrix (Polynomial.Dense.Basic.CoefficientPolynomial K) n),
    (PolynomialMatrix.Determinant.determinant n matrix).eval t =
      SquareMatrix.Determinant.Laplace.scalarDeterminant n
        (SquareMatrix.matrixOfFn fun row column =>
          (matrix row column).eval t)
  | 0, _ => by
      change (Dense.Basic.DensePolynomial.constant 1).eval t = 1
      exact Dense.Basic.DensePolynomial.eval_constant 1 t
  | n + 1, matrix => by
      rw [PolynomialMatrix.Determinant.determinant, SquareMatrix.Determinant.Laplace.scalarDeterminant,
        Purelib.LinearAlgebra.PolynomialMatrix.Determinant.eval_foldl_add,
        Dense.Basic.DensePolynomial.eval_zero,
        Purelib.Data.List.OfFn.Basic.map_ofFn]
      apply congrArg (fun values : List K =>
        values.foldl (fun a b => a + b) 0)
      apply Purelib.Data.List.OfFn.Basic.ofFn_congr
      intro row
      simp only [Function.comp_apply,
        SquareMatrix.matrixOfFn_apply]
      change
        (Dense.Basic.DensePolynomial.scale ((-1 : K) ^ (row : Nat))
            (matrix row 0 * PolynomialMatrix.Determinant.determinant n
              (PolynomialMatrix.Determinant.firstColumnMinor matrix row))).eval t =
          (-1 : K) ^ (row : Nat) * (matrix row 0).eval t *
            SquareMatrix.Determinant.Laplace.scalarDeterminant n
              (SquareMatrix.Minor.scalarFirstColumnMinor
                (SquareMatrix.matrixOfFn
                  fun matrixRow column =>
                    (matrix matrixRow column).eval t) row)
      rw [Dense.Basic.DensePolynomial.eval_scale,
        Dense.Basic.DensePolynomial.eval_mul]
      rw [Purelib.LinearAlgebra.PolynomialMatrix.Determinant.eval_determinant t n
        (PolynomialMatrix.Determinant.firstColumnMinor matrix row)]
      have minorDeterminantEqual := SquareMatrix.Determinant.Laplace.scalarDeterminant_congr
        (SquareMatrix.matrixOfFn fun minorRow column =>
          (PolynomialMatrix.Determinant.firstColumnMinor matrix row minorRow column).eval t)
        (SquareMatrix.Minor.scalarFirstColumnMinor
          (SquareMatrix.matrixOfFn fun matrixRow column =>
            (matrix matrixRow column).eval t) row)
        (fun minorRow column => by
          rw [SquareMatrix.matrixOfFn_apply,
            PolynomialMatrix.Determinant.firstColumnMinor, SquareMatrix.Minor.scalarFirstColumnMinor,
            SquareMatrix.matrixOfFn_apply,
            SquareMatrix.matrixOfFn_apply,
            SquareMatrix.matrixOfFn_apply])
      rw [minorDeterminantEqual]
      exact (mul_assoc _ _ _).symm
end Purelib.LinearAlgebra.PolynomialMatrix.Determinant

end
