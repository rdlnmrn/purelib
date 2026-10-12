module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Fin
-- Exposed coefficient readback retains this original list coordinate API.
public import Purelib.Data.List.GetD
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.LinearAlgebra.Matrix.Determinant.Laplace
public import Purelib.LinearAlgebra.PolynomialMatrix.Determinant
import Purelib.Polynomial.Dense.Basic
public import Purelib.Polynomial.Dense.Bivariate.Basic
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Evaluation

open Purelib.Algebra.Field

open Purelib

open Purelib.LinearAlgebra.Matrix.Bivariate renaming Square -> BivariateMatrix

open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix

open Purelib.LinearAlgebra

open Purelib.Polynomial

public section

/-!
# Finite bivariate coordinate polynomials and determinants

Both variables are represented by finite high-to-low coefficient lists.  The
determinant is an explicit Laplace recursion over `Fin n`; it does not use a
sparse polynomial, a generic matrix determinant, or any infinite carrier.
-/

namespace Purelib.Polynomial.Dense.Bivariate.Resultant
variable {K : Type*} [ExplicitField K] [DecidableEq K]

/-! ## Finite Laplace determinant and Sylvester output -/

/-- Read an ascending outer coefficient from the descending bivariate table.

The same original reversed coefficient table and natural coordinate determine
the retained dense inner polynomial. The original zero polynomial is returned
beyond the table without replacing its carrier or selected coefficient data. -/
@[expose] def outerCoeff (p : Dense.Bivariate.Basic.DenseBivariate K) (n : Nat) : Basic.CoefficientPolynomial K :=
  Data.List.getD p.coeffs.reverse n 0

/-- Construct the displayed finite Sylvester matrix from two bivariate polynomials and retained outer degree bounds.

Its left block uses shifted coefficients of the second polynomial and its right block those of the first, with zero
outside each displayed coefficient band. -/
@[expose] def sylvester (f g : Dense.Bivariate.Basic.DenseBivariate K) (m n : Nat) :
    BivariateMatrix (Basic.CoefficientPolynomial K) (m + n) :=
  SquareMatrix.matrixOfFn fun row column =>
    Data.Fin.addCases
    (fun left =>
      if (left : Nat) ≤ (row : Nat) ∧ (row : Nat) ≤ (left : Nat) + n
      then Dense.Bivariate.Resultant.outerCoeff g ((row : Nat) - left) else 0)
    (fun right =>
      if (right : Nat) ≤ (row : Nat) ∧ (row : Nat) ≤ (right : Nat) + m
      then Dense.Bivariate.Resultant.outerCoeff f ((row : Nat) - right) else 0) column

omit [ExplicitField K] [DecidableEq K] in
/-- Read a displayed entry in the left Sylvester block.

The original cast index selects the supplied left coefficient branch. Its
retained row and column bounds determine the same coefficient or zero without
identifying the two functions supplied to the finite index splitter. -/
theorem sylvester_left_apply (f g : Dense.Bivariate.Basic.DenseBivariate K) (m n : Nat)
    (row : Fin (m + n)) (column : Fin m) :
    Dense.Bivariate.Resultant.sylvester f g m n row (Fin.castAdd n column) =
      if (column : Nat) ≤ (row : Nat) ∧
          (row : Nat) ≤ (column : Nat) + n then
        Dense.Bivariate.Resultant.outerCoeff g ((row : Nat) - column)
      else 0 := by
  unfold Dense.Bivariate.Resultant.sylvester
  rw [SquareMatrix.matrixOfFn_apply,
    Data.Fin.addCases_left]

omit [ExplicitField K] [DecidableEq K] in
/-- Read a displayed entry in the right Sylvester block.

The original shifted index selects the supplied right coefficient branch. The
same row, column and degree bounds determine the retained first-polynomial
coefficient or the original zero polynomial. -/
theorem sylvester_right_apply (f g : Dense.Bivariate.Basic.DenseBivariate K) (m n : Nat)
    (row : Fin (m + n)) (column : Fin n) :
    Dense.Bivariate.Resultant.sylvester f g m n row (Fin.natAdd m column) =
      if (column : Nat) ≤ (row : Nat) ∧
          (row : Nat) ≤ (column : Nat) + m then
        Dense.Bivariate.Resultant.outerCoeff f ((row : Nat) - column)
      else 0 := by
  unfold Dense.Bivariate.Resultant.sylvester
  rw [SquareMatrix.matrixOfFn_apply,
    Data.Fin.addCases_right]

/-- Compute the finite polynomial determinant of the displayed Sylvester matrix.

The original matrix and retained sum of degree bounds are passed to the same
finite determinant procedure. Its coefficient polynomials remain in their
original dense representation. -/
@[expose] def resultant (f g : Dense.Bivariate.Basic.DenseBivariate K) (m n : Nat) : Basic.CoefficientPolynomial K :=
  PolynomialMatrix.Determinant.determinant (m + n) (Dense.Bivariate.Resultant.sylvester f g m n)

/-- Evaluate the resultant as the scalar Laplace determinant of its evaluated entries.

The original Sylvester matrix, degree bounds and scalar evaluation point are
retained. Pointwise inner-polynomial evaluation transports the same finite
matrix determinant without selecting a new polynomial realization. -/
theorem eval_resultant (f g : Dense.Bivariate.Basic.DenseBivariate K) (m n : Nat) (t : K) :
    (Dense.Bivariate.Resultant.resultant f g m n).eval t =
      SquareMatrix.Determinant.Laplace.scalarDeterminant (m + n)
        (SquareMatrix.matrixOfFn fun row column =>
          (Dense.Bivariate.Resultant.sylvester f g m n row column).eval t) :=
  PolynomialMatrix.Determinant.eval_determinant t (m + n) (Dense.Bivariate.Resultant.sylvester f g m n)

end Purelib.Polynomial.Dense.Bivariate.Resultant
