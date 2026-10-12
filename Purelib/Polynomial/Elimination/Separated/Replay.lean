module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Vector.Basic
public import Purelib.LinearAlgebra.Matrix.Inverse.Scaled.Compute
public import Purelib.LinearAlgebra.Matrix.Inverse.Scaled.GaussianColumn
import Purelib.LinearAlgebra.Matrix.Multiplication
import Purelib.LinearAlgebra.PolynomialMatrix.Evaluation
public import Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Evaluation
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Gaussian.Ascending
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Path.Components
import Purelib.Polynomial.Dense.Rational.Extensionality
import Purelib.Polynomial.Elimination.Separated.Bezout
public import Purelib.Polynomial.Elimination.Separated.Bezout.Normalized
public import Purelib.Polynomial.Elimination.Separated.Scalar
import Purelib.Polynomial.Elimination.Separated.Sylvester
import Purelib.LinearAlgebra.Matrix.Basic
public import Purelib.Polynomial.Dense.Rational.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.LinearAlgebra.Matrix.Inverse.Scaled.Basic
import Purelib.LinearAlgebra.PolynomialMatrix.Basic
import Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Basic
import Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Compute
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix

open Purelib.LinearAlgebra

open Purelib.Polynomial

/-!
Checked finite witnesses for the original separated-Sylvester clearances.
An untrusted column solves the evaluated matrix equation. The original scaled
inverse proves uniqueness, so the saved column supplies the original normalized
cofactors, rather than merely some valid Bezout coefficients. Equality of the
resulting rational polynomials uses the existing explicit finite-grid theorem.
-/

public section

namespace Purelib.Polynomial.Elimination.Separated.Replay

/-- Evaluate the separated Sylvester matrix at the embedded rational parameter. -/
@[expose] def matrix (p : CoefficientPolynomial) (parameter :
  Fraction.Rational) :
    SquareMatrix Gaussian.Basic.Canonical (p.natDegree + p.natDegree) :=
  PolynomialMatrix.Evaluation.evalMatrix (Gaussian.Cast.Path.ofCoordinate parameter)
    (Elimination.Separated.Sylvester.separatedSylvester p)

set_option genInjectivity false in
/-- A displayed solution of the evaluated separated Sylvester unit-column equation.

The vector retains the original polynomial, positive degree, parameter and exact matrix-vector equation. -/
structure Column (p : CoefficientPolynomial) (positive : 0 < p.natDegree)
  (parameter
  : Fraction.Rational) where
  /-- The retained Gaussian vector solving the original evaluated system. -/ values :
    SquareMatrix.Inverse.Scaled.GaussianColumn.Vector Gaussian.Basic.Canonical (p.natDegree + p.natDegree)
  /-- Multiplication by the original evaluated Sylvester matrix gives the first unit column. -/ equation :
    SquareMatrix.Multiplication.matrixVector (matrix p parameter) values =
    SquareMatrix.Inverse.Scaled.GaussianColumn.unitColumn (Elimination.Separated.Bezout.firstColumnIndex p positive)

constructive_injectivity Column

set_option genInjectivity false in
/-- A witnessed failure of the supplied vector to solve the evaluated unit-column equation.

The failure keeps the computed product vector, its computation equality and the negated pointwise target equation. -/
inductive Invalid (p : CoefficientPolynomial) (positive : 0 < p.natDegree)
    (parameter : Fraction.Rational) (values : SquareMatrix.Inverse.Scaled.GaussianColumn.Vector Gaussian.Basic.Canonical
      (p.natDegree + p.natDegree)) where
  /-- The retained matrix-vector product fails the pointwise first-unit-column equation. -/ | equation (actual :
    SquareMatrix.Inverse.Scaled.GaussianColumn.Vector Gaussian.Basic.Canonical (p.natDegree + p.natDegree))
      (actual_eq : actual = SquareMatrix.Multiplication.matrixVector (matrix p parameter)
        values)
      (failed : ¬ ∀ row, actual row = SquareMatrix.Inverse.Scaled.GaussianColumn.unitColumn
        (Elimination.Separated.Bezout.firstColumnIndex p positive) row)

constructive_injectivity Invalid

/-- Check every row of a displayed separated Sylvester column.

Return the original vector with its exact matrix equation, or retain the computed vector and a proof that the pointwise
target equation fails. -/
@[expose] def check (p : CoefficientPolynomial) (positive : 0 < p.natDegree)
  (parameter : Fraction.Rational)
    (values : SquareMatrix.Inverse.Scaled.GaussianColumn.Vector Gaussian.Basic.Canonical (p.natDegree + p.natDegree)) :
    Except (Invalid p positive parameter values) (Column p
      positive parameter) :=
  let actual := SquareMatrix.Multiplication.matrixVector (matrix p parameter) values
  if equal : ∀ row, actual row = SquareMatrix.Inverse.Scaled.GaussianColumn.unitColumn
    (Elimination.Separated.Bezout.firstColumnIndex p positive) row then
    .ok ⟨values, Data.Vector.Basic.vector_ext equal⟩
  else .error (.equation actual rfl equal)

/-- A finite witness producer, separately checked by `check`. Its result is
not a new trust boundary and does not invoke the symbolic inverse generator. -/
@[expose] def propose (p : CoefficientPolynomial) (positive : 0 <
  p.natDegree)
  (parameter : Fraction.Rational) :
    SquareMatrix.Inverse.Scaled.GaussianColumn.Vector Gaussian.Basic.Canonical (p.natDegree + p.natDegree) :=
  let inverse := SquareMatrix.Inverse.Scaled.Compute.scaledInverse (matrix p parameter)
  let reciprocal := inverse.scalar⁻¹
  Data.Vector.Basic.vectorOfFn fun row => reciprocal * inverse.inverse row
    (Elimination.Separated.Bezout.firstColumnIndex p positive)

/-- A checked column equals the normalized original scaled-inverse column at every row.

The selected scalar eliminant must be nonzero at the same parameter; uniqueness then identifies the exact original
cofactor data. -/
theorem Column.value_eq {p : CoefficientPolynomial} {positive : 0 <
  p.natDegree}
    {parameter : Fraction.Rational} (column : Column p positive parameter)
    (nonzero : (Elimination.Separated.Scalar.scalarEliminant p).eval parameter ≠ 0) (row : Fin (p.natDegree +
      p.natDegree)) :
    column.values row = ((Elimination.Separated.Bezout.separatedData p).scalar.eval
        (Gaussian.Cast.Path.ofCoordinate parameter))⁻¹ *
      ((Elimination.Separated.Bezout.separatedData p).inverse row (Elimination.Separated.Bezout.firstColumnIndex p
        positive)).eval
        (Gaussian.Cast.Path.ofCoordinate parameter) := by
  simpa only [PolynomialMatrix.Inverse.Scaled.Evaluation.evaluatedScaledInverse,
    PolynomialMatrix.Evaluation.evalMatrix_apply, Elimination.Separated.Bezout.separatedData] using
    SquareMatrix.Inverse.Scaled.GaussianColumn.solution_eq_column (matrix p parameter)
    (PolynomialMatrix.Inverse.Scaled.Evaluation.evaluatedScaledInverse
      (Gaussian.Cast.Path.ofCoordinate parameter) (Elimination.Separated.Sylvester.separatedSylvester p))
    (Elimination.Separated.Scalar.scalar_ne_zero_of_eliminant_eval_ne_zero p parameter nonzero)
    (Elimination.Separated.Bezout.firstColumnIndex p positive) column.values column.equation row

/-- Read the checked column's first half as the ascending left Gaussian cofactor. -/
@[expose] def Column.left {p positive parameter} (column : Column p positive parameter) :
  CoefficientPolynomial :=
  Dense.Gaussian.Ascending.polynomialFromLow p.natDegree (fun index => column.values (Fin.castAdd p.natDegree index))

/-- Read the checked column's second half as the ascending right Gaussian cofactor. -/
@[expose] def Column.right {p positive parameter} (column : Column p positive parameter) :
  CoefficientPolynomial :=
  Dense.Gaussian.Ascending.polynomialFromLow p.natDegree (fun index => column.values (Fin.natAdd p.natDegree index))

/-- The checked left cofactor evaluates as the original normalized left cofactor when the scalar eliminant is nonzero.
-/
theorem Column.eval_left {p positive parameter} (column : Column p positive parameter)
    (nonzero : (Elimination.Separated.Scalar.scalarEliminant p).eval parameter ≠ 0) (point : Gaussian.Basic.Canonical) :
    column.left.eval point = (Elimination.Separated.Bezout.Normalized.normalizedLeftCofactor p positive parameter).eval
      point := open Purelib.Algebra in by
  rw [Elimination.Separated.Replay.Column.left, Elimination.Separated.Bezout.Normalized.normalizedLeftCofactor,
    DensePolynomial.eval_scale, Elimination.Separated.Bezout.leftCofactor,
    Dense.Gaussian.Ascending.eval_polynomialFromLow, Dense.Gaussian.Ascending.eval_polynomialFromLow, ←
      FiniteSum.Fin.sumFin_mul_left]
  apply FiniteSum.Fin.sumFin_congr
  intro index
  rw [column.value_eq nonzero]
  exact _root_.mul_assoc _ _ _

/-- The checked right cofactor evaluates as the original normalized right cofactor when the scalar eliminant is nonzero.
-/
theorem Column.eval_right {p positive parameter} (column : Column p positive parameter)
    (nonzero : (Elimination.Separated.Scalar.scalarEliminant p).eval parameter ≠ 0) (point : Gaussian.Basic.Canonical) :
    column.right.eval point = (Elimination.Separated.Bezout.Normalized.normalizedRightCofactor p positive
      parameter).eval point := open Purelib.Algebra in by
  rw [Elimination.Separated.Replay.Column.right, Elimination.Separated.Bezout.Normalized.normalizedRightCofactor,
    DensePolynomial.eval_scale, Elimination.Separated.Bezout.rightCofactor,
    Dense.Gaussian.Ascending.eval_polynomialFromLow, Dense.Gaussian.Ascending.eval_polynomialFromLow, ←
      FiniteSum.Fin.sumFin_mul_left]
  apply FiniteSum.Fin.sumFin_congr
  intro index
  rw [column.value_eq nonzero]
  exact _root_.mul_assoc _ _ _

/-- Sum the real coordinate polynomials of both checked cofactors along the displayed affine path. -/
@[expose] def Column.pathLeft {p positive parameter} (column : Column p positive parameter)
    (origin direction : Gaussian.Basic.Canonical) : Dense.Rational.Basic.CoordinatePolynomial :=
  Dense.Gaussian.Path.Components.pathReal column.left origin direction +
    Dense.Gaussian.Path.Components.pathReal column.right origin direction

/-- Subtract the right cofactor's imaginary path polynomial from the left cofactor's imaginary path polynomial. -/
@[expose] def Column.pathRight {p positive parameter} (column : Column p positive
  parameter)
    (origin direction : Gaussian.Basic.Canonical) : Dense.Rational.Basic.CoordinatePolynomial :=
  Dense.Gaussian.Path.Components.pathImag column.left origin direction -
    Dense.Gaussian.Path.Components.pathImag column.right origin direction

/-- The checked real-path cofactor sum is exactly the original normalized-cofactor sum when the scalar eliminant is
nonzero. -/
theorem Column.pathLeft_eq {p positive parameter} (column : Column p positive parameter)
    (nonzero : (Elimination.Separated.Scalar.scalarEliminant p).eval parameter ≠ 0) (origin direction :
      Gaussian.Basic.Canonical) :
    column.pathLeft origin direction =
      Dense.Gaussian.Path.Components.pathReal (Elimination.Separated.Bezout.Normalized.normalizedLeftCofactor p positive
        parameter) origin direction +
        Dense.Gaussian.Path.Components.pathReal (Elimination.Separated.Bezout.Normalized.normalizedRightCofactor p
          positive parameter) origin direction := by
  apply Dense.Rational.Extensionality.rational_normalized_eq_of_eval_eq
    (DensePolynomial.normalize_add _ _) (DensePolynomial.normalize_add _ _)
  intro point
  simp only [DensePolynomial.eval_add, Dense.Gaussian.Path.Components.eval_pathReal,
    column.eval_left nonzero, column.eval_right nonzero, -eq_self]
  rfl

/-- The checked imaginary-path cofactor difference is exactly the original normalized-cofactor difference when the
scalar eliminant is nonzero. -/
theorem Column.pathRight_eq {p positive parameter} (column : Column p positive parameter)
    (nonzero : (Elimination.Separated.Scalar.scalarEliminant p).eval parameter ≠ 0) (origin direction :
      Gaussian.Basic.Canonical) :
    column.pathRight origin direction =
      Dense.Gaussian.Path.Components.pathImag (Elimination.Separated.Bezout.Normalized.normalizedLeftCofactor p positive
        parameter) origin direction -
        Dense.Gaussian.Path.Components.pathImag (Elimination.Separated.Bezout.Normalized.normalizedRightCofactor p
          positive parameter) origin direction := by
  apply Dense.Rational.Extensionality.rational_normalized_eq_of_eval_eq
    (DensePolynomial.normalize_sub _ _) (DensePolynomial.normalize_sub _ _)
  intro point
  simp only [DensePolynomial.eval_sub, Dense.Gaussian.Path.Components.eval_pathImag,
    column.eval_left nonzero, column.eval_right nonzero, -eq_self]
  rfl
end Purelib.Polynomial.Elimination.Separated.Replay

end
