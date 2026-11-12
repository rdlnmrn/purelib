module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Vector.Basic
public import Purelib.LinearAlgebra.Matrix.Inverse.Scaled.Action
import Purelib.LinearAlgebra.Matrix.Inverse.Scaled.Compute
public import Purelib.LinearAlgebra.Matrix.Inverse.Scaled.GaussianColumn
import Purelib.LinearAlgebra.Matrix.Multiplication
public import Purelib.LinearAlgebra.Matrix.Multiplication.Gaussian
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
-- Prepared-column agreement retains the original normalized cofactor owner.
public import Purelib.Polynomial.Elimination.Separated.Bezout.Prepared
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

open Purelib.Polynomial.Dense.Gaussian
open Purelib.LinearAlgebra.Matrix.Inverse.Scaled

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

open Purelib.Polynomial.Dense

open Preparation renaming Prepared -> SylvesterPreparation

/-- Evaluate the separated Sylvester matrix at the embedded rational parameter. -/
@[expose] def matrix (p : CoefficientPolynomial) (parameter :
  Fraction.Rational) :
    SquareMatrix Gaussian.Basic.Canonical (p.natDegree + p.natDegree) :=
  PolynomialMatrix.Evaluation.evalMatrix (Gaussian.Cast.Path.ofCoordinate parameter)
    (Sylvester.separatedSylvester p)

set_option genInjectivity false in
/-- A displayed solution of the evaluated separated Sylvester unit-column equation.

The vector retains the original polynomial, positive degree, parameter and exact matrix-vector equation. -/
structure Column (p : CoefficientPolynomial) (positive : 0 < p.natDegree)
  (parameter
  : Fraction.Rational) where
  /-- The retained Gaussian vector solving the original evaluated system. -/ values :
    GaussianColumn.Vector Gaussian.Basic.Canonical (p.natDegree + p.natDegree)
  /-- Multiplication by the original evaluated Sylvester matrix gives the first unit column. -/ equation :
    SquareMatrix.Multiplication.matrixVector (matrix p parameter) values =
    GaussianColumn.unitColumn (Bezout.firstColumnIndex p positive)

constructive_injectivity Column

set_option genInjectivity false in
/-- A witnessed failure of the supplied vector to solve the evaluated unit-column equation.

The failure keeps the computed product vector, its computation equality and the negated pointwise target equation. -/
inductive Invalid (p : CoefficientPolynomial) (positive : 0 < p.natDegree)
    (parameter : Fraction.Rational) (values : GaussianColumn.Vector Gaussian.Basic.Canonical
      (p.natDegree + p.natDegree)) where
  /-- The retained matrix-vector product fails the pointwise first-unit-column equation. -/ | equation (actual :
    GaussianColumn.Vector Gaussian.Basic.Canonical (p.natDegree + p.natDegree))
      (actual_eq : actual = SquareMatrix.Multiplication.matrixVector (matrix p parameter)
        values)
      (failed : ¬ ∀ row, actual row = GaussianColumn.unitColumn
        (Bezout.firstColumnIndex p positive) row)

constructive_injectivity Invalid

/-- Check every row of a displayed separated Sylvester column.

Return the original vector with its exact matrix equation, or retain the computed vector and a proof that the pointwise
target equation fails. -/
@[expose] def check (p : CoefficientPolynomial) (positive : 0 < p.natDegree)
  (parameter : Fraction.Rational)
    (values : GaussianColumn.Vector Gaussian.Basic.Canonical (p.natDegree + p.natDegree)) :
    Except (Invalid p positive parameter values) (Column p
      positive parameter) :=
  let actual := SquareMatrix.Multiplication.Gaussian.matrixVector (matrix p parameter) values
  have actual_eq := SquareMatrix.Multiplication.Gaussian.matrixVector_eq (matrix p parameter) values
  if equal : ∀ row, actual row = GaussianColumn.unitColumn
    (Bezout.firstColumnIndex p positive) row then
    .ok ⟨values, actual_eq.symm.trans (Data.Vector.Basic.vector_ext equal)⟩
  else .error (.equation actual actual_eq equal)

/-- Integer accumulation preserves the original complete column-checking result.

Success retains the supplied vector. Invalidity retains the same complete
matrix product and the same failed row equation, including for singular inputs.
-/
theorem check_eq (p : CoefficientPolynomial) (positive : 0 < p.natDegree)
    (parameter : Fraction.Rational)
    (values : GaussianColumn.Vector Gaussian.Basic.Canonical (p.natDegree + p.natDegree)) :
    check p positive parameter values =
      let actual := SquareMatrix.Multiplication.matrixVector (matrix p parameter) values
      if equal : ∀ row, actual row = GaussianColumn.unitColumn
          (Bezout.firstColumnIndex p positive) row then
        .ok ⟨values, Data.Vector.Basic.vector_ext equal⟩
      else .error (.equation actual rfl equal) := by
  have transport (actual : GaussianColumn.Vector Gaussian.Basic.Canonical
      (p.natDegree + p.natDegree))
      (actual_eq : actual = SquareMatrix.Multiplication.matrixVector (matrix p parameter) values) :
      (if equal : ∀ row, actual row = GaussianColumn.unitColumn
          (Bezout.firstColumnIndex p positive) row then
        Except.ok ⟨values, actual_eq.symm.trans (Data.Vector.Basic.vector_ext equal)⟩
      else Except.error (Invalid.equation actual actual_eq equal)) =
        (let original := SquareMatrix.Multiplication.matrixVector (matrix p parameter) values
         if equal : ∀ row, original row = GaussianColumn.unitColumn
             (Bezout.firstColumnIndex p positive) row then
           Except.ok (⟨values, Data.Vector.Basic.vector_ext equal⟩ : Column p positive parameter)
         else Except.error (Invalid.equation original rfl equal)) := by
    cases actual_eq
    rfl
  exact transport _ (SquareMatrix.Multiplication.Gaussian.matrixVector_eq (matrix p parameter) values)

/-- A finite witness producer, separately checked by `check`. Its result is
not a new trust boundary and does not invoke the symbolic inverse generator. -/
@[expose] def propose (p : CoefficientPolynomial) (positive : 0 <
  p.natDegree)
  (parameter : Fraction.Rational) :
    GaussianColumn.Vector Gaussian.Basic.Canonical (p.natDegree + p.natDegree) :=
  let action := Action.compute (matrix p parameter)
    (GaussianColumn.unitColumn
      (Bezout.firstColumnIndex p positive))
  let reciprocal := action.scalar⁻¹
  Data.Vector.Basic.vectorOfFn fun row => reciprocal * action.values row

/-- The action producer returns exactly the original normalized inverse column.

The equality also covers vanishing scalars. The separately checked equation and
the original certificate fallback retain their existing success conditions. -/
theorem propose_eq (p : CoefficientPolynomial) (positive : 0 < p.natDegree)
    (parameter : Fraction.Rational) :
    propose p positive parameter =
      Data.Vector.Basic.vectorOfFn (fun row =>
        (Compute.scaledInverse (matrix p parameter)).scalar⁻¹ *
          (Compute.scaledInverse (matrix p parameter)).inverse row
            (Bezout.firstColumnIndex p positive)) := by
  unfold propose
  apply Data.Vector.Basic.vector_ext
  intro row
  rewrite [Data.Vector.Basic.vectorOfFn_apply, Data.Vector.Basic.vectorOfFn_apply,
    Action.Applied.scalar_eq,
    Action.Applied.values_eq,
    GaussianColumn.matrixVector_unit]
  rfl

/-- A checked column equals the normalized original scaled-inverse column at every row.

The selected scalar eliminant must be nonzero at the same parameter; uniqueness then identifies the exact original
cofactor data. -/
theorem Column.value_eq {p : CoefficientPolynomial} {positive : 0 <
  p.natDegree}
    {parameter : Fraction.Rational} (column : Column p positive parameter)
    (nonzero : (Scalar.scalarEliminant p).eval parameter ≠ 0) (row : Fin (p.natDegree +
      p.natDegree)) :
    column.values row = ((Bezout.separatedData p).scalar.eval
        (Gaussian.Cast.Path.ofCoordinate parameter))⁻¹ *
      ((Bezout.separatedData p).inverse row (Bezout.firstColumnIndex p
        positive)).eval
        (Gaussian.Cast.Path.ofCoordinate parameter) := by
  simpa only [PolynomialMatrix.Inverse.Scaled.Evaluation.evaluatedScaledInverse,
    PolynomialMatrix.Evaluation.evalMatrix_apply, Bezout.separatedData] using
    GaussianColumn.solution_eq_column (matrix p parameter)
    (PolynomialMatrix.Inverse.Scaled.Evaluation.evaluatedScaledInverse
      (Gaussian.Cast.Path.ofCoordinate parameter) (Sylvester.separatedSylvester p))
    (Scalar.scalar_ne_zero_of_eliminant_eval_ne_zero p parameter nonzero)
    (Bezout.firstColumnIndex p positive) column.values column.equation row

/-- Read the checked column's first half as the ascending left Gaussian cofactor. -/
@[expose] def Column.left {p positive parameter} (column : Column p positive parameter) :
  CoefficientPolynomial :=
  Ascending.polynomialFromLow p.natDegree (fun index => column.values (Fin.castAdd p.natDegree index))

/-- Read the checked column's second half as the ascending right Gaussian cofactor. -/
@[expose] def Column.right {p positive parameter} (column : Column p positive parameter) :
  CoefficientPolynomial :=
  Ascending.polynomialFromLow p.natDegree (fun index => column.values (Fin.natAdd p.natDegree index))

/-- The checked left cofactor evaluates as the original normalized left cofactor when the scalar eliminant is nonzero.
-/
theorem Column.eval_left {p positive parameter} (column : Column p positive parameter)
    (nonzero : (Scalar.scalarEliminant p).eval parameter ≠ 0) (point : Gaussian.Basic.Canonical) :
    column.left.eval point = (Bezout.Normalized.normalizedLeftCofactor p positive parameter).eval
      point := open Purelib.Algebra in by
  rw [Column.left, Bezout.Normalized.normalizedLeftCofactor,
    DensePolynomial.eval_scale, Bezout.leftCofactor,
    Ascending.eval_polynomialFromLow, Ascending.eval_polynomialFromLow, ←
      FiniteSum.Fin.sumFin_mul_left]
  apply FiniteSum.Fin.sumFin_congr
  intro index
  rw [column.value_eq nonzero]
  exact _root_.mul_assoc _ _ _

/-- The checked right cofactor evaluates as the original normalized right cofactor when the scalar eliminant is nonzero.
-/
theorem Column.eval_right {p positive parameter} (column : Column p positive parameter)
    (nonzero : (Scalar.scalarEliminant p).eval parameter ≠ 0) (point : Gaussian.Basic.Canonical) :
    column.right.eval point = (Bezout.Normalized.normalizedRightCofactor p positive
      parameter).eval point := open Purelib.Algebra in by
  rw [Column.right, Bezout.Normalized.normalizedRightCofactor,
    DensePolynomial.eval_scale, Bezout.rightCofactor,
    Ascending.eval_polynomialFromLow, Ascending.eval_polynomialFromLow, ←
      FiniteSum.Fin.sumFin_mul_left]
  apply FiniteSum.Fin.sumFin_congr
  intro index
  rw [column.value_eq nonzero]
  exact _root_.mul_assoc _ _ _

/-- Sum the real coordinate polynomials of both checked cofactors along the displayed affine path. -/
@[expose] def Column.pathLeft {p positive parameter} (column : Column p positive parameter)
    (origin direction : Gaussian.Basic.Canonical) : Dense.Rational.Basic.CoordinatePolynomial :=
  Path.Components.pathReal column.left origin direction +
    Path.Components.pathReal column.right origin direction

/-- Subtract the right cofactor's imaginary path polynomial from the left cofactor's imaginary path polynomial. -/
@[expose] def Column.pathRight {p positive parameter} (column : Column p positive
  parameter)
    (origin direction : Gaussian.Basic.Canonical) : Dense.Rational.Basic.CoordinatePolynomial :=
  Path.Components.pathImag column.left origin direction -
    Path.Components.pathImag column.right origin direction

/-- Both original rational path cofactors after combining the retained Gaussian halves.

Each column half is read once. Its sum and difference are formed before affine
substitution, so cancellation precedes multiplication by the path coordinates.
Linear tables compute only the requested rational coordinate of each product.
Normalizing the two coordinate projections preserves the complete original tables.
-/
@[expose] def Column.pathCofactors {p positive parameter} (column : Column p positive parameter)
    (origin direction : Gaussian.Basic.Canonical) :
    Dense.Rational.Basic.CoordinatePolynomial × Dense.Rational.Basic.CoordinatePolynomial :=
  let left := column.left
  let right := column.right
  (Path.Components.normalizedReal (left + right) origin direction,
    Path.Components.normalizedImag (left - right) origin direction)

/-- The retained real sum is exactly the original checked left-path cofactor for every input. -/
theorem Column.pathCofactors_left {p positive parameter} (column : Column p positive parameter)
    (origin direction : Gaussian.Basic.Canonical) :
    (column.pathCofactors origin direction).1 = column.pathLeft origin direction := by
  apply Rational.Extensionality.rational_normalized_eq_of_eval_eq
    (by rw [pathCofactors, Path.Components.normalizedReal_eq]; exact DensePolynomial.normalize_normalize _)
    (DensePolynomial.normalize_add _ _)
  intro point
  rewrite [pathCofactors, Path.Components.normalizedReal_eq, DensePolynomial.eval_normalize,
    Path.Components.eval_pathReal, DensePolynomial.eval_add,
    Gaussian.Basic.add_re]
  rewrite [DensePolynomial.eval_add, Path.Components.eval_pathReal, Path.Components.eval_pathReal]
  rfl

/-- The retained imaginary difference is exactly the original checked right-path cofactor for every input. -/
theorem Column.pathCofactors_right {p positive parameter} (column : Column p positive parameter)
    (origin direction : Gaussian.Basic.Canonical) :
    (column.pathCofactors origin direction).2 = column.pathRight origin direction := by
  apply Rational.Extensionality.rational_normalized_eq_of_eval_eq
    (by rw [pathCofactors, Path.Components.normalizedImag_eq]; exact DensePolynomial.normalize_normalize _)
    (DensePolynomial.normalize_sub _ _)
  intro point
  rewrite [pathCofactors, Path.Components.normalizedImag_eq, DensePolynomial.eval_normalize,
    Path.Components.eval_pathImag, DensePolynomial.eval_sub,
    Gaussian.Basic.sub_im]
  rewrite [DensePolynomial.eval_sub, Path.Components.eval_pathImag, Path.Components.eval_pathImag]
  rfl

/-- The checked real-path cofactor sum is exactly the original normalized-cofactor sum when the scalar eliminant is
nonzero. -/
theorem Column.pathLeft_eq {p positive parameter} (column : Column p positive parameter)
    (nonzero : (Scalar.scalarEliminant p).eval parameter ≠ 0) (origin direction :
      Gaussian.Basic.Canonical) :
    column.pathLeft origin direction =
      Path.Components.pathReal (Bezout.Normalized.normalizedLeftCofactor p positive
        parameter) origin direction +
        Path.Components.pathReal (Bezout.Normalized.normalizedRightCofactor p
          positive parameter) origin direction := by
  apply Rational.Extensionality.rational_normalized_eq_of_eval_eq
    (DensePolynomial.normalize_add _ _) (DensePolynomial.normalize_add _ _)
  intro point
  simp only [DensePolynomial.eval_add, Path.Components.eval_pathReal,
    column.eval_left nonzero, column.eval_right nonzero, -eq_self]
  rfl

/-- The checked imaginary-path cofactor difference is exactly the original normalized-cofactor difference when the
scalar eliminant is nonzero. -/
theorem Column.pathRight_eq {p positive parameter} (column : Column p positive parameter)
    (nonzero : (Scalar.scalarEliminant p).eval parameter ≠ 0) (origin direction :
      Gaussian.Basic.Canonical) :
    column.pathRight origin direction =
      Path.Components.pathImag (Bezout.Normalized.normalizedLeftCofactor p positive
        parameter) origin direction -
        Path.Components.pathImag (Bezout.Normalized.normalizedRightCofactor p
          positive parameter) origin direction := by
  apply Rational.Extensionality.rational_normalized_eq_of_eval_eq
    (DensePolynomial.normalize_sub _ _) (DensePolynomial.normalize_sub _ _)
  intro point
  simp only [DensePolynomial.eval_sub, Path.Components.eval_pathImag,
    column.eval_left nonzero, column.eval_right nonzero, -eq_self]
  rfl

namespace Column

open Bezout
open Purelib.Algebra
open Purelib.LinearAlgebra.Matrix.Inverse.Scaled.Basic (ScaledInverse)

/-- Construct the exact unit column from the same retained prepared inverse.

The nonzero evaluated scalar is inverted once before reading the selected
inverse entries. The retained right product law certifies the complete unit
equation; no canonical inverse or independent matrix producer is invoked. -/
@[expose] def ofPrepared {p positive parameter} (prepared : SylvesterPreparation p)
    (nonzero : prepared.data.scalar.eval (Gaussian.Cast.Path.ofCoordinate parameter) ≠ 0) :
    Column p positive parameter := by
  let embedded := Gaussian.Cast.Path.ofCoordinate parameter
  let scalar := prepared.data.scalar.eval embedded
  let reciprocal := scalar⁻¹
  let first := firstColumnIndex p positive
  let values := Data.Vector.Basic.vectorOfFn fun row =>
    reciprocal * (prepared.data.inverse row first).eval embedded
  refine ⟨values, ?_⟩
  apply Data.Vector.Basic.vector_ext
  intro row
  have entry := SquareMatrix.matrix_eq_at (prepared.specializations embedded).2 row first
  rewrite [SquareMatrix.Multiplication.mul_apply, SquareMatrix.Multiplication.scaleIdentity,
    SquareMatrix.matrixOfFn_apply] at entry
  have product : FiniteSum.Fin.sumFin (fun middle => matrix p parameter row middle *
      (prepared.data.inverse middle first).eval embedded) =
      if row = first then scalar else 0 := by
    calc
      _ = FiniteSum.Fin.sumFin (fun middle => matrix p parameter row middle *
          PolynomialMatrix.Evaluation.evalMatrix embedded prepared.data.inverse middle first) :=
        FiniteSum.Fin.sumFin_congr fun middle =>
          congrArg (fun value => matrix p parameter row middle * value)
            (PolynomialMatrix.Evaluation.evalMatrix_apply embedded prepared.data.inverse middle first).symm
      _ = _ := entry
  rewrite [SquareMatrix.Multiplication.matrixVector_apply]
  change FiniteSum.Fin.sumFin (fun middle => matrix p parameter row middle * values middle) =
    (GaussianColumn.unitColumn first) row
  calc
    _ = reciprocal * FiniteSum.Fin.sumFin (fun middle => matrix p parameter row middle *
        (prepared.data.inverse middle first).eval embedded) := by
      rewrite [← FiniteSum.Fin.sumFin_mul_left]
      apply FiniteSum.Fin.sumFin_congr
      intro middle
      change matrix p parameter row middle *
        (Data.Vector.Basic.vectorOfFn (fun index =>
          reciprocal * (prepared.data.inverse index first).eval embedded)) middle = _
      rewrite [Data.Vector.Basic.vectorOfFn_apply]
      exact _root_.mul_left_comm _ _ _
    _ = reciprocal * (if row = first then scalar else 0) :=
      congrArg (fun value => reciprocal * value) product
    _ = (GaussianColumn.unitColumn first) row := by
      rewrite [GaussianColumn.unitColumn, Data.Vector.Basic.vectorOfFn_apply]
      by_cases same : row = first
      · rewrite [if_pos same, if_pos same]
        exact Gaussian.Basic.Canonical.inv_mul_cancel scalar nonzero
      · rewrite [if_neg same, if_neg same, mul_zero]
        rfl

/-- A checked unit column reads the normalized column of the same retained prepared inverse.

The prepared scalar must be nonzero at the original rational parameter. Its
two retained product identities supply the original matrix-uniqueness lemma;
neither inverse construction nor an alternate column is computed. -/
private theorem value_eq_prepared {p positive parameter} (column : Column p positive parameter)
    (prepared : SylvesterPreparation p)
    (nonzero : prepared.data.scalar.eval (Gaussian.Cast.Path.ofCoordinate parameter) ≠ 0)
    (row : Fin (p.natDegree + p.natDegree)) :
    column.values row = (prepared.data.scalar.eval (Gaussian.Cast.Path.ofCoordinate parameter))⁻¹ *
      (prepared.data.inverse row (firstColumnIndex p positive)).eval
        (Gaussian.Cast.Path.ofCoordinate parameter) := by
  let inverse : ScaledInverse (matrix p parameter) :=
    { scalar := prepared.data.scalar.eval (Gaussian.Cast.Path.ofCoordinate parameter)
      inverse := PolynomialMatrix.Evaluation.evalMatrix (Gaussian.Cast.Path.ofCoordinate parameter)
        prepared.data.inverse
      left_identity := (prepared.specializations (Gaussian.Cast.Path.ofCoordinate parameter)).1
      right_identity := (prepared.specializations (Gaussian.Cast.Path.ofCoordinate parameter)).2 }
  simpa only [inverse, PolynomialMatrix.Evaluation.evalMatrix_apply] using
    GaussianColumn.solution_eq_column (matrix p parameter) inverse nonzero
      (firstColumnIndex p positive) column.values column.equation row

/-- The checked left cofactor evaluates as the same retained prepared normalized cofactor. -/
private theorem eval_left_prepared {p positive parameter} (column : Column p positive parameter)
    (prepared : SylvesterPreparation p)
    (nonzero : prepared.data.scalar.eval (Gaussian.Cast.Path.ofCoordinate parameter) ≠ 0)
    (point : Gaussian.Basic.Canonical) :
    column.left.eval point = (Prepared.normalizedLeft prepared positive parameter).eval point := by
  rw [Column.left, Prepared.normalizedLeft, DensePolynomial.eval_scale, Prepared.left,
    Ascending.eval_polynomialFromLow, Ascending.eval_polynomialFromLow, ← FiniteSum.Fin.sumFin_mul_left]
  apply FiniteSum.Fin.sumFin_congr
  intro index
  rw [column.value_eq_prepared prepared nonzero]
  exact _root_.mul_assoc _ _ _

/-- The checked right cofactor evaluates as the same retained prepared normalized cofactor. -/
private theorem eval_right_prepared {p positive parameter} (column : Column p positive parameter)
    (prepared : SylvesterPreparation p)
    (nonzero : prepared.data.scalar.eval (Gaussian.Cast.Path.ofCoordinate parameter) ≠ 0)
    (point : Gaussian.Basic.Canonical) :
    column.right.eval point = (Prepared.normalizedRight prepared positive parameter).eval point := by
  rw [Column.right, Prepared.normalizedRight, DensePolynomial.eval_scale, Prepared.right,
    Ascending.eval_polynomialFromLow, Ascending.eval_polynomialFromLow, ← FiniteSum.Fin.sumFin_mul_left]
  apply FiniteSum.Fin.sumFin_congr
  intro index
  rw [column.value_eq_prepared prepared nonzero]
  exact _root_.mul_assoc _ _ _

/-- Both checked path tables equal the complete same-preparation cofactor tables.

The actual source polynomial, rational parameter, prepared inverse and affine
path are retained. Scalar nonvanishing and the checked unit-column equation
identify both normalized rational coefficient tables, including leading zeros. -/
theorem pathCofactors_eq_prepared {p positive parameter} (column : Column p positive parameter)
    (prepared : SylvesterPreparation p)
    (nonzero : prepared.data.scalar.eval (Gaussian.Cast.Path.ofCoordinate parameter) ≠ 0)
    (origin direction : Gaussian.Basic.Canonical) :
    column.pathCofactors origin direction =
      (Path.Components.pathReal (Prepared.normalizedLeft prepared positive parameter) origin direction +
          Path.Components.pathReal (Prepared.normalizedRight prepared positive parameter) origin direction,
        Path.Components.pathImag (Prepared.normalizedLeft prepared positive parameter) origin direction -
          Path.Components.pathImag (Prepared.normalizedRight prepared positive parameter) origin direction) := by
  apply Prod.ext
  · refine (column.pathCofactors_left origin direction).trans ?_
    apply Rational.Extensionality.rational_normalized_eq_of_eval_eq
      (DensePolynomial.normalize_add _ _) (DensePolynomial.normalize_add _ _)
    intro point
    simp only [DensePolynomial.eval_add, Path.Components.eval_pathReal,
      column.eval_left_prepared prepared nonzero, column.eval_right_prepared prepared nonzero,
      -eq_self, -iff_self]
    rfl
  · refine (column.pathCofactors_right origin direction).trans ?_
    apply Rational.Extensionality.rational_normalized_eq_of_eval_eq
      (DensePolynomial.normalize_sub _ _) (DensePolynomial.normalize_sub _ _)
    intro point
    simp only [DensePolynomial.eval_sub, Path.Components.eval_pathImag,
      column.eval_left_prepared prepared nonzero, column.eval_right_prepared prepared nonzero,
      -eq_self, -iff_self]
    rfl

end Column

end Purelib.Polynomial.Elimination.Separated.Replay

end
