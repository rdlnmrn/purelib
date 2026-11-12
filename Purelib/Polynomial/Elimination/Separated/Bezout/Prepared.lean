module

public import Purelib.Polynomial.Elimination.Separated.Preparation
import Purelib.Data.Gaussian.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Gaussian
import Purelib.Data.Fin
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.LinearAlgebra.Matrix.Gaussian.WeightedSum
public import Purelib.LinearAlgebra.Matrix.Multiplication
import Purelib.LinearAlgebra.PolynomialMatrix.Evaluation
import Purelib.Polynomial.Dense.Bivariate.Basic
public import Purelib.Polynomial.Dense.Gaussian.Ascending
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Elimination.Separated.Bezout
import Purelib.Polynomial.Elimination.Separated.Sylvester.Evaluation

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Field
import Purelib.LinearAlgebra.PolynomialMatrix.Basic
import Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Bivariate.Gaussian.Lift
import Purelib.Polynomial.Dense.Bivariate.Gaussian.Reflection.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring

/-! # Cofactors from checked separated Sylvester preparation -/

public section

namespace Purelib.Polynomial.Elimination.Separated.Bezout.Prepared

open Purelib
open Purelib.Data
open Purelib.Data.Rat
open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix
open Purelib.LinearAlgebra
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Bivariate.Gaussian
open Purelib.Polynomial.Dense.Bivariate.Gaussian.Reflection.Basic

/-- Read the retained first half of this prepared inverse column as an ascending cofactor. -/
@[expose] def left {p : CoefficientPolynomial} (prepared : Preparation.Prepared p)
    (degreePositive : 0 < p.natDegree) (parameter : Gaussian.Basic.Canonical) :
    Dense.Basic.DensePolynomial Gaussian.Basic.Canonical :=
  Dense.Gaussian.Ascending.polynomialFromLow p.natDegree (fun index =>
    (prepared.data.inverse (Fin.castAdd p.natDegree index) (firstColumnIndex p degreePositive)).eval parameter)

/-- Read the retained second half of this prepared inverse column as an ascending cofactor. -/
@[expose] def right {p : CoefficientPolynomial} (prepared : Preparation.Prepared p)
    (degreePositive : 0 < p.natDegree) (parameter : Gaussian.Basic.Canonical) :
    Dense.Basic.DensePolynomial Gaussian.Basic.Canonical :=
  Dense.Gaussian.Ascending.polynomialFromLow p.natDegree (fun index =>
    (prepared.data.inverse (Fin.natAdd p.natDegree index) (firstColumnIndex p degreePositive)).eval parameter)

/-- This same retained scaled inverse supplies a separated Bezout identity with its own scalar.

The complete original product law is specialized at the supplied parameter.
Both cofactors read that same cached inverse and the original source's bounded
column indices, without invoking any symbolic inverse producer.
-/
theorem identity {p : CoefficientPolynomial} (prepared : Preparation.Prepared p)
    (nonzero : p.isZero = false) (degreePositive : 0 < p.natDegree)
    (outer parameter : Gaussian.Basic.Canonical) :
    (left prepared degreePositive parameter).eval outer *
        Dense.Bivariate.Basic.eval (SeparatedVariables.reflected p) outer parameter +
      (right prepared degreePositive parameter).eval outer *
        Dense.Bivariate.Basic.eval (Lift.SeparatedVariables.lifted p) outer parameter =
      prepared.data.scalar.eval parameter := open Purelib.Algebra in by
  let size := p.natDegree + p.natDegree
  let matrix := PolynomialMatrix.Evaluation.evalMatrix parameter
    (Sylvester.separatedSylvester p)
  let inverse := PolynomialMatrix.Evaluation.evalMatrix parameter
    prepared.data.inverse
  let scalar := prepared.data.scalar.eval parameter
  let first := firstColumnIndex p degreePositive
  let vector : Data.Vector Gaussian.Basic.Canonical size :=
    Data.Vector.Basic.vectorOfFn fun column =>
      inverse column first
  let weights : Data.Vector Gaussian.Basic.Canonical size :=
    Data.Vector.Basic.vectorOfFn fun row => outer ^ (row : Nat)
  have inverseIdentity :=
    (prepared.specializations parameter).2
  have matrixVectorIdentity :
      SquareMatrix.Multiplication.matrixVector matrix vector =
        Data.Vector.Basic.vectorOfFn fun row =>
          if row = first then scalar else 0 := by
    apply Data.Vector.Basic.vector_ext
    intro row
    have entryIdentity := SquareMatrix.matrix_eq_at
      inverseIdentity row first
    change SquareMatrix.Multiplication.mul matrix inverse row first =
      SquareMatrix.Multiplication.scaleIdentity scalar row first
      at entryIdentity
    rewrite [SquareMatrix.Multiplication.mul_apply,
      SquareMatrix.Multiplication.scaleIdentity,
      SquareMatrix.matrixOfFn_apply] at entryIdentity
    rewrite [SquareMatrix.Multiplication.matrixVector_apply matrix vector row,
      Data.Vector.Basic.vectorOfFn_apply (fun row : Fin size => if row = first then scalar else 0) row]
    calc
      _ = FiniteSum.Fin.sumFin (fun column => matrix row column * inverse column first) := by
        apply FiniteSum.Fin.sumFin_congr
        intro column
        change matrix row column *
          (Data.Vector.Basic.vectorOfFn (fun column => inverse column first)) column = _
        rewrite [Data.Vector.Basic.vectorOfFn_apply]
        rfl
      _ = _ := entryIdentity
  have weightedIdentity :
      FiniteSum.Fin.sumFin
          (fun row =>
            SquareMatrix.Multiplication.matrixVector matrix vector row *
              weights row) = scalar := by
    rw [matrixVectorIdentity]
    rw [FiniteSum.Fin.sumFin_congr
      (left := fun row =>
        (Data.Vector.Basic.vectorOfFn fun row =>
          if row = first then scalar else 0) row * weights row)
      (right := fun row =>
        (if row = first then scalar else 0) * weights row)
      (fun row => by
        rw [Data.Vector.Basic.vectorOfFn_apply])]
    rw [FiniteSum.Fin.sumFin_congr
      (left := fun row =>
        (if row = first then scalar else 0) * weights row)
      (right := fun row =>
        if row = first then scalar * weights row else 0)
      (fun row => by
        split <;> ring1)]
    rw [FiniteSum.Fin.sumFin_ite_eq]
    simp only [weights, first,
      Data.Vector.Basic.vectorOfFn_apply, firstColumnIndex]
    rw [pow_zero, mul_one]
  have columnIdentity := SquareMatrix.Gaussian.WeightedSum.weighted_matrixVector
    matrix vector
    weights
  rw [weightedIdentity] at columnIdentity
  calc
    (left prepared degreePositive parameter).eval outer *
          Dense.Bivariate.Basic.eval (SeparatedVariables.reflected p) outer
            parameter +
        (right prepared degreePositive parameter).eval outer *
          Dense.Bivariate.Basic.eval (Lift.SeparatedVariables.lifted p) outer parameter =
      FiniteSum.Fin.sumFin
        (fun column : Fin size =>
          FiniteSum.Fin.sumFin
              (fun row : Fin size => matrix row column * weights row) *
            vector column) := by
              rw [FiniteSum.Fin.sumFin_congr
                (left := fun column : Fin size =>
                  FiniteSum.Fin.sumFin
                      (fun row : Fin size => matrix row column * weights row) *
                    vector column)
                (right := fun column : Fin size =>
                  Data.Fin.addCases
                    (fun index =>
                      (outer ^ (index : Nat) *
                        Dense.Bivariate.Basic.eval
                          (SeparatedVariables.reflected p)
                          outer parameter) * vector (Fin.castAdd p.natDegree index))
                    (fun index =>
                      (outer ^ (index : Nat) *
                        Dense.Bivariate.Basic.eval (Lift.SeparatedVariables.lifted p)
                          outer parameter) * vector
                            (Fin.natAdd p.natDegree index)) column)
                (fun column => by
                  rcases Data.Fin.addCases_split column with
                    ⟨index, rfl⟩ | ⟨index, rfl⟩
                  · simp only [Data.Fin.addCases_left]
                    rw [show
                      FiniteSum.Fin.sumFin
                          (fun row : Fin size =>
                            matrix row (Fin.castAdd p.natDegree index) *
                              weights row) =
                        outer ^ (index : Nat) *
                          Dense.Bivariate.Basic.eval
                            (SeparatedVariables.reflected p)
                            outer parameter by
                          calc
                            FiniteSum.Fin.sumFin
                                (fun row : Fin size =>
                                  matrix row
                                      (Fin.castAdd p.natDegree index) *
                                    weights row) =
                                FiniteSum.Fin.sumFin
                                  (fun row : Fin size =>
                                    PolynomialMatrix.Evaluation.evalMatrix
                                        parameter (Sylvester.separatedSylvester p) row
                                        (Fin.castAdd p.natDegree index) *
                                      outer ^ (row : Nat)) := by
                              apply FiniteSum.Fin.sumFin_congr
                              intro row
                              rw [Data.Vector.Basic.vectorOfFn_apply]
                            _ = outer ^ (index : Nat) *
                                  Dense.Bivariate.Basic.eval
                                    (SeparatedVariables.reflected p)
                                    outer parameter :=
                              Sylvester.Evaluation.separatedLeftColumnPowerSum p nonzero
                                outer parameter index]
                  · simp only [Data.Fin.addCases_right]
                    rw [show
                      FiniteSum.Fin.sumFin
                          (fun row : Fin size =>
                            matrix row (Fin.natAdd p.natDegree index) *
                              weights row) =
                        outer ^ (index : Nat) *
                          Dense.Bivariate.Basic.eval (Lift.SeparatedVariables.lifted p)
                            outer parameter by
                          calc
                            FiniteSum.Fin.sumFin
                                (fun row : Fin size =>
                                  matrix row
                                      (Fin.natAdd p.natDegree index) *
                                    weights row) =
                                FiniteSum.Fin.sumFin
                                  (fun row : Fin size =>
                                    PolynomialMatrix.Evaluation.evalMatrix
                                        parameter (Sylvester.separatedSylvester p) row
                                        (Fin.natAdd p.natDegree index) *
                                      outer ^ (row : Nat)) := by
                              apply FiniteSum.Fin.sumFin_congr
                              intro row
                              rw [Data.Vector.Basic.vectorOfFn_apply]
                            _ = outer ^ (index : Nat) *
                                  Dense.Bivariate.Basic.eval (Lift.SeparatedVariables.lifted p)
                                    outer parameter :=
                              Sylvester.Evaluation.separatedRightColumnPowerSum p nonzero
                                outer parameter index])]
              rw [FiniteSum.Gaussian.sumFin_addCases]
              unfold left right
              rw [Dense.Gaussian.Ascending.eval_polynomialFromLow, Dense.Gaussian.Ascending.eval_polynomialFromLow]
              rw [FiniteSum.Fin.sumFin_congr
                (left := fun index : Fin p.natDegree =>
                  (outer ^ (index : Nat) *
                    Dense.Bivariate.Basic.eval (SeparatedVariables.reflected
                      p)
                      outer parameter) *
                    vector (Fin.castAdd p.natDegree index))
                (right := fun index : Fin p.natDegree =>
                  ((prepared.data.inverse
                    (Fin.castAdd p.natDegree index)
                    (firstColumnIndex p degreePositive)).eval parameter *
                      outer ^ (index : Nat)) *
                    Dense.Bivariate.Basic.eval (SeparatedVariables.reflected
                      p)
                      outer parameter)
                (fun index => by
                  dsimp only [vector, inverse]
                  rw [Data.Vector.Basic.vectorOfFn_apply,
                    PolynomialMatrix.Evaluation.evalMatrix_apply]
                  ring1)]
              rw [FiniteSum.Fin.sumFin_mul_right]
              rw [FiniteSum.Fin.sumFin_congr
                (left := fun index : Fin p.natDegree =>
                  (outer ^ (index : Nat) *
                    Dense.Bivariate.Basic.eval (Lift.SeparatedVariables.lifted p)
                      outer parameter) *
                    vector (Fin.natAdd p.natDegree index))
                (right := fun index : Fin p.natDegree =>
                  ((prepared.data.inverse
                    (Fin.natAdd p.natDegree index)
                    (firstColumnIndex p degreePositive)).eval parameter *
                      outer ^ (index : Nat)) *
                    Dense.Bivariate.Basic.eval (Lift.SeparatedVariables.lifted p)
                      outer parameter)
                (fun index => by
                  dsimp only [vector, inverse]
                  rw [Data.Vector.Basic.vectorOfFn_apply,
                    PolynomialMatrix.Evaluation.evalMatrix_apply]
                  ring1)]
              rw [FiniteSum.Fin.sumFin_mul_right]
    _ = scalar := columnIdentity.symm
    _ = prepared.data.scalar.eval parameter := rfl
/-- Scale the left separated Bézout cofactor by the inverse evaluated Sylvester scalar.

The rational parameter is embedded into the Gaussian field, and the original first-column coefficient polynomial is
retained up to this scalar multiplication. -/
@[expose] def normalizedLeft {p : CoefficientPolynomial} (prepared : Preparation.Prepared p)
    (degreePositive : 0 < p.natDegree) (parameter : Fraction.Rational) :
    (DensePolynomial Gaussian.Basic.Canonical) :=
  let gaussianParameter :=
    Gaussian.Cast.Path.ofCoordinate parameter
  DensePolynomial.scale (prepared.data.scalar.eval gaussianParameter)⁻¹
    (left prepared degreePositive gaussianParameter)

/-- Scale the right separated Bézout cofactor by the inverse evaluated Sylvester scalar.

The rational parameter is embedded into the Gaussian field, and the original second-half coefficient polynomial is
retained up to this scalar multiplication. -/
@[expose] def normalizedRight {p : CoefficientPolynomial} (prepared : Preparation.Prepared p)
    (degreePositive : 0 < p.natDegree) (parameter : Fraction.Rational) :
    (DensePolynomial Gaussian.Basic.Canonical) :=
  let gaussianParameter :=
    Gaussian.Cast.Path.ofCoordinate parameter
  DensePolynomial.scale (prepared.data.scalar.eval gaussianParameter)⁻¹
    (right prepared degreePositive gaussianParameter)

/-- Retain both normalized cofactor halves after evaluating their same scalar inverse once.

The left and right polynomials read the same original cached inverse entries.
The retained pair shares their scalar normalization before either half is
passed to a path-coordinate producer.
-/
@[expose] def normalizedCofactors {p : CoefficientPolynomial} (prepared : Preparation.Prepared p)
    (degreePositive : 0 < p.natDegree) (parameter : Fraction.Rational) :
    DensePolynomial Gaussian.Basic.Canonical × DensePolynomial Gaussian.Basic.Canonical :=
  let gaussianParameter := Gaussian.Cast.Path.ofCoordinate parameter
  let reciprocal := (prepared.data.scalar.eval gaussianParameter)⁻¹
  let left := DensePolynomial.scale reciprocal (left prepared degreePositive gaussianParameter)
  let right := DensePolynomial.scale reciprocal (right prepared degreePositive gaussianParameter)
  (left, right)

/-- The retained left half is the same original normalized cofactor polynomial for every input. -/
theorem normalizedCofactors_left {p : CoefficientPolynomial} (prepared : Preparation.Prepared p)
    (degreePositive : 0 < p.natDegree) (parameter : Fraction.Rational) :
    (normalizedCofactors prepared degreePositive parameter).1 = normalizedLeft prepared degreePositive parameter := rfl

/-- The retained right half is the same original normalized cofactor polynomial for every input. -/
theorem normalizedCofactors_right {p : CoefficientPolynomial} (prepared : Preparation.Prepared p)
    (degreePositive : 0 < p.natDegree) (parameter : Fraction.Rational) :
    (normalizedCofactors prepared degreePositive parameter).2 = normalizedRight prepared degreePositive parameter := rfl

/-- The normalized separated cofactors give an exact Bézout identity equal to one.

The source polynomial is nonzero of positive degree, and the specialized Sylvester scalar must be nonzero at the
displayed rational parameter. -/
theorem normalizedIdentity {p : CoefficientPolynomial} (prepared : Preparation.Prepared p)
    (nonzero : p.isZero = false) (degreePositive : 0 < p.natDegree)
    (parameter : Fraction.Rational)
    (scalarNonzero : prepared.data.scalar.eval
      (Gaussian.Cast.Path.ofCoordinate parameter) ≠ 0)
    (outer : Gaussian.Basic.Canonical) :
    (normalizedLeft prepared degreePositive parameter).eval outer *
        Dense.Bivariate.Basic.eval (SeparatedVariables.reflected p) outer
          (Gaussian.Cast.Path.ofCoordinate parameter) +
      (normalizedRight prepared degreePositive parameter).eval outer *
        Dense.Bivariate.Basic.eval (Dense.Bivariate.Gaussian.Lift.SeparatedVariables.lifted p) outer
          (Gaussian.Cast.Path.ofCoordinate parameter) = 1 := by
  rw [normalizedLeft,
    normalizedRight, DensePolynomial.eval_scale,
    DensePolynomial.eval_scale]
  let scalar := prepared.data.scalar.eval
    (Gaussian.Cast.Path.ofCoordinate parameter)
  have identity := identity prepared nonzero degreePositive outer
    (Gaussian.Cast.Path.ofCoordinate parameter)
  change scalar⁻¹ * (left prepared degreePositive
      (Gaussian.Cast.Path.ofCoordinate parameter)).eval outer *
        Dense.Bivariate.Basic.eval (SeparatedVariables.reflected p) outer
          (Gaussian.Cast.Path.ofCoordinate parameter) +
      scalar⁻¹ * (right prepared degreePositive
        (Gaussian.Cast.Path.ofCoordinate parameter)).eval outer *
          Dense.Bivariate.Basic.eval (Dense.Bivariate.Gaussian.Lift.SeparatedVariables.lifted p) outer
            (Gaussian.Cast.Path.ofCoordinate parameter) = 1
  calc
    scalar⁻¹ * (left prepared degreePositive
          (Gaussian.Cast.Path.ofCoordinate parameter)).eval outer *
          Dense.Bivariate.Basic.eval (SeparatedVariables.reflected p) outer
            (Gaussian.Cast.Path.ofCoordinate parameter) +
        scalar⁻¹ * (right prepared degreePositive
          (Gaussian.Cast.Path.ofCoordinate parameter)).eval outer *
          Dense.Bivariate.Basic.eval (Dense.Bivariate.Gaussian.Lift.SeparatedVariables.lifted p) outer
            (Gaussian.Cast.Path.ofCoordinate parameter) =
      scalar⁻¹ *
        ((left prepared degreePositive
            (Gaussian.Cast.Path.ofCoordinate parameter)).eval outer *
            Dense.Bivariate.Basic.eval (SeparatedVariables.reflected p) outer
              (Gaussian.Cast.Path.ofCoordinate parameter) +
          (right prepared degreePositive
            (Gaussian.Cast.Path.ofCoordinate parameter)).eval outer *
            Dense.Bivariate.Basic.eval (Dense.Bivariate.Gaussian.Lift.SeparatedVariables.lifted p) outer
              (Gaussian.Cast.Path.ofCoordinate parameter)) := by
                rw [Gaussian.Basic.mul_assoc,
                  Gaussian.Basic.mul_assoc]
                exact
                  (Gaussian.Basic.left_distrib _ _ _).symm
    _ = scalar⁻¹ * scalar := by rw [identity]
    _ = 1 := by
      rw [Gaussian.Field.inv_eq]
      exact Gaussian.Field.inv_mul scalar scalarNonzero
end Purelib.Polynomial.Elimination.Separated.Bezout.Prepared

end
