module
import Purelib.Data.Gaussian.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Gaussian
import Purelib.Data.Fin
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.LinearAlgebra.Matrix.Gaussian.WeightedSum
public import Purelib.LinearAlgebra.Matrix.Multiplication
import Purelib.LinearAlgebra.PolynomialMatrix.Evaluation
import Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Compute
import Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Evaluation
import Purelib.Polynomial.Dense.Bivariate.Basic
public import Purelib.Polynomial.Dense.Gaussian.Ascending
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Elimination.Separated.Sylvester
import Purelib.Polynomial.Elimination.Separated.Sylvester.Evaluation

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Field
import Purelib.LinearAlgebra.PolynomialMatrix.Basic
import Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Basic
import Purelib.LinearAlgebra.Vector.Dot
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Bivariate.Gaussian.Lift
import Purelib.Polynomial.Dense.Bivariate.Gaussian.Reflection.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

open Purelib.Data

open Purelib

open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix

open Purelib.LinearAlgebra

open Purelib.Polynomial

section
@[expose] public section

/-!
# Finite Bézout extraction from the separated Sylvester inverse

This module turns the first column of the fraction-free scaled inverse into
two explicit dense cofactors.  The only summation identity involved is a
finite shifted coefficient-list calculation.
-/

namespace Purelib.Polynomial.Elimination.Separated.Bezout

/-- Compute the fraction-free scaled inverse data of the separated Sylvester matrix.

The matrix has twice the source polynomial's degree, and the result retains the scaled inverse matrix and its scalar. -/
def separatedData (p :
  CoefficientPolynomial) :=
  PolynomialMatrix.Inverse.Scaled.Compute.scaledInverseData
    (p.natDegree + p.natDegree) (Elimination.Separated.Sylvester.separatedSylvester p)

/-- The zero column index of the separated Sylvester matrix, justified by positive polynomial degree. -/
def firstColumnIndex (p :
  CoefficientPolynomial)
    (degreePositive : 0 < p.natDegree) :
    Fin (p.natDegree + p.natDegree) :=
  ⟨0, by omega⟩

/-- Read the first half of the scaled inverse's first column as an ascending polynomial.

Evaluate each retained matrix entry at the supplied parameter; these coefficients multiply the reflected member of the
separated pair. -/
def leftCofactor (p :
  CoefficientPolynomial)
    (degreePositive : 0 < p.natDegree) (parameter : Gaussian.Basic.Canonical) :
    (Dense.Basic.DensePolynomial Gaussian.Basic.Canonical) :=
  Dense.Gaussian.Ascending.polynomialFromLow p.natDegree (fun index =>
    ((separatedData p).inverse (Fin.castAdd p.natDegree index)
      (firstColumnIndex p degreePositive)).eval parameter)

/-- Read the second half of the scaled inverse's first column as an ascending polynomial.

Evaluate each retained matrix entry at the supplied parameter; these coefficients multiply the lifted member of the
separated pair. -/
def rightCofactor (p :
  CoefficientPolynomial)
    (degreePositive : 0 < p.natDegree) (parameter : Gaussian.Basic.Canonical) :
    (Dense.Basic.DensePolynomial Gaussian.Basic.Canonical) :=
  Dense.Gaussian.Ascending.polynomialFromLow p.natDegree (fun index =>
    ((separatedData p).inverse (Fin.natAdd p.natDegree index)
      (firstColumnIndex p degreePositive)).eval parameter)

/-- The specialized first inverse column is an explicit Bézout identity for
the separated pair. -/
theorem separated_bezout_identity (p :
  CoefficientPolynomial)
    (nonzero : p.isZero = false) (degreePositive : 0 < p.natDegree)
    (outer parameter : Gaussian.Basic.Canonical) :
    (leftCofactor p degreePositive parameter).eval outer *
        Dense.Bivariate.Basic.eval (Dense.Bivariate.Gaussian.Reflection.Basic.SeparatedVariables.reflected p) outer
          parameter +
      (rightCofactor p degreePositive parameter).eval outer *
        Dense.Bivariate.Basic.eval (Dense.Bivariate.Gaussian.Lift.SeparatedVariables.lifted p) outer parameter =
      (separatedData p).scalar.eval parameter := open Purelib.Algebra in by
  let size := p.natDegree + p.natDegree
  let matrix := PolynomialMatrix.Evaluation.evalMatrix parameter
    (Elimination.Separated.Sylvester.separatedSylvester p)
  let inverse := PolynomialMatrix.Evaluation.evalMatrix parameter
    (separatedData p).inverse
  let scalar := (separatedData p).scalar.eval parameter
  let first := firstColumnIndex p degreePositive
  let vector : Data.Vector Gaussian.Basic.Canonical size :=
    Data.Vector.Basic.vectorOfFn fun column =>
      inverse column first
  let weights : Data.Vector Gaussian.Basic.Canonical size :=
    Data.Vector.Basic.vectorOfFn fun row => outer ^ (row : Nat)
  have inverseIdentity :=
    (PolynomialMatrix.Inverse.Scaled.Evaluation.scaledInverseData_spec parameter size
      (Elimination.Separated.Sylvester.separatedSylvester p)).2
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
    rw [SquareMatrix.Multiplication.mul,
      SquareMatrix.matrixOfFn_apply,
      SquareMatrix.Multiplication.scaleIdentity,
      SquareMatrix.matrixOfFn_apply] at entryIdentity
    rw [SquareMatrix.Multiplication.matrixVector,
      Data.Vector.Basic.vectorOfFn_apply,
      Data.Vector.Basic.vectorOfFn_apply]
    exact entryIdentity
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
  have columnIdentity := Purelib.LinearAlgebra.Matrix.Gaussian.WeightedSum.weighted_matrixVector
    matrix vector
    weights
  rw [weightedIdentity] at columnIdentity
  calc
    (leftCofactor p degreePositive parameter).eval outer *
          Dense.Bivariate.Basic.eval (Dense.Bivariate.Gaussian.Reflection.Basic.SeparatedVariables.reflected p) outer
            parameter +
        (rightCofactor p degreePositive parameter).eval outer *
          Dense.Bivariate.Basic.eval (Dense.Bivariate.Gaussian.Lift.SeparatedVariables.lifted p) outer parameter =
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
                          (Dense.Bivariate.Gaussian.Reflection.Basic.SeparatedVariables.reflected p)
                          outer parameter) * vector (Fin.castAdd p.natDegree index))
                    (fun index =>
                      (outer ^ (index : Nat) *
                        Dense.Bivariate.Basic.eval (Dense.Bivariate.Gaussian.Lift.SeparatedVariables.lifted p)
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
                            (Dense.Bivariate.Gaussian.Reflection.Basic.SeparatedVariables.reflected p)
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
                                        parameter (Elimination.Separated.Sylvester.separatedSylvester p) row
                                        (Fin.castAdd p.natDegree index) *
                                      outer ^ (row : Nat)) := by
                              apply FiniteSum.Fin.sumFin_congr
                              intro row
                              rw [Data.Vector.Basic.vectorOfFn_apply]
                            _ = outer ^ (index : Nat) *
                                  Dense.Bivariate.Basic.eval
                                    (Dense.Bivariate.Gaussian.Reflection.Basic.SeparatedVariables.reflected p)
                                    outer parameter :=
                              Elimination.Separated.Sylvester.Evaluation.separatedLeftColumnPowerSum p nonzero
                                outer parameter index]
                  · simp only [Data.Fin.addCases_right]
                    rw [show
                      FiniteSum.Fin.sumFin
                          (fun row : Fin size =>
                            matrix row (Fin.natAdd p.natDegree index) *
                              weights row) =
                        outer ^ (index : Nat) *
                          Dense.Bivariate.Basic.eval (Dense.Bivariate.Gaussian.Lift.SeparatedVariables.lifted p)
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
                                        parameter (Elimination.Separated.Sylvester.separatedSylvester p) row
                                        (Fin.natAdd p.natDegree index) *
                                      outer ^ (row : Nat)) := by
                              apply FiniteSum.Fin.sumFin_congr
                              intro row
                              rw [Data.Vector.Basic.vectorOfFn_apply]
                            _ = outer ^ (index : Nat) *
                                  Dense.Bivariate.Basic.eval (Dense.Bivariate.Gaussian.Lift.SeparatedVariables.lifted p)
                                    outer parameter :=
                              Elimination.Separated.Sylvester.Evaluation.separatedRightColumnPowerSum p nonzero
                                outer parameter index])]
              rw [Purelib.Algebra.FiniteSum.Gaussian.sumFin_addCases]
              unfold leftCofactor rightCofactor
              rw [Dense.Gaussian.Ascending.eval_polynomialFromLow, Dense.Gaussian.Ascending.eval_polynomialFromLow]
              rw [FiniteSum.Fin.sumFin_congr
                (left := fun index : Fin p.natDegree =>
                  (outer ^ (index : Nat) *
                    Dense.Bivariate.Basic.eval (Dense.Bivariate.Gaussian.Reflection.Basic.SeparatedVariables.reflected
                      p)
                      outer parameter) *
                    vector (Fin.castAdd p.natDegree index))
                (right := fun index : Fin p.natDegree =>
                  (((separatedData p).inverse
                    (Fin.castAdd p.natDegree index)
                    (firstColumnIndex p degreePositive)).eval parameter *
                      outer ^ (index : Nat)) *
                    Dense.Bivariate.Basic.eval (Dense.Bivariate.Gaussian.Reflection.Basic.SeparatedVariables.reflected
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
                    Dense.Bivariate.Basic.eval (Dense.Bivariate.Gaussian.Lift.SeparatedVariables.lifted p)
                      outer parameter) *
                    vector (Fin.natAdd p.natDegree index))
                (right := fun index : Fin p.natDegree =>
                  (((separatedData p).inverse
                    (Fin.natAdd p.natDegree index)
                    (firstColumnIndex p degreePositive)).eval parameter *
                      outer ^ (index : Nat)) *
                    Dense.Bivariate.Basic.eval (Dense.Bivariate.Gaussian.Lift.SeparatedVariables.lifted p)
                      outer parameter)
                (fun index => by
                  dsimp only [vector, inverse]
                  rw [Data.Vector.Basic.vectorOfFn_apply,
                    PolynomialMatrix.Evaluation.evalMatrix_apply]
                  ring1)]
              rw [FiniteSum.Fin.sumFin_mul_right]
    _ = scalar := columnIdentity.symm
    _ = (separatedData p).scalar.eval parameter := rfl
end Purelib.Polynomial.Elimination.Separated.Bezout

end
