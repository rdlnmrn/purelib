module
import Purelib.Data.Gaussian.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Fin
import Purelib.Data.List.GetD
import Purelib.LinearAlgebra.Matrix.Basic
public import Purelib.LinearAlgebra.PolynomialMatrix.Evaluation
import Purelib.Polynomial.Dense.Bivariate.Basic
import Purelib.Polynomial.Dense.Bivariate.Gaussian.Ascending
import Purelib.Polynomial.Dense.Bivariate.Gaussian.Lift
import Purelib.Polynomial.Dense.Bivariate.Gaussian.Reflection.Shape
import Purelib.Polynomial.Dense.Bivariate.Resultant
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Elimination.Separated.Sylvester

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Polynomial.Dense.Bivariate.Gaussian.Reflection.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic

open Purelib.Algebra

open Purelib

open Purelib.Data

open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix

open Purelib.LinearAlgebra

open Purelib.Polynomial

public section

/-!
# Finite Bézout extraction from the separated Sylvester inverse

This module turns the first column of the fraction-free scaled inverse into
two explicit dense cofactors.  The only summation identity involved is a
finite shifted coefficient-list calculation.
-/

namespace Purelib.Polynomial.Elimination.Separated.Sylvester.Evaluation

/-- The power-weighted sum of a left Sylvester column evaluates the reflected polynomial.

The original nonzero polynomial supplies the reflected coefficient-table length.
The selected left column retains its natural offset and row coordinates, so its
finite power-weighted sum reads that same table and shifts its evaluation by the
original column power. -/
theorem separatedLeftColumnPowerSum (p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
    (nonzero : p.isZero = false) (outer parameter : Gaussian.Basic.Canonical)
    (column : Fin p.natDegree) :
    FiniteSum.Fin.sumFin
      (fun row : Fin (p.natDegree + p.natDegree) =>
        (PolynomialMatrix.Evaluation.evalMatrix parameter
          (Elimination.Separated.Sylvester.separatedSylvester p) row
          (Fin.castAdd p.natDegree column)) * outer ^ (row : Nat)) =
      outer ^ (column : Nat) *
        Dense.Bivariate.Basic.eval (Dense.Bivariate.Gaussian.Reflection.Basic.SeparatedVariables.reflected p) outer
          parameter := by
  let suffix := p.natDegree - ((column : Nat) + 1)
  have coefficientsLength := Dense.Bivariate.Gaussian.Reflection.Shape.reflectedCoefficients_shape p nonzero
  have totalIdentity :
      (column : Nat) + (Dense.Bivariate.Gaussian.Reflection.Basic.SeparatedVariables.reflectedCoefficients p).length +
        suffix =
        p.natDegree + p.natDegree := by
    dsimp only [suffix]
    rw [coefficientsLength.length_eq]
    have columnBound := column.isLt
    omega
  have shifted := Dense.Bivariate.Gaussian.Ascending.sumShifted_evalLow outer parameter (column : Nat)
    (Dense.Bivariate.Gaussian.Reflection.Basic.SeparatedVariables.reflectedCoefficients p) suffix
  rw [totalIdentity] at shifted
  have summandsEqual :
      FiniteSum.Fin.sumFin
        (fun row : Fin (p.natDegree + p.natDegree) =>
        (PolynomialMatrix.Evaluation.evalMatrix parameter
          (Elimination.Separated.Sylvester.separatedSylvester p) row
          (Fin.castAdd p.natDegree column)) * outer ^ (row : Nat)) =
      FiniteSum.Fin.sumFin
        (fun row : Fin (p.natDegree + p.natDegree) =>
        if (column : Nat) ≤ (row : Nat) ∧
            (row : Nat) <
              (column : Nat) + (Dense.Bivariate.Gaussian.Reflection.Basic.SeparatedVariables.reflectedCoefficients
                p).length then
          (Data.List.getD (Dense.Bivariate.Gaussian.Reflection.Basic.SeparatedVariables.reflectedCoefficients p)
            ((row : Nat) - (column : Nat)) 0).eval parameter *
              outer ^ (row : Nat)
        else 0) := by
          apply FiniteSum.Fin.sumFin_congr
          intro row
          simp only [Elimination.Separated.Sylvester.separatedSylvester,
            Dense.Bivariate.Resultant.sylvester,
            PolynomialMatrix.Evaluation.evalMatrix_apply,
            SquareMatrix.matrixOfFn_apply,
            Data.Fin.addCases_left]
          have upperIdentity :
              (row : Nat) ≤ (column : Nat) + p.natDegree ↔
                (row : Nat) <
                  (column : Nat) + (Dense.Bivariate.Gaussian.Reflection.Basic.SeparatedVariables.reflectedCoefficients
                    p).length := by
            rw [coefficientsLength.length_eq]
            rw [← Nat.add_assoc]
            exact Nat.lt_add_one_iff.symm
          by_cases inside :
              (column : Nat) ≤ (row : Nat) ∧
                (row : Nat) ≤ (column : Nat) + p.natDegree
          · rw [if_pos inside, if_pos ⟨inside.1, upperIdentity.mp inside.2⟩,
              Dense.Bivariate.Gaussian.Reflection.Shape.outerCoeff_reflected]
          · have outside :
                ¬((column : Nat) ≤ (row : Nat) ∧
                  (row : Nat) <
                    (column : Nat) + (Dense.Bivariate.Gaussian.Reflection.Basic.SeparatedVariables.reflectedCoefficients
                      p).length) := by
              intro candidate
              exact inside ⟨candidate.1, upperIdentity.mpr candidate.2⟩
            rw [if_neg inside, if_neg outside, Dense.Basic.DensePolynomial.eval_zero, zero_mul]
  rw [summandsEqual]
  change _ = outer ^ (column : Nat) *
    Dense.Bivariate.Gaussian.Ascending.evalLow
      (Dense.Bivariate.Gaussian.Reflection.Basic.SeparatedVariables.reflectedCoefficients p) outer parameter
  exact shifted

/-- The power-weighted sum of a right Sylvester column evaluates the lifted polynomial.

The original nonzero polynomial supplies the lifted coefficient-table length.
The selected right column retains its natural offset and row coordinates, so its
finite power-weighted sum reads that same table and shifts its evaluation by the
original column power. -/
theorem separatedRightColumnPowerSum (p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
    (nonzero : p.isZero = false) (outer parameter : Gaussian.Basic.Canonical)
    (column : Fin p.natDegree) :
    FiniteSum.Fin.sumFin
      (fun row : Fin (p.natDegree + p.natDegree) =>
        (PolynomialMatrix.Evaluation.evalMatrix parameter
          (Elimination.Separated.Sylvester.separatedSylvester p) row
          (Fin.natAdd p.natDegree column)) * outer ^ (row : Nat)) =
      outer ^ (column : Nat) *
        Dense.Bivariate.Basic.eval (Dense.Bivariate.Gaussian.Lift.SeparatedVariables.lifted p) outer parameter := by
  let suffix := p.natDegree - ((column : Nat) + 1)
  have coefficientsLength := Dense.Bivariate.Gaussian.Lift.liftedCoefficients_length p nonzero
  have totalIdentity :
      (column : Nat) + (Dense.Bivariate.Gaussian.Lift.SeparatedVariables.liftedCoefficients p).length + suffix =
        p.natDegree + p.natDegree := by
    dsimp only [suffix]
    rw [coefficientsLength]
    have columnBound := column.isLt
    omega
  have shifted := Dense.Bivariate.Gaussian.Ascending.sumShifted_evalLow outer parameter (column : Nat)
    (Dense.Bivariate.Gaussian.Lift.SeparatedVariables.liftedCoefficients p) suffix
  rw [totalIdentity] at shifted
  have summandsEqual :
      FiniteSum.Fin.sumFin
        (fun row : Fin (p.natDegree + p.natDegree) =>
        (PolynomialMatrix.Evaluation.evalMatrix parameter
          (Elimination.Separated.Sylvester.separatedSylvester p) row
          (Fin.natAdd p.natDegree column)) * outer ^ (row : Nat)) =
      FiniteSum.Fin.sumFin
        (fun row : Fin (p.natDegree + p.natDegree) =>
        if (column : Nat) ≤ (row : Nat) ∧
            (row : Nat) < (column : Nat) + (Dense.Bivariate.Gaussian.Lift.SeparatedVariables.liftedCoefficients
              p).length then
          (Data.List.getD (Dense.Bivariate.Gaussian.Lift.SeparatedVariables.liftedCoefficients p)
            ((row : Nat) - (column : Nat)) 0).eval parameter *
              outer ^ (row : Nat)
        else 0) := by
          apply FiniteSum.Fin.sumFin_congr
          intro row
          simp only [Elimination.Separated.Sylvester.separatedSylvester,
            Dense.Bivariate.Resultant.sylvester,
            PolynomialMatrix.Evaluation.evalMatrix_apply,
            SquareMatrix.matrixOfFn_apply,
            Data.Fin.addCases_right]
          have upperIdentity :
              (row : Nat) ≤ (column : Nat) + p.natDegree ↔
                (row : Nat) <
                  (column : Nat) + (Dense.Bivariate.Gaussian.Lift.SeparatedVariables.liftedCoefficients p).length := by
            rw [coefficientsLength]
            rw [← Nat.add_assoc]
            exact Nat.lt_add_one_iff.symm
          by_cases inside :
              (column : Nat) ≤ (row : Nat) ∧
                (row : Nat) ≤ (column : Nat) + p.natDegree
          · rw [if_pos inside, if_pos ⟨inside.1, upperIdentity.mp inside.2⟩,
              Dense.Bivariate.Gaussian.Lift.outerCoeff_lifted]
          · have outside :
                ¬((column : Nat) ≤ (row : Nat) ∧
                  (row : Nat) <
                    (column : Nat) + (Dense.Bivariate.Gaussian.Lift.SeparatedVariables.liftedCoefficients p).length) :=
                      by
              intro candidate
              exact inside ⟨candidate.1, upperIdentity.mpr candidate.2⟩
            rw [if_neg inside, if_neg outside, Dense.Basic.DensePolynomial.eval_zero, zero_mul]
  rw [summandsEqual]
  change _ = outer ^ (column : Nat) *
    Dense.Bivariate.Gaussian.Ascending.evalLow (Dense.Bivariate.Gaussian.Lift.SeparatedVariables.liftedCoefficients p)
      outer parameter
  exact shifted
end Purelib.Polynomial.Elimination.Separated.Sylvester.Evaluation
