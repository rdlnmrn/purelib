module
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Components.Bounds
import Purelib.LinearAlgebra.Gaussian.QuadraticForm
public import Purelib.LinearAlgebra.Matrix.Rational.Budget
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Tactic.Ring

open Purelib.Algebra

open Purelib

open Purelib.Data.Rat

open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix

section
@[expose] public section

/-!
# Finite robustness certificates for period-matrix positivity

A positivity request reads finitely many rational balls.  This module reduces
the universal box statement to entrywise rational radii, entrywise rational
error budgets, and one strict rational margin at the displayed centre matrix.
The perturbation estimate is a finite double sum; no least eigenvalue,
compactness, or completed matrix is used.
-/

namespace Purelib.LinearAlgebra.Gaussian.QuadraticForm.Perturbation

/-- Expanding a candidate matrix around a displayed centre turns its
quadratic form into the centre value plus a finite perturbation sum. -/
theorem
  imaginaryQuadraticForm_eq_center_add_perturbation
  {size : Nat}
    (vector : LinearAlgebra.Gaussian.QuadraticForm.RationalVector size) (candidate center :
      LinearAlgebra.Gaussian.QuadraticForm.GaussianMatrix size) :
    LinearAlgebra.Gaussian.QuadraticForm.imaginaryQuadraticForm vector candidate =
      LinearAlgebra.Gaussian.QuadraticForm.imaginaryQuadraticForm vector center +
        FiniteSum.Fin.sumFin fun row =>
          FiniteSum.Fin.sumFin fun column =>
            vector row * (candidate row column - center row column).im *
              vector column := by
  unfold LinearAlgebra.Gaussian.QuadraticForm.imaginaryQuadraticForm
  rw [← FiniteSum.Fin.sumFin_add]
  apply FiniteSum.Fin.sumFin_congr
  intro row
  rw [← FiniteSum.Fin.sumFin_add]
  apply FiniteSum.Fin.sumFin_congr
  intro column
  simp only [Data.Gaussian.Basic.sub_im]
  ring1

/-- An entrywise squared-distance comparison gives a lower bound for the
whole finite imaginary quadratic form.  The bound is the same automatic
double-sum budget used for public matrix boxes, so it can also compare an
exact synchronized quotient with a separately refined persistent centre. -/
theorem imaginaryQuadraticForm_sub_automaticBudget_le
  {size : Nat}
    (vector : LinearAlgebra.Gaussian.QuadraticForm.RationalVector size) (reference candidate :
      LinearAlgebra.Gaussian.QuadraticForm.GaussianMatrix size)
    (radius : SquareMatrix.Rational.Budget.RationalMatrix size)
    (radiusPositive : forall row column, 0 < radius row column)
    (close : forall row column,
      Data.Gaussian.Norm.Basic.normSq
          (candidate row column - reference row column) <
        (radius row column) ^ 2) :
    LinearAlgebra.Gaussian.QuadraticForm.imaginaryQuadraticForm vector reference -
        SquareMatrix.Rational.Budget.totalBudget (SquareMatrix.Rational.Budget.automaticBudget vector radius) <=
      LinearAlgebra.Gaussian.QuadraticForm.imaginaryQuadraticForm vector candidate := by
  let perturbation : Fraction.Rational :=
    FiniteSum.Fin.sumFin fun row =>
      FiniteSum.Fin.sumFin fun column =>
        vector row * (candidate row column - reference row column).im *
          vector column
  have perturbationLower :
      -SquareMatrix.Rational.Budget.totalBudget (SquareMatrix.Rational.Budget.automaticBudget vector radius) <=
        perturbation := by
    unfold SquareMatrix.Rational.Budget.totalBudget perturbation
    rw [← FiniteSum.Fin.sumFin_neg]
    apply FiniteSum.Rational.Order.Positivity.sumFin_mono
    intro row
    rw [← FiniteSum.Fin.sumFin_neg]
    apply FiniteSum.Rational.Order.Positivity.sumFin_mono
    intro column
    let delta := candidate row column - reference row column
    have bounds := Data.Gaussian.Norm.Components.Bounds.imaginary_bounds_of_normSq_lt_sq
      (radiusPositive row column) (by simpa only [delta] using close row column)
    exact SquareMatrix.Rational.Budget.automaticBudget_weighted_lower vector radius radiusPositive
      row column delta.im bounds.1 bounds.2
  have shifted :
      LinearAlgebra.Gaussian.QuadraticForm.imaginaryQuadraticForm vector reference -
          SquareMatrix.Rational.Budget.totalBudget (SquareMatrix.Rational.Budget.automaticBudget vector radius) <=
        LinearAlgebra.Gaussian.QuadraticForm.imaginaryQuadraticForm vector reference + perturbation := by
    simpa only [sub_eq_add_neg, add_comm] using
      add_le_add_left perturbationLower
        (LinearAlgebra.Gaussian.QuadraticForm.imaginaryQuadraticForm vector reference)
  have identity := imaginaryQuadraticForm_eq_center_add_perturbation
    vector candidate reference
  rw [show LinearAlgebra.Gaussian.QuadraticForm.imaginaryQuadraticForm vector candidate =
      LinearAlgebra.Gaussian.QuadraticForm.imaginaryQuadraticForm vector reference + perturbation by
        simpa only [perturbation] using identity]
  exact shifted

end Purelib.LinearAlgebra.Gaussian.QuadraticForm.Perturbation

end
