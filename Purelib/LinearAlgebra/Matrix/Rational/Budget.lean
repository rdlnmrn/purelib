module
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Quadratic.Bounds
public import Purelib.LinearAlgebra.Gaussian.QuadraticForm
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.Data.Rat.Fraction.Field
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Tactic.Ring

open Purelib.Algebra

open Purelib.Data.Rat

open Purelib

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

namespace Purelib.LinearAlgebra.Matrix.Rational.Budget

/-- A finite square structural matrix of exact rational entries. -/
abbrev RationalMatrix (size : Nat) :=
  SquareMatrix Fraction.Rational size

/-- Total displayed perturbation budget of a finite matrix. -/
def totalBudget {size : Nat} (budget :
  SquareMatrix.Rational.Budget.RationalMatrix size) : Fraction.Rational :=
  FiniteSum.Fin.sumFin fun row =>
    FiniteSum.Fin.sumFin fun column => budget row column

/-- Automatically computed entrywise perturbation budget for one vector and
one positive radius matrix. -/
def automaticBudget {size : Nat} (vector :
  LinearAlgebra.Gaussian.QuadraticForm.RationalVector size)
    (radius : SquareMatrix.Rational.Budget.RationalMatrix size) : SquareMatrix.Rational.Budget.RationalMatrix size :=
  SquareMatrix.matrixOfFn fun row column =>
    ((vector row * vector column) ^ 2 + 1) * radius row column

/-- Read one automatic perturbation budget as the squared coordinate product plus one, times its retained radius. -/
@[simp] theorem automaticBudget_apply {size :
  Nat}
    (vector : LinearAlgebra.Gaussian.QuadraticForm.RationalVector size) (radius :
      SquareMatrix.Rational.Budget.RationalMatrix size)
    (row column : Fin size) :
    SquareMatrix.Rational.Budget.automaticBudget vector radius row column =
      ((vector row * vector column) ^ 2 + 1) * radius row column :=
  SquareMatrix.matrixOfFn_apply _ _ _

/-- Nonnegative entrywise radii give nonnegative automatic perturbation budgets. -/
theorem automaticBudget_nonnegative {size : Nat}
    (vector : LinearAlgebra.Gaussian.QuadraticForm.RationalVector size) (radius :
      SquareMatrix.Rational.Budget.RationalMatrix size)
    (radiusNonnegative : forall row column, 0 <= radius row column)
    (row column : Fin size) :
    0 <= SquareMatrix.Rational.Budget.automaticBudget vector radius row column := by
  rw [SquareMatrix.Rational.Budget.automaticBudget_apply]
  exact Fraction.Order.Arithmetic.mul_nonneg_direct
    (add_nonneg
      (Fraction.Order.Arithmetic.sq_nonneg_direct
        (vector row * vector column)) (by decide))
    (radiusNonnegative row column)

/-- The automatically assembled finite double-sum budget is nonnegative. -/
theorem totalAutomaticBudget_nonnegative {size :
  Nat}
    (vector : LinearAlgebra.Gaussian.QuadraticForm.RationalVector size) (radius :
      SquareMatrix.Rational.Budget.RationalMatrix size)
    (radiusNonnegative : forall row column, 0 <= radius row column) :
    0 <= SquareMatrix.Rational.Budget.totalBudget (SquareMatrix.Rational.Budget.automaticBudget vector radius) := by
  unfold SquareMatrix.Rational.Budget.totalBudget
  calc
    0 = FiniteSum.Fin.sumFin
          (fun _ : Fin size => (0 : Fraction.Rational)) :=
      FiniteSum.Fin.sumFin_zero.symm
    _ <= FiniteSum.Fin.sumFin (fun row =>
          FiniteSum.Fin.sumFin (fun column =>
            SquareMatrix.Rational.Budget.automaticBudget vector radius row column)) := by
      apply FiniteSum.Rational.Order.Positivity.sumFin_mono
      intro row
      calc
        0 = FiniteSum.Fin.sumFin
              (fun _ : Fin size => (0 : Fraction.Rational)) :=
          FiniteSum.Fin.sumFin_zero.symm
        _ <= FiniteSum.Fin.sumFin (fun column =>
              SquareMatrix.Rational.Budget.automaticBudget vector radius row column) := by
          apply FiniteSum.Rational.Order.Positivity.sumFin_mono
          intro column
          exact SquareMatrix.Rational.Budget.automaticBudget_nonnegative vector radius radiusNonnegative
            row column

/-- The negative automatic entry budget bounds the corresponding weighted perturbation from below.

The perturbation lies strictly inside the supplied positive rational radius, and the original two vector coordinates
supply the weights. -/
theorem automaticBudget_weighted_lower {size :
  Nat}
    (vector : LinearAlgebra.Gaussian.QuadraticForm.RationalVector size) (radius :
      SquareMatrix.Rational.Budget.RationalMatrix size)
    (radiusPositive : forall row column, 0 < radius row column)
    (row column : Fin size) (delta : Fraction.Rational)
    (lower : -(radius row column) < delta)
    (upper : delta < radius row column) :
    -(SquareMatrix.Rational.Budget.automaticBudget vector radius row column) <=
      vector row * delta * vector column := by
  rw [SquareMatrix.Rational.Budget.automaticBudget_apply]
  calc
    -(((vector row * vector column) ^ 2 + 1) * radius row column) <=
        (vector row * vector column) * delta :=
      Data.Rat.Quadratic.Bounds.weighted_lower_of_radius (vector row * vector column) delta
        (radius row column) (radiusPositive row column) lower upper
    _ = vector row * delta * vector column := by ring1

end Purelib.LinearAlgebra.Matrix.Rational.Budget

end
