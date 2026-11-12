module

public import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Data.Gaussian.Scale
public import Purelib.LinearAlgebra.Matrix.Multiplication
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Data.Gaussian.Norm.Weighted
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Vector.Basic
import Purelib.Tactic.Ring

/-! # Squared norms of finite Gaussian vectors and matrices

The vector norm is the sum of the original coordinate quadrances. The
matrix norm sums the same quantities in its retained structural rows.
Finite weighted-sum inequalities give an executable coefficient bound for
the original matrix-vector action, including dimension zero.
-/

public section

namespace Purelib.LinearAlgebra.Gaussian.Norm

open Purelib
open Purelib.Algebra.FiniteSum.Fin
open Purelib.Algebra.FiniteSum.Rational.Order (weight_sum_nonnegative weight_le_sum)
open Purelib.Algebra.FiniteSum.Rational.Order.IndexedBudget (sumFin_le)
open Purelib.Data renaming Vector → Vec
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Scale (scale)
open Purelib.Data.Gaussian.Norm
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Order.Arithmetic
open Purelib.Data.Vector (map zipWith)
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply map_apply zipWith_apply)

/-- Sum the squared norms of the coordinates of one original finite structural vector. -/
@[expose] def vector {size : Nat} (values : Vec Canonical size) : Rational :=
  sumFin fun index => Basic.normSq (values index)

/-- Every finite Gaussian vector has nonnegative squared norm, including the empty vector. -/
theorem vector_nonnegative {size : Nat} (values : Vec Canonical size) : 0 ≤ vector values :=
  weight_sum_nonnegative _ (fun index => Basic.normSq_nonneg (values index))

/-- Each actual coordinate quadrance is bounded by the squared norm of the original vector. -/
theorem coordinate_le_vector {size : Nat} (values : Vec Canonical size) (index : Fin size) :
    Basic.normSq (values index) ≤ vector values :=
  weight_le_sum _ (fun position => Basic.normSq_nonneg (values position)) index

/-- Pointwise coordinate identities preserve vector quadrance without replacing either vector owner. -/
theorem vector_congr {size : Nat} (first last : Vec Canonical size)
    (same : ∀ index, first index = last index) : vector first = vector last :=
  sumFin_congr (fun index => congrArg Basic.normSq (same index))

/-- Materializing an entry function gives the sum of those exact original coordinate quadrances. -/
theorem vector_ofFn {size : Nat} (values : Fin size → Canonical) :
    vector (vectorOfFn values) = sumFin (fun index => Basic.normSq (values index)) :=
  sumFin_congr (fun index => congrArg Basic.normSq (vectorOfFn_apply values index))

/-- Rational scaling multiplies vector quadrance by the square of that same scalar. -/
theorem vector_scale {size : Nat} (factor : Rational) (values : Vec Canonical size) :
    vector (map (scale factor) values) = factor ^ 2 * vector values := by
  calc
    _ = sumFin (fun index => factor ^ 2 * Basic.normSq (values index)) :=
      sumFin_congr (fun index =>
        (congrArg Basic.normSq (map_apply (scale factor) values index)).trans
          (Data.Gaussian.Scale.normSq_scale factor (values index)))
    _ = _ := sumFin_mul_left _ _

/-- A positive rational weight gives the same weighted addition bound on complete finite Gaussian vectors. -/
theorem vector_add_le_parameter {size : Nat} (weight : Rational) (positive : 0 < weight)
    (left right : Vec Canonical size) :
    vector (zipWith (fun first last => first + last) left right) ≤
      (weight + 1) * vector left + ((weight + 1) / weight) * vector right := by
  calc
    _ ≤ sumFin (fun index => (weight + 1) * Basic.normSq (left index) +
        ((weight + 1) / weight) * Basic.normSq (right index)) :=
      sumFin_le (fun index =>
        (congrArg Basic.normSq (zipWith_apply (fun first last : Canonical => first + last)
          left right index)).trans_le
          (Weighted.normSq_add_le_parameter weight positive (left index) (right index)))
    _ = _ := by rewrite [sumFin_add, sumFin_mul_left, sumFin_mul_left]; rfl

/-- Sum the squared norms of all entries of one original finite structural matrix. -/
@[expose] def matrix {size : Nat} (coefficients : Matrix Canonical size) : Rational :=
  sumFin fun row => vector (coefficients row)

/-- The coefficient quadrance of a finite matrix is nonnegative, including dimension zero. -/
theorem matrix_nonnegative {size : Nat} (coefficients : Matrix Canonical size) : 0 ≤ matrix coefficients :=
  weight_sum_nonnegative _ (fun row => vector_nonnegative (coefficients row))

/-- The original matrix-vector action has a finite squared-norm bound computed from its actual coefficient rows.

The dimension factor comes from the finite row-sum inequality. Each input
coordinate is paid by the same original vector norm, and summing the
original row coefficients introduces no step-count or refinement factor.
-/
theorem matrixVector_le {size : Nat} (coefficients : Matrix Canonical size) (values : Vec Canonical size) :
    vector (Matrix.Multiplication.matrixVector coefficients values) ≤
      (size : Rational) * matrix coefficients * vector values := by
  have rowBound (row : Fin size) :
      Basic.normSq (Matrix.Multiplication.matrixVector coefficients values row) ≤
        (size : Rational) * vector (coefficients row) * vector values := by
    have terms (column : Fin size) : Basic.normSq (coefficients row column * values column) ≤
        Basic.normSq (coefficients row column) * vector values :=
      (Basic.normSq_mul _ _).trans_le
        (mul_le_mul_of_nonneg_left_direct (coordinate_le_vector values column)
          (Basic.normSq_nonneg (coefficients row column)))
    have summed := Sum.Indexed.normSq_sumFin_le_count_mul_sumFin
      (fun column => coefficients row column * values column)
      (fun column => Basic.normSq (coefficients row column) * vector values) terms
    exact (congrArg Basic.normSq (Matrix.Multiplication.matrixVector_apply coefficients values row)).trans_le
      (summed.trans_eq (by rewrite [sumFin_mul_right]; unfold vector; ring1))
  calc
    _ ≤ sumFin (fun row => (size : Rational) * vector (coefficients row) * vector values) :=
      sumFin_le rowBound
    _ = (size : Rational) * sumFin (fun row => vector (coefficients row) * vector values) :=
      (sumFin_congr (fun row => by ring1)).trans (sumFin_mul_left _ _)
    _ = _ := by rewrite [sumFin_mul_right]; unfold matrix; ring1

end Purelib.LinearAlgebra.Gaussian.Norm

end
