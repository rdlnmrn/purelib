module

public import Purelib.Algebra.Ring.Weight
public import Purelib.LinearAlgebra.Matrix.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-!
# Squared weights of structural matrix entries

The total reads every entry of the original finite matrix. The original
matrix product has a uniform bound obtained from the same bounded row and
column sums, without installing a second matrix ring.
-/

public section

namespace Purelib.LinearAlgebra.Matrix.Weight

open Purelib.LinearAlgebra renaming Matrix → SquareMatrix
open Purelib.Algebra.Ring (Weight)
open Purelib.Algebra.FiniteSum.Fin
open Purelib.Algebra.FiniteSum.Rational.Order
open Purelib.Data.Rat.Fraction

variable {K : Type*} [CommRing K] {dimension : Nat}

/-- Sum the retained scalar weight over every original matrix entry. -/
@[expose] def total (weight : Weight K) (matrix : SquareMatrix K dimension) : Rational :=
  sumFin (fun row => sumFin (fun column => weight.value (matrix row column)))

/-- Every original structural matrix has nonnegative total weight. -/
theorem total_nonnegative (weight : Weight K) (matrix : SquareMatrix K dimension) :
    0 ≤ total weight matrix :=
  weight_sum_nonnegative _ (fun _ => weight_sum_nonnegative _ (fun _ => weight.nonnegative _))

/-- The original structural zero matrix has zero total weight. -/
theorem total_zero (weight : Weight K) : total weight (Arithmetic.zero : SquareMatrix K dimension) = 0 := by
  apply (sumFin_congr (right := fun _ => 0) ?_).trans sumFin_zero
  intro row
  apply (sumFin_congr (right := fun _ => 0) ?_).trans sumFin_zero
  intro column
  rewrite [Arithmetic.zero_apply, weight.zero]
  rfl

/-- Entrywise negation of the original matrix preserves its total weight. -/
theorem total_neg (weight : Weight K) (matrix : SquareMatrix K dimension) :
    total weight (Arithmetic.neg matrix) = total weight matrix := by
  apply sumFin_congr
  intro row
  apply sumFin_congr
  intro column
  rewrite [Arithmetic.neg_apply, weight.neg]
  rfl

/-- The original matrix addition retains the squared triangle constant two. -/
theorem total_add_le (weight : Weight K) (left right : SquareMatrix K dimension) :
    total weight (Arithmetic.add left right) ≤ 2 * (total weight left + total weight right) := by
  apply (IndexedBudget.sumFin_le (fun row => IndexedBudget.sumFin_le (fun column => by
    rewrite [Arithmetic.add_apply]
    exact weight.add_le _ _))).trans
  apply Eq.le
  calc
    _ = sumFin (fun row => 2 *
        (sumFin (fun column => weight.value (left row column)) +
          sumFin (fun column => weight.value (right row column)))) :=
      sumFin_congr (fun _ => (sumFin_mul_left 2 _).trans (congrArg (2 * ·) (sumFin_add _ _)))
    _ = _ := (sumFin_mul_left 2 _).trans (congrArg (2 * ·) (sumFin_add _ _))

/-- Each same retained matrix entry is bounded by the total over its original matrix. -/
theorem entry_le_total (weight : Weight K) (matrix : SquareMatrix K dimension) (row column : Fin dimension) :
    weight.value (matrix row column) ≤ total weight matrix :=
  (entry_le_sumFin _ (fun _ => weight.nonnegative _) column).trans
    (entry_le_sumFin _ (fun _ => weight_sum_nonnegative _ (fun _ => weight.nonnegative _)) row)

/-- One original column's weight sum is bounded by the total over the same retained matrix. -/
theorem column_le_total (weight : Weight K) (matrix : SquareMatrix K dimension) (column : Fin dimension) :
    sumFin (fun row => weight.value (matrix row column)) ≤ total weight matrix :=
  IndexedBudget.sumFin_le (fun _ => entry_le_sumFin _ (fun _ => weight.nonnegative _) column)

/-- The original structural product has an explicit finite bound in the two original total weights.

The retained intermediate dimension contributes the rational factor `2^dimension`.
All remaining factors are the original coefficient multiplier and the two
original complete entry totals.
-/
theorem total_mul_le (weight : Weight K) (left right : SquareMatrix K dimension) :
    total weight (Multiplication.mul left right) ≤
      ((2 : Rational) ^ dimension * weight.multiplier) * total weight left * total weight right := by
  have powerNonnegative := Order.Arithmetic.pow_nonneg_direct (by decide : (0 : Rational) ≤ 2) dimension
  have entryBound (row column : Fin dimension) :
      weight.value (Multiplication.mul left right row column) ≤
        (2 ^ dimension * weight.multiplier) *
          (sumFin (fun middle => weight.value (left row middle)) *
            sumFin (fun middle => weight.value (right middle column))) := by
    rewrite [Multiplication.mul_apply]
    calc
      _ ≤ 2 ^ dimension * sumFin (fun middle => weight.value (left row middle * right middle column)) :=
        weight.sum_le _
      _ ≤ 2 ^ dimension *
          (weight.multiplier * sumFin (fun middle => weight.value (left row middle) *
            weight.value (right middle column))) := by
        apply Order.Arithmetic.mul_le_mul_of_nonneg_left_direct _ powerNonnegative
        apply (IndexedBudget.sumFin_le (fun _ => weight.mul_le _ _)).trans
        apply Eq.le
        apply (sumFin_congr (fun _ => mul_assoc _ _ _)).trans
        exact sumFin_mul_left _ _
      _ ≤ 2 ^ dimension * (weight.multiplier *
          (sumFin (fun middle => weight.value (left row middle)) *
            sumFin (fun middle => weight.value (right middle column)))) :=
        Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            (sumFin_mul_le _ _ (fun _ => weight.nonnegative _) (fun _ => weight.nonnegative _))
            weight.multiplier_nonnegative) powerNonnegative
      _ = _ := by ring0
  apply (IndexedBudget.sumFin_le (fun row => IndexedBudget.sumFin_le (entryBound row))).trans
  apply Eq.le
  calc
    _ = sumFin (fun row =>
        ((2 : Rational) ^ dimension * weight.multiplier) *
          sumFin (fun middle => weight.value (left row middle)) *
            sumFin (fun column => sumFin (fun middle => weight.value (right middle column)))) := by
      apply sumFin_congr
      intro row
      apply (sumFin_congr (fun _ => (mul_assoc _ _ _).symm)).trans
      exact sumFin_mul_left _ _
    _ = ((2 : Rational) ^ dimension * weight.multiplier) * total weight left *
        sumFin (fun column => sumFin (fun middle => weight.value (right middle column))) := by
      apply (sumFin_mul_right _ _).trans
      exact congrArg (· * _) (sumFin_mul_left _ _)
    _ = _ := congrArg (((2 : Rational) ^ dimension * weight.multiplier) * total weight left * ·)
      (sumFin_swap _)

end Purelib.LinearAlgebra.Matrix.Weight

end
