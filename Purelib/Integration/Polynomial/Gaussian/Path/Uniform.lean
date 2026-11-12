module

public import Purelib.Integration.Polynomial.Gaussian.Path.Allowance
public import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.List.Membership
import Purelib.Algebra.NatCast
import Purelib.Algebra.Semiring.Normalization
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Exact finite count cancellation for uniform Gaussian integration meshes -/

public section

namespace Purelib.Integration.Polynomial.Gaussian.Path.Basic.PathModel

open Purelib
open Purelib.Data.Rat
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Norm.Basic (normSq_eq_canonical)
open Purelib.Approximation.Rational
open Purelib.Integration.Polynomial.Gaussian.Cell
open Purelib.Integration.Polynomial.Gaussian.Path

/-- Multiplying a quarter radius by the square of its dyadic edge count recovers the original scale. -/
private theorem countSquare_quarterRadius (scale : Fraction.Rational) (depth : Nat) :
    ((2 ^ depth : Nat) : Fraction.Rational) * (((2 ^ depth : Nat) : Fraction.Rational) *
      Geometric.Basic.quarterRadius scale depth) = scale := by
  unfold Geometric.Basic.quarterRadius
  simp only [Purelib.Algebra.NatCast.pow, Nat.cast_ofNat]
  have countSquare : (2 : Fraction.Rational) ^ depth * (2 : Fraction.Rational) ^ depth =
      (4 : Fraction.Rational) ^ depth := by
    rw [← Purelib.Algebra.Semiring.Normalization.product_pow]
    congr 1
  calc
    (2 : Fraction.Rational) ^ depth * ((2 : Fraction.Rational) ^ depth * (scale / (4 : Fraction.Rational) ^
      depth)) =
        (scale / (4 : Fraction.Rational) ^ depth) *
          ((2 : Fraction.Rational) ^ depth * (2 : Fraction.Rational) ^ depth) := by ring1
    _ = (scale / (4 : Fraction.Rational) ^ depth) * (4 : Fraction.Rational) ^ depth := by rw [countSquare]
    _ = scale := Fraction.Field.div_mul_cancel_of_ne _ _
      (ne_of_gt (Fraction.Order.Arithmetic.pow_pos_direct (by decide) depth))

/-- Uniform displacement and local allowance bounds control the total weighted allowance of the retained cell list. -/
private theorem totalWeightedAllowance_le (cells : List Basic.CellModel)
    (movement allowance : Fraction.Rational) (movementNonnegative : 0 ≤ movement)
    (bounds : ∀ cell ∈ cells, Data.Gaussian.Norm.Basic.normSq cell.displacement ≤ movement ∧ cell.localAllowance ≤
      allowance)
      :
    (Basic.PathModel.mk cells).totalWeightedAllowance ≤
      (cells.length : Fraction.Rational) * (movement * allowance) := by
  induction cells with
  | nil =>
      simp only [Basic.PathModel.totalWeightedAllowance,
        List.foldr_nil, List.length_nil, Nat.cast_zero, Fraction.Field.zero_mul_direct]
      exact le_rfl
  | cons cell cells ih =>
      have head := bounds cell (List.mem_cons_self ..)
      have headBound : cell.weightedAllowance ≤ movement * allowance := by
        have scalar := (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct head.1
          cell.localAllowance_nonneg).trans
          (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct head.2 movementNonnegative)
        rw [normSq_eq_canonical] at scalar
        exact scalar
      have tailBound := ih (fun child member => bounds child (List.mem_cons_of_mem _ member))
      simp only [Basic.PathModel.totalWeightedAllowance,
        List.foldr_cons, List.length_cons, Nat.cast_succ]
      calc
        cell.weightedAllowance + _ ≤ movement * allowance +
            (cells.length : Fraction.Rational) * (movement * allowance) := add_le_add headBound tailBound
        _ = ((cells.length : Fraction.Rational) + 1) * (movement * allowance) := by ring1

/-- A dyadic path with quarter-radius movement bounds has aggregate allowance at most the original movement scale times
the uniform allowance.

The exact cell count cancels both dyadic factors, retaining the supplied pointwise displacement and allowance bounds. -/
theorem uniform_aggregateAllowance_le (path : Basic.PathModel)
    (depth : Nat) (movement allowance : Fraction.Rational) (movementNonnegative : 0 ≤ movement)
    (count : path.cells.length = 2 ^ depth)
    (bounds : ∀ cell ∈ path.cells,
      Data.Gaussian.Norm.Basic.normSq cell.displacement ≤ Geometric.Basic.quarterRadius movement depth ∧
      cell.localAllowance ≤ allowance) :
    path.aggregateAllowance ≤ movement * allowance := by
  have total := totalWeightedAllowance_le path.cells _ allowance
    (Geometric.Basic.quarterRadius_nonneg movementNonnegative depth) bounds
  have countNonnegative : (0 : Fraction.Rational) ≤ ((2 ^ depth : Nat) : Fraction.Rational) := by
    exact Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)
  unfold Basic.PathModel.aggregateAllowance
  rw [count] at total ⊢
  calc
    _ ≤ ((2 ^ depth : Nat) : Fraction.Rational) * (((2 ^ depth : Nat) : Fraction.Rational) *
        (Geometric.Basic.quarterRadius movement depth * allowance)) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct total countNonnegative
    _ = (((2 ^ depth : Nat) : Fraction.Rational) * (((2 ^ depth : Nat) : Fraction.Rational) *
        Geometric.Basic.quarterRadius movement depth)) * allowance := by ring1
    _ = movement * allowance := by rw [countSquare_quarterRadius]
end Purelib.Integration.Polynomial.Gaussian.Path.Basic.PathModel
