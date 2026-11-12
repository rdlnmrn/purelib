module
import Purelib.Data.Nat.Subtraction
import Purelib.Algebra.NatCast
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Prefix
import Purelib.Approximation.Gaussian.Exponential.Taylor.Basic
import Purelib.Approximation.Gaussian.Exponential.Taylor.Bounds
public import Purelib.Approximation.Gaussian.Exponential.Taylor.Cauchy
public import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Gaussian.FiniteSum.Bounds
import Purelib.Data.Gaussian.FiniteSum.Geometric
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Nat.Addition
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Geometric.Bounds
import Purelib.Data.Rat.Geometric.Quarter

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Data.Nat.Cast.Basic

open Purelib.Data.Rat.Fraction.Order

section
public section

/-! Approximation Gaussian Exponential Taylor Cauchy Bounds and its finite structural certificates. -/

namespace Purelib.Approximation.Gaussian.Exponential.Taylor.Cauchy.Bounds

open Purelib
open Purelib.Algebra.FiniteSum
open Purelib.Approximation.Gaussian.Exponential
open Purelib.Approximation.Gaussian.Exponential.Taylor
open Purelib.Approximation.Rational
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.FiniteSum
open Purelib.Data.Nat
open Purelib.Data.Rat
open Purelib.Data.Rat.Geometric

/-- A finite exponential Cauchy-tail product term is bounded by the quarter-powers of its retained total degree and
offset on the unit disks. -/
theorem cauchyUpperTail_term_normSq_le {x y : Basic.Canonical}
    (xUnit : Norm.Basic.normSq x ≤ 1) (yUnit : Norm.Basic.normSq y ≤ 1)
    {degree leftDegree : Nat} (degreePositive : 1 ≤ degree)
    (leftOrder : leftDegree ≤ degree) (offset : Nat) :
    Norm.Basic.normSq
        (Basic.taylorTerm x leftDegree *
          Basic.taylorTerm y (degree - leftDegree + 1 + offset)) ≤
      (1 / 4 : Fraction.Rational) ^ (degree - 1) *
        (1 / 4 : Fraction.Rational) ^ offset := by
  rw [Norm.Basic.normSq_mul]
  cases leftDegree with
  | zero =>
      rw [taylorTerm_zero, Norm.Basic.normSq_one, Fraction.Field.one_mul]
      have rightBound := Bounds.taylorTerm_succ_normSq_le yUnit (degree + offset)
      have rightIndex : degree - 0 + 1 + offset = degree + offset + 1 := by
        simp only [Nat.sub_zero]
        exact Addition.add_one_add degree offset
      rw [rightIndex]
      calc
        Norm.Basic.normSq (Basic.taylorTerm y (degree + offset + 1)) ≤
            (1 / 4 : Fraction.Rational) ^ (degree + offset) := rightBound
        _ ≤ (1 / 4 : Fraction.Rational) ^ (degree - 1 + offset) := by
          have exponentIdentity : degree + offset =
              (degree - 1 + offset) + 1 := by
            calc
              degree + offset = (degree - 1 + 1) + offset :=
                congrArg (fun value => value + offset)
                  (Subtraction.sub_add_cancel degreePositive).symm
              _ = (degree - 1 + offset) + 1 :=
                Addition.add_one_add (degree - 1) offset
          rw [exponentIdentity]
          exact Quarter.quarter_pow_succ_le _
        _ = (1 / 4 : Fraction.Rational) ^ (degree - 1) *
              (1 / 4 : Fraction.Rational) ^ offset := by
          rw [← pow_add]
  | succ leftPred =>
      have leftBound := Bounds.taylorTerm_succ_normSq_le xUnit leftPred
      have rightIndex :
          degree - (leftPred + 1) + 1 + offset =
            (degree - (leftPred + 1) + offset) + 1 := by
        exact Addition.add_one_add (degree - (leftPred + 1)) offset
      rw [rightIndex]
      have rightBound := Bounds.taylorTerm_succ_normSq_le yUnit
        (degree - (leftPred + 1) + offset)
      have productBound := Arithmetic.mul_le_mul_direct
        leftBound rightBound (Norm.Basic.normSq_nonneg _) (by
          exact Arithmetic.pow_nonneg_direct (by decide) _)
      calc
        Norm.Basic.normSq (Basic.taylorTerm x (leftPred + 1)) *
            Norm.Basic.normSq
              (Basic.taylorTerm y (degree - (leftPred + 1) + offset + 1)) ≤
          (1 / 4 : Fraction.Rational) ^ leftPred *
            (1 / 4 : Fraction.Rational) ^
              (degree - (leftPred + 1) + offset) := productBound
        _ = (1 / 4 : Fraction.Rational) ^ (degree - 1) *
              (1 / 4 : Fraction.Rational) ^ offset := by
          rw [← pow_add, ← pow_add]
          congr 1
          have decomposition : degree =
              (leftPred + (degree - (leftPred + 1))) + 1 := by
            calc
              degree = (leftPred + 1) +
                  (degree - (leftPred + 1)) :=
                (Subtraction.add_sub_of_le leftOrder).symm
              _ = (leftPred + (degree - (leftPred + 1))) + 1 := by
                exact Addition.add_one_add leftPred (degree - (leftPred + 1))
          have core : degree - 1 =
              leftPred + (degree - (leftPred + 1)) :=
            Subtraction.sub_eq_of_eq_add decomposition
          rw [← Nat.add_assoc, ← core]

/-- Each finite high-degree Cauchy-tail row is bounded in squared norm by four times the quarter-power at total degree
minus one. -/
theorem cauchyUpperTail_row_normSq_le {x y : Basic.Canonical}
    (xUnit : Norm.Basic.normSq x ≤ 1) (yUnit : Norm.Basic.normSq y ≤ 1)
    {degree leftDegree : Nat} (degreePositive : 1 ≤ degree)
    (leftOrder : leftDegree ≤ degree) :
    Norm.Basic.normSq
        (Prefix.sum
          (fun offset =>
            Basic.taylorTerm x leftDegree *
              Basic.taylorTerm y (degree - leftDegree + 1 + offset))
          leftDegree) ≤
      4 * (1 / 4 : Fraction.Rational) ^ (degree - 1) := by
  exact Geometric.sum_geometric_normSq_le _ leftDegree
    ((1 / 4 : Fraction.Rational) ^ (degree - 1))
    (Arithmetic.pow_nonneg_direct (by decide) _)
    (cauchyUpperTail_term_normSq_le xUnit yUnit degreePositive
      leftOrder)

/-- Explicit bound for the finite high-degree corner in the exponential Cauchy product. -/
theorem cauchyUpperTail_normSq_le {x y : Basic.Canonical}
    (xUnit : Norm.Basic.normSq x ≤ 1) (yUnit : Norm.Basic.normSq y ≤ 1)
    {degree : Nat} (degreePositive : 1 ≤ degree) :
    Norm.Basic.normSq (cauchyUpperTail x y degree) ≤
      (2 : Fraction.Rational) ^ (degree + 2) *
        (4 * (1 / 4 : Fraction.Rational) ^ (degree - 1)) := by
  let bound : Fraction.Rational := 4 * (1 / 4 : Fraction.Rational) ^ (degree - 1)
  let row : Nat → Basic.Canonical := fun leftDegree =>
    Prefix.sum
      (fun offset =>
        Basic.taylorTerm x leftDegree *
          Basic.taylorTerm y (degree - leftDegree + 1 + offset))
      leftDegree
  have boundNonnegative : 0 ≤ bound :=
    Arithmetic.mul_nonneg_direct (by decide)
      (Arithmetic.pow_nonneg_direct (by decide) _)
  have weighted := Bounds.sum_uniform_normSq_le row (degree + 1) bound
    boundNonnegative
    (fun leftDegree order => cauchyUpperTail_row_normSq_le xUnit
      yUnit
      degreePositive (Nat.le_of_lt_succ order))
  have weightOrderNat := Bounds.sumWeight_le_two_pow (degree + 1)
  have weightOrder : (Bounds.sumWeight (degree + 1) : Fraction.Rational) ≤
      (2 : Fraction.Rational) ^ (degree + 2) := by
    have castOrder := Fraction.Cast.Order.natCast_le_direct weightOrderNat
    simpa only [Algebra.NatCast.pow, Nat.cast_ofNat] using castOrder
  have result := weighted.trans
      (Arithmetic.mul_le_mul_of_nonneg_right_direct
        weightOrder boundNonnegative)
  simpa only [cauchyUpperTail, row, bound] using result

/-- At the synchronized even truncation degree `2 * index + 2`, the finite exponential addition-law error has the
explicit quarter-power allowance `16 / 4^index`. -/
theorem truncatedExp_addition_error_even {x y : Basic.Canonical}
    (xUnit : Norm.Basic.normSq x ≤ 1) (yUnit : Norm.Basic.normSq y ≤ 1)
      (index : Nat) :
    Norm.Basic.normSq
        (Basic.truncatedExp x (2 * index + 2) *
            Basic.truncatedExp y (2 * index + 2) -
          Basic.truncatedExp (x + y) (2 * index + 2)) ≤
      Geometric.Basic.quarterRadius 16 index := by
  rw [truncatedExp_mul_sub_truncatedExp_eq_upper]
  calc
    Norm.Basic.normSq (cauchyUpperTail x y (2 * index + 2)) ≤
        (2 : Fraction.Rational) ^ (2 * index + 2 + 2) *
          (4 * (1 / 4 : Fraction.Rational) ^ (2 * index + 2 - 1)) :=
      cauchyUpperTail_normSq_le xUnit yUnit
        (Nat.succ_le_succ (Nat.zero_le (2 * index + 1)))
    _ = Geometric.Basic.quarterRadius 16 index :=
      Bounds.even_cauchy_bound_identity index
end Purelib.Approximation.Gaussian.Exponential.Taylor.Cauchy.Bounds

end
