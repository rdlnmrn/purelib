module
public import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Gaussian.Field
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

/-! Finite Gaussian squared-norm bounds with retained rational weights.
Scalar square identities bound two original values and their finite indexed sums,
including nonnegative zero-weight cases and explicit strict threshold budgets. -/

public section

namespace Purelib.Data.Gaussian.Norm.Weighted

open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Algebra

/-- The norm square of a Gaussian sum is at most sixteen times the first norm plus sixteen fifteenths of the second.

Multiplying the displayed difference by fifteen gives the sum of two scalar squares. Their nonnegativity yields the
exact rational weighted bound. -/
theorem normSq_add_le_weighted (u v : Basic.Canonical) :
    Basic.normSq (u + v) ≤ 16 * Basic.normSq u + (16 / 15) * Basic.normSq v :=
      by
  let difference :=
    16 * Basic.normSq u + (16 / 15) * Basic.normSq v - Basic.normSq (u + v)
  have scaledIdentity :
      15 * difference =
        (15 * u.re - v.re) ^ 2 + (15 * u.im - v.im) ^ 2 := by
    have coefficient : (15 : Fraction.Rational) * (16 / 15) = 16 := by
      calc
        (15 : Fraction.Rational) * (16 / 15) = (16 / 15) * 15 :=
          Fraction.Field.mul_comm _ _
        _ = 16 :=
          Fraction.Field.div_mul_cancel_of_ne 16 15 (by decide)
    calc
      15 * difference =
          (15 * 16) * Basic.normSq u +
            (15 * (16 / 15)) * Basic.normSq v -
            15 * Basic.normSq (u + v) := by
        dsimp only [difference]
        ring1
      _ = 240 * Basic.normSq u + 16 * Basic.normSq v -
            15 * Basic.normSq (u + v) := by
        rw [coefficient]
        ring1
      _ = (15 * u.re - v.re) ^ 2 +
            (15 * u.im - v.im) ^ 2 := by
        simp only [Basic.normSq, Basic.add_re, Basic.add_im]
        ring1
  have scaledNonnegative : 0 ≤ 15 * difference := by
    rw [scaledIdentity]
    exact add_nonneg
      (Fraction.Order.Arithmetic.sq_nonneg_direct _)
      (Fraction.Order.Arithmetic.sq_nonneg_direct _)
  have differenceNonnegative : 0 ≤ difference := by
    apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct
      (c := (15 : Fraction.Rational)) _ (by decide)
    calc
      0 * 15 = 0 := by ring1
      _ ≤ 15 * difference := scaledNonnegative
      _ = difference * 15 := Fraction.Field.mul_comm _ _
  apply Fraction.Order.Arithmetic.le_of_add_le_add_right_direct
    (c := -Basic.normSq (u + v))
  calc
    Basic.normSq (u + v) + -Basic.normSq (u + v) = 0 := by ring1
    _ ≤ difference := differenceNonnegative
    _ = (16 * Basic.normSq u + (16 / 15) * Basic.normSq v) +
          -Basic.normSq (u + v) := by
      dsimp only [difference]
      ring1

/-- A positive parameter gives the sum-norm bound with weights one plus the parameter and one plus its reciprocal.

The positive parameter scales the same sum-norm difference to an explicit Gaussian norm square. The two original
summands and reciprocal weight remain fixed. -/
theorem normSq_add_le_parameter (weight : Fraction.Rational)
    (weightPositive : 0 < weight) (u v : Basic.Canonical) :
    Basic.normSq (u + v) ≤
      (weight + 1) * Basic.normSq u +
        ((weight + 1) / weight) * Basic.normSq v := by
  let difference :=
    (weight + 1) * Basic.normSq u +
      ((weight + 1) / weight) * Basic.normSq v - Basic.normSq (u + v)
  let scalar : Basic.Canonical := ⟨weight, 0⟩
  have coefficient :
      weight * ((weight + 1) / weight) = weight + 1 := by
    calc
      weight * ((weight + 1) / weight) =
          ((weight + 1) / weight) * weight :=
        Fraction.Field.mul_comm _ _
      _ = weight + 1 :=
        Fraction.Field.div_mul_cancel_of_ne _ _
          weightPositive.ne'
  have scaledIdentity :
      weight * difference = Basic.normSq (scalar * u - v) := by
    calc
      weight * difference =
          (weight * (weight + 1)) * Basic.normSq u +
            (weight * ((weight + 1) / weight)) * Basic.normSq v -
            weight * Basic.normSq (u + v) := by
        dsimp only [difference]
        ring1
      _ = (weight * (weight + 1)) * Basic.normSq u +
            (weight + 1) * Basic.normSq v - weight * Basic.normSq (u + v) := by
        rw [coefficient]
      _ = Basic.normSq (scalar * u - v) := by
        dsimp only [scalar, Basic.normSq]
        simp only [Basic.sub_re, Basic.sub_im, Basic.add_re, Basic.add_im, Basic.mul_re, Basic.mul_im]
        ring1
  have scaledNonnegative : 0 ≤ weight * difference := by
    rw [scaledIdentity]
    exact Norm.Basic.normSq_nonneg _
  have differenceNonnegative : 0 ≤ difference := by
    apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct
      (c := weight) _ weightPositive
    calc
      0 * weight = 0 := by ring1
      _ ≤ weight * difference := scaledNonnegative
      _ = difference * weight :=
        Fraction.Field.mul_comm _ _
  apply Fraction.Order.Arithmetic.le_of_add_le_add_right_direct
    (c := -Basic.normSq (u + v))
  calc
    Basic.normSq (u + v) + -Basic.normSq (u + v) = 0 := by ring1
    _ ≤ difference := differenceNonnegative
    _ = ((weight + 1) * Basic.normSq u +
        ((weight + 1) / weight) * Basic.normSq v) +
        -Basic.normSq (u + v) := by
      dsimp only [difference]
      ring1

/-- Nonnegative endpoint weights and their squared norm bounds bound the sum norm by the square of the weight sum.

The two weights are nonnegative; each endpoint norm is bounded by a common density times its weight squared. The
conclusion retains that same density and the exact sum of the weights, including zero-weight cases. -/
theorem normSq_add_weighted {x y : Basic.Canonical} {density a b : Fraction.Rational}
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hx : Basic.normSq x ≤ density * a ^ 2) (hy : Basic.normSq y ≤ density * b ^ 2) :
    Basic.normSq (x + y) ≤ density * (a + b)^2 := by
  by_cases az : a = 0
  · subst a
    have hx0 : Basic.normSq x ≤ 0 := hx.trans_eq (by ring1)
    have xz : x = 0 := Norm.Basic.normSq_eq_zero.mp (hx0.antisymm (Norm.Basic.normSq_nonneg x))
    rw [xz, _root_.zero_add, _root_.zero_add]
    exact hy
  by_cases bz : b = 0
  · subst b
    have hy0 : Basic.normSq y ≤ 0 := hy.trans_eq (by ring1)
    have yz : y = 0 := Norm.Basic.normSq_eq_zero.mp (hy0.antisymm (Norm.Basic.normSq_nonneg y))
    rw [yz, _root_.add_zero]
    exact hx.trans_eq (by ring1)
  have ap : 0 < a := lt_of_le_of_ne ha (Ne.symm az)
  have bp : 0 < b := lt_of_le_of_ne hb (Ne.symm bz)
  have square := Norm.Basic.normSq_nonneg (⟨b * x.re - a * y.re, b * x.im - a * y.im⟩ : Basic.Canonical)
  have identity : Basic.normSq (⟨b * x.re - a * y.re, b * x.im - a * y.im⟩ : Basic.Canonical) =
      (a + b) * (b * Basic.normSq x + a * Basic.normSq y) - Basic.normSq (x +
        y) * (a * b) := by
    simp only [Basic.normSq, Basic.add_re, Basic.add_im]
    ring1
  rw [identity] at square
  have estimate : Basic.normSq (x + y) * (a * b) ≤ (a + b) * (b * Basic.normSq x + a *
    Basic.normSq y) :=
    Fraction.Order.Arithmetic.le_of_sub_nonneg_direct square
  have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.add_le_add_direct (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct hx hb)
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct hy ha)) (add_nonneg ha hb)
  apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct (c := a * b) _ (Fraction.Order.Arithmetic.mul_pos_direct
    ap bp)
  exact (estimate.trans scaled).trans_eq (by ring1)

/-- Nonnegative finite-index weights and their pointwise squared bounds bound the sum norm by the square of the sum of
weights.

Retain the given finite-index family, its nonnegative weights and one common density. The estimate uses the original
finite sums of values and weights and does not replace the indexing or select new witnesses. -/
theorem normSq_sumFin_weighted {count : Nat} (values : Fin count → Basic.Canonical)
    (weights : Fin count → Fraction.Rational) {density : Fraction.Rational}
    (nonnegative : ∀ index, 0 ≤ weights index)
    (bounded : ∀ index, Basic.normSq (values index) ≤ density * (weights index) ^ 2) :
    Basic.normSq (FiniteSum.Fin.sumFin values) ≤ density * (FiniteSum.Fin.sumFin weights)^2 := by
  induction count with
  | zero =>
    change Basic.normSq (0 : Basic.Canonical) ≤ density * (0 : Fraction.Rational)^2
    rw [Norm.Basic.normSq_zero]
    exact le_of_eq (by ring1)
  | succ count ih =>
    have tailNonnegative : 0 ≤ FiniteSum.Fin.sumFin (fun index : Fin count => weights index.succ) := by
      have estimate := FiniteSum.Rational.Order.IndexedBudget.sumFin_le
        (left := fun _ : Fin count => (0 : Fraction.Rational))
        (right := fun index : Fin count => weights index.succ)
        (fun index => nonnegative index.succ)
      rw [FiniteSum.Fin.sumFin_zero] at estimate
      exact estimate
    rw [FiniteSum.Fin.sumFin_succ, FiniteSum.Fin.sumFin_succ]
    exact normSq_add_weighted (nonnegative 0) tailNonnegative (bounded 0)
      (ih (fun index => values index.succ) (fun index => weights index.succ)
        (fun index => nonnegative index.succ) (fun index => bounded index.succ))

/-- Multiplying sum norm by the product of two rational weights gives the retained algebraic weighted norm inequality.

The difference between the weighted right side and sum-norm left side is a sum of two scalar squares. The inequality
therefore holds for arbitrary displayed rational weights. -/
theorem weighted_normSq_add_le (left right : Basic.Canonical)
    (leftWeight rightWeight : Fraction.Rational) :
    leftWeight * rightWeight * Basic.normSq (left + right) ≤
      leftWeight * (leftWeight + rightWeight) * Basic.normSq left +
        rightWeight * (leftWeight + rightWeight) * Basic.normSq right := by
  apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
  have squareSumNonnegative :
      0 ≤
        (leftWeight * left.re - rightWeight * right.re) ^ 2 +
          (leftWeight * left.im - rightWeight * right.im) ^ 2 :=
    add_nonneg
      (Fraction.Order.Arithmetic.sq_nonneg_direct _)
      (Fraction.Order.Arithmetic.sq_nonneg_direct _)
  calc
    0 ≤ (leftWeight * left.re - rightWeight * right.re) ^ 2 +
        (leftWeight * left.im - rightWeight * right.im) ^ 2 :=
      squareSumNonnegative
    _ =
        (leftWeight * (leftWeight + rightWeight) * Basic.normSq left +
            rightWeight * (leftWeight + rightWeight) * Basic.normSq right) -
          leftWeight * rightWeight * Basic.normSq (left + right) := by
      simp only [Basic.normSq, Basic.add_re,
        Basic.add_im]
      ring1

/-- Positive weights, the exact threshold budget identity and strict endpoint norm bounds imply sum squared norm below
one.

The two positive weight coefficients preserve the supplied strict bounds. Their exact threshold budget pays the original
product-weighted sum norm, and positive cancellation gives the strict unit bound. -/
public theorem weighted_sum_lt_one
    {left right : Basic.Canonical}
    (leftWeight rightWeight threshold : Fraction.Rational)
    (leftWeightPositive : 0 < leftWeight)
    (rightWeightPositive : 0 < rightWeight)
    (budget :
      leftWeight * (leftWeight + rightWeight) * threshold +
          rightWeight * (leftWeight + rightWeight) * (1 / 2 : Fraction.Rational) =
        leftWeight * rightWeight)
    (leftSmall : Basic.normSq left < threshold)
    (rightSmall : Basic.normSq right < (1 / 2 : Fraction.Rational)) :
    Basic.normSq (left + right) < 1 := by
  have sumPositive : 0 < leftWeight + rightWeight := by
    have added := Fraction.Order.Arithmetic.add_lt_add_direct
      leftWeightPositive rightWeightPositive
    simpa only [_root_.zero_add] using added
  have leftCoefficientPositive :
      0 < leftWeight * (leftWeight + rightWeight) :=
    Fraction.Order.Arithmetic.mul_pos_direct leftWeightPositive sumPositive
  have rightCoefficientPositive :
      0 < rightWeight * (leftWeight + rightWeight) :=
    Fraction.Order.Arithmetic.mul_pos_direct rightWeightPositive sumPositive
  have productPositive : 0 < leftWeight * rightWeight :=
    Fraction.Order.Arithmetic.mul_pos_direct leftWeightPositive
      rightWeightPositive
  have leftScaled :=
    Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
      leftCoefficientPositive leftSmall
  have rightScaled :=
    Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
      rightCoefficientPositive rightSmall
  have scaledBound :
      leftWeight * rightWeight * Basic.normSq (left + right) <
        leftWeight * rightWeight := by
    calc
      leftWeight * rightWeight * Basic.normSq (left + right) ≤
          leftWeight * (leftWeight + rightWeight) * Basic.normSq left +
            rightWeight * (leftWeight + rightWeight) * Basic.normSq right :=
        weighted_normSq_add_le left right leftWeight rightWeight
      _ < leftWeight * (leftWeight + rightWeight) * threshold +
          rightWeight * (leftWeight + rightWeight) * (1 / 2 : Fraction.Rational) :=
        Fraction.Order.Arithmetic.add_lt_add_direct leftScaled rightScaled
      _ = leftWeight * rightWeight := budget
  apply Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct
    (c := leftWeight * rightWeight)
  · calc
      Basic.normSq (left + right) * (leftWeight * rightWeight) =
          leftWeight * rightWeight * Basic.normSq (left + right) := by ring1
      _ < leftWeight * rightWeight := scaledBound
      _ = (1 : Fraction.Rational) * (leftWeight * rightWeight) := by ring1
  · exact productPositive

/-- A strict unit bound on the left norm and weak half bound on the right norm give a strict half bound on product norm.

The original Gaussian product retains its multiplicative squared norm. Scaling the left strict bound by the positive
half and the right weak bound by the nonnegative left norm preserves the strict half comparison. -/
public theorem normSq_mul_lt_half_of_left_lt_one_of_right_le_half
    {left right : Basic.Canonical}
    (leftInside : Basic.normSq left < 1)
    (rightBound : Basic.normSq right ≤ (1 / 2 : Fraction.Rational)) :
    Basic.normSq (left * right) < 1 / 2 := by
  rw [Norm.Basic.normSq_mul]
  calc
    Basic.normSq left * Basic.normSq right ≤
        Basic.normSq left * (1 / 2 : Fraction.Rational) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct rightBound
        (Norm.Basic.normSq_nonneg left)
    _ < (1 : Fraction.Rational) * (1 / 2 : Fraction.Rational) :=
      Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct leftInside
        (by decide)
    _ = 1 / 2 := by ring1

end Purelib.Data.Gaussian.Norm.Weighted

end
