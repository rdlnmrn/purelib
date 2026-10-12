module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Field
public import Purelib.Approximation.Gaussian.Exponential.Horner.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Scale
import Purelib.Data.Rat.Bounds.ReciprocalNatural
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib

open Purelib.Approximation.Gaussian.Exponential

open Purelib.Data.Gaussian

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Exact integration and finite reading bounds for exponential polynomials

`polynomial n` has degree `n+1`, matching the existing finite Horner sample
at index `n`.  Its integral has the next sample index.  All statements concern
displayed coefficient lists and rational points, not a completed exponential.
-/

namespace Purelib.Approximation.Gaussian.Exponential.Horner.Bounds

/-- A direct finite lower bound for each positive-input Horner tail. -/
theorem horner_one_re_lower : ∀ (depth denominator :
  Nat),
    (1 : Fraction.Rational) ≤ (Horner.Basic.horner 1 denominator depth).re
  | 0, _ => le_rfl
  | depth + 1, denominator => by
      rw [Horner.Basic.horner_succ, Horner.Basic.step_eq, _root_.one_mul, Data.Gaussian.Basic.add_re,
        Data.Gaussian.Basic.one_re, Scale.scale_re]
      have tailNonnegative := (show (0 : Fraction.Rational) ≤ 1 from by decide).trans
        (horner_one_re_lower depth (denominator + 1))
      have reciprocalNonnegative := Fraction.Order.Field.div_nonneg_direct
        (show (0 : Fraction.Rational) ≤ 1 from by decide)
        (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le denominator))
      calc
        1 = (1 : Fraction.Rational) + 0 := by decide
        _ ≤ 1 + (1 / (denominator : Fraction.Rational)) *
            (Horner.Basic.horner 1 (denominator + 1) depth).re :=
          add_le_add le_rfl
            (Fraction.Order.Arithmetic.mul_nonneg_direct reciprocalNonnegative tailNonnegative)
end Purelib.Approximation.Gaussian.Exponential.Horner.Bounds

end

section
@[expose] public section

/-!
# Finite exponential Horner approximation

This is a finite operational exponential on Gaussian rationals in the closed
unit disk.  `sample x n` evaluates exactly one finite Horner program.  The
pairwise theorem compares any two displayed truncations and supplies an
explicit rational squared-error sidecar.  Nothing in this module defines a
completed exponential value or invokes an infinite series or a limit.
-/

namespace Purelib.Approximation.Gaussian.Exponential.Horner.Bounds

/-- An exponential Horner step with denominator at least two preserves squared-norm bound four for unit-disk input. -/
theorem step_bounded (x : Canonical)
  (unitInput : Data.Gaussian.Norm.Basic.normSq x ≤ 1)
    {denominator : Nat} (atLeastTwo : 2 ≤ denominator) {tail : Canonical}
    (tailBound : Data.Gaussian.Norm.Basic.normSq tail ≤ 4) :
    Data.Gaussian.Norm.Basic.normSq (Horner.Basic.step x denominator tail) ≤ 4 := by
  rw [Horner.Basic.step_eq]
  have productBound : Data.Gaussian.Norm.Basic.normSq (x * tail) ≤ 4 := by
    rw [Data.Gaussian.Norm.Basic.normSq_mul]
    have multiplied := Fraction.Order.Arithmetic.mul_le_mul_direct unitInput
      tailBound (Data.Gaussian.Norm.Basic.normSq_nonneg tail) (by decide : (0 : Fraction.Rational) ≤ 1)
    simpa only [_root_.one_mul] using multiplied
  have reciprocalBound := Bounds.ReciprocalNatural.reciprocal_nat_sq_le_quarter atLeastTwo
  have reciprocalNonnegative :
      0 ≤ (1 / (denominator : Fraction.Rational)) ^ 2 :=
    Fraction.Order.Arithmetic.sq_nonneg_direct _
  have scaledBound :
      Data.Gaussian.Norm.Basic.normSq (Scale.scale (1 / (denominator : Fraction.Rational)) (x * tail)) ≤ 1 :=
        by
    rw [Scale.normSq_scale]
    calc
      (1 / (denominator : Fraction.Rational)) ^ 2 * Data.Gaussian.Norm.Basic.normSq (x * tail) ≤
          (1 / (denominator : Fraction.Rational)) ^ 2 * 4 :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct productBound
          reciprocalNonnegative
      _ ≤ (1 / 4 : Fraction.Rational) * 4 :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          reciprocalBound (by decide)
      _ = 1 := by decide
  calc
    Data.Gaussian.Norm.Basic.normSq (1 + Scale.scale (1 / (denominator : Fraction.Rational)) (x * tail)) ≤
        2 * (Data.Gaussian.Norm.Basic.normSq (1 : Canonical) +
          Data.Gaussian.Norm.Basic.normSq (Scale.scale (1 / (denominator : Fraction.Rational)) (x * tail))) :=
      Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _
    _ ≤ 2 * (1 + 1) := by
      rw [Data.Gaussian.Norm.Basic.normSq_one]
      exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (add_le_add le_rfl scaledBound) (by decide)
    _ = 4 := by decide

/-- Every finite exponential Horner value with starting denominator at least two has squared norm at most four on the
unit disk. -/
theorem horner_bounded (x :
  Canonical) (unitInput : Data.Gaussian.Norm.Basic.normSq x ≤ 1) :
    ∀ (depth denominator : Nat), 2 ≤ denominator →
      Data.Gaussian.Norm.Basic.normSq (Horner.Basic.horner x denominator depth) ≤ 4
  | 0, _, _ => by
      rw [Horner.Basic.horner_zero, Data.Gaussian.Norm.Basic.normSq_one]
      decide
  | depth + 1, denominator, atLeastTwo => by
      rw [Horner.Basic.horner_succ]
      exact step_bounded x unitInput atLeastTwo
        (horner_bounded x unitInput depth (denominator + 1) (by
          omega))

/-- The squared deviation from one of an inner exponential Horner value is at most ten on the unit disk. -/
theorem horner_sub_one_bounded (x :
  Canonical) (unitInput : Data.Gaussian.Norm.Basic.normSq x ≤ 1)
    (depth denominator : Nat) (atLeastTwo : 2 ≤ denominator) :
    Data.Gaussian.Norm.Basic.normSq (Horner.Basic.horner x denominator depth - 1) ≤ 10 := by
  calc
    Data.Gaussian.Norm.Basic.normSq (Horner.Basic.horner x denominator depth - 1) ≤
        2 * (Data.Gaussian.Norm.Basic.normSq (Horner.Basic.horner x denominator depth) +
          Data.Gaussian.Norm.Basic.normSq (1 : Canonical)) :=
      Data.Gaussian.Norm.Bounds.normSq_sub_le_two _ _
    _ ≤ 2 * (4 + 1) := by
      rw [Data.Gaussian.Norm.Basic.normSq_one]
      exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (add_le_add (horner_bounded x unitInput depth denominator
          atLeastTwo)
          le_rfl) (by decide)
    _ = 10 := by decide

/-- Each shared inner Horner stage contracts squared disagreement by one quarter. -/
theorem step_difference_contract (x :
  Canonical) (unitInput : Data.Gaussian.Norm.Basic.normSq x ≤ 1)
    {denominator : Nat} (atLeastTwo : 2 ≤ denominator)
    (left right : Canonical) :
    Data.Gaussian.Norm.Basic.normSq (Horner.Basic.step x denominator left - Horner.Basic.step x denominator
      right) ≤
      (1 / 4 : Fraction.Rational) * Data.Gaussian.Norm.Basic.normSq (left - right) := by
  rw [Horner.Basic.step_sub_step, Scale.normSq_scale, Data.Gaussian.Norm.Basic.normSq_mul]
  have inputScaled : Data.Gaussian.Norm.Basic.normSq x * Data.Gaussian.Norm.Basic.normSq (left -
    right) ≤
      1 * Data.Gaussian.Norm.Basic.normSq (left - right) :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct unitInput
      (Data.Gaussian.Norm.Basic.normSq_nonneg (left - right))
  have reciprocalNonnegative :
      0 ≤ (1 / (denominator : Fraction.Rational)) ^ 2 :=
    Fraction.Order.Arithmetic.sq_nonneg_direct _
  calc
    (1 / (denominator : Fraction.Rational)) ^ 2 *
          (Data.Gaussian.Norm.Basic.normSq x * Data.Gaussian.Norm.Basic.normSq (left - right)) ≤
        (1 / (denominator : Fraction.Rational)) ^ 2 *
          (1 * Data.Gaussian.Norm.Basic.normSq (left - right)) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct inputScaled
        reciprocalNonnegative
    _ = (1 / (denominator : Fraction.Rational)) ^ 2 *
        Data.Gaussian.Norm.Basic.normSq (left - right) := by ring1
    _ ≤ (1 / 4 : Fraction.Rational) * Data.Gaussian.Norm.Basic.normSq (left - right) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        (Bounds.ReciprocalNatural.reciprocal_nat_sq_le_quarter atLeastTwo)
        (Data.Gaussian.Norm.Basic.normSq_nonneg (left - right))

/-- The difference of exponential Horner steps separates input change from retained-tail change under the common
denominator. -/
theorem step_inputs_sub (x y :
  Canonical) (denominator : Nat)
    (xTail yTail : Canonical) :
    Horner.Basic.step x denominator xTail - Horner.Basic.step y denominator yTail =
      Scale.scale (1 / (denominator : Fraction.Rational))
        ((x - y) * xTail + y * (xTail - yTail)) := by
  rw [Horner.Basic.step_eq, Horner.Basic.step_eq]
  apply Data.Gaussian.Basic.ext <;>
    simp only [Scale.scale_re, Scale.scale_im, Data.Gaussian.Basic.add_re, Basic.add_im, Basic.sub_re, Basic.sub_im,
      Data.Gaussian.Basic.one_re, Basic.one_im, Basic.mul_re, Basic.mul_im] <;> ring1

/-- Uniform finite sensitivity of equal-depth inner Horner programs on the rational unit disk. -/
theorem horner_input_close (x y :
  Canonical) (xUnit : Data.Gaussian.Norm.Basic.normSq x ≤ 1)
    (yUnit : Data.Gaussian.Norm.Basic.normSq y ≤ 1) :
    ∀ (depth denominator : Nat), 2 ≤ denominator →
      Data.Gaussian.Norm.Basic.normSq (Horner.Basic.horner x denominator depth - Horner.Basic.horner y
        denominator depth) ≤
        4 * Data.Gaussian.Norm.Basic.normSq (x - y)
  | 0, _, _ => by
      rw [Horner.Basic.horner_zero, Horner.Basic.horner_zero, _root_.sub_self, Data.Gaussian.Norm.Basic.normSq_zero]
      exact Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        (Data.Gaussian.Norm.Basic.normSq_nonneg (x - y))
  | depth + 1, denominator, atLeastTwo => by
      rw [Horner.Basic.horner_succ, Horner.Basic.horner_succ,
        step_inputs_sub, Scale.normSq_scale]
      let xTail := Horner.Basic.horner x (denominator + 1) depth
      let yTail := Horner.Basic.horner y (denominator + 1) depth
      let difference := Data.Gaussian.Norm.Basic.normSq (x - y)
      have xTailBound : Data.Gaussian.Norm.Basic.normSq xTail ≤ 4 :=
        horner_bounded x xUnit depth (denominator + 1) (by omega)
      have tailDifference : Data.Gaussian.Norm.Basic.normSq (xTail - yTail) ≤ 4 * difference :=
        horner_input_close x y xUnit yUnit depth (denominator +
          1) (by omega)
      have firstBound : Data.Gaussian.Norm.Basic.normSq ((x - y) * xTail) ≤ 4 * difference := by
        rw [Data.Gaussian.Norm.Basic.normSq_mul]
        have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          xTailBound (Data.Gaussian.Norm.Basic.normSq_nonneg (x - y))
        calc
          Data.Gaussian.Norm.Basic.normSq (x - y) * Data.Gaussian.Norm.Basic.normSq xTail ≤
            Data.Gaussian.Norm.Basic.normSq (x - y) * 4 := scaled
          _ = 4 * difference := by
            dsimp only [difference]
            ring1
      have secondBound : Data.Gaussian.Norm.Basic.normSq (y * (xTail - yTail)) ≤ 4 * difference := by
        rw [Data.Gaussian.Norm.Basic.normSq_mul]
        have scaled := Fraction.Order.Arithmetic.mul_le_mul_direct yUnit
          tailDifference (Data.Gaussian.Norm.Basic.normSq_nonneg (xTail - yTail))
          (by decide : (0 : Fraction.Rational) ≤ 1)
        simpa only [_root_.one_mul] using scaled
      have sumBound :
          Data.Gaussian.Norm.Basic.normSq ((x - y) * xTail + y * (xTail - yTail)) ≤
            16 * difference := by
        calc
          Data.Gaussian.Norm.Basic.normSq ((x - y) * xTail + y * (xTail - yTail)) ≤
              2 * (Data.Gaussian.Norm.Basic.normSq ((x - y) * xTail) +
                Data.Gaussian.Norm.Basic.normSq (y * (xTail - yTail))) :=
                  Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _
          _ ≤ 2 * (4 * difference + 4 * difference) :=
            Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
              (add_le_add firstBound secondBound) (by decide)
          _ = 16 * difference := by ring1
      have reciprocalNonnegative :
          0 ≤ (1 / (denominator : Fraction.Rational)) ^ 2 :=
        Fraction.Order.Arithmetic.sq_nonneg_direct _
      calc
        (1 / (denominator : Fraction.Rational)) ^ 2 *
            Data.Gaussian.Norm.Basic.normSq ((x - y) * xTail + y * (xTail - yTail)) ≤
          (1 / (denominator : Fraction.Rational)) ^ 2 * (16 * difference) :=
            Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
              sumBound reciprocalNonnegative
        _ ≤ (1 / 4 : Fraction.Rational) * (16 * difference) :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
            (Bounds.ReciprocalNatural.reciprocal_nat_sq_le_quarter atLeastTwo)
            (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
              (Data.Gaussian.Norm.Basic.normSq_nonneg (x - y)))
        _ = 4 * Data.Gaussian.Norm.Basic.normSq (x - y) := by
          dsimp only [difference]
          calc
            (1 / 4 : Fraction.Rational) * (16 * Data.Gaussian.Norm.Basic.normSq (x - y)) =
                ((1 / 4 : Fraction.Rational) * 16) * Data.Gaussian.Norm.Basic.normSq (x - y) := by ring1
            _ = 4 * Data.Gaussian.Norm.Basic.normSq (x - y) := by
              rw [show (1 / 4 : Fraction.Rational) * 16 = 4 by decide]

/-- Any two displayed truncations compare directly, with no mention of a limit or a completed exponential. -/
theorem horner_add_depth_close (x :
  Canonical) (unitInput : Data.Gaussian.Norm.Basic.normSq x ≤ 1) :
    ∀ (earlier extra denominator : Nat), 2 ≤ denominator →
      Data.Gaussian.Norm.Basic.normSq (Horner.Basic.horner x denominator (earlier + extra) -
        Horner.Basic.horner x denominator earlier) ≤
          10 * (1 / 4 : Fraction.Rational) ^ earlier
  | 0, extra, denominator, atLeastTwo => by
      simp only [Nat.zero_add, Horner.Basic.horner_zero, pow_zero]
      simpa only [Fraction.Field.mul_one_direct] using
        horner_sub_one_bounded x unitInput extra denominator atLeastTwo
  | earlier + 1, extra, denominator, atLeastTwo => by
      rw [show earlier + 1 + extra = (earlier + extra) + 1 by ring1,
        Horner.Basic.horner_succ, Horner.Basic.horner_succ]
      calc
        Data.Gaussian.Norm.Basic.normSq
            (Horner.Basic.step x denominator (Horner.Basic.horner x (denominator + 1) (earlier + extra)) -
              Horner.Basic.step x denominator (Horner.Basic.horner x (denominator + 1) earlier)) ≤
            (1 / 4 : Fraction.Rational) *
              Data.Gaussian.Norm.Basic.normSq (Horner.Basic.horner x (denominator + 1) (earlier + extra) -
                Horner.Basic.horner x (denominator + 1) earlier) :=
          step_difference_contract x unitInput atLeastTwo _ _
        _ ≤ (1 / 4 : Fraction.Rational) *
            (10 * (1 / 4 : Fraction.Rational) ^ earlier) :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            (horner_add_depth_close x unitInput earlier extra
              (denominator + 1)
              (atLeastTwo.trans (Nat.le_add_right denominator 1))) (by decide)
        _ = 10 * (1 / 4 : Fraction.Rational) ^ (earlier + 1) := by
          rw [pow_succ]
          ring1
end Purelib.Approximation.Gaussian.Exponential.Horner.Bounds

end
