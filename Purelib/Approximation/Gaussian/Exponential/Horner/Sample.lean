module
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Gaussian.Exponential.Horner.Basic
import Purelib.Approximation.Gaussian.Exponential.Horner.Bounds
public import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Scale
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Tactic.QuotientFreeOmega
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
import Purelib.Data.Nat.Subtraction

/-!
# Finite exponential Horner samples

The outer denominator-one Horner stage retains an inner finite
program beginning at denominator two. Bounds compare displayed Gaussian
samples on the unit disk at their supplied inputs and finite depths.
-/

namespace Purelib.Approximation.Gaussian.Exponential.Horner.Sample

open Purelib
open Purelib.Approximation.Gaussian.Exponential
open Purelib.Approximation.Rational
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction
open Purelib.Data.Nat

/-- The displayed finite exponential sample. The recurrence retains `index` inner stages.

The displayed outer stage uses denominator one and the retained inner
Horner program starting at denominator two with the supplied finite depth. -/
@[expose] public def sample (x : Basic.Canonical) (index : Nat) : Basic.Canonical :=
  Basic.step x 1 (Basic.horner x 2 index)

/-- The displayed finite exponential program satisfies `exp(0) = 1` exactly at every depth.

Every inner stage at zero input has the exact zero-input Horner readback.
The original outer scalar stage therefore retains the Gaussian value one. -/
public theorem sample_zero (index : Nat) : sample 0 index = 1 := by
  rw [sample, Basic.step_eq, Basic.horner_zero_input]
  apply Basic.ext <;>
    simp only [Basic.add_re, Basic.add_im, Basic.one_re, Basic.one_im, Scale.scale_re, Scale.scale_im,
      Basic.mul_re, Basic.mul_im, Basic.zero_re, Basic.zero_im] <;> ring1

/-- A finite exponential Horner sample at a real input has zero imaginary coordinate. -/
public theorem sample_im_zero (x : Basic.Canonical) (input : x.im = 0) (depth : Nat) :
    (sample x depth).im = 0 :=
  Basic.step_im_zero x input 1 (Basic.horner x 2 depth) (Basic.horner_im_zero x input depth 2)

/-- Uniform finite sensitivity of displayed outer exponential samples.

Both displayed inputs have quadrance at most one and use the same finite
depth. The two retained inner tails and their original difference bound control the outer samples. -/
public theorem sample_input_close (x y : Basic.Canonical) (xUnit : Norm.Basic.normSq x ≤ 1)
    (yUnit : Norm.Basic.normSq y ≤ 1) (depth : Nat) :
    Norm.Basic.normSq (sample x depth - sample y depth) ≤ 16 * Norm.Basic.normSq (x - y) :=
      by
  rw [sample, sample, Bounds.step_inputs_sub, Scale.normSq_scale]
  let xTail := Basic.horner x 2 depth
  let yTail := Basic.horner y 2 depth
  let difference := Norm.Basic.normSq (x - y)
  have xTailBound : Norm.Basic.normSq xTail ≤ 4 :=
    Bounds.horner_bounded x xUnit depth 2 (by decide)
  have tailDifference : Norm.Basic.normSq (xTail - yTail) ≤ 4 * difference :=
    Bounds.horner_input_close x y xUnit yUnit depth 2 (by decide)
  have firstBound : Norm.Basic.normSq ((x - y) * xTail) ≤ 4 * difference := by
    rw [Norm.Basic.normSq_mul]
    have scaled := Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      xTailBound (Norm.Basic.normSq_nonneg (x - y))
    calc
      Norm.Basic.normSq (x - y) * Norm.Basic.normSq xTail ≤ Norm.Basic.normSq
        (x - y) * 4 :=
        scaled
      _ = 4 * difference := by
        dsimp only [difference]
        ring1
  have secondBound : Norm.Basic.normSq (y * (xTail - yTail)) ≤ 4 * difference := by
    rw [Norm.Basic.normSq_mul]
    have scaled := Order.Arithmetic.mul_le_mul_direct yUnit
      tailDifference (Norm.Basic.normSq_nonneg (xTail - yTail))
      (by decide : (0 : Rational) ≤ 1)
    simpa only [Field.one_mul] using scaled
  have sumBound := Norm.Bounds.normSq_add_le_two ((x - y) * xTail)
    (y * (xTail - yTail))
  have scalar : (1 / ((1 : Nat) : Rational)) ^ 2 = 1 := by decide
  rw [scalar, Field.one_mul]
  calc
    Norm.Basic.normSq ((x - y) * xTail + y * (xTail - yTail)) ≤
        2 * (Norm.Basic.normSq ((x - y) * xTail) +
          Norm.Basic.normSq (y * (xTail - yTail))) := sumBound
    _ ≤ 2 * (4 * difference + 4 * difference) :=
      Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (add_le_add firstBound secondBound) (by decide)
    _ = 16 * Norm.Basic.normSq (x - y) := by
      dsimp only [difference]
      ring1

/-- The squared distance between two outer exponential samples is bounded by the distance between their inner Horner
samples on the unit disk.

The displayed input lies in the unit disk. The original denominator-one
outer stage scales the inner-tail difference by that same Gaussian input. -/
public theorem sample_difference_le_inner (x : Basic.Canonical) (unitInput : Norm.Basic.normSq x ≤ 1)
    (left right : Nat) :
    Norm.Basic.normSq (sample x left - sample x right) ≤
      Norm.Basic.normSq (Basic.horner x 2 left - Basic.horner x 2 right) := by
  rw [sample, sample, Basic.step_sub_step, Scale.normSq_scale, Norm.Basic.normSq_mul]
  have scalar : (1 / ((1 : Nat) : Rational)) ^ 2 = 1 := by decide
  rw [scalar, Field.one_mul]
  have scaled := Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    unitInput (Norm.Basic.normSq_nonneg (Basic.horner x 2 left - Basic.horner x 2 right))
  simpa only [Field.one_mul] using scaled

/-- Later exponential samples on the unit disk stay within the earlier index's scale-ten quarter-radius allowance.

The displayed input lies in the unit disk. Its explicit finite stage
difference extends the earlier inner Horner program by the same retained number of stages. -/
public theorem sample_later_close (x : Basic.Canonical) (unitInput : Norm.Basic.normSq x ≤ 1)
    {earlier later : Nat} (order : earlier ≤ later) :
    Norm.Basic.normSq (sample x later - sample x earlier) ≤
      Geometric.Basic.quarterRadius 10 earlier := by
  let extra := later - earlier
  have extension : earlier + extra = later := Subtraction.add_sub_of_le order
  rw [← extension]
  calc
    Norm.Basic.normSq (sample x (earlier + extra) - sample x earlier) ≤
        Norm.Basic.normSq (Basic.horner x 2 (earlier + extra) - Basic.horner x 2 earlier) :=
      sample_difference_le_inner x unitInput _ _
    _ ≤ 10 * (1 / 4 : Rational) ^ earlier :=
      Bounds.horner_add_depth_close x unitInput earlier extra 2 (by decide)
    _ = Geometric.Basic.quarterRadius 10 earlier :=
      (Geometric.Basic.quarterRadius_eq_mul_pow 10 earlier).symm

/-- Every displayed outer sample has a uniform finite center bound.

The unit-disk input bounds the original inner tail's quadrance by four.
The retained denominator-one outer stage then has quadrance at most ten. -/
public theorem sample_bounded (x : Basic.Canonical) (unitInput : Norm.Basic.normSq x ≤ 1)
    (index : Nat) :
    Norm.Basic.normSq (sample x index) ≤ 10 := by
  have tailBound := Bounds.horner_bounded x unitInput index 2 (by decide)
  have productBound : Norm.Basic.normSq (x * Basic.horner x 2 index) ≤ 4 := by
    rw [Norm.Basic.normSq_mul]
    have multiplied := Order.Arithmetic.mul_le_mul_direct unitInput
      tailBound (Norm.Basic.normSq_nonneg (Basic.horner x 2 index))
      (by decide : (0 : Rational) ≤ 1)
    simpa only [Field.one_mul] using multiplied
  have scaledIdentity :
      Scale.scale (1 / ((1 : Nat) : Rational)) (x * Basic.horner x 2 index) =
        x * Basic.horner x 2 index := by
    apply Basic.ext <;>
      simp only [Scale.scale_re, Scale.scale_im] <;>
      rw [show (1 / ((1 : Nat) : Rational)) = 1 by decide,
        Field.one_mul]
  rw [sample, Basic.step_eq, scaledIdentity]
  calc
    Norm.Basic.normSq (1 + x * Basic.horner x 2 index) ≤
        2 * (Norm.Basic.normSq (1 : Basic.Canonical) + Norm.Basic.normSq (x *
          Basic.horner x 2
          index)) :=
      Norm.Bounds.normSq_add_le_two _ _
    _ ≤ 2 * (1 + 4) := by
      rw [Norm.Basic.normSq_one]
      exact Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (add_le_add le_rfl productBound) (by decide)
    _ = 10 := by decide

end Purelib.Approximation.Gaussian.Exponential.Horner.Sample
