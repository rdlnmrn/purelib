module
import Purelib.Approximation.Rat.Logarithm.Horner.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Logarithm.Local.Horner.Basic
import Purelib.Approximation.Gaussian.Logarithm.Local.Horner.Bounds
public import Purelib.Approximation.Gaussian.Logarithm.Local.Horner.Sample
import Purelib.Approximation.Rat.Logarithm.Horner.Sensitivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.RationalEmbedding
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib

open Purelib.Approximation.Gaussian.Logarithm.Local

open Purelib.Approximation.Gaussian.Logarithm.Local.Horner

open Purelib.Approximation.Rat.Logarithm.Horner

open Purelib.Approximation.Rat.Logarithm.Horner.Basic

open Purelib.Data.Gaussian

open Purelib.Data.Gaussian.RationalEmbedding

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Finite complex logarithm on a reduced Gaussian-rational disk

For a displayed Gaussian rational `z` with `normSq z <= 1/9`, this module
computes finite truncations of

`2 z (1 + z^2/3 + z^4/5 + ...)`.

The ellipsis is descriptive only.  The implementation is a finite Horner
recurrence indexed by a natural depth.  The input is already the reduced
argument `(u - 1) / (u + 1)`; constructing that quotient, proving its
denominator apart, and selecting a logarithm branch are handled separately.
-/

namespace Purelib.Approximation.Gaussian.Logarithm.Local.Horner.Sensitivity

/-- The difference between two logarithm Horner steps splits into the input difference and the retained-tail difference.
-/
theorem step_inputs_sub (w v :
  Canonical) (index : Nat)
    (wTail vTail : Canonical) :
    Horner.Basic.step w index wTail - Horner.Basic.step v index vTail =
      ComplexLog.scalar (ComplexLog.coefficient index) *
        ((w - v) * wTail + v * (wTail - vTail)) := by
  rw [Horner.Basic.step_eq, Horner.Basic.step_eq]
  apply Data.Gaussian.Basic.ext <;>
    simp only [Basic.sub_re, Basic.sub_im, Basic.add_re, Basic.add_im, Basic.mul_re, Basic.mul_im,
      ComplexLog.scalar, Basic.one_re, Basic.one_im] <;> ring1

/-- The squared-distance input sensitivity scale for logarithm Horner tails is sixteen. -/
def hornerInputScale : Fraction.Rational := 16

/-- Equal-depth logarithm Horner tails at a positive index have squared distance at most sixteen times the squared input
distance on the one-ninth disk. -/
theorem horner_input_close {w v :
  Canonical}
    (wBound : Data.Gaussian.Norm.Basic.normSq w ≤ 1 / 9) (vBound : Data.Gaussian.Norm.Basic.normSq v ≤
      1 / 9) :
    ∀ (depth index : Nat), 1 ≤ index →
      Data.Gaussian.Norm.Basic.normSq (Horner.Basic.horner w index depth - Horner.Basic.horner v index depth) ≤
        hornerInputScale *
          Data.Gaussian.Norm.Basic.normSq (w - v)
  | 0, _, _ => by
      rw [Horner.Basic.horner_zero, Horner.Basic.horner_zero, _root_.sub_self, Data.Gaussian.Norm.Basic.normSq_zero]
      exact Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        (Data.Gaussian.Norm.Basic.normSq_nonneg (w - v))
  | depth + 1, index, positive => by
      rw [Horner.Basic.horner_succ, Horner.Basic.horner_succ,
        step_inputs_sub, Data.Gaussian.Norm.Basic.normSq_mul,
        RationalEmbedding.normSq_scalar]
      let wTail := Horner.Basic.horner w (index + 1) depth
      let vTail := Horner.Basic.horner v (index + 1) depth
      let difference := Data.Gaussian.Norm.Basic.normSq (w - v)
      have firstBound : Data.Gaussian.Norm.Basic.normSq ((w - v) * wTail) ≤ 4 * difference := by
        rw [Data.Gaussian.Norm.Basic.normSq_mul]
        calc
          Data.Gaussian.Norm.Basic.normSq (w - v) * Data.Gaussian.Norm.Basic.normSq wTail ≤ difference
            * 4 :=
            Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
              (Horner.Bounds.horner_bound wBound depth (index + 1) (by omega))
              (Data.Gaussian.Norm.Basic.normSq_nonneg (w - v))
          _ = 4 * difference :=
            Fraction.Field.mul_comm _ _
      have tailDifference : Data.Gaussian.Norm.Basic.normSq (wTail - vTail) ≤
          hornerInputScale * difference :=
        horner_input_close wBound vBound depth (index
          + 1) (by omega)
      have secondBound : Data.Gaussian.Norm.Basic.normSq (v * (wTail - vTail)) ≤
          2 * difference := by
        rw [Data.Gaussian.Norm.Basic.normSq_mul]
        calc
          Data.Gaussian.Norm.Basic.normSq v * Data.Gaussian.Norm.Basic.normSq (wTail - vTail) ≤
              (1 / 9 : Fraction.Rational) * (hornerInputScale
                * difference) :=
            Fraction.Order.Arithmetic.mul_le_mul_direct vBound tailDifference
              (Data.Gaussian.Norm.Basic.normSq_nonneg _) (by decide)
          _ ≤ 2 * difference := by
            rw [hornerInputScale]
            have nonnegative : 0 ≤ difference := Data.Gaussian.Norm.Basic.normSq_nonneg _
            calc
              (1 / 9 : Fraction.Rational) * (16 * difference) =
                  ((1 / 9 : Fraction.Rational) * 16) * difference := by
                rw [Fraction.Field.mul_assoc]
              _ = (16 / 9 : Fraction.Rational) * difference := by
                rw [show (1 / 9 : Fraction.Rational) * 16 = 16 / 9 by decide]
              _ ≤ 2 * difference :=
                Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
                  (by decide) nonnegative
      have sumBound :
          Data.Gaussian.Norm.Basic.normSq ((w - v) * wTail + v * (wTail - vTail)) ≤
            hornerInputScale * difference := by
        calc
          Data.Gaussian.Norm.Basic.normSq ((w - v) * wTail + v * (wTail - vTail)) ≤
              2 * (Data.Gaussian.Norm.Basic.normSq ((w - v) * wTail) +
                Data.Gaussian.Norm.Basic.normSq (v * (wTail - vTail))) :=
                  Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _
          _ ≤ 2 * (4 * difference + 2 * difference) :=
            Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
              (add_le_add firstBound secondBound) (by decide)
          _ ≤ hornerInputScale * difference := by
            rw [hornerInputScale]
            have nonnegative : 0 ≤ difference := Data.Gaussian.Norm.Basic.normSq_nonneg _
            calc
              2 * (4 * difference + 2 * difference) = 12 * difference := by
                ring1
              _ ≤ 16 * difference :=
                Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
                  (by decide) nonnegative
      have multiplied := Fraction.Order.Arithmetic.mul_le_mul_direct
        (Sensitivity.coefficient_sq_le_one positive) sumBound
        (Data.Gaussian.Norm.Basic.normSq_nonneg _) (by decide : (0 : Fraction.Rational) ≤ 1)
      simpa only [Fraction.Field.one_mul] using multiplied

/-- The difference of the squared logarithm arguments factors as their difference times their sum. -/
theorem squaredArgument_sub {z y :
  Canonical} :
    Sample.squaredArgument z - Sample.squaredArgument y = (z - y) * (z + y) := by
  rw [Sample.squaredArgument_eq, Sample.squaredArgument_eq]
  apply Data.Gaussian.Basic.ext <;>
    simp only [Basic.sub_re, Basic.sub_im, Basic.add_re, Basic.add_im, Basic.mul_re, Basic.mul_im] <;> ring1

/-- Squaring inputs in the one-ninth disk does not increase their squared distance. -/
theorem squaredArgument_input_close {z y :
  Canonical}
    (zBound : Data.Gaussian.Norm.Basic.normSq z ≤ 1 / 9) (yBound : Data.Gaussian.Norm.Basic.normSq y ≤
      1 / 9) :
    Data.Gaussian.Norm.Basic.normSq (Sample.squaredArgument z - Sample.squaredArgument y) ≤
      Data.Gaussian.Norm.Basic.normSq (z - y) := by
  rw [squaredArgument_sub,
    Data.Gaussian.Norm.Basic.normSq_mul]
  have sumBound : Data.Gaussian.Norm.Basic.normSq (z + y) ≤ 1 := by
    calc
      Data.Gaussian.Norm.Basic.normSq (z + y) ≤ 2 * (Data.Gaussian.Norm.Basic.normSq z +
        Data.Gaussian.Norm.Basic.normSq y) :=
        Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _
      _ ≤ 2 * ((1 / 9 : Fraction.Rational) + 1 / 9) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (add_le_add zBound yBound) (by decide)
      _ ≤ 1 := by decide
  simpa only [Fraction.Field.mul_one_direct] using
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct sumBound
      (Data.Gaussian.Norm.Basic.normSq_nonneg (z - y))

/-- The squared-distance input sensitivity scale for local logarithm samples is sixty-four. -/
def sampleInputScale : Fraction.Rational := 2 *
  (16 + 16)

/-- The local logarithm sample input sensitivity scale is nonnegative. -/
theorem sampleInputScale_nonneg : 0 ≤
  sampleInputScale :=
  Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
    (add_nonneg (by decide) (by decide))

/-- Equal-depth local logarithm samples have squared distance bounded by the retained sensitivity scale times the
squared input distance on the one-ninth disk. -/
theorem sample_input_close {z y :
  Canonical}
    (zBound : Data.Gaussian.Norm.Basic.normSq z ≤ 1 / 9) (yBound : Data.Gaussian.Norm.Basic.normSq y ≤
      1 / 9)
    (depth : Nat) :
    Data.Gaussian.Norm.Basic.normSq (Sample.sample z depth - Sample.sample y depth) ≤
      sampleInputScale *
        Data.Gaussian.Norm.Basic.normSq (z - y) := by
  rw [Sample.sample_eq, Sample.sample_eq]
  let zTail := Horner.Basic.horner (Sample.squaredArgument z) 1 depth
  let yTail := Horner.Basic.horner (Sample.squaredArgument y) 1 depth
  let difference := Data.Gaussian.Norm.Basic.normSq (z - y)
  have factorDifference :
      Data.Gaussian.Norm.Basic.normSq (Sample.outputFactor z - Sample.outputFactor y) ≤ 4 * difference := by
    rw [Sample.outputFactor_eq, Sample.outputFactor_eq]
    have identity : ComplexLog.scalar 2 * z - ComplexLog.scalar 2 * y = ComplexLog.scalar 2 * (z - y) := by
      apply Data.Gaussian.Basic.ext <;>
        simp only [Basic.sub_re, Basic.sub_im, Basic.mul_re, Basic.mul_im, ComplexLog.scalar] <;> ring1
    rw [identity, Data.Gaussian.Norm.Basic.normSq_mul, RationalEmbedding.normSq_scalar]
    change (2 : Fraction.Rational) ^ 2 * Data.Gaussian.Norm.Basic.normSq (z - y) ≤ 4 * difference
    rw [show (2 : Fraction.Rational) ^ 2 = 4 by decide]
  have zTailBound : Data.Gaussian.Norm.Basic.normSq zTail ≤ 4 :=
    Horner.Bounds.horner_bound (Sample.squaredArgument_bound zBound) depth 1 (by decide)
  have tailDifference : Data.Gaussian.Norm.Basic.normSq (zTail - yTail) ≤
      hornerInputScale * difference :=
    (horner_input_close (Sample.squaredArgument_bound zBound)
      (Sample.squaredArgument_bound yBound) depth 1 (by decide)).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (squaredArgument_input_close zBound yBound) (by
          decide))
  have firstBound :
      Data.Gaussian.Norm.Basic.normSq ((Sample.outputFactor z - Sample.outputFactor y) * zTail) ≤
        16 * difference := by
    rw [Data.Gaussian.Norm.Basic.normSq_mul]
    calc
      Data.Gaussian.Norm.Basic.normSq (Sample.outputFactor z - Sample.outputFactor y) *
        Data.Gaussian.Norm.Basic.normSq zTail ≤
          (4 * difference) * 4 :=
        Fraction.Order.Arithmetic.mul_le_mul_direct factorDifference zTailBound
          (Data.Gaussian.Norm.Basic.normSq_nonneg _) (by
            exact Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
              (Data.Gaussian.Norm.Basic.normSq_nonneg _))
      _ = 16 * difference := by ring1
  have secondBound :
      Data.Gaussian.Norm.Basic.normSq (Sample.outputFactor y * (zTail - yTail)) ≤ 16 * difference := by
    rw [Data.Gaussian.Norm.Basic.normSq_mul]
    have multiplied := Fraction.Order.Arithmetic.mul_le_mul_direct
      (Sample.outputFactor_bound yBound) tailDifference (Data.Gaussian.Norm.Basic.normSq_nonneg _)
      (by decide : (0 : Fraction.Rational) ≤ 1)
    simpa only [hornerInputScale, Fraction.Field.one_mul]
      using multiplied
  have identity : Sample.outputFactor z * zTail - Sample.outputFactor y * yTail =
      (Sample.outputFactor z - Sample.outputFactor y) * zTail +
        Sample.outputFactor y * (zTail - yTail) := by
    apply Data.Gaussian.Basic.ext <;>
      simp only [Basic.sub_re, Basic.sub_im, Basic.add_re, Basic.add_im, Basic.mul_re, Basic.mul_im] <;> ring1
  rw [identity]
  calc
    Data.Gaussian.Norm.Basic.normSq ((Sample.outputFactor z - Sample.outputFactor y) * zTail +
        Sample.outputFactor y * (zTail - yTail)) ≤
      2 * (Data.Gaussian.Norm.Basic.normSq ((Sample.outputFactor z - Sample.outputFactor y) * zTail) +
        Data.Gaussian.Norm.Basic.normSq (Sample.outputFactor y * (zTail - yTail))) :=
          Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _
    _ ≤ 2 * (16 * difference + 16 * difference) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (add_le_add firstBound secondBound) (by decide)
    _ = sampleInputScale *
      Data.Gaussian.Norm.Basic.normSq (z - y) := by
      rw [sampleInputScale]
      ring1

end Purelib.Approximation.Gaussian.Logarithm.Local.Horner.Sensitivity

end
