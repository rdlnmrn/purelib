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

open Purelib.Data.Rat.Fraction.Order

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
    Basic.step w index wTail - Basic.step v index vTail =
      ComplexLog.scalar (ComplexLog.coefficient index) *
        ((w - v) * wTail + v * (wTail - vTail)) := by
  rw [Basic.step_eq, Basic.step_eq]
  apply Basic.ext <;>
    simp only [Basic.sub_re, Basic.sub_im, Basic.add_re, Basic.add_im, Basic.mul_re, Basic.mul_im,
      ComplexLog.scalar, Basic.one_re, Basic.one_im] <;> ring1

/-- The squared-distance input sensitivity scale for logarithm Horner tails is sixteen. -/
def hornerInputScale : Fraction.Rational := 16

/-- Equal-depth logarithm Horner tails at a positive index have squared distance at most sixteen times the squared input
distance on the one-ninth disk. -/
theorem horner_input_close {w v :
  Canonical}
    (wBound : Norm.Basic.normSq w ≤ 1 / 9) (vBound : Norm.Basic.normSq v ≤
      1 / 9) :
    ∀ (depth index : Nat), 1 ≤ index →
      Norm.Basic.normSq (Basic.horner w index depth - Basic.horner v index depth) ≤
        hornerInputScale *
          Norm.Basic.normSq (w - v)
  | 0, _, _ => by
      rw [Basic.horner_zero, Basic.horner_zero, _root_.sub_self, Norm.Basic.normSq_zero]
      exact Arithmetic.mul_nonneg_direct (by decide)
        (Norm.Basic.normSq_nonneg (w - v))
  | depth + 1, index, positive => by
      rw [Basic.horner_succ, Basic.horner_succ,
        step_inputs_sub, Norm.Basic.normSq_mul,
        RationalEmbedding.normSq_scalar]
      let wTail := Basic.horner w (index + 1) depth
      let vTail := Basic.horner v (index + 1) depth
      let difference := Norm.Basic.normSq (w - v)
      have firstBound : Norm.Basic.normSq ((w - v) * wTail) ≤ 4 * difference := by
        rw [Norm.Basic.normSq_mul]
        calc
          Norm.Basic.normSq (w - v) * Norm.Basic.normSq wTail ≤ difference
            * 4 :=
            Arithmetic.mul_le_mul_of_nonneg_left_direct
              (Bounds.horner_bound wBound depth (index + 1) (by omega))
              (Norm.Basic.normSq_nonneg (w - v))
          _ = 4 * difference :=
            Fraction.Field.mul_comm _ _
      have tailDifference : Norm.Basic.normSq (wTail - vTail) ≤
          hornerInputScale * difference :=
        horner_input_close wBound vBound depth (index
          + 1) (by omega)
      have secondBound : Norm.Basic.normSq (v * (wTail - vTail)) ≤
          2 * difference := by
        rw [Norm.Basic.normSq_mul]
        calc
          Norm.Basic.normSq v * Norm.Basic.normSq (wTail - vTail) ≤
              (1 / 9 : Fraction.Rational) * (hornerInputScale
                * difference) :=
            Arithmetic.mul_le_mul_direct vBound tailDifference
              (Norm.Basic.normSq_nonneg _) (by decide)
          _ ≤ 2 * difference := by
            rw [hornerInputScale]
            have nonnegative : 0 ≤ difference := Norm.Basic.normSq_nonneg _
            calc
              (1 / 9 : Fraction.Rational) * (16 * difference) =
                  ((1 / 9 : Fraction.Rational) * 16) * difference := by
                rw [Fraction.Field.mul_assoc]
              _ = (16 / 9 : Fraction.Rational) * difference := by
                rw [show (1 / 9 : Fraction.Rational) * 16 = 16 / 9 by decide]
              _ ≤ 2 * difference :=
                Arithmetic.mul_le_mul_of_nonneg_right_direct
                  (by decide) nonnegative
      have sumBound :
          Norm.Basic.normSq ((w - v) * wTail + v * (wTail - vTail)) ≤
            hornerInputScale * difference := by
        calc
          Norm.Basic.normSq ((w - v) * wTail + v * (wTail - vTail)) ≤
              2 * (Norm.Basic.normSq ((w - v) * wTail) +
                Norm.Basic.normSq (v * (wTail - vTail))) :=
                  Norm.Bounds.normSq_add_le_two _ _
          _ ≤ 2 * (4 * difference + 2 * difference) :=
            Arithmetic.mul_le_mul_of_nonneg_left_direct
              (add_le_add firstBound secondBound) (by decide)
          _ ≤ hornerInputScale * difference := by
            rw [hornerInputScale]
            have nonnegative : 0 ≤ difference := Norm.Basic.normSq_nonneg _
            calc
              2 * (4 * difference + 2 * difference) = 12 * difference := by
                ring1
              _ ≤ 16 * difference :=
                Arithmetic.mul_le_mul_of_nonneg_right_direct
                  (by decide) nonnegative
      have multiplied := Arithmetic.mul_le_mul_direct
        (Sensitivity.coefficient_sq_le_one positive) sumBound
        (Norm.Basic.normSq_nonneg _) (by decide : (0 : Fraction.Rational) ≤ 1)
      simpa only [Fraction.Field.one_mul] using multiplied

/-- The difference of the squared logarithm arguments factors as their difference times their sum. -/
theorem squaredArgument_sub {z y :
  Canonical} :
    Sample.squaredArgument z - Sample.squaredArgument y = (z - y) * (z + y) := by
  rw [Sample.squaredArgument_eq, Sample.squaredArgument_eq]
  apply Basic.ext <;>
    simp only [Basic.sub_re, Basic.sub_im, Basic.add_re, Basic.add_im, Basic.mul_re, Basic.mul_im] <;> ring1

/-- Squaring inputs in the one-ninth disk does not increase their squared distance. -/
theorem squaredArgument_input_close {z y :
  Canonical}
    (zBound : Norm.Basic.normSq z ≤ 1 / 9) (yBound : Norm.Basic.normSq y ≤
      1 / 9) :
    Norm.Basic.normSq (Sample.squaredArgument z - Sample.squaredArgument y) ≤
      Norm.Basic.normSq (z - y) := by
  rw [squaredArgument_sub,
    Norm.Basic.normSq_mul]
  have sumBound : Norm.Basic.normSq (z + y) ≤ 1 := by
    calc
      Norm.Basic.normSq (z + y) ≤ 2 * (Norm.Basic.normSq z +
        Norm.Basic.normSq y) :=
        Norm.Bounds.normSq_add_le_two _ _
      _ ≤ 2 * ((1 / 9 : Fraction.Rational) + 1 / 9) :=
        Arithmetic.mul_le_mul_of_nonneg_left_direct
          (add_le_add zBound yBound) (by decide)
      _ ≤ 1 := by decide
  simpa only [Fraction.Field.mul_one_direct] using
    Arithmetic.mul_le_mul_of_nonneg_left_direct sumBound
      (Norm.Basic.normSq_nonneg (z - y))

/-- The squared-distance input sensitivity scale for local logarithm samples is sixty-four. -/
def sampleInputScale : Fraction.Rational := 2 *
  (16 + 16)

/-- The local logarithm sample input sensitivity scale is nonnegative. -/
theorem sampleInputScale_nonneg : 0 ≤
  sampleInputScale :=
  Arithmetic.mul_nonneg_direct (by decide)
    (add_nonneg (by decide) (by decide))

/-- Equal-depth local logarithm samples have squared distance bounded by the retained sensitivity scale times the
squared input distance on the one-ninth disk. -/
theorem sample_input_close {z y :
  Canonical}
    (zBound : Norm.Basic.normSq z ≤ 1 / 9) (yBound : Norm.Basic.normSq y ≤
      1 / 9)
    (depth : Nat) :
    Norm.Basic.normSq (Sample.sample z depth - Sample.sample y depth) ≤
      sampleInputScale *
        Norm.Basic.normSq (z - y) := by
  rw [Sample.sample_eq, Sample.sample_eq]
  let zTail := Basic.horner (Sample.squaredArgument z) 1 depth
  let yTail := Basic.horner (Sample.squaredArgument y) 1 depth
  let difference := Norm.Basic.normSq (z - y)
  have factorDifference :
      Norm.Basic.normSq (Sample.outputFactor z - Sample.outputFactor y) ≤ 4 * difference := by
    rw [Sample.outputFactor_eq, Sample.outputFactor_eq]
    have identity : ComplexLog.scalar 2 * z - ComplexLog.scalar 2 * y = ComplexLog.scalar 2 * (z - y) := by
      apply Basic.ext <;>
        simp only [Basic.sub_re, Basic.sub_im, Basic.mul_re, Basic.mul_im, ComplexLog.scalar] <;> ring1
    rw [identity, Norm.Basic.normSq_mul, RationalEmbedding.normSq_scalar]
    change (2 : Fraction.Rational) ^ 2 * Norm.Basic.normSq (z - y) ≤ 4 * difference
    rw [show (2 : Fraction.Rational) ^ 2 = 4 by decide]
  have zTailBound : Norm.Basic.normSq zTail ≤ 4 :=
    Bounds.horner_bound (Sample.squaredArgument_bound zBound) depth 1 (by decide)
  have tailDifference : Norm.Basic.normSq (zTail - yTail) ≤
      hornerInputScale * difference :=
    (horner_input_close (Sample.squaredArgument_bound zBound)
      (Sample.squaredArgument_bound yBound) depth 1 (by decide)).trans
      (Arithmetic.mul_le_mul_of_nonneg_left_direct
        (squaredArgument_input_close zBound yBound) (by
          decide))
  have firstBound :
      Norm.Basic.normSq ((Sample.outputFactor z - Sample.outputFactor y) * zTail) ≤
        16 * difference := by
    rw [Norm.Basic.normSq_mul]
    calc
      Norm.Basic.normSq (Sample.outputFactor z - Sample.outputFactor y) *
        Norm.Basic.normSq zTail ≤
          (4 * difference) * 4 :=
        Arithmetic.mul_le_mul_direct factorDifference zTailBound
          (Norm.Basic.normSq_nonneg _) (by
            exact Arithmetic.mul_nonneg_direct (by decide)
              (Norm.Basic.normSq_nonneg _))
      _ = 16 * difference := by ring1
  have secondBound :
      Norm.Basic.normSq (Sample.outputFactor y * (zTail - yTail)) ≤ 16 * difference := by
    rw [Norm.Basic.normSq_mul]
    have multiplied := Arithmetic.mul_le_mul_direct
      (Sample.outputFactor_bound yBound) tailDifference (Norm.Basic.normSq_nonneg _)
      (by decide : (0 : Fraction.Rational) ≤ 1)
    simpa only [hornerInputScale, Fraction.Field.one_mul]
      using multiplied
  have identity : Sample.outputFactor z * zTail - Sample.outputFactor y * yTail =
      (Sample.outputFactor z - Sample.outputFactor y) * zTail +
        Sample.outputFactor y * (zTail - yTail) := by
    apply Basic.ext <;>
      simp only [Basic.sub_re, Basic.sub_im, Basic.add_re, Basic.add_im, Basic.mul_re, Basic.mul_im] <;> ring1
  rw [identity]
  calc
    Norm.Basic.normSq ((Sample.outputFactor z - Sample.outputFactor y) * zTail +
        Sample.outputFactor y * (zTail - yTail)) ≤
      2 * (Norm.Basic.normSq ((Sample.outputFactor z - Sample.outputFactor y) * zTail) +
        Norm.Basic.normSq (Sample.outputFactor y * (zTail - yTail))) :=
          Norm.Bounds.normSq_add_le_two _ _
    _ ≤ 2 * (16 * difference + 16 * difference) :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct
        (add_le_add firstBound secondBound) (by decide)
    _ = sampleInputScale *
      Norm.Basic.normSq (z - y) := by
      rw [sampleInputScale]
      ring1

end Purelib.Approximation.Gaussian.Logarithm.Local.Horner.Sensitivity

end
