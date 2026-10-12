module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Approximation.Gaussian.Logarithm.Rational.Sample
import Purelib.Approximation.Rat.Logarithm.Horner.Basic
import Purelib.Approximation.Rat.Logarithm.Horner.Bounds
import Purelib.Approximation.Rat.Logarithm.Horner.Sample
public import Purelib.Approximation.Rat.Logarithm.Horner.Sensitivity
import Purelib.Approximation.Rat.Logarithm.Reduction
import Purelib.Approximation.Rat.Logarithm.Reduction.Sensitivity
import Purelib.Data.Gaussian.RationalEmbedding
import Purelib.Data.Rat.Bounds.Square
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Approximation.Gaussian.Logarithm.Rational

open Purelib.Approximation.Rat.Logarithm

open Purelib.Approximation.Rat.Logarithm.Horner

open Purelib.Approximation.Rat.Logarithm.Reduction

open Purelib.Data.Gaussian

open Purelib.Data.Rat

section
public section

/-!
# Finite logarithm input sensitivity

All estimates compare two displayed rational inputs and two finite Horner
programs.  The overlapping input chart `[1/2,2]` supplies explicit rational
denominator and contraction bounds; there is no continuity axiom or completed
function value.
-/

namespace Purelib.Approximation.Gaussian.Logarithm.Rational.Sensitivity

/-- Equal-depth finite logarithm samples on the interval from one half to two satisfy the retained squared-input
sensitivity bound.

The estimate combines the original output-factor and inner-Horner difference certificates at the same displayed depth.
-/
theorem sample_input_close {x y : Fraction.Rational}
    (xHalf : 1 / 2 ≤ x) (xTwo : x ≤ 2)
    (yHalf : 1 / 2 ≤ y) (yTwo : y ≤ 2) (depth : Nat) :
    Data.Gaussian.Norm.Basic.normSq (Sample.sample x depth - Sample.sample y depth) ≤
      Horner.Sensitivity.sampleInputScale * (x - y) ^ 2 := by
  rw [Sample.sample, Sample.sample, RationalEmbedding.normSq_real_sub, Sample.sampleCoordinate_eq,
    Sample.sampleCoordinate_eq]
  let xTail := Horner.Basic.horner (Reduction.squaredArgument x) 1 depth
  let yTail := Horner.Basic.horner (Reduction.squaredArgument y) 1 depth
  let differenceSq := (x - y) ^ 2
  have xTailBounds := Horner.Bounds.horner_bounds (Reduction.squaredArgument_nonneg x)
    (Reduction.squaredArgument_le_ninth xHalf xTwo) depth 1 (by decide)
  have xTailSq : xTail ^ 2 ≤ 4 := by
    have squared := Fraction.Order.Arithmetic.pow_le_pow_direct
      ((by decide : (0 : Fraction.Rational) ≤ 1).trans xTailBounds.1)
      xTailBounds.2 2
    simpa only [xTail] using squared.trans_eq (by decide)
  have factorDifference :
      (Sample.outputFactor x - Sample.outputFactor y) ^ 2 ≤ 4 * differenceSq :=
    Horner.Sensitivity.outputFactor_sub_sq_le xHalf yHalf
  have tailDifference : (xTail - yTail) ^ 2 ≤
      Horner.Sensitivity.hornerInputScale * differenceSq := by
    exact (Horner.Sensitivity.horner_input_close (Reduction.squaredArgument_nonneg x)
      (Reduction.squaredArgument_le_ninth xHalf xTwo) (Reduction.squaredArgument_nonneg y)
      (Reduction.squaredArgument_le_ninth yHalf yTwo) depth 1 (by decide)).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Reduction.Sensitivity.squaredArgument_sub_sq_le xHalf xTwo yHalf yTwo) (by decide))
  have firstBound : ((Sample.outputFactor x - Sample.outputFactor y) * xTail) ^ 2 ≤
      16 * differenceSq := by
    rw [show ((Sample.outputFactor x - Sample.outputFactor y) * xTail) ^ 2 =
      (Sample.outputFactor x - Sample.outputFactor y) ^ 2 * xTail ^ 2 by ring1]
    calc
      (Sample.outputFactor x - Sample.outputFactor y) ^ 2 * xTail ^ 2 ≤
          (4 * differenceSq) * 4 :=
        Fraction.Order.Arithmetic.mul_le_mul_direct factorDifference xTailSq
          (Fraction.Order.Arithmetic.sq_nonneg_direct xTail)
          (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
            (Fraction.Order.Arithmetic.sq_nonneg_direct (x - y)))
      _ = 16 * differenceSq := by ring1
  have secondBound : (Sample.outputFactor y * (xTail - yTail)) ^ 2 ≤
      16 * differenceSq := by
    rw [show (Sample.outputFactor y * (xTail - yTail)) ^ 2 =
      Sample.outputFactor y ^ 2 * (xTail - yTail) ^ 2 by ring1]
    have multiplied := Fraction.Order.Arithmetic.mul_le_mul_direct
      (Sample.outputFactor_sq_le_one yHalf yTwo) tailDifference
      (Fraction.Order.Arithmetic.sq_nonneg_direct (xTail - yTail))
      (by decide : (0 : Fraction.Rational) ≤ 1)
    simpa only [Fraction.Field.one_mul, Horner.Sensitivity.hornerInputScale] using multiplied
  have identity : Sample.outputFactor x * xTail - Sample.outputFactor y * yTail =
      (Sample.outputFactor x - Sample.outputFactor y) * xTail +
        Sample.outputFactor y * (xTail - yTail) := by ring1
  rw [identity]
  calc
    ((Sample.outputFactor x - Sample.outputFactor y) * xTail +
        Sample.outputFactor y * (xTail - yTail)) ^ 2 ≤
      2 * (((Sample.outputFactor x - Sample.outputFactor y) * xTail) ^ 2 +
        (Sample.outputFactor y * (xTail - yTail)) ^ 2) := Bounds.Square.sq_add_le_two _ _
    _ ≤ 2 * (16 * differenceSq + 16 * differenceSq) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (add_le_add firstBound secondBound) (by decide)
    _ = Horner.Sensitivity.sampleInputScale * (x - y) ^ 2 := by
      dsimp only [Horner.Sensitivity.sampleInputScale, differenceSq]
      ring1

end Purelib.Approximation.Gaussian.Logarithm.Rational.Sensitivity

end
