module
public import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Data.Gaussian.Norm

namespace Purelib.Approximation.Gaussian.Sequence.Arithmetic.ContractiveScale

open Purelib
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Sequence
open Purelib.Data.Rat

public section

/-!
# Finite coherence of progressive transcendental outputs

The local exponential and logarithm algorithms first build limit-free
`Approximation` sidechannels.  Their CCL processes are therefore coherent by
construction.  This module propagates that certificate through global dyadic
range reduction, repeated squaring, and the finite correction arithmetic.

These are statements about every finite rational process branch.  They do not
assert that a completed exponential or logarithm value has been selected.
-/

open Purelib.Approximation

/-- Multiplication by an explicitly contractive Gaussian rational, applied directly to every sample of a finite
approximation. -/
@[expose] def contractiveScaleApproximation (factor : Data.Gaussian.Basic.Canonical)
    (contractive : Basic.normSq factor ≤ 1) (source :
      ApproximationData) :
    ApproximationData where
  sample index := factor * source.sample index
  radiusSq := source.radiusSq
  radiusSq_nonneg := source.radiusSq_nonneg
  later_close := by
    intro earlier later order
    have identity :
        factor * source.sample later - factor * source.sample earlier =
          factor * (source.sample later - source.sample earlier) := by
      apply Data.Gaussian.Basic.ext <;>
        simp only [Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im,
          Data.Gaussian.Basic.mul_re, Data.Gaussian.Basic.mul_im] <;> ring1
    rw [identity, Basic.normSq_mul]
    calc
      Basic.normSq factor * Basic.normSq (source.sample later -
        source.sample earlier) ≤
          1 * Basic.normSq (source.sample later - source.sample earlier) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          contractive (Basic.normSq_nonneg _)
      _ ≤ 1 * source.radiusSq earlier :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (source.later_close order) (by decide)
      _ = source.radiusSq earlier :=
        Fraction.Field.one_mul _
  refineIndex := source.refineIndex
  refineIndex_ge := source.refineIndex_ge
  refineIndex_accurate := source.refineIndex_accurate
  centerBound := source.centerBound
  centerBound_nonneg := source.centerBound_nonneg
  sample_bounded := by
    intro index
    rw [Basic.normSq_mul]
    calc
      Basic.normSq factor * Basic.normSq (source.sample index) ≤
          1 * Basic.normSq (source.sample index) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          contractive (Basic.normSq_nonneg _)
      _ ≤ 1 * source.centerBound :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (source.sample_bounded index) (by decide)
      _ = source.centerBound := Fraction.Field.one_mul _

/-- Sampling a contractively scaled approximation multiplies the original sample by the retained Gaussian factor. -/
@[simp] theorem contractiveScaleApproximation_sample
    (factor : Data.Gaussian.Basic.Canonical) (contractive : Basic.normSq factor ≤ 1)
    (source : ApproximationData) (index : Nat) :
    (contractiveScaleApproximation factor contractive
      source).sample index =
      factor * source.sample index :=
  rfl

/-- Contractive pointwise scaling preserves finite operational equality. -/
@[expose] def contractiveScaleApproximation_respects (factor : Data.Gaussian.Basic.Canonical)
    (contractive : Basic.normSq factor ≤ 1) {left right :
      ApproximationData}
    (equivalent : Equivalent left right) :
    Equivalent
      (contractiveScaleApproximation factor contractive
        left)
      (contractiveScaleApproximation factor contractive
        right) where
  compare := by
    intro leftStart rightStart target positive
    let comparison := equivalent.compare leftStart rightStart target positive
    exact
      { leftIndex := comparison.leftIndex
        rightIndex := comparison.rightIndex
        left_ge := comparison.left_ge
        right_ge := comparison.right_ge
        close := by
          intro leftLater rightLater leftOrder rightOrder
          have sourceClose := comparison.close leftOrder rightOrder
          have identity :
              factor * left.sample leftLater - factor * right.sample rightLater =
                factor *
                  (left.sample leftLater - right.sample rightLater) := by
            apply Data.Gaussian.Basic.ext <;>
              simp only [Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im,
                Data.Gaussian.Basic.mul_re, Data.Gaussian.Basic.mul_im] <;> ring1
          rw [contractiveScaleApproximation_sample,
            contractiveScaleApproximation_sample, identity,
              Basic.normSq_mul]
          exact
            (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
              contractive (Basic.normSq_nonneg _)).trans_lt
                (by
                    simpa only [Fraction.Field.one_mul]
                      using sourceClose) }

end

end Purelib.Approximation.Gaussian.Sequence.Arithmetic.ContractiveScale
