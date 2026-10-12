module
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Sequence.Name
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Sequence
public import Purelib.Approximation.Gaussian.Sequence.Arithmetic.Multiplication.Bridge
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

namespace Purelib.Approximation.Gaussian.Sequence.Arithmetic.Square

open Purelib
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Sequence
open Purelib.Approximation.Gaussian.Sequence.Arithmetic.Multiplication
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

/-! ## Canonical finite squaring and its congruence -/

/-- The positive error amplification factor four times one plus the source center bound. -/
@[expose] def squareApproximationFactor (source : ApproximationData) : Fraction.Rational :=
  4 * (1 + source.centerBound)

/-- The finite squaring error amplification factor is strictly positive. -/
theorem squareApproximationFactor_pos (source : ApproximationData) :
    0 < Purelib.Approximation.Gaussian.Sequence.Arithmetic.Square.squareApproximationFactor source := by
  unfold Arithmetic.Square.squareApproximationFactor
  exact Fraction.Order.Arithmetic.mul_pos_direct (by decide)
    (add_pos_of_pos_of_nonneg (by decide) source.centerBound_nonneg)

/-- Pointwise squaring of displayed finite samples, with an explicit finite error transport and refinement request. -/
@[expose] def squareApproximation (source : ApproximationData) :
  ApproximationData where
  sample index := source.sample index * source.sample index
  radiusSq index := Purelib.Approximation.Gaussian.Sequence.Arithmetic.Square.squareApproximationFactor source *
    source.radiusSq index
  radiusSq_nonneg index :=
    Fraction.Order.Arithmetic.mul_nonneg_direct
      (Approximation.Gaussian.Sequence.Arithmetic.Square.squareApproximationFactor_pos source).le
      (source.radiusSq_nonneg index)
  later_close := by
    intro earlier later order
    have movement := source.later_close order
    have firstTerm :
        Data.Gaussian.Norm.Basic.normSq
            ((source.sample later - source.sample earlier) *
              source.sample later) ≤
          source.radiusSq earlier * source.centerBound := by
      rw [Data.Gaussian.Norm.Basic.normSq_mul]
      exact Fraction.Order.Arithmetic.mul_le_mul_direct movement
        (source.sample_bounded later) (Data.Gaussian.Norm.Basic.normSq_nonneg _)
        (source.radiusSq_nonneg earlier)
    have secondTerm :
        Data.Gaussian.Norm.Basic.normSq
            (source.sample earlier *
              (source.sample later - source.sample earlier)) ≤
          source.centerBound * source.radiusSq earlier := by
      rw [Data.Gaussian.Norm.Basic.normSq_mul]
      exact Fraction.Order.Arithmetic.mul_le_mul_direct
        (source.sample_bounded earlier) movement (Data.Gaussian.Norm.Basic.normSq_nonneg _)
        source.centerBound_nonneg
    have identity :
        source.sample later * source.sample later -
            source.sample earlier * source.sample earlier =
          (source.sample later - source.sample earlier) *
              source.sample later +
            source.sample earlier *
              (source.sample later - source.sample earlier) := by
      apply Data.Gaussian.Basic.ext <;>
        simp only [Purelib.Data.Gaussian.Basic.sub_re, Purelib.Data.Gaussian.Basic.sub_im,
          Purelib.Data.Gaussian.Basic.add_re, Purelib.Data.Gaussian.Basic.add_im, Purelib.Data.Gaussian.Basic.mul_re,
          Purelib.Data.Gaussian.Basic.mul_im] <;> ring1
    rw [identity]
    calc
      Data.Gaussian.Norm.Basic.normSq
          ((source.sample later - source.sample earlier) *
              source.sample later +
            source.sample earlier *
              (source.sample later - source.sample earlier)) ≤
        2 *
          (Data.Gaussian.Norm.Basic.normSq
              ((source.sample later - source.sample earlier) *
                source.sample later) +
            Data.Gaussian.Norm.Basic.normSq
              (source.sample earlier *
                (source.sample later - source.sample earlier))) :=
        Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _
      _ ≤ 2 *
          (source.radiusSq earlier * source.centerBound +
            source.centerBound * source.radiusSq earlier) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (add_le_add firstTerm secondTerm) (by decide)
      _ = 4 * source.centerBound * source.radiusSq earlier := by ring1
      _ ≤ Purelib.Approximation.Gaussian.Sequence.Arithmetic.Square.squareApproximationFactor source * source.radiusSq
        earlier := by
        apply Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        · unfold Purelib.Approximation.Gaussian.Sequence.Arithmetic.Square.squareApproximationFactor
          have oneNonnegative : (0 : Fraction.Rational) ≤ 1 := by decide
          have boundOrder : source.centerBound ≤ 1 + source.centerBound :=
            le_add_of_nonneg_left oneNonnegative
          exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            boundOrder (by decide)
        · exact source.radiusSq_nonneg earlier
  refineIndex current target positive :=
    source.refineIndex current (target /
      Purelib.Approximation.Gaussian.Sequence.Arithmetic.Square.squareApproximationFactor source)
      (Fraction.Order.Field.div_pos_direct positive
        (Approximation.Gaussian.Sequence.Arithmetic.Square.squareApproximationFactor_pos source))
  refineIndex_ge current target positive :=
    source.refineIndex_ge current
      (target / Purelib.Approximation.Gaussian.Sequence.Arithmetic.Square.squareApproximationFactor source)
      (Fraction.Order.Field.div_pos_direct positive
        (Approximation.Gaussian.Sequence.Arithmetic.Square.squareApproximationFactor_pos source))
  refineIndex_accurate := by
    intro current target positive
    let inputTarget := target / Purelib.Approximation.Gaussian.Sequence.Arithmetic.Square.squareApproximationFactor
      source
    have inputPositive : 0 < inputTarget :=
      Fraction.Order.Field.div_pos_direct positive
        (Approximation.Gaussian.Sequence.Arithmetic.Square.squareApproximationFactor_pos source)
    have small := source.refineIndex_accurate current inputTarget inputPositive
    calc
      Purelib.Approximation.Gaussian.Sequence.Arithmetic.Square.squareApproximationFactor source *
          source.radiusSq (source.refineIndex current inputTarget inputPositive) <
        Purelib.Approximation.Gaussian.Sequence.Arithmetic.Square.squareApproximationFactor source * inputTarget :=
        Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
          (Approximation.Gaussian.Sequence.Arithmetic.Square.squareApproximationFactor_pos source) small
      _ = target := by
        rw [Fraction.Field.mul_comm]
        exact Fraction.Field.div_mul_cancel_of_ne target
          (Purelib.Approximation.Gaussian.Sequence.Arithmetic.Square.squareApproximationFactor source)
          (Approximation.Gaussian.Sequence.Arithmetic.Square.squareApproximationFactor_pos source).ne'
  centerBound := source.centerBound * source.centerBound
  centerBound_nonneg :=
    Fraction.Order.Arithmetic.mul_nonneg_direct source.centerBound_nonneg
      source.centerBound_nonneg
  sample_bounded := by
    intro index
    rw [Data.Gaussian.Norm.Basic.normSq_mul]
    exact Fraction.Order.Arithmetic.mul_le_mul_direct
      (source.sample_bounded index) (source.sample_bounded index)
      (Data.Gaussian.Norm.Basic.normSq_nonneg _) source.centerBound_nonneg

/-- Sampling the squared approximation squares the original sample at that same index. -/
@[simp] theorem squareApproximation_sample (source : ApproximationData)
    (index : Nat) :
    (Approximation.Gaussian.Sequence.Arithmetic.Square.squareApproximation source).sample index =
      source.sample index * source.sample index :=
  rfl

/-- Pointwise finite squaring respects operational equivalence of its source approximations. -/
@[expose] def squareApproximation_respects {left right : ApproximationData}
    (equivalent : Gaussian.Equivalence.Equivalent left right) :
    Gaussian.Equivalence.Equivalent (Approximation.Gaussian.Sequence.Arithmetic.Square.squareApproximation left)
      (Approximation.Gaussian.Sequence.Arithmetic.Square.squareApproximation right) where
  compare := by
    intro leftStart rightStart target positive
    let inputTarget := Bridge.approximationMulBridgeTarget left right target
    have inputPositive : 0 < inputTarget :=
      Bridge.approximationMulBridgeTarget_pos left right positive
    let comparison := equivalent.compare leftStart rightStart
      inputTarget inputPositive
    exact
      { leftIndex := comparison.leftIndex
        rightIndex := comparison.rightIndex
        left_ge := comparison.left_ge
        right_ge := comparison.right_ge
        close := by
          intro leftLater rightLater leftOrder rightOrder
          have inputClose := comparison.close leftOrder rightOrder
          have firstTerm :
              Data.Gaussian.Norm.Basic.normSq
                  ((left.sample leftLater - right.sample rightLater) *
                    left.sample leftLater) ≤
                Data.Gaussian.Norm.Basic.normSq (left.sample leftLater - right.sample rightLater) *
                  left.centerBound := by
            rw [Data.Gaussian.Norm.Basic.normSq_mul]
            exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
              (left.sample_bounded leftLater) (Data.Gaussian.Norm.Basic.normSq_nonneg _)
          have secondTerm :
              Data.Gaussian.Norm.Basic.normSq
                  (right.sample rightLater *
                    (left.sample leftLater - right.sample rightLater)) ≤
                right.centerBound *
                  Data.Gaussian.Norm.Basic.normSq (left.sample leftLater - right.sample rightLater) := by
            rw [Data.Gaussian.Norm.Basic.normSq_mul]
            exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
              (right.sample_bounded rightLater) (Data.Gaussian.Norm.Basic.normSq_nonneg _)
          have identity :
              left.sample leftLater * left.sample leftLater -
                  right.sample rightLater * right.sample rightLater =
                (left.sample leftLater - right.sample rightLater) *
                    left.sample leftLater +
                  right.sample rightLater *
                    (left.sample leftLater - right.sample rightLater) := by
            apply Data.Gaussian.Basic.ext <;>
              simp only [Purelib.Data.Gaussian.Basic.sub_re, Purelib.Data.Gaussian.Basic.sub_im,
                Purelib.Data.Gaussian.Basic.add_re, Purelib.Data.Gaussian.Basic.add_im,
                Purelib.Data.Gaussian.Basic.mul_re, Purelib.Data.Gaussian.Basic.mul_im] <;>
                ring1
          change Data.Gaussian.Norm.Basic.normSq
              (left.sample leftLater * left.sample leftLater -
                right.sample rightLater * right.sample rightLater) < target
          rw [identity]
          calc
            Data.Gaussian.Norm.Basic.normSq
                ((left.sample leftLater - right.sample rightLater) *
                    left.sample leftLater +
                  right.sample rightLater *
                    (left.sample leftLater - right.sample rightLater)) ≤
              2 *
                (Data.Gaussian.Norm.Basic.normSq
                    ((left.sample leftLater - right.sample rightLater) *
                      left.sample leftLater) +
                  Data.Gaussian.Norm.Basic.normSq
                    (right.sample rightLater *
                      (left.sample leftLater - right.sample rightLater))) :=
              Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _
            _ ≤ 2 *
                (Data.Gaussian.Norm.Basic.normSq (left.sample leftLater - right.sample rightLater) *
                    left.centerBound +
                  right.centerBound *
                    Data.Gaussian.Norm.Basic.normSq
                      (left.sample leftLater - right.sample rightLater)) :=
              Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
                (add_le_add firstTerm secondTerm) (by decide)
            _ = Data.Gaussian.Norm.Basic.normSq (left.sample leftLater - right.sample rightLater) *
                (2 * (left.centerBound + right.centerBound)) := by ring1
            _ ≤ Data.Gaussian.Norm.Basic.normSq (left.sample leftLater - right.sample rightLater) *

                  Multiplication.Bridge.approximationMulBridgeCoefficient
                  left right := by
              apply Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
              · unfold
                  Multiplication.Bridge.approximationMulBridgeCoefficient
                have nonnegative :
                    0 ≤ 8 + 2 * (left.centerBound + right.centerBound) :=
                  add_nonneg (by decide)
                    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
                      (add_nonneg left.centerBound_nonneg
                        right.centerBound_nonneg))
                apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
                have difference :
                    (8 + 4 * (left.centerBound + right.centerBound)) -
                        2 * (left.centerBound + right.centerBound) =
                      8 + 2 * (left.centerBound + right.centerBound) := by ring1
                rw [difference]
                exact nonnegative
              · exact Data.Gaussian.Norm.Basic.normSq_nonneg _
            _ < inputTarget *

                  Multiplication.Bridge.approximationMulBridgeCoefficient
                  left right :=
              Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct
                inputClose
                (Bridge.approximationMulBridgeCoefficient_pos left right)
            _ < target :=
              Bridge.approximationMulBridgeTarget_budget_lt left right positive }

end

end Purelib.Approximation.Gaussian.Sequence.Arithmetic.Square
