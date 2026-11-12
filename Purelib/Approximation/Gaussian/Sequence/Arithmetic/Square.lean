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

open Purelib.Data.Gaussian.Norm
open Purelib.Data.Rat.Fraction.Order

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
    0 < squareApproximationFactor source := by
  unfold squareApproximationFactor
  exact Arithmetic.mul_pos_direct (by decide)
    (add_pos_of_pos_of_nonneg (by decide) source.centerBound_nonneg)

/-- Pointwise squaring of displayed finite samples, with an explicit finite error transport and refinement request. -/
@[expose] def squareApproximation (source : ApproximationData) :
  ApproximationData where
  sample index := source.sample index * source.sample index
  radiusSq index := squareApproximationFactor source *
    source.radiusSq index
  radiusSq_nonneg index :=
    Arithmetic.mul_nonneg_direct
      (squareApproximationFactor_pos source).le
      (source.radiusSq_nonneg index)
  later_close := by
    intro earlier later order
    have movement := source.later_close order
    have firstTerm :
        Basic.normSq
            ((source.sample later - source.sample earlier) *
              source.sample later) ≤
          source.radiusSq earlier * source.centerBound := by
      rw [Basic.normSq_mul]
      exact Arithmetic.mul_le_mul_direct movement
        (source.sample_bounded later) (Basic.normSq_nonneg _)
        (source.radiusSq_nonneg earlier)
    have secondTerm :
        Basic.normSq
            (source.sample earlier *
              (source.sample later - source.sample earlier)) ≤
          source.centerBound * source.radiusSq earlier := by
      rw [Basic.normSq_mul]
      exact Arithmetic.mul_le_mul_direct
        (source.sample_bounded earlier) movement (Basic.normSq_nonneg _)
        source.centerBound_nonneg
    have identity :
        source.sample later * source.sample later -
            source.sample earlier * source.sample earlier =
          (source.sample later - source.sample earlier) *
              source.sample later +
            source.sample earlier *
              (source.sample later - source.sample earlier) := by
      apply Data.Gaussian.Basic.ext <;>
        simp only [Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im,
          Data.Gaussian.Basic.add_re, Data.Gaussian.Basic.add_im, Data.Gaussian.Basic.mul_re,
          Data.Gaussian.Basic.mul_im] <;> ring1
    rw [identity]
    calc
      Basic.normSq
          ((source.sample later - source.sample earlier) *
              source.sample later +
            source.sample earlier *
              (source.sample later - source.sample earlier)) ≤
        2 *
          (Basic.normSq
              ((source.sample later - source.sample earlier) *
                source.sample later) +
            Basic.normSq
              (source.sample earlier *
                (source.sample later - source.sample earlier))) :=
        Bounds.normSq_add_le_two _ _
      _ ≤ 2 *
          (source.radiusSq earlier * source.centerBound +
            source.centerBound * source.radiusSq earlier) :=
        Arithmetic.mul_le_mul_of_nonneg_left_direct
          (add_le_add firstTerm secondTerm) (by decide)
      _ = 4 * source.centerBound * source.radiusSq earlier := by ring1
      _ ≤ squareApproximationFactor source * source.radiusSq
        earlier := by
        apply Arithmetic.mul_le_mul_of_nonneg_right_direct
        · unfold squareApproximationFactor
          have oneNonnegative : (0 : Fraction.Rational) ≤ 1 := by decide
          have boundOrder : source.centerBound ≤ 1 + source.centerBound :=
            le_add_of_nonneg_left oneNonnegative
          exact Arithmetic.mul_le_mul_of_nonneg_left_direct
            boundOrder (by decide)
        · exact source.radiusSq_nonneg earlier
  refineIndex current target positive :=
    source.refineIndex current (target /
      squareApproximationFactor source)
      (Field.div_pos_direct positive
        (squareApproximationFactor_pos source))
  refineIndex_ge current target positive :=
    source.refineIndex_ge current
      (target / squareApproximationFactor source)
      (Field.div_pos_direct positive
        (squareApproximationFactor_pos source))
  refineIndex_accurate := by
    intro current target positive
    let inputTarget := target / squareApproximationFactor
      source
    have inputPositive : 0 < inputTarget :=
      Field.div_pos_direct positive
        (squareApproximationFactor_pos source)
    have small := source.refineIndex_accurate current inputTarget inputPositive
    calc
      squareApproximationFactor source *
          source.radiusSq (source.refineIndex current inputTarget inputPositive) <
        squareApproximationFactor source * inputTarget :=
        Arithmetic.mul_lt_mul_of_pos_left_direct
          (squareApproximationFactor_pos source) small
      _ = target := by
        rw [Fraction.Field.mul_comm]
        exact Fraction.Field.div_mul_cancel_of_ne target
          (squareApproximationFactor source)
          (squareApproximationFactor_pos source).ne'
  centerBound := source.centerBound * source.centerBound
  centerBound_nonneg :=
    Arithmetic.mul_nonneg_direct source.centerBound_nonneg
      source.centerBound_nonneg
  sample_bounded := by
    intro index
    rw [Basic.normSq_mul]
    exact Arithmetic.mul_le_mul_direct
      (source.sample_bounded index) (source.sample_bounded index)
      (Basic.normSq_nonneg _) source.centerBound_nonneg

/-- Sampling the squared approximation squares the original sample at that same index. -/
@[simp] theorem squareApproximation_sample (source : ApproximationData)
    (index : Nat) :
    (squareApproximation source).sample index =
      source.sample index * source.sample index :=
  rfl

/-- Pointwise finite squaring respects operational equivalence of its source approximations. -/
@[expose] def squareApproximation_respects {left right : ApproximationData}
    (equivalent : Equivalent left right) :
    Equivalent (squareApproximation left)
      (squareApproximation right) where
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
              Basic.normSq
                  ((left.sample leftLater - right.sample rightLater) *
                    left.sample leftLater) ≤
                Basic.normSq (left.sample leftLater - right.sample rightLater) *
                  left.centerBound := by
            rw [Basic.normSq_mul]
            exact Arithmetic.mul_le_mul_of_nonneg_left_direct
              (left.sample_bounded leftLater) (Basic.normSq_nonneg _)
          have secondTerm :
              Basic.normSq
                  (right.sample rightLater *
                    (left.sample leftLater - right.sample rightLater)) ≤
                right.centerBound *
                  Basic.normSq (left.sample leftLater - right.sample rightLater) := by
            rw [Basic.normSq_mul]
            exact Arithmetic.mul_le_mul_of_nonneg_right_direct
              (right.sample_bounded rightLater) (Basic.normSq_nonneg _)
          have identity :
              left.sample leftLater * left.sample leftLater -
                  right.sample rightLater * right.sample rightLater =
                (left.sample leftLater - right.sample rightLater) *
                    left.sample leftLater +
                  right.sample rightLater *
                    (left.sample leftLater - right.sample rightLater) := by
            apply Data.Gaussian.Basic.ext <;>
              simp only [Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im,
                Data.Gaussian.Basic.add_re, Data.Gaussian.Basic.add_im,
                Data.Gaussian.Basic.mul_re, Data.Gaussian.Basic.mul_im] <;>
                ring1
          change Basic.normSq
              (left.sample leftLater * left.sample leftLater -
                right.sample rightLater * right.sample rightLater) < target
          rw [identity]
          calc
            Basic.normSq
                ((left.sample leftLater - right.sample rightLater) *
                    left.sample leftLater +
                  right.sample rightLater *
                    (left.sample leftLater - right.sample rightLater)) ≤
              2 *
                (Basic.normSq
                    ((left.sample leftLater - right.sample rightLater) *
                      left.sample leftLater) +
                  Basic.normSq
                    (right.sample rightLater *
                      (left.sample leftLater - right.sample rightLater))) :=
              Bounds.normSq_add_le_two _ _
            _ ≤ 2 *
                (Basic.normSq (left.sample leftLater - right.sample rightLater) *
                    left.centerBound +
                  right.centerBound *
                    Basic.normSq
                      (left.sample leftLater - right.sample rightLater)) :=
              Arithmetic.mul_le_mul_of_nonneg_left_direct
                (add_le_add firstTerm secondTerm) (by decide)
            _ = Basic.normSq (left.sample leftLater - right.sample rightLater) *
                (2 * (left.centerBound + right.centerBound)) := by ring1
            _ ≤ Basic.normSq (left.sample leftLater - right.sample rightLater) *

                  Bridge.approximationMulBridgeCoefficient
                  left right := by
              apply Arithmetic.mul_le_mul_of_nonneg_left_direct
              · unfold
                  Bridge.approximationMulBridgeCoefficient
                have nonnegative :
                    0 ≤ 8 + 2 * (left.centerBound + right.centerBound) :=
                  add_nonneg (by decide)
                    (Arithmetic.mul_nonneg_direct (by decide)
                      (add_nonneg left.centerBound_nonneg
                        right.centerBound_nonneg))
                apply Arithmetic.le_of_sub_nonneg_direct
                have difference :
                    (8 + 4 * (left.centerBound + right.centerBound)) -
                        2 * (left.centerBound + right.centerBound) =
                      8 + 2 * (left.centerBound + right.centerBound) := by ring1
                rw [difference]
                exact nonnegative
              · exact Basic.normSq_nonneg _
            _ < inputTarget *

                  Bridge.approximationMulBridgeCoefficient
                  left right :=
              Arithmetic.mul_lt_mul_of_pos_right_direct
                inputClose
                (Bridge.approximationMulBridgeCoefficient_pos left right)
            _ < target :=
              Bridge.approximationMulBridgeTarget_budget_lt left right positive }

end

end Purelib.Approximation.Gaussian.Sequence.Arithmetic.Square
