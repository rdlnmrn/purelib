module
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Sequence.Name
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Sampling
public import Purelib.Approximation.Gaussian.Sequence.Arithmetic.Multiplication.Bridge
public import Purelib.Approximation.Gaussian.Sequence.Arithmetic.Product
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Tactic.QuotientFreeOmega
import Init.Data.Nat.MinMax
import Purelib.Data.Nat.Order
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

/-!
# Operational congruence of Gaussian sampled products

The two supplied operand comparisons retain their original owners and finite
observations. Their paired indices and common request payment bound the same
sampled products at every later retained observation.
-/

namespace Purelib.Approximation.Gaussian.Sequence.Arithmetic.Product.Congruence

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Name
open Purelib.Approximation.Gaussian.Sequence.Arithmetic.Multiplication
open Purelib.Data.Rat
open Purelib.Data.Nat

/-- Canonical finite products respect operational equivalence in both operands.

The supplied comparisons retain both input owners and finite observation indices. The same paired maxima and rational
request payment bound their product observations at every later pair of indices. -/
@[expose] public def sampledProductApproximation_respects
    {leftOne leftTwo rightOne rightTwo : Gaussian.Name.Basic.Named}
    (leftEquivalent : Gaussian.Equivalence.NamedEquivalent leftOne leftTwo)
    (rightEquivalent : Gaussian.Equivalence.NamedEquivalent rightOne rightTwo) :
    Gaussian.Equivalence.Equivalent
      (Gaussian.Sequence.Arithmetic.Product.sampledProductApproximation leftOne rightOne)
      (Gaussian.Sequence.Arithmetic.Product.sampledProductApproximation leftTwo rightTwo) where
  compare := by
    intro firstStart secondStart target positive
    let firstLeftSource :=
      Sampling.approximation leftOne
    let secondLeftSource :=
      Sampling.approximation leftTwo
    let firstRightSource :=
      Sampling.approximation rightOne
    let secondRightSource :=
      Sampling.approximation rightTwo
    let inputTarget := Bridge.approximationMulBridgeTarget
      firstRightSource secondLeftSource target
    have inputPositive : 0 < inputTarget :=
      Bridge.approximationMulBridgeTarget_pos _ _ positive
    let leftComparison := leftEquivalent.compare firstStart secondStart
      inputTarget inputPositive
    let rightComparison := rightEquivalent.compare firstStart secondStart
      inputTarget inputPositive
    let firstIndex := max leftComparison.leftIndex rightComparison.leftIndex
    let secondIndex := max leftComparison.rightIndex rightComparison.rightIndex
    exact
      { leftIndex := firstIndex
        rightIndex := secondIndex
        left_ge := leftComparison.left_ge.trans
          (Order.le_max_left _ _)
        right_ge := leftComparison.right_ge.trans
          (Order.le_max_left _ _)
        close := by
          intro firstLater secondLater firstOrder secondOrder
          have leftClose := leftComparison.close
            ((Order.le_max_left leftComparison.leftIndex
              rightComparison.leftIndex).trans firstOrder)
            ((Order.le_max_left leftComparison.rightIndex
              rightComparison.rightIndex).trans secondOrder)
          have rightClose := rightComparison.close
            ((Order.le_max_right leftComparison.leftIndex
              rightComparison.leftIndex).trans firstOrder)
            ((Order.le_max_right leftComparison.rightIndex
              rightComparison.rightIndex).trans secondOrder)
          have firstTerm :
              Data.Gaussian.Norm.Basic.normSq
                  ((firstLeftSource.sample firstLater -
                      secondLeftSource.sample secondLater) *
                    firstRightSource.sample firstLater) ≤
                Data.Gaussian.Norm.Basic.normSq
                    (firstLeftSource.sample firstLater -
                      secondLeftSource.sample secondLater) *
                  firstRightSource.centerBound := by
            rw [Data.Gaussian.Norm.Basic.normSq_mul]
            exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
              (firstRightSource.sample_bounded firstLater) (Data.Gaussian.Norm.Basic.normSq_nonneg _)
          have secondTerm :
              Data.Gaussian.Norm.Basic.normSq
                  (secondLeftSource.sample secondLater *
                    (firstRightSource.sample firstLater -
                      secondRightSource.sample secondLater)) ≤
                secondLeftSource.centerBound *
                  Data.Gaussian.Norm.Basic.normSq
                    (firstRightSource.sample firstLater -
                      secondRightSource.sample secondLater) := by
            rw [Data.Gaussian.Norm.Basic.normSq_mul]
            exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
              (secondLeftSource.sample_bounded secondLater) (Data.Gaussian.Norm.Basic.normSq_nonneg _)
          have identity :
              firstLeftSource.sample firstLater *
                    firstRightSource.sample firstLater -
                  secondLeftSource.sample secondLater *
                    secondRightSource.sample secondLater =
                (firstLeftSource.sample firstLater -
                    secondLeftSource.sample secondLater) *
                    firstRightSource.sample firstLater +
                  secondLeftSource.sample secondLater *
                    (firstRightSource.sample firstLater -
                      secondRightSource.sample secondLater) := by
            apply Data.Gaussian.Basic.ext <;>
              simp only [Purelib.Data.Gaussian.Basic.sub_re, Purelib.Data.Gaussian.Basic.sub_im,
                Purelib.Data.Gaussian.Basic.add_re, Purelib.Data.Gaussian.Basic.add_im,
                Purelib.Data.Gaussian.Basic.mul_re, Purelib.Data.Gaussian.Basic.mul_im] <;>
                ring1
          change Data.Gaussian.Norm.Basic.normSq
              (firstLeftSource.sample firstLater *
                    firstRightSource.sample firstLater -
                secondLeftSource.sample secondLater *
                    secondRightSource.sample secondLater) < target
          rw [identity]
          calc
            Data.Gaussian.Norm.Basic.normSq
                ((firstLeftSource.sample firstLater -
                    secondLeftSource.sample secondLater) *
                    firstRightSource.sample firstLater +
                  secondLeftSource.sample secondLater *
                    (firstRightSource.sample firstLater -
                      secondRightSource.sample secondLater)) ≤
              2 *
                (Data.Gaussian.Norm.Basic.normSq
                    ((firstLeftSource.sample firstLater -
                        secondLeftSource.sample secondLater) *
                      firstRightSource.sample firstLater) +
                  Data.Gaussian.Norm.Basic.normSq
                    (secondLeftSource.sample secondLater *
                      (firstRightSource.sample firstLater -
                        secondRightSource.sample secondLater))) :=
              Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _
            _ ≤ 2 *
                (inputTarget * firstRightSource.centerBound +
                  secondLeftSource.centerBound * inputTarget) :=
              Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
                (add_le_add
                  (firstTerm.trans
                    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
                      leftClose.le firstRightSource.centerBound_nonneg))
                  (secondTerm.trans
                    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
                      rightClose.le secondLeftSource.centerBound_nonneg)))
                (by decide)
            _ = inputTarget *
                (2 * (firstRightSource.centerBound +
                  secondLeftSource.centerBound)) := by ring1
            _ ≤ inputTarget *

                  Multiplication.Bridge.approximationMulBridgeCoefficient
                  firstRightSource secondLeftSource := by
              apply Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
              · unfold
                  Multiplication.Bridge.approximationMulBridgeCoefficient
                have nonnegative :
                    0 ≤ 8 +
                        2 * (firstRightSource.centerBound +
                          secondLeftSource.centerBound) :=
                  add_nonneg (by decide)
                    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
                      (add_nonneg firstRightSource.centerBound_nonneg
                        secondLeftSource.centerBound_nonneg))
                apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
                convert nonnegative using 1
                ring1
              · exact inputPositive.le
            _ < target :=
              Bridge.approximationMulBridgeTarget_budget_lt _ _ positive }

end Purelib.Approximation.Gaussian.Sequence.Arithmetic.Product.Congruence
