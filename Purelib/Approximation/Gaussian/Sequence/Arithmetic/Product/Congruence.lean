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

open Purelib.Data.Gaussian.Norm
open Purelib.Data.Rat.Fraction.Order

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

/-- Combine two paid finite operand comparisons through their actual pointwise product samples.

The output bound uses the first right and second left operands' certified
squared-magnitude ceilings. The positive combined margin pays strictness
even when a ceiling is zero. Defaults retain the original center bounds,
request tolerances and complete output. The paired maxima retain both
original comparisons and paid starts.
-/
@[expose] public def pointwiseComparison
    {leftOne leftTwo rightOne rightTwo firstProduct secondProduct : ApproximationData}
    {firstStart secondStart : Nat} {leftTarget rightTarget : Fraction.Rational}
    (leftComparison : Comparison leftOne leftTwo firstStart secondStart leftTarget)
    (rightComparison : Comparison rightOne rightTwo firstStart secondStart rightTarget)
    (firstSamples : ∀ index, firstProduct.sample index = leftOne.sample index * rightOne.sample index)
    (secondSamples : ∀ index, secondProduct.sample index = leftTwo.sample index * rightTwo.sample index)
    (firstRightCeiling : { upper : Fraction.Rational //
        ∀ index, Basic.normSq (rightOne.sample index) ≤ upper } :=
      ⟨rightOne.centerBound, rightOne.sample_bounded⟩)
    (secondLeftCeiling : { upper : Fraction.Rational //
        ∀ index, Basic.normSq (leftTwo.sample index) ≤ upper } :=
      ⟨leftTwo.centerBound, leftTwo.sample_bounded⟩)
    (margins : { pair : Fraction.Rational × Fraction.Rational // 0 < pair.1 + pair.2 } :=
      ⟨(leftTarget, rightTarget), Arithmetic.add_pos_of_pos_of_nonneg_direct
        leftComparison.target_positive rightComparison.target_positive.le⟩) :
    Comparison firstProduct secondProduct firstStart secondStart
      (2 * (leftTarget * firstRightCeiling.val + secondLeftCeiling.val * rightTarget) +
        margins.val.1 + margins.val.2) := by
  let firstIndex := max leftComparison.leftIndex rightComparison.leftIndex
  let secondIndex := max leftComparison.rightIndex rightComparison.rightIndex
  have firstLeft : leftComparison.leftIndex ≤ firstIndex := Order.le_max_left _ _
  have firstRight : rightComparison.leftIndex ≤ firstIndex := Order.le_max_right _ _
  have secondLeft : leftComparison.rightIndex ≤ secondIndex := Order.le_max_left _ _
  have secondRight : rightComparison.rightIndex ≤ secondIndex := Order.le_max_right _ _
  refine ⟨firstIndex, secondIndex, leftComparison.left_ge.trans firstLeft,
    leftComparison.right_ge.trans secondLeft, ?_⟩
  intro firstLater secondLater firstOrder secondOrder
  have leftClose := leftComparison.close (firstLeft.trans firstOrder) (secondLeft.trans secondOrder)
  have rightClose := rightComparison.close (firstRight.trans firstOrder) (secondRight.trans secondOrder)
  have secondUpperNonnegative : 0 ≤ secondLeftCeiling.val :=
    (Basic.normSq_nonneg _).trans (secondLeftCeiling.property 0)
  have firstTerm : Basic.normSq (leftOne.sample firstLater - leftTwo.sample secondLater) *
      Basic.normSq (rightOne.sample firstLater) ≤ leftTarget * firstRightCeiling.val :=
    Arithmetic.mul_le_mul_direct leftClose.le (firstRightCeiling.property firstLater)
      (Basic.normSq_nonneg _) leftComparison.target_positive.le
  have secondTerm : Basic.normSq (leftTwo.sample secondLater) *
      Basic.normSq (rightOne.sample firstLater - rightTwo.sample secondLater) ≤ secondLeftCeiling.val * rightTarget :=
    Arithmetic.mul_le_mul_direct (secondLeftCeiling.property secondLater) rightClose.le
      (Basic.normSq_nonneg _) secondUpperNonnegative
  rewrite [firstSamples firstLater, secondSamples secondLater]
  have bounded := (Bounds.normSq_mul_sub_mul_le _ _ _ _).trans
    (Arithmetic.mul_le_mul_of_nonneg_left_direct (Arithmetic.add_le_add_direct firstTerm secondTerm) (by decide))
  have strict := Arithmetic.add_lt_add_left_direct margins.property
    (2 * (leftTarget * firstRightCeiling.val + secondLeftCeiling.val * rightTarget))
  rewrite [_root_.add_zero] at strict
  have same : 2 * (leftTarget * firstRightCeiling.val + secondLeftCeiling.val * rightTarget) +
      (margins.val.1 + margins.val.2) =
      2 * (leftTarget * firstRightCeiling.val + secondLeftCeiling.val * rightTarget) + margins.val.1 + margins.val.2 :=
    (Fraction.Field.add_assoc _ _ _).symm
  exact bounded.trans_lt (strict.trans_eq same)

/-- Canonical finite products respect operational equivalence in both operands.

The supplied comparisons retain both input owners and finite observation indices. The same paired maxima and rational
request payment bound their product observations at every later pair of indices. -/
@[expose] public def sampledProductApproximation_respects
    {leftOne leftTwo rightOne rightTwo : Basic.Named}
    (leftEquivalent : NamedEquivalent leftOne leftTwo)
    (rightEquivalent : NamedEquivalent rightOne rightTwo) :
    Equivalent
      (sampledProductApproximation leftOne rightOne)
      (sampledProductApproximation leftTwo rightTwo) where
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
    let result := pointwiseComparison leftComparison rightComparison
      (sampledProductApproximation_sample leftOne rightOne)
      (sampledProductApproximation_sample leftTwo rightTwo)
    have paid := Bridge.approximationMulBridgeCoefficient_pair_bound firstRightSource secondLeftSource
      inputTarget inputPositive.le
    exact result.weaken target (paid.trans (Bridge.approximationMulBridgeTarget_budget_lt _ _ positive).le)

end Purelib.Approximation.Gaussian.Sequence.Arithmetic.Product.Congruence
