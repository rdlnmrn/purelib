module
public import Purelib.Approximation.Gaussian.Equivalence
public import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Sequence
public import Purelib.Approximation.Gaussian.Sequence.Arithmetic.Sum
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Field

import Init.Data.Nat.MinMax
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

-- The existing public Fraction.Order.Field → Fraction.Field path exposes Nat.Order.
import Purelib.Data.Nat.Order

open Purelib.Data.Gaussian.Norm

/-!
# Finite equivalence of sampled sums

Sum comparisons retain both input comparisons, select the same maximum later
indices, and combine their squared-distance certificates at quarter tolerance.
-/

namespace Purelib.Approximation.Gaussian.Sequence.Arithmetic.Sum.Congruence

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Name
open Purelib.Approximation.Gaussian.Sequence
open Purelib.Data.Rat
open Purelib.Data.Nat

/-- Combine two paid finite operand comparisons through their actual pointwise sum samples.

Both input comparisons keep the same requested starts. Their paired maxima
synchronize the actual observations without another refinement. The output
squared tolerance is twice the sum of the two retained operand tolerances.
-/
@[expose] public def pointwiseComparison
    {leftOne leftTwo rightOne rightTwo firstSum secondSum : ApproximationData}
    {firstStart secondStart : Nat} {leftTarget rightTarget : Fraction.Rational}
    (leftComparison : Comparison leftOne leftTwo firstStart secondStart leftTarget)
    (rightComparison : Comparison rightOne rightTwo firstStart secondStart rightTarget)
    (firstSamples : ∀ index, firstSum.sample index = leftOne.sample index + rightOne.sample index)
    (secondSamples : ∀ index, secondSum.sample index = leftTwo.sample index + rightTwo.sample index) :
    Comparison firstSum secondSum firstStart secondStart (2 * (leftTarget + rightTarget)) := by
  let firstIndex := max leftComparison.leftIndex rightComparison.leftIndex
  let secondIndex := max leftComparison.rightIndex rightComparison.rightIndex
  have firstLeft : leftComparison.leftIndex ≤ firstIndex := by
    dsimp only [firstIndex]
    rewrite [Order.max_eq_natMax]
    exact Order.le_max_left _ _
  have firstRight : rightComparison.leftIndex ≤ firstIndex := by
    dsimp only [firstIndex]
    rewrite [Order.max_eq_natMax]
    exact Order.le_max_right _ _
  have secondLeft : leftComparison.rightIndex ≤ secondIndex := by
    dsimp only [secondIndex]
    rewrite [Order.max_eq_natMax]
    exact Order.le_max_left _ _
  have secondRight : rightComparison.rightIndex ≤ secondIndex := by
    dsimp only [secondIndex]
    rewrite [Order.max_eq_natMax]
    exact Order.le_max_right _ _
  refine ⟨firstIndex, secondIndex, leftComparison.left_ge.trans firstLeft,
    leftComparison.right_ge.trans secondLeft, ?_⟩
  intro firstLater secondLater firstOrder secondOrder
  have leftClose := leftComparison.close (firstLeft.trans firstOrder) (secondLeft.trans secondOrder)
  have rightClose := rightComparison.close (firstRight.trans firstOrder) (secondRight.trans secondOrder)
  rewrite [firstSamples firstLater, secondSamples secondLater]
  exact (Bounds.normSq_add_sub_add_le _ _ _ _).trans_lt
    (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide)
      (Fraction.Order.Arithmetic.add_lt_add_direct leftClose rightClose))

/-- Canonical finite sums respect operational equivalence in both operands.

The two retained comparisons synchronize both operand samples at the same
maximum index. Quarter tolerances combine into the requested squared bound. -/
@[expose] public def sampledSumApproximation_respects
    {leftOne leftTwo rightOne rightTwo : Basic.Named}
    (leftEquivalent : NamedEquivalent leftOne leftTwo)
    (rightEquivalent : NamedEquivalent rightOne rightTwo) :
    Equivalent
      (sampledSumApproximation leftOne rightOne)
      (sampledSumApproximation leftTwo rightTwo) where
  compare := by
    intro firstStart secondStart target positive
    let smallTarget := target / 4
    have smallPositive : 0 < smallTarget := Fraction.Order.Field.div_pos_direct positive (by decide)
    let leftComparison := leftEquivalent.compare firstStart secondStart smallTarget smallPositive
    let rightComparison := rightEquivalent.compare firstStart secondStart smallTarget smallPositive
    let result := pointwiseComparison leftComparison rightComparison
      (sampledSumApproximation_sample leftOne rightOne) (sampledSumApproximation_sample leftTwo rightTwo)
    exact result.weaken target (by
      change 2 * (target / 4 + target / 4) ≤ target
      have same : 2 * (target / 4 + target / 4) = target := by
        calc
          _ = (target / 4) * 4 := by ring1
          _ = target := Fraction.Field.div_mul_cancel_of_ne target 4 (by decide)
      rewrite [same]
      exact Fraction.Order.Basic.le_refl target)

/-- Pointwise addition transports two approximation equivalences.

The supplied sample equations identify the two sums at every finite index.
The comparison retains the component indices and their squared-error bounds. -/
@[expose] public def pointwiseSumApproximation_respects
    {leftOne leftTwo rightOne rightTwo firstSum secondSum : ApproximationData}
    (leftEquivalent : Equivalent leftOne leftTwo)
    (rightEquivalent : Equivalent rightOne rightTwo)
    (firstSamples : ∀ index,
      firstSum.sample index = leftOne.sample index + rightOne.sample index)
    (secondSamples : ∀ index,
      secondSum.sample index = leftTwo.sample index + rightTwo.sample index) :
    Equivalent firstSum secondSum where
  compare := by
    intro firstStart secondStart target positive
    let smallTarget := target / 4
    have smallPositive : 0 < smallTarget := Fraction.Order.Field.div_pos_direct positive (by decide)
    let leftComparison := leftEquivalent.compare firstStart secondStart smallTarget smallPositive
    let rightComparison := rightEquivalent.compare firstStart secondStart smallTarget smallPositive
    let result := pointwiseComparison leftComparison rightComparison firstSamples secondSamples
    exact result.weaken target (by
      change 2 * (target / 4 + target / 4) ≤ target
      have same : 2 * (target / 4 + target / 4) = target := by
        calc
          _ = (target / 4) * 4 := by ring1
          _ = target := Fraction.Field.div_mul_cancel_of_ne target 4 (by decide)
      rewrite [same]
      exact Fraction.Order.Basic.le_refl target)

end Purelib.Approximation.Gaussian.Sequence.Arithmetic.Sum.Congruence
