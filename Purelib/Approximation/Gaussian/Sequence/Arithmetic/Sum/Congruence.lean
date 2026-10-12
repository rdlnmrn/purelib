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

/-- Canonical finite sums respect operational equivalence in both operands.

The two retained comparisons synchronize both operand samples at the same
maximum index. Quarter tolerances combine into the requested squared bound. -/
@[expose] public def sampledSumApproximation_respects
    {leftOne leftTwo rightOne rightTwo : Gaussian.Name.Basic.Named}
    (leftEquivalent : Gaussian.Equivalence.NamedEquivalent leftOne leftTwo)
    (rightEquivalent : Gaussian.Equivalence.NamedEquivalent rightOne rightTwo) :
    Gaussian.Equivalence.Equivalent
      (Gaussian.Sequence.Arithmetic.Sum.sampledSumApproximation leftOne rightOne)
      (Gaussian.Sequence.Arithmetic.Sum.sampledSumApproximation leftTwo rightTwo) where
  compare := by
    intro firstStart secondStart target positive
    let smallTarget := target / 4
    have smallPositive : 0 < smallTarget :=
      Fraction.Order.Field.div_pos_direct positive (by decide)
    let leftComparison := leftEquivalent.compare firstStart secondStart
      smallTarget smallPositive
    let rightComparison := rightEquivalent.compare firstStart secondStart
      smallTarget smallPositive
    let firstIndex := max leftComparison.leftIndex rightComparison.leftIndex
    let secondIndex := max leftComparison.rightIndex rightComparison.rightIndex
    have firstLeft : leftComparison.leftIndex ≤ firstIndex := by
      dsimp only [firstIndex]
      rw [Order.max_eq_natMax]
      exact Order.le_max_left _ _
    have firstRight : rightComparison.leftIndex ≤ firstIndex := by
      dsimp only [firstIndex]
      rw [Order.max_eq_natMax]
      exact Order.le_max_right _ _
    have secondLeft : leftComparison.rightIndex ≤ secondIndex := by
      dsimp only [secondIndex]
      rw [Order.max_eq_natMax]
      exact Order.le_max_left _ _
    have secondRight : rightComparison.rightIndex ≤ secondIndex := by
      dsimp only [secondIndex]
      rw [Order.max_eq_natMax]
      exact Order.le_max_right _ _
    exact
      { leftIndex := firstIndex
        rightIndex := secondIndex
        left_ge := leftComparison.left_ge.trans firstLeft
        right_ge := leftComparison.right_ge.trans secondLeft
        close := by
          intro firstLater secondLater firstOrder secondOrder
          have leftClose := leftComparison.close
            (firstLeft.trans firstOrder)
            (secondLeft.trans secondOrder)
          have rightClose := rightComparison.close
            (firstRight.trans firstOrder)
            (secondRight.trans secondOrder)
          have identity :
              (Sampling.approximation leftOne).sample
                    firstLater +
                  (Sampling.approximation rightOne).sample
                    firstLater -
                ((Sampling.approximation leftTwo).sample
                    secondLater +
                  (Sampling.approximation rightTwo).sample
                    secondLater) =
              ((Sampling.approximation leftOne).sample
                    firstLater -
                  (Sampling.approximation leftTwo).sample
                    secondLater) +
                ((Sampling.approximation rightOne).sample
                    firstLater -
                  (Sampling.approximation rightTwo).sample
                    secondLater) := by
            apply Data.Gaussian.Basic.ext <;>
              simp only [Purelib.Data.Gaussian.Basic.sub_re, Purelib.Data.Gaussian.Basic.sub_im,
                Purelib.Data.Gaussian.Basic.add_re, Purelib.Data.Gaussian.Basic.add_im] <;> ring1
          rw [Gaussian.Sequence.Arithmetic.Sum.sampledSumApproximation_sample,
            Gaussian.Sequence.Arithmetic.Sum.sampledSumApproximation_sample, identity]
          calc
            Data.Gaussian.Norm.Basic.normSq
                (((Sampling.approximation leftOne).sample
                      firstLater -
                    (Sampling.approximation leftTwo).sample
                      secondLater) +
                  ((Sampling.approximation rightOne).sample
                      firstLater -
                    (Sampling.approximation rightTwo).sample
                      secondLater)) ≤
              2 *
                (Data.Gaussian.Norm.Basic.normSq
                    ((Sampling.approximation leftOne).sample
                        firstLater -
                      (Sampling.approximation leftTwo).sample
                        secondLater) +
                  Data.Gaussian.Norm.Basic.normSq
                    ((Sampling.approximation rightOne).sample
                        firstLater -
                      (Sampling.approximation rightTwo).sample
                        secondLater)) :=
              Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _
            _ < 2 * (smallTarget + smallTarget) :=
              Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
                (by decide)
                (Fraction.Order.Arithmetic.add_lt_add_direct
                  leftClose rightClose)
            _ = target := by
              dsimp only [smallTarget]
              calc
                2 * (target / 4 + target / 4) = 4 * (target / 4) := by ring1
                _ = target := Fraction.Compatibility.four_mul_quarter_scale target }

/-- Pointwise addition transports two approximation equivalences.

The supplied sample equations identify the two sums at every finite index.
The comparison retains the component indices and their squared-error bounds. -/
@[expose] public def pointwiseSumApproximation_respects
    {leftOne leftTwo rightOne rightTwo firstSum secondSum : ApproximationData}
    (leftEquivalent : Gaussian.Equivalence.Equivalent leftOne leftTwo)
    (rightEquivalent : Gaussian.Equivalence.Equivalent rightOne rightTwo)
    (firstSamples : ∀ index,
      firstSum.sample index = leftOne.sample index + rightOne.sample index)
    (secondSamples : ∀ index,
      secondSum.sample index = leftTwo.sample index + rightTwo.sample index) :
    Gaussian.Equivalence.Equivalent firstSum secondSum where
  compare := by
    intro firstStart secondStart target positive
    let smallTarget := target / 4
    have smallPositive : 0 < smallTarget :=
      Fraction.Order.Field.div_pos_direct positive (by decide)
    let leftComparison := leftEquivalent.compare firstStart secondStart
      smallTarget smallPositive
    let rightComparison := rightEquivalent.compare firstStart secondStart
      smallTarget smallPositive
    let firstIndex := max leftComparison.leftIndex rightComparison.leftIndex
    let secondIndex := max leftComparison.rightIndex rightComparison.rightIndex
    have firstLeft : leftComparison.leftIndex ≤ firstIndex := by
      dsimp only [firstIndex]
      rw [Order.max_eq_natMax]
      exact Order.le_max_left _ _
    have firstRight : rightComparison.leftIndex ≤ firstIndex := by
      dsimp only [firstIndex]
      rw [Order.max_eq_natMax]
      exact Order.le_max_right _ _
    have secondLeft : leftComparison.rightIndex ≤ secondIndex := by
      dsimp only [secondIndex]
      rw [Order.max_eq_natMax]
      exact Order.le_max_left _ _
    have secondRight : rightComparison.rightIndex ≤ secondIndex := by
      dsimp only [secondIndex]
      rw [Order.max_eq_natMax]
      exact Order.le_max_right _ _
    exact
      { leftIndex := firstIndex
        rightIndex := secondIndex
        left_ge := leftComparison.left_ge.trans firstLeft
        right_ge := leftComparison.right_ge.trans secondLeft
        close := by
          intro firstLater secondLater firstOrder secondOrder
          have leftClose := leftComparison.close
            (firstLeft.trans firstOrder)
            (secondLeft.trans secondOrder)
          have rightClose := rightComparison.close
            (firstRight.trans firstOrder)
            (secondRight.trans secondOrder)
          have identity :
              (leftOne.sample firstLater + rightOne.sample firstLater) -
                  (leftTwo.sample secondLater + rightTwo.sample secondLater) =
                (leftOne.sample firstLater - leftTwo.sample secondLater) +
                  (rightOne.sample firstLater -
                    rightTwo.sample secondLater) := by
            apply Data.Gaussian.Basic.ext <;>
              simp only [Purelib.Data.Gaussian.Basic.sub_re, Purelib.Data.Gaussian.Basic.sub_im,
                Purelib.Data.Gaussian.Basic.add_re, Purelib.Data.Gaussian.Basic.add_im] <;> ring1
          rw [firstSamples, secondSamples, identity]
          calc
            Data.Gaussian.Norm.Basic.normSq
                ((leftOne.sample firstLater - leftTwo.sample secondLater) +
                  (rightOne.sample firstLater -
                    rightTwo.sample secondLater)) ≤
              2 *
                (Data.Gaussian.Norm.Basic.normSq
                    (leftOne.sample firstLater - leftTwo.sample secondLater) +
                  Data.Gaussian.Norm.Basic.normSq
                    (rightOne.sample firstLater -
                      rightTwo.sample secondLater)) :=
              Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _
            _ < 2 * (smallTarget + smallTarget) :=
              Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
                (by decide)
                (Fraction.Order.Arithmetic.add_lt_add_direct
                  leftClose rightClose)
            _ = target := by
              dsimp only [smallTarget]
              calc
                2 * (target / 4 + target / 4) = 4 * (target / 4) := by ring1
                _ = target := Fraction.Compatibility.four_mul_quarter_scale target }
end Purelib.Approximation.Gaussian.Sequence.Arithmetic.Sum.Congruence
