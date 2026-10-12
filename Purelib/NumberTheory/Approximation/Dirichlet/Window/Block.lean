module
import Purelib.Algebra.NatCast
import Purelib.Data.GaussianInt.Pair.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.GaussianInt.Fraction.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.SignedFraction.Arithmetic
import Purelib.Data.Rat.SignedFraction.Basic
import Purelib.Data.Rat.SignedFraction.Normalization
import Purelib.NumberTheory.Approximation.Best.Consecutive.Basic
import Purelib.NumberTheory.Approximation.Best.Consecutive.RepeatedIndex
public import Purelib.NumberTheory.Approximation.Dirichlet.Window.Basic
import Purelib.NumberTheory.Approximation.Dirichlet.Window.IndexOne.Bounds
import Purelib.NumberTheory.Approximation.Dirichlet.Window.IndexOne.Chambers
import Purelib.NumberTheory.Approximation.Dirichlet.Window.IndexTwo.Bounds
public import Purelib.NumberTheory.Approximation.Dirichlet.Window.IndexTwo.Optimal
import Purelib.NumberTheory.Approximation.Dirichlet.Window.SourceBound
import Purelib.Data.GaussianInt.Pair.LinearCombination
import Purelib.NumberTheory.Approximation.Best.Consecutive.Index
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.NumberTheory.Approximation

section
@[expose] public section

/-!
# Two-window Dirichlet bounds

This file combines the rational bound for one consecutive Dirichlet window
with the finite exclusion of two successive coefficient indices equal to two.
Thus every adjacent pair of windows contains an index-one window, and their
sum has a smaller bound than two independent applications of the universal
one-window estimate.
-/

namespace Purelib.NumberTheory.Approximation.Dirichlet.Window.Block

open Purelib.Algebra

/-- Shallow displayed record for the two-window sum bound `1224/35`. -/
def refinedTwoWindowSumBound : Fraction.Rational :=
  Data.Rat.SignedFraction.Normalization.ofFraction ⟨1224, 35, by decide⟩

/-- Shallow displayed record for the sharper two-window sum bound `1189/34`. -/
def quadraticTwoWindowSumBound : Fraction.Rational :=
  Data.Rat.SignedFraction.Normalization.ofFraction ⟨1189, 34, by decide⟩

/-- Exact rational sum bound supplied by the finite-octant index-one
certificate and the index-two centered-coset certificate. -/
def octantTwoWindowSumBound : Fraction.Rational :=
  Data.Rat.SignedFraction.Normalization.ofFraction ⟨224, 71, by decide⟩

/-- Near-optimal dyadic bound `512/205` for two successive squared windows. -/
def dyadicTwoWindowSumBound : Fraction.Rational :=
  Data.Rat.SignedFraction.Normalization.ofFraction ⟨512, 205, by decide⟩

/-- Clearing the denominator of the dyadic two-window bound gives the integer numerator 512. -/
theorem dyadicTwoWindowSumBound_mul_denominator :
    Dirichlet.Window.Block.dyadicTwoWindowSumBound * 205 = 512 := by
  unfold Dirichlet.Window.Block.dyadicTwoWindowSumBound
  have clearance := Data.Rat.SignedFraction.Arithmetic.ofFraction_mul_den
    ({ num := 512, den := 205, den_pos := by decide } :
      Data.Rat.SignedFraction)
  simpa only [Int.cast_ofNat] using clearance

/-- Clearing the denominator of the octant two-window bound gives the integer numerator 224. -/
theorem octantTwoWindowSumBound_mul_denominator :
    Dirichlet.Window.Block.octantTwoWindowSumBound * 71 = 224 := by
  unfold Dirichlet.Window.Block.octantTwoWindowSumBound
  have clearance := Data.Rat.SignedFraction.Arithmetic.ofFraction_mul_den
    ({ num := 224, den := 71, den_pos := by decide } :
      Data.Rat.SignedFraction)
  simpa only [Int.cast_ofNat] using clearance

/-- Three times the refined single-index factor is the refined two-window sum bound. -/
theorem refinedIndexFactor_mul_three :
    Dirichlet.Window.Basic.refinedIndexFactor * 3 =
      Dirichlet.Window.Block.refinedTwoWindowSumBound := by
  unfold Dirichlet.Window.Basic.refinedIndexFactor Dirichlet.Window.Block.refinedTwoWindowSumBound
  calc
    Data.Rat.SignedFraction.Normalization.ofFraction ⟨408, 35, by decide⟩ * 3 =
        Data.Rat.SignedFraction.Normalization.ofFraction ⟨408, 35, by decide⟩ *
          Data.Rat.SignedFraction.Normalization.ofFraction ⟨3, 1, by decide⟩ :=
      congrArg
        (fun value : Fraction.Rational =>
          Data.Rat.SignedFraction.Normalization.ofFraction ⟨408, 35, by decide⟩ * value)
        (Data.Rat.SignedFraction.Arithmetic.natCast_eq_fraction 3)
    _ = Data.Rat.SignedFraction.Normalization.ofFraction ⟨1224, 35, by decide⟩ := by
      rw [Data.Rat.SignedFraction.Arithmetic.ofFraction_mulFraction]
      apply Data.Rat.SignedFraction.Normalization.ofFraction_eq_of_equivalent
      change (408 * 3 : Int) * 35 = 1224 * (35 * 1)
      ring1

/-- Clearing the denominator of the refined two-window bound gives the integer numerator 1224. -/
theorem refinedTwoWindowSumBound_mul_denominator :
    Dirichlet.Window.Block.refinedTwoWindowSumBound * 35 = 1224 := by
  unfold Dirichlet.Window.Block.refinedTwoWindowSumBound
  have clearance := Data.Rat.SignedFraction.Arithmetic.ofFraction_mul_den
    ({ num := 1224, den := 35, den_pos := by decide } :
      Data.Rat.SignedFraction)
  simpa only [Int.cast_ofNat] using clearance

/-- Three times the quadratic single-index factor gives the intermediate two-window bound 1189/34. -/
theorem quadraticIndexFactor_mul_three :
    Dirichlet.Window.Basic.quadraticIndexFactor * 3 =
      Dirichlet.Window.Block.quadraticTwoWindowSumBound := by
  unfold Dirichlet.Window.Basic.quadraticIndexFactor Dirichlet.Window.Block.quadraticTwoWindowSumBound
  calc
    Data.Rat.SignedFraction.Normalization.ofFraction ⟨1189, 102, by decide⟩ * 3 =
        Data.Rat.SignedFraction.Normalization.ofFraction ⟨1189, 102, by decide⟩ *
          Data.Rat.SignedFraction.Normalization.ofFraction ⟨3, 1, by decide⟩ :=
      congrArg
        (fun value : Fraction.Rational =>
          Data.Rat.SignedFraction.Normalization.ofFraction ⟨1189, 102, by decide⟩ * value)
        (Data.Rat.SignedFraction.Arithmetic.natCast_eq_fraction 3)
    _ = Data.Rat.SignedFraction.Normalization.ofFraction ⟨1189, 34, by decide⟩ := by
      rw [Data.Rat.SignedFraction.Arithmetic.ofFraction_mulFraction]
      apply Data.Rat.SignedFraction.Normalization.ofFraction_eq_of_equivalent
      change (1189 * 3 : Int) * 34 = 1189 * (102 * 1)
      ring1

/-- Clearing the denominator of the quadratic two-window bound gives the integer numerator 1189. -/
theorem quadraticTwoWindowSumBound_mul_denominator :
    Dirichlet.Window.Block.quadraticTwoWindowSumBound * 34 = 1189 := by
  unfold Dirichlet.Window.Block.quadraticTwoWindowSumBound
  have clearance := Data.Rat.SignedFraction.Arithmetic.ofFraction_mul_den
    ({ num := 1189, den := 34, den_pos := by decide } :
      Data.Rat.SignedFraction)
  simpa only [Int.cast_ofNat] using clearance

/-- The coefficient indices of two successive best transitions have sum at
most three: an index-two transition must be followed by index one. -/
theorem coefficientIndexQuadrance_add_le_three
    {source : GaussianInt.Fraction} {lower middle upper : GaussianInt.Pair.Basic.ConvergentPair}
    (first : Best.Consecutive.Basic.AreConsecutiveBest source.value lower middle)
    (second : Best.Consecutive.Basic.AreConsecutiveBest source.value middle upper) :
    GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower middle +
        GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance middle upper ≤ 3 := by
  rcases (Best.Consecutive.Index.AreConsecutiveBest.coefficientIndexQuadrance_eq_one_or_two first) with
      leftIndexOne | leftIndexTwo
  · rw [leftIndexOne]
    simpa only [Nat.one_add, Nat.reduceSucc] using
      Nat.succ_le_succ (Best.Consecutive.Index.AreConsecutiveBest.coefficientIndexQuadrance_le_two second)
  · have rightIndexOne :=
      Best.Consecutive.RepeatedIndex.nextCoefficientIndexQuadrance_eq_one_of_eq_two
        first second leftIndexTwo
    rw [leftIndexTwo, rightIndexOne]

/-- For any rational threshold passing the quadratic boundary test, at least
one of two successive windows satisfies the index-one scaled bound. -/
theorem
  quadraticThreshold_mul_one_dirichletWindow_le_one
    {source : GaussianInt.Fraction} {lower middle upper : GaussianInt.Pair.Basic.ConvergentPair}
    (first : Best.Consecutive.Basic.AreConsecutiveBest source.value lower middle)
    (second : Best.Consecutive.Basic.AreConsecutiveBest source.value middle upper)
    (threshold : Fraction.Rational)
    (thresholdLtHalf : threshold < (1 / 2 : Fraction.Rational))
    (thresholdPolynomialNonnegative :
      0 ≤ threshold ^ 2 - 3 * threshold + 1 / 4) :
    threshold * Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value lower middle ≤ 1 ∨
      threshold * Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value middle upper ≤ 1 := by
  rcases (Best.Consecutive.Index.AreConsecutiveBest.coefficientIndexQuadrance_eq_one_or_two first) with
      leftIndexOne | leftIndexTwo
  · left
    have bound :=
      Dirichlet.Window.Basic.AreConsecutiveBest.quadraticThreshold_mul_dirichletWindow_le_index
        first threshold thresholdLtHalf thresholdPolynomialNonnegative
    simpa only [leftIndexOne, Nat.cast_one] using bound
  · right
    have rightIndexOne :=
      Best.Consecutive.RepeatedIndex.nextCoefficientIndexQuadrance_eq_one_of_eq_two
        first second leftIndexTwo
    have bound :=
      Dirichlet.Window.Basic.AreConsecutiveBest.quadraticThreshold_mul_dirichletWindow_le_index
        second threshold thresholdLtHalf thresholdPolynomialNonnegative
    simpa only [rightIndexOne, Nat.cast_one] using bound

/-- Parameterized two-window form of the quadratic-threshold certificate:
the threshold times the sum of two successive windows is at most three. -/
theorem
  quadraticThreshold_mul_dirichletWindowSum_le_three
    {source : GaussianInt.Fraction} {lower middle upper : GaussianInt.Pair.Basic.ConvergentPair}
    (first : Best.Consecutive.Basic.AreConsecutiveBest source.value lower middle)
    (second : Best.Consecutive.Basic.AreConsecutiveBest source.value middle upper)
    (threshold : Fraction.Rational)
    (thresholdLtHalf : threshold < (1 / 2 : Fraction.Rational))
    (thresholdPolynomialNonnegative :
      0 ≤ threshold ^ 2 - 3 * threshold + 1 / 4) :
    threshold *
        (Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value lower middle +
          Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value middle upper) ≤ 3 := by
  have firstBound :=
    Dirichlet.Window.Basic.AreConsecutiveBest.quadraticThreshold_mul_dirichletWindow_le_index
      first threshold thresholdLtHalf thresholdPolynomialNonnegative
  have secondBound :=
    Dirichlet.Window.Basic.AreConsecutiveBest.quadraticThreshold_mul_dirichletWindow_le_index
      second threshold thresholdLtHalf thresholdPolynomialNonnegative
  have addedBounds :=
    Fraction.Order.Arithmetic.add_le_add_direct firstBound secondBound
  have indexSumBound := Dirichlet.Window.Block.coefficientIndexQuadrance_add_le_three first second
  have castIndexSumBound :
      ((GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower middle +
          GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance middle upper : Nat) : Fraction.Rational) ≤ 3 :=
    Fraction.Cast.Order.natCast_le_direct indexSumBound
  calc
    threshold *
        (Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value lower middle +
          Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value middle upper) =
        threshold * Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value lower middle +
          threshold * Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value middle upper := by
      ring1
    _ ≤ (GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower middle : Fraction.Rational) +
          (GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance middle upper : Fraction.Rational) := addedBounds
    _ = ((GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower middle +
          GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance middle upper : Nat) : Fraction.Rational) := by
      rw [NatCast.add]
    _ ≤ 3 := castIndexSumBound

/-- Among two successive best transitions, at least one squared window is
bounded by the index-one constant `408/35`. -/
theorem
  one_dirichletWindowQuadrance_le_refinedIndexFactor
    {source : GaussianInt.Fraction} {lower middle upper : GaussianInt.Pair.Basic.ConvergentPair}
    (first : Best.Consecutive.Basic.AreConsecutiveBest source.value lower middle)
    (second : Best.Consecutive.Basic.AreConsecutiveBest source.value middle upper) :
    Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value lower middle ≤
        Dirichlet.Window.Basic.refinedIndexFactor ∨
      Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value middle upper ≤
        Dirichlet.Window.Basic.refinedIndexFactor := by
  rcases (Best.Consecutive.Index.AreConsecutiveBest.coefficientIndexQuadrance_eq_one_or_two first) with
      leftIndexOne | leftIndexTwo
  · left
    have bound :=
      Dirichlet.Window.Basic.AreConsecutiveBest.dirichletWindowQuadrance_le_refinedIndexFactor
        first
    simpa only [leftIndexOne, Nat.cast_one, mul_one] using bound
  · right
    have rightIndexOne :=
      Best.Consecutive.RepeatedIndex.nextCoefficientIndexQuadrance_eq_one_of_eq_two
        first second leftIndexTwo
    have bound :=
      Dirichlet.Window.Basic.AreConsecutiveBest.dirichletWindowQuadrance_le_refinedIndexFactor
        second
    simpa only [rightIndexOne, Nat.cast_one, mul_one] using bound

/-- Among two successive best transitions, at least one squared window is
bounded by the sharper index-one constant `1189/102`. -/
theorem
  one_dirichletWindowQuadrance_le_quadraticIndexFactor
    {source : GaussianInt.Fraction} {lower middle upper : GaussianInt.Pair.Basic.ConvergentPair}
    (first : Best.Consecutive.Basic.AreConsecutiveBest source.value lower middle)
    (second : Best.Consecutive.Basic.AreConsecutiveBest source.value middle upper) :
    Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value lower middle ≤
        Dirichlet.Window.Basic.quadraticIndexFactor ∨
      Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value middle upper ≤
        Dirichlet.Window.Basic.quadraticIndexFactor := by
  rcases (Best.Consecutive.Index.AreConsecutiveBest.coefficientIndexQuadrance_eq_one_or_two first) with
      leftIndexOne | leftIndexTwo
  · left
    have bound :=
      Dirichlet.Window.Basic.AreConsecutiveBest.dirichletWindowQuadrance_le_quadraticIndexFactor
        first
    simpa only [leftIndexOne, Nat.cast_one, mul_one] using bound
  · right
    have rightIndexOne :=
      Best.Consecutive.RepeatedIndex.nextCoefficientIndexQuadrance_eq_one_of_eq_two
        first second leftIndexTwo
    have bound :=
      Dirichlet.Window.Basic.AreConsecutiveBest.dirichletWindowQuadrance_le_quadraticIndexFactor
        second
    simpa only [rightIndexOne, Nat.cast_one, mul_one] using bound

/-- The sum of two successive squared Dirichlet-window products is at most
`1224/35`, improving the sum of two independent universal bounds. -/
theorem
  dirichletWindowQuadrance_add_le_refinedTwoWindowSumBound
    {source : GaussianInt.Fraction} {lower middle upper : GaussianInt.Pair.Basic.ConvergentPair}
    (first : Best.Consecutive.Basic.AreConsecutiveBest source.value lower middle)
    (second : Best.Consecutive.Basic.AreConsecutiveBest source.value middle upper) :
    Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value lower middle +
        Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value middle upper ≤
      Dirichlet.Window.Block.refinedTwoWindowSumBound := by
  have firstBound :=
    Dirichlet.Window.Basic.AreConsecutiveBest.dirichletWindowQuadrance_le_refinedIndexFactor
      first
  have secondBound :=
    Dirichlet.Window.Basic.AreConsecutiveBest.dirichletWindowQuadrance_le_refinedIndexFactor
      second
  have indexSumBound := Dirichlet.Window.Block.coefficientIndexQuadrance_add_le_three first second
  have castIndexSumBound :
      ((GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower middle +
          GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance middle upper : Nat) : Fraction.Rational) ≤ 3 :=
    Fraction.Cast.Order.natCast_le_direct indexSumBound
  have scaledIndexSumBound :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      castIndexSumBound Dirichlet.Window.Basic.refinedIndexFactor_nonneg
  calc
    Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value lower middle +
        Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value middle upper ≤
        Dirichlet.Window.Basic.refinedIndexFactor *
            (GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower middle : Fraction.Rational) +
          Dirichlet.Window.Basic.refinedIndexFactor *
            (GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance middle upper : Fraction.Rational) :=
      Fraction.Order.Arithmetic.add_le_add_direct firstBound secondBound
    _ = Dirichlet.Window.Basic.refinedIndexFactor *
        ((GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower middle +
          GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance middle upper : Nat) : Fraction.Rational) := by
      rw [NatCast.add]
      ring1
    _ ≤ Dirichlet.Window.Basic.refinedIndexFactor * 3 := scaledIndexSumBound
    _ = Dirichlet.Window.Block.refinedTwoWindowSumBound := Dirichlet.Window.Block.refinedIndexFactor_mul_three

/-- The sum of two successive squared Dirichlet-window products is at most
the sharper rational `1189/34`. -/
theorem
  dirichletWindowQuadrance_add_le_quadraticTwoWindowSumBound
    {source : GaussianInt.Fraction} {lower middle upper : GaussianInt.Pair.Basic.ConvergentPair}
    (first : Best.Consecutive.Basic.AreConsecutiveBest source.value lower middle)
    (second : Best.Consecutive.Basic.AreConsecutiveBest source.value middle upper) :
    Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value lower middle +
        Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value middle upper ≤
      Dirichlet.Window.Block.quadraticTwoWindowSumBound := by
  have firstBound :=
    Dirichlet.Window.Basic.AreConsecutiveBest.dirichletWindowQuadrance_le_quadraticIndexFactor
      first
  have secondBound :=
    Dirichlet.Window.Basic.AreConsecutiveBest.dirichletWindowQuadrance_le_quadraticIndexFactor
      second
  have indexSumBound := Dirichlet.Window.Block.coefficientIndexQuadrance_add_le_three first second
  have castIndexSumBound :
      ((GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower middle +
          GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance middle upper : Nat) : Fraction.Rational) ≤ 3 :=
    Fraction.Cast.Order.natCast_le_direct indexSumBound
  have scaledIndexSumBound :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      castIndexSumBound Dirichlet.Window.Basic.quadraticIndexFactor_nonneg
  calc
    Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value lower middle +
        Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value middle upper ≤
        Dirichlet.Window.Basic.quadraticIndexFactor *
            (GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower middle : Fraction.Rational) +
          Dirichlet.Window.Basic.quadraticIndexFactor *
            (GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance middle upper : Fraction.Rational) :=
      Fraction.Order.Arithmetic.add_le_add_direct firstBound secondBound
    _ = Dirichlet.Window.Basic.quadraticIndexFactor *
        ((GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance lower middle +
          GaussianInt.Pair.LinearCombination.coefficientIndexQuadrance middle upper : Nat) : Fraction.Rational) := by
      rw [NatCast.add]
      ring1
    _ ≤ Dirichlet.Window.Basic.quadraticIndexFactor * 3 :=
      scaledIndexSumBound
    _ = Dirichlet.Window.Block.quadraticTwoWindowSumBound := Dirichlet.Window.Block.quadraticIndexFactor_mul_three

/-- The index-aware one-window theorem bounds the sum of any two successive
squared windows by `1189/51`.  This improves the earlier index-sum bound
`1189/34`: determinant index two is now handled by its centered-coset gap
rather than by twice the generic index-one factor. -/
theorem
  dirichletWindowQuadrance_add_le_quadraticUniversalWindowBound
    {source : GaussianInt.Fraction} {lower middle upper : GaussianInt.Pair.Basic.ConvergentPair}
    (first : Best.Consecutive.Basic.AreConsecutiveBest source.value lower middle)
    (second : Best.Consecutive.Basic.AreConsecutiveBest source.value middle upper) :
    Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value lower middle +
        Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value middle upper ≤
      Dirichlet.Window.Basic.quadraticUniversalWindowBound := by
  have firstBound :=
    Dirichlet.Window.IndexTwo.Bounds.AreConsecutiveBest.dirichletWindowQuadrance_le_quadraticIndexFactorUniversal
      first
  have secondBound :=
    Dirichlet.Window.IndexTwo.Bounds.AreConsecutiveBest.dirichletWindowQuadrance_le_quadraticIndexFactorUniversal
      second
  calc
    Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value lower middle +
        Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value middle upper ≤
        Dirichlet.Window.Basic.quadraticIndexFactor +
          Dirichlet.Window.Basic.quadraticIndexFactor :=
      Fraction.Order.Arithmetic.add_le_add_direct firstBound secondBound
    _ = Dirichlet.Window.Basic.quadraticIndexFactor * 2 := by ring1
    _ = Dirichlet.Window.Basic.quadraticUniversalWindowBound :=
      Dirichlet.Window.Basic.quadraticIndexFactor_mul_two

/-- Two successive windows have sum at most `224/71`, by applying the current
rational universal bound `112/71` to each supplied transition. -/
theorem
  dirichletWindowQuadrance_add_le_octantTwoWindowSumBound
    {source : GaussianInt.Fraction} {lower middle upper : GaussianInt.Pair.Basic.ConvergentPair}
    (first : Best.Consecutive.Basic.AreConsecutiveBest source.value lower middle)
    (second : Best.Consecutive.Basic.AreConsecutiveBest source.value middle upper) :
    Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value lower middle +
        Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value middle upper ≤
      Dirichlet.Window.Block.octantTwoWindowSumBound := by
  have firstBound :=
    Dirichlet.Window.IndexOne.Bounds.AreConsecutiveBest.dirichletWindowQuadrance_le_normTwoUniversalWindowBound
      first
  have secondBound :=
    Dirichlet.Window.IndexOne.Bounds.AreConsecutiveBest.dirichletWindowQuadrance_le_normTwoUniversalWindowBound
      second
  calc
    Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value lower middle +
        Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value middle upper ≤
        Dirichlet.Window.IndexOne.Bounds.normTwoIndexOneWindowBound +
          Dirichlet.Window.IndexOne.Bounds.normTwoIndexOneWindowBound :=
      Fraction.Order.Arithmetic.add_le_add_direct firstBound secondBound
    _ = Dirichlet.Window.Block.octantTwoWindowSumBound := by
      unfold Dirichlet.Window.Block.octantTwoWindowSumBound
      unfold Dirichlet.Window.IndexOne.Bounds.normTwoIndexOneWindowBound
      rw [Data.Rat.SignedFraction.Arithmetic.ofFraction_addFraction]
      apply Data.Rat.SignedFraction.Normalization.ofFraction_eq_of_equivalent
      change ((112 * 71 + 112 * 71) * 71 : Int) = 224 * (71 * 71)
      ring1

/-- Two successive squared windows have sum at most `512/205`, by applying
the dyadic five-obstruction/centered-coset bound to both transitions. -/
theorem
  dirichletWindowQuadrance_add_le_dyadicTwoWindowSumBound
    {source : GaussianInt.Fraction} {lower middle upper : GaussianInt.Pair.Basic.ConvergentPair}
    (first : Best.Consecutive.Basic.AreConsecutiveBest source.value lower middle)
    (second : Best.Consecutive.Basic.AreConsecutiveBest source.value middle upper) :
    Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value lower middle +
        Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value middle upper ≤
      Dirichlet.Window.Block.dyadicTwoWindowSumBound := by
  have firstBound :=
    Dirichlet.Window.IndexOne.Bounds.AreConsecutiveBest.dirichletWindowQuadrance_le_sharpDyadicUniversalWindowBound
      first
  have secondBound :=
    Dirichlet.Window.IndexOne.Bounds.AreConsecutiveBest.dirichletWindowQuadrance_le_sharpDyadicUniversalWindowBound
      second
  calc
    Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value lower middle +
        Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value middle upper ≤
        Dirichlet.Window.IndexOne.Bounds.sharpIndexOneWindowBound +
          Dirichlet.Window.IndexOne.Bounds.sharpIndexOneWindowBound :=
      Fraction.Order.Arithmetic.add_le_add_direct firstBound secondBound
    _ = Dirichlet.Window.Block.dyadicTwoWindowSumBound := by
      unfold Dirichlet.Window.Block.dyadicTwoWindowSumBound
        Dirichlet.Window.IndexOne.Bounds.sharpIndexOneWindowBound
        Dirichlet.Window.IndexOne.Chambers.firstRegionWindowBound
      rw [Data.Rat.SignedFraction.Arithmetic.ofFraction_addFraction]
      apply Data.Rat.SignedFraction.Normalization.ofFraction_eq_of_equivalent
      change ((256 * 205 + 256 * 205) * 205 : Int) =
        512 * (205 * 205)
      ring1

/-- Every displayed point of the exact root-free quadratic cut scales the
sum of two successive windows by at most two. -/
theorem
  gapThreshold_mul_dirichletWindowQuadrance_add_le_two
    {source : GaussianInt.Fraction} {lower middle upper : GaussianInt.Pair.Basic.ConvergentPair}
    (gap : Fraction.Rational)
    (certificate : Dirichlet.Window.IndexTwo.Optimal.IsCenteredGapThreshold gap)
    (first : Best.Consecutive.Basic.AreConsecutiveBest source.value lower middle)
    (second : Best.Consecutive.Basic.AreConsecutiveBest source.value middle upper) :
    gap * (Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value lower middle +
      Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value middle upper) ≤ 2 := by
  have firstBound :=
    Dirichlet.Window.IndexOne.Bounds.AreConsecutiveBest.gapThreshold_mul_dirichletWindow_le_one
      gap certificate first
  have secondBound :=
    Dirichlet.Window.IndexOne.Bounds.AreConsecutiveBest.gapThreshold_mul_dirichletWindow_le_one
      gap certificate second
  calc
    gap * (Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value lower middle +
        Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value middle upper) =
        gap * Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value lower middle +
          gap * Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value middle upper := by ring1
    _ ≤ 1 + 1 :=
      Fraction.Order.Arithmetic.add_le_add_direct firstBound secondBound
    _ = 2 := by ring1

/-- The finite-octant one-window theorem bounds two successive squared
windows by four. -/
theorem dirichletWindowQuadrance_add_le_four
    {source : GaussianInt.Fraction} {lower middle upper : GaussianInt.Pair.Basic.ConvergentPair}
    (first : Best.Consecutive.Basic.AreConsecutiveBest source.value lower middle)
    (second : Best.Consecutive.Basic.AreConsecutiveBest source.value middle upper) :
    Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value lower middle +
        Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value middle upper ≤ 4 := by
  have firstBound :=
    Dirichlet.Window.IndexOne.Bounds.AreConsecutiveBest.dirichletWindowQuadrance_le_two
      first
  have secondBound :=
    Dirichlet.Window.IndexOne.Bounds.AreConsecutiveBest.dirichletWindowQuadrance_le_two
      second
  calc
    Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value lower middle +
        Dirichlet.Window.SourceBound.dirichletWindowQuadrance source.value middle upper ≤ 2 + 2 :=
      Fraction.Order.Arithmetic.add_le_add_direct firstBound secondBound
    _ = 4 := by ring1

end Purelib.NumberTheory.Approximation.Dirichlet.Window.Block

end
