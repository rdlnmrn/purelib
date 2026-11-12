module
import Purelib.Data.GaussianInt.Pair.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.GaussianInt.Fraction.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Nat.Remainder.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.NumberTheory.Approximation.Best.Consecutive.Basic
import Purelib.NumberTheory.Approximation.Dirichlet.Window.Basic
import Purelib.NumberTheory.Approximation.Dirichlet.Window.Block
public import Purelib.NumberTheory.Approximation.Dirichlet.Window.IndexOne.Bounds
import Purelib.NumberTheory.Approximation.Dirichlet.Window.IndexTwo.Bounds
import Purelib.NumberTheory.Approximation.Dirichlet.Window.IndexTwo.Optimal
import Purelib.NumberTheory.Approximation.Dirichlet.Window.SourceBound

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.GaussianInt.Pair.LinearCombination
import Purelib.NumberTheory.Approximation.Best.Consecutive.Index
public import Batteries.Data.List.Basic
public import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Data.GaussianInt.Pair
open Purelib.Data.Rat.Fraction.Order

open Purelib.Data

open Purelib.Data.Rat

open Purelib.NumberTheory.Approximation

section
@[expose] public section

/-!
# Finite chains of Dirichlet windows

This file packages the adjacent-window result over one supplied finite list
of best pairs.  The chain predicate checks only neighbouring records.  Its
computed index and window lists therefore have one entry per transition, and
the exclusion of successive index two gives an explicit alternating-pattern
bound on their finite sums.
-/

namespace Purelib.NumberTheory.Approximation.Dirichlet.Window.Chain

/-- Structural tail recursion for adjacent coefficient-index quadrances. -/
@[simp] private def coefficientIndexQuadrancesFrom
  (lower : Basic.ConvergentPair) :
    List Basic.ConvergentPair → List Nat
  | [] => []
  | upper :: rest =>
      LinearCombination.coefficientIndexQuadrance lower upper ::
        Chain.coefficientIndexQuadrancesFrom upper rest

/-- Exposed implementation of the same finite adjacent-index calculation. -/
@[simp] def coefficientIndexQuadrancesFromExposed
  (lower : Basic.ConvergentPair) :
    List Basic.ConvergentPair → List Nat
  | [] => []
  | upper :: rest =>
      LinearCombination.coefficientIndexQuadrance lower upper ::
        Chain.coefficientIndexQuadrancesFromExposed upper rest

/-- The exposed coefficient-index recursion returns exactly the list computed by the private recursion. -/
private theorem
  coefficientIndexQuadrancesFromExposed_eq_private
    (lower : Basic.ConvergentPair) (pairs : List Basic.ConvergentPair) :
    coefficientIndexQuadrancesFromExposed lower pairs =
      coefficientIndexQuadrancesFrom lower pairs := by
  induction pairs generalizing lower with
  | nil => rfl
  | cons upper rest inductionHypothesis =>
      change LinearCombination.coefficientIndexQuadrance lower upper ::
          coefficientIndexQuadrancesFromExposed upper rest =
        LinearCombination.coefficientIndexQuadrance lower upper ::
          coefficientIndexQuadrancesFrom upper rest
      exact congrArg (List.cons (LinearCombination.coefficientIndexQuadrance lower upper))
        (inductionHypothesis upper)

/-- One coefficient-index quadrance for each adjacent pair in a supplied
finite list. -/
def coefficientIndexQuadrances : List
  Basic.ConvergentPair → List Nat
  | [] => []
  | lower :: rest => coefficientIndexQuadrancesFromExposed lower rest

/-- Structural tail recursion for adjacent squared Dirichlet windows. -/
@[simp] private def dirichletWindowQuadrancesFrom
    (source : Gaussian.Basic.Canonical) (lower : Basic.ConvergentPair) :
    List Basic.ConvergentPair → List Fraction.Rational
  | [] => []
  | upper :: rest =>
      SourceBound.dirichletWindowQuadrance source lower upper ::
        Chain.dirichletWindowQuadrancesFrom source upper rest

/-- Exposed implementation of the same finite adjacent-window calculation. -/
@[simp] def dirichletWindowQuadrancesFromExposed
    (source : Gaussian.Basic.Canonical) (lower : Basic.ConvergentPair) :
    List Basic.ConvergentPair → List Fraction.Rational
  | [] => []
  | upper :: rest =>
      SourceBound.dirichletWindowQuadrance source lower upper ::
        Chain.dirichletWindowQuadrancesFromExposed source upper rest

/-- The exposed window-quadrance recursion returns exactly the list computed by the private recursion. -/
private theorem
  dirichletWindowQuadrancesFromExposed_eq_private
    (source : Gaussian.Basic.Canonical) (lower : Basic.ConvergentPair) (pairs : List
      Basic.ConvergentPair) :
    dirichletWindowQuadrancesFromExposed source lower pairs =
      dirichletWindowQuadrancesFrom source lower pairs := by
  induction pairs generalizing lower with
  | nil => rfl
  | cons upper rest inductionHypothesis =>
      change SourceBound.dirichletWindowQuadrance source lower upper ::
          dirichletWindowQuadrancesFromExposed source upper rest =
        SourceBound.dirichletWindowQuadrance source lower upper ::
          dirichletWindowQuadrancesFrom source upper rest
      exact congrArg (List.cons (SourceBound.dirichletWindowQuadrance source lower upper))
        (inductionHypothesis upper)

/-- One exact squared Dirichlet-window product for each adjacent pair in a
supplied finite list. -/
def dirichletWindowQuadrances
    (source : Gaussian.Basic.Canonical) : List Basic.ConvergentPair → List Fraction.Rational
  | [] => []
  | lower :: rest => dirichletWindowQuadrancesFromExposed source lower rest

/-- Window quadrances and coefficient-index quadrances have the same number of adjacent-pair entries. -/
theorem
  dirichletWindowQuadrances_length_eq_coefficientIndexQuadrances_length
    (source : Gaussian.Basic.Canonical) (pairs : List Basic.ConvergentPair) :
    (dirichletWindowQuadrances source pairs).length =
      (coefficientIndexQuadrances pairs).length := by
  match pairs with
  | [] => rfl
  | [_] => rfl
  | _ :: upper :: rest =>
      simp only [dirichletWindowQuadrances,
        dirichletWindowQuadrancesFromExposed,
        coefficientIndexQuadrances, coefficientIndexQuadrancesFromExposed,
        List.length_cons]
      exact congrArg Nat.succ

          (dirichletWindowQuadrances_length_eq_coefficientIndexQuadrances_length
          source (upper :: rest))
termination_by pairs.length
decreasing_by
  all_goals
    simp only [-eq_self, -iff_self, List.length_cons]
    omega0

/-- Along a finite chain of consecutive best levels, the sum of the
coefficient indices obeys the exact alternating-pattern inequality.  The
parity term records the possible final unpaired index-two transition. -/
theorem
  two_mul_coefficientIndexQuadrances_sum_le_with_parity
    {source : GaussianInt.Fraction} (pairs : List Basic.ConvergentPair)
    (chain : pairs.IsChain (Best.Consecutive.Basic.AreConsecutiveBest source.value)) :
    2 * (coefficientIndexQuadrances pairs).sum ≤
      3 * (coefficientIndexQuadrances pairs).length +
        (coefficientIndexQuadrances pairs).length % 2 := by
  match pairs with
  | [] => exact Nat.le_refl 0
  | [_] => exact Nat.le_refl 0
  | [lower, upper] =>
      have consecutive : Best.Consecutive.Basic.AreConsecutiveBest source.value lower upper :=
        (List.isChain_cons_cons.mp chain).1
      have indexBound := (Best.Consecutive.Index.AreConsecutiveBest.coefficientIndexQuadrance_le_two consecutive)
      simp only [coefficientIndexQuadrances,
        coefficientIndexQuadrancesFromExposed,
        List.sum_cons, List.sum_nil, Nat.add_zero, List.length_cons,
        List.length_nil]
      simpa only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceMod]
        using Nat.mul_le_mul_left 2 indexBound
  | lower :: middle :: upper :: rest =>
      have first : Best.Consecutive.Basic.AreConsecutiveBest source.value lower middle :=
        (List.isChain_cons_cons.mp chain).1
      have middleChain :
          (middle :: upper :: rest).IsChain
            (Best.Consecutive.Basic.AreConsecutiveBest source.value) :=
        (List.isChain_cons_cons.mp chain).2
      have second : Best.Consecutive.Basic.AreConsecutiveBest source.value middle upper :=
        (List.isChain_cons_cons.mp middleChain).1
      have tailChain :
          (upper :: rest).IsChain (Best.Consecutive.Basic.AreConsecutiveBest source.value) :=
        (List.isChain_cons_cons.mp middleChain).2
      have firstTwoBound :=
        Block.coefficientIndexQuadrance_add_le_three first second
      have tailBound :=
        Chain.two_mul_coefficientIndexQuadrances_sum_le_with_parity
          (upper :: rest) tailChain
      simp only [coefficientIndexQuadrances,
        coefficientIndexQuadrancesFromExposed,
        List.sum_cons, List.length_cons]
      have firstScaled := Nat.mul_le_mul_left 2 firstTwoBound
      have added := Nat.add_le_add firstScaled tailBound
      calc
        2 * (LinearCombination.coefficientIndexQuadrance lower middle +
            (LinearCombination.coefficientIndexQuadrance middle upper +
              (coefficientIndexQuadrances (upper :: rest)).sum)) =
            2 * (LinearCombination.coefficientIndexQuadrance lower middle +
              LinearCombination.coefficientIndexQuadrance middle upper) +
              2 * (coefficientIndexQuadrances (upper :: rest)).sum := by
          ring1
        _ ≤ 2 * 3 +
            (3 * (coefficientIndexQuadrances (upper :: rest)).length +
              (coefficientIndexQuadrances (upper :: rest)).length % 2) :=
          added
        _ = 3 * ((coefficientIndexQuadrances (upper :: rest)).length + 1 + 1) +
            ((coefficientIndexQuadrances (upper :: rest)).length + 1 + 1) % 2 := by
          rw [show (coefficientIndexQuadrances (upper :: rest)).length + 1 + 1 =
            (coefficientIndexQuadrances (upper :: rest)).length + 2 by ring1,
            show ((coefficientIndexQuadrances (upper :: rest)).length + 2) % 2 =
                (coefficientIndexQuadrances (upper :: rest)).length % 2 from
              (Nat.Remainder.Arithmetic.add_mod_right
                (coefficientIndexQuadrances (upper :: rest)).length 2 2).symm]
          ring1
termination_by pairs.length
decreasing_by
  all_goals
    simp only [-eq_self, -iff_self, List.length_cons]
    omega0

/-- Parity-free consequence of the exact alternating-pattern bound. -/
theorem two_mul_coefficientIndexQuadrances_sum_le
    {source : GaussianInt.Fraction} (pairs : List Basic.ConvergentPair)
    (chain : pairs.IsChain (Best.Consecutive.Basic.AreConsecutiveBest source.value)) :
    2 * (coefficientIndexQuadrances pairs).sum ≤
      3 * (coefficientIndexQuadrances pairs).length + 1 := by
  have parityBound :=
    two_mul_coefficientIndexQuadrances_sum_le_with_parity pairs chain
  have remainderLt :
      (coefficientIndexQuadrances pairs).length % 2 < 2 :=
    Nat.mod_lt _ (by decide)
  exact parityBound.trans
    (Nat.add_le_add_left (Nat.lt_succ_iff.mp remainderLt) _)

/-- Summing the one-window quadratic-threshold certificates over a finite
displayed chain bounds the scaled sum by the sum of its coefficient indices. -/
theorem
  quadraticThreshold_mul_dirichletWindowQuadrances_sum_le_indexSum
    {source : GaussianInt.Fraction} (pairs : List Basic.ConvergentPair)
    (chain : pairs.IsChain (Best.Consecutive.Basic.AreConsecutiveBest source.value))
    (threshold : Fraction.Rational)
    (thresholdLtHalf : threshold < (1 / 2 : Fraction.Rational))
    (thresholdPolynomialNonnegative :
      0 ≤ threshold ^ 2 - 3 * threshold + 1 / 4) :
    threshold * (dirichletWindowQuadrances source.value pairs).sum ≤
      ((coefficientIndexQuadrances pairs).sum : Fraction.Rational) := by
  match pairs with
  | [] =>
      change threshold * (0 : Fraction.Rational) ≤ 0
      rewrite [Fraction.Field.mul_zero_direct]
      exact Basic.le_refl 0
  | [_] =>
      change threshold * (0 : Fraction.Rational) ≤ 0
      rewrite [Fraction.Field.mul_zero_direct]
      exact Basic.le_refl 0
  | lower :: upper :: rest =>
      have consecutive : Best.Consecutive.Basic.AreConsecutiveBest source.value lower upper :=
        (List.isChain_cons_cons.mp chain).1
      have tailChain :
          (upper :: rest).IsChain (Best.Consecutive.Basic.AreConsecutiveBest source.value) :=
        (List.isChain_cons_cons.mp chain).2
      have firstBound :=
        Basic.AreConsecutiveBest.quadraticThreshold_mul_dirichletWindow_le_index
          consecutive threshold thresholdLtHalf
            thresholdPolynomialNonnegative
      have tailBound :=

          quadraticThreshold_mul_dirichletWindowQuadrances_sum_le_indexSum
          (upper :: rest) tailChain threshold thresholdLtHalf
            thresholdPolynomialNonnegative
      have addedBounds :=
        Arithmetic.add_le_add_direct firstBound tailBound
      simp only [dirichletWindowQuadrances,
        dirichletWindowQuadrancesFromExposed,
        coefficientIndexQuadrances, coefficientIndexQuadrancesFromExposed,
        List.sum_cons, Fraction.Cast.natCast_add_direct]
      calc
        threshold *
            (SourceBound.dirichletWindowQuadrance source.value lower upper +
              (dirichletWindowQuadrances source.value (upper :: rest)).sum) =
            threshold * SourceBound.dirichletWindowQuadrance source.value lower upper +
              threshold *
                (dirichletWindowQuadrances source.value (upper :: rest)).sum := by
          ring1
        _ ≤ (LinearCombination.coefficientIndexQuadrance lower upper : Fraction.Rational) +
              ((coefficientIndexQuadrances (upper :: rest)).sum : Fraction.Rational) :=
          addedBounds
termination_by pairs.length
decreasing_by
  all_goals
    simp only [-eq_self, -iff_self, List.length_cons]
    omega0

/-- Division-free finite-chain window certificate.  If a displayed rational
threshold passes the quadratic test, twice that threshold times the sum of
all chain windows is at most `3 * transitionCount + 1`. -/
theorem
  two_mul_quadraticThreshold_mul_dirichletWindowQuadrances_sum_le
    {source : GaussianInt.Fraction} (pairs : List Basic.ConvergentPair)
    (chain : pairs.IsChain (Best.Consecutive.Basic.AreConsecutiveBest source.value))
    (threshold : Fraction.Rational)
    (thresholdLtHalf : threshold < (1 / 2 : Fraction.Rational))
    (thresholdPolynomialNonnegative :
      0 ≤ threshold ^ 2 - 3 * threshold + 1 / 4) :
    2 * threshold * (dirichletWindowQuadrances source.value pairs).sum ≤
      (3 * (coefficientIndexQuadrances pairs).length + 1 : Nat) := by
  have windowSumBound :=
    quadraticThreshold_mul_dirichletWindowQuadrances_sum_le_indexSum pairs
      chain threshold thresholdLtHalf thresholdPolynomialNonnegative
  have scaledWindowSumBound :=
    Arithmetic.mul_le_mul_of_nonneg_left_direct windowSumBound
      (show (0 : Fraction.Rational) ≤ 2 by decide)
  have indexSumBound :=
    two_mul_coefficientIndexQuadrances_sum_le pairs chain
  have castIndexSumBound :
      ((2 * (coefficientIndexQuadrances pairs).sum : Nat) : Fraction.Rational) ≤
        (3 * (coefficientIndexQuadrances pairs).length + 1 : Nat) :=
    Fraction.Cast.Order.natCast_le_direct indexSumBound
  calc
    2 * threshold * (dirichletWindowQuadrances source.value pairs).sum =
        2 *
          (threshold *
            (dirichletWindowQuadrances source.value pairs).sum) := by
      ring1
    _ ≤ 2 * ((coefficientIndexQuadrances pairs).sum : Fraction.Rational) :=
      scaledWindowSumBound
    _ = ((2 * (coefficientIndexQuadrances pairs).sum : Nat) : Fraction.Rational) := by
      rw [Fraction.Cast.natCast_mul_direct, Nat.cast_ofNat]
    _ ≤ (3 * (coefficientIndexQuadrances pairs).length + 1 : Nat) :=
      castIndexSumBound

/-- Exact parity-sensitive finite-chain window certificate. -/
theorem
  two_mul_quadraticThreshold_mul_dirichletWindowQuadrances_sum_le_with_parity
    {source : GaussianInt.Fraction} (pairs : List Basic.ConvergentPair)
    (chain : pairs.IsChain (Best.Consecutive.Basic.AreConsecutiveBest source.value))
    (threshold : Fraction.Rational)
    (thresholdLtHalf : threshold < (1 / 2 : Fraction.Rational))
    (thresholdPolynomialNonnegative :
      0 ≤ threshold ^ 2 - 3 * threshold + 1 / 4) :
    2 * threshold * (dirichletWindowQuadrances source.value pairs).sum ≤
      (3 * (coefficientIndexQuadrances pairs).length +
        (coefficientIndexQuadrances pairs).length % 2 : Nat) := by
  have windowSumBound :=
    quadraticThreshold_mul_dirichletWindowQuadrances_sum_le_indexSum pairs
      chain threshold thresholdLtHalf thresholdPolynomialNonnegative
  have scaledWindowSumBound :=
    Arithmetic.mul_le_mul_of_nonneg_left_direct windowSumBound
      (show (0 : Fraction.Rational) ≤ 2 by decide)
  have indexSumBound :=
    two_mul_coefficientIndexQuadrances_sum_le_with_parity pairs chain
  have castIndexSumBound :
      ((2 * (coefficientIndexQuadrances pairs).sum : Nat) : Fraction.Rational) ≤
        (3 * (coefficientIndexQuadrances pairs).length +
          (coefficientIndexQuadrances pairs).length % 2 : Nat) :=
    Fraction.Cast.Order.natCast_le_direct indexSumBound
  calc
    2 * threshold * (dirichletWindowQuadrances source.value pairs).sum =
        2 *
          (threshold *
            (dirichletWindowQuadrances source.value pairs).sum) := by
      ring1
    _ ≤ 2 * ((coefficientIndexQuadrances pairs).sum : Fraction.Rational) :=
      scaledWindowSumBound
    _ = ((2 * (coefficientIndexQuadrances pairs).sum : Nat) : Fraction.Rational) := by
      rw [Fraction.Cast.natCast_mul_direct, Nat.cast_ofNat]
    _ ≤ (3 * (coefficientIndexQuadrances pairs).length +
          (coefficientIndexQuadrances pairs).length % 2 : Nat) :=
      castIndexSumBound

/-- Cancel any quadratic-certified threshold against a displayed nonnegative
reciprocal in the exact finite-chain inequality. -/
theorem
  two_mul_dirichletWindowQuadrances_sum_le_factor_mul_parityBound_of_quadraticThreshold
    {source : GaussianInt.Fraction} (pairs : List Basic.ConvergentPair)
    (chain : pairs.IsChain (Best.Consecutive.Basic.AreConsecutiveBest source.value))
    (threshold factor : Fraction.Rational)
    (thresholdLtHalf : threshold < (1 / 2 : Fraction.Rational))
    (thresholdPolynomialNonnegative :
      0 ≤ threshold ^ 2 - 3 * threshold + 1 / 4)
    (thresholdMulFactor : threshold * factor = 1)
    (factorNonnegative : 0 ≤ factor) :
    2 * (dirichletWindowQuadrances source.value pairs).sum ≤
      factor *
        (3 * (coefficientIndexQuadrances pairs).length +
          (coefficientIndexQuadrances pairs).length % 2 : Nat) := by
  have thresholdBound :=
    two_mul_quadraticThreshold_mul_dirichletWindowQuadrances_sum_le_with_parity
      pairs chain threshold thresholdLtHalf thresholdPolynomialNonnegative
  have scaledThresholdBound :=
    Arithmetic.mul_le_mul_of_nonneg_left_direct thresholdBound
      factorNonnegative
  calc
    2 * (dirichletWindowQuadrances source.value pairs).sum =
        2 * 1 *
          (dirichletWindowQuadrances source.value pairs).sum := by
      ring1
    _ =
        2 * (threshold * factor) *
          (dirichletWindowQuadrances source.value pairs).sum := by
      rw [thresholdMulFactor]
    _ = factor *
        (2 * threshold *
          (dirichletWindowQuadrances source.value pairs).sum) := by
      ring1
    _ ≤ factor *
        (3 * (coefficientIndexQuadrances pairs).length +
          (coefficientIndexQuadrances pairs).length % 2 : Nat) :=
      scaledThresholdBound

/-- Concrete specialization at the displayed threshold `35/408`, using its
exact reciprocal `408/35`. -/
theorem
  two_mul_dirichletWindowQuadrances_sum_le_refinedIndexFactor_mul_parityBound
    {source : GaussianInt.Fraction} (pairs : List Basic.ConvergentPair)
    (chain : pairs.IsChain (Best.Consecutive.Basic.AreConsecutiveBest source.value)) :
    2 * (dirichletWindowQuadrances source.value pairs).sum ≤
      Basic.refinedIndexFactor *
        (3 * (coefficientIndexQuadrances pairs).length +
          (coefficientIndexQuadrances pairs).length % 2 : Nat) :=
  two_mul_dirichletWindowQuadrances_sum_le_factor_mul_parityBound_of_quadraticThreshold
    pairs chain Basic.refinedGapThreshold
      Basic.refinedIndexFactor
      Basic.refinedGapThreshold_lt_half
      Basic.refinedGapThreshold_quadratic_nonnegative
      Basic.refinedGapThreshold_mul_refinedIndexFactor
      Basic.refinedIndexFactor_nonneg

/-- Sharper concrete finite-chain specialization at threshold `102/1189`. -/
theorem
  two_mul_dirichletWindowQuadrances_sum_le_quadraticIndexFactor_mul_parityBound
    {source : GaussianInt.Fraction} (pairs : List Basic.ConvergentPair)
    (chain : pairs.IsChain (Best.Consecutive.Basic.AreConsecutiveBest source.value)) :
    2 * (dirichletWindowQuadrances source.value pairs).sum ≤
      Basic.quadraticIndexFactor *
        (3 * (coefficientIndexQuadrances pairs).length +
          (coefficientIndexQuadrances pairs).length % 2 : Nat) :=
  two_mul_dirichletWindowQuadrances_sum_le_factor_mul_parityBound_of_quadraticThreshold
    pairs chain Basic.quadraticGapThreshold
      Basic.quadraticIndexFactor
      Basic.quadraticGapThreshold_lt_half
      Basic.quadraticGapThreshold_quadratic_nonnegative
      Basic.quadraticGapThreshold_mul_quadraticIndexFactor
      Basic.quadraticIndexFactor_nonneg

/-- The index-aware one-window bound accumulates directly along any supplied
finite chain.  Each transition contributes at most `1189/102`, independently
of its determinant index. -/
theorem
  dirichletWindowQuadrances_sum_le_quadraticIndexFactor_mul_length
    {source : GaussianInt.Fraction} (pairs : List Basic.ConvergentPair)
    (chain : pairs.IsChain (Best.Consecutive.Basic.AreConsecutiveBest source.value)) :
    (dirichletWindowQuadrances source.value pairs).sum ≤
      Basic.quadraticIndexFactor *
        ((coefficientIndexQuadrances pairs).length : Fraction.Rational) := by
  match pairs with
  | [] =>
      change (0 : Fraction.Rational) ≤ _ * (0 : Fraction.Rational)
      rewrite [Fraction.Field.mul_zero_direct]
      exact Basic.le_refl 0
  | [_] =>
      change (0 : Fraction.Rational) ≤ _ * (0 : Fraction.Rational)
      rewrite [Fraction.Field.mul_zero_direct]
      exact Basic.le_refl 0
  | lower :: upper :: rest =>
      have consecutive : Best.Consecutive.Basic.AreConsecutiveBest source.value lower upper :=
        (List.isChain_cons_cons.mp chain).1
      have tailChain :
          (upper :: rest).IsChain (Best.Consecutive.Basic.AreConsecutiveBest source.value) :=
        (List.isChain_cons_cons.mp chain).2
      have firstBound :=
        IndexTwo.Bounds.AreConsecutiveBest.dirichletWindowQuadrance_le_quadraticIndexFactorUniversal
          consecutive
      have tailBound :=

          dirichletWindowQuadrances_sum_le_quadraticIndexFactor_mul_length
          (upper :: rest) tailChain
      simp only [dirichletWindowQuadrances,
        dirichletWindowQuadrancesFromExposed,
        coefficientIndexQuadrances, coefficientIndexQuadrancesFromExposed,
        List.sum_cons, List.length_cons, Fraction.Cast.natCast_add_direct, Nat.cast_one]
      calc
        SourceBound.dirichletWindowQuadrance source.value lower upper +
            (dirichletWindowQuadrances source.value (upper :: rest)).sum ≤
            Basic.quadraticIndexFactor +
              Basic.quadraticIndexFactor *
                ((coefficientIndexQuadrances (upper :: rest)).length :
                  Fraction.Rational) :=
          Arithmetic.add_le_add_direct firstBound tailBound
        _ = Basic.quadraticIndexFactor *
            (((coefficientIndexQuadrances (upper :: rest)).length :
                Fraction.Rational) + 1) := by ring1

/-- The rational universal one-window bound accumulates directly along any
supplied finite chain. -/
theorem
  dirichletWindowQuadrances_sum_le_twentyEight_fifteenths_mul_length
    {source : GaussianInt.Fraction} (pairs : List Basic.ConvergentPair)
    (chain : pairs.IsChain (Best.Consecutive.Basic.AreConsecutiveBest source.value)) :
    (dirichletWindowQuadrances source.value pairs).sum ≤
      (28 / 15 : Fraction.Rational) *
        ((coefficientIndexQuadrances pairs).length : Fraction.Rational) := by
  match pairs with
  | [] =>
      change (0 : Fraction.Rational) ≤ _ * (0 : Fraction.Rational)
      rewrite [Fraction.Field.mul_zero_direct]
      exact Basic.le_refl 0
  | [_] =>
      change (0 : Fraction.Rational) ≤ _ * (0 : Fraction.Rational)
      rewrite [Fraction.Field.mul_zero_direct]
      exact Basic.le_refl 0
  | lower :: upper :: rest =>
      have consecutive : Best.Consecutive.Basic.AreConsecutiveBest source.value lower upper :=
        (List.isChain_cons_cons.mp chain).1
      have tailChain :
          (upper :: rest).IsChain (Best.Consecutive.Basic.AreConsecutiveBest source.value) :=
        (List.isChain_cons_cons.mp chain).2
      have firstBound :=
        IndexOne.Bounds.AreConsecutiveBest.dirichletWindowQuadrance_le_twentyEight_fifteenths
          consecutive
      have tailBound :=

          dirichletWindowQuadrances_sum_le_twentyEight_fifteenths_mul_length
          (upper :: rest) tailChain
      simp only [dirichletWindowQuadrances,
        dirichletWindowQuadrancesFromExposed,
        coefficientIndexQuadrances, coefficientIndexQuadrancesFromExposed,
        List.sum_cons, List.length_cons, Fraction.Cast.natCast_add_direct, Nat.cast_one]
      calc
        SourceBound.dirichletWindowQuadrance source.value lower upper +
            (dirichletWindowQuadrances source.value (upper :: rest)).sum ≤
            (28 / 15 : Fraction.Rational) +
              (28 / 15 : Fraction.Rational) *
                ((coefficientIndexQuadrances (upper :: rest)).length :
                  Fraction.Rational) :=
          Arithmetic.add_le_add_direct firstBound tailBound
        _ = (28 / 15 : Fraction.Rational) *
            (((coefficientIndexQuadrances (upper :: rest)).length :
                Fraction.Rational) + 1) := by ring1

/-- The norm-two-coefficient universal one-window bound accumulates directly
along any supplied finite chain. -/
theorem
  dirichletWindowQuadrances_sum_le_normTwoUniversalWindowBound_mul_length
    {source : GaussianInt.Fraction} (pairs : List Basic.ConvergentPair)
    (chain : pairs.IsChain (Best.Consecutive.Basic.AreConsecutiveBest source.value)) :
    (dirichletWindowQuadrances source.value pairs).sum ≤
      IndexOne.Bounds.normTwoIndexOneWindowBound *
        ((coefficientIndexQuadrances pairs).length : Fraction.Rational) := by
  match pairs with
  | [] =>
      change (0 : Fraction.Rational) ≤ _ * (0 : Fraction.Rational)
      rewrite [Fraction.Field.mul_zero_direct]
      exact Basic.le_refl 0
  | [_] =>
      change (0 : Fraction.Rational) ≤ _ * (0 : Fraction.Rational)
      rewrite [Fraction.Field.mul_zero_direct]
      exact Basic.le_refl 0
  | lower :: upper :: rest =>
      have consecutive : Best.Consecutive.Basic.AreConsecutiveBest source.value lower upper :=
        (List.isChain_cons_cons.mp chain).1
      have tailChain :
          (upper :: rest).IsChain (Best.Consecutive.Basic.AreConsecutiveBest source.value) :=
        (List.isChain_cons_cons.mp chain).2
      have firstBound :=
        IndexOne.Bounds.AreConsecutiveBest.dirichletWindowQuadrance_le_normTwoUniversalWindowBound
          consecutive
      have tailBound :=

          dirichletWindowQuadrances_sum_le_normTwoUniversalWindowBound_mul_length
          (upper :: rest) tailChain
      simp only [dirichletWindowQuadrances,
        dirichletWindowQuadrancesFromExposed,
        coefficientIndexQuadrances, coefficientIndexQuadrancesFromExposed,
        List.sum_cons, List.length_cons, Fraction.Cast.natCast_add_direct, Nat.cast_one]
      calc
        SourceBound.dirichletWindowQuadrance source.value lower upper +
            (dirichletWindowQuadrances source.value (upper :: rest)).sum ≤
            IndexOne.Bounds.normTwoIndexOneWindowBound +
              IndexOne.Bounds.normTwoIndexOneWindowBound *
                ((coefficientIndexQuadrances (upper :: rest)).length :
                  Fraction.Rational) :=
          Arithmetic.add_le_add_direct firstBound tailBound
        _ = IndexOne.Bounds.normTwoIndexOneWindowBound *
            (((coefficientIndexQuadrances (upper :: rest)).length :
                Fraction.Rational) + 1) := by ring1

/-- The dyadic near-optimal one-window bound accumulates directly along any
supplied finite chain. -/
theorem
  dirichletWindowQuadrances_sum_le_sharpDyadicUniversalWindowBound_mul_length
    {source : GaussianInt.Fraction} (pairs : List Basic.ConvergentPair)
    (chain : pairs.IsChain (Best.Consecutive.Basic.AreConsecutiveBest source.value)) :
    (dirichletWindowQuadrances source.value pairs).sum ≤
      IndexOne.Bounds.sharpIndexOneWindowBound *
        ((coefficientIndexQuadrances pairs).length : Fraction.Rational) := by
  match pairs with
  | [] =>
      change (0 : Fraction.Rational) ≤ _ * (0 : Fraction.Rational)
      rewrite [Fraction.Field.mul_zero_direct]
      exact Basic.le_refl 0
  | [_] =>
      change (0 : Fraction.Rational) ≤ _ * (0 : Fraction.Rational)
      rewrite [Fraction.Field.mul_zero_direct]
      exact Basic.le_refl 0
  | lower :: upper :: rest =>
      have consecutive : Best.Consecutive.Basic.AreConsecutiveBest source.value lower upper :=
        (List.isChain_cons_cons.mp chain).1
      have tailChain :
          (upper :: rest).IsChain (Best.Consecutive.Basic.AreConsecutiveBest source.value) :=
        (List.isChain_cons_cons.mp chain).2
      have firstBound :=
        IndexOne.Bounds.AreConsecutiveBest.dirichletWindowQuadrance_le_sharpDyadicUniversalWindowBound
          consecutive
      have tailBound :=

          dirichletWindowQuadrances_sum_le_sharpDyadicUniversalWindowBound_mul_length
          (upper :: rest) tailChain
      simp only [dirichletWindowQuadrances,
        dirichletWindowQuadrancesFromExposed,
        coefficientIndexQuadrances, coefficientIndexQuadrancesFromExposed,
        List.sum_cons, List.length_cons, Fraction.Cast.natCast_add_direct, Nat.cast_one]
      calc
        SourceBound.dirichletWindowQuadrance source.value lower upper +
            (dirichletWindowQuadrances source.value (upper :: rest)).sum ≤
            IndexOne.Bounds.sharpIndexOneWindowBound +
              IndexOne.Bounds.sharpIndexOneWindowBound *
                ((coefficientIndexQuadrances (upper :: rest)).length :
                  Fraction.Rational) :=
          Arithmetic.add_le_add_direct firstBound tailBound
        _ = IndexOne.Bounds.sharpIndexOneWindowBound *
            (((coefficientIndexQuadrances (upper :: rest)).length :
                Fraction.Rational) + 1) := by ring1

/-- Every displayed point of the exact root-free quadratic cut scales the
sum along a supplied finite best chain by at most its transition count. -/
theorem
  gapThreshold_mul_dirichletWindowQuadrances_sum_le_length
    {source : GaussianInt.Fraction} (gap : Fraction.Rational)
    (certificate : IndexTwo.Optimal.IsCenteredGapThreshold gap)
    (pairs : List Basic.ConvergentPair)
    (chain : pairs.IsChain (Best.Consecutive.Basic.AreConsecutiveBest source.value)) :
    gap * (dirichletWindowQuadrances source.value pairs).sum ≤
      ((coefficientIndexQuadrances pairs).length : Fraction.Rational) := by
  match pairs with
  | [] =>
      change gap * (0 : Fraction.Rational) ≤ 0
      rewrite [Fraction.Field.mul_zero_direct]
      exact Basic.le_refl 0
  | [_] =>
      change gap * (0 : Fraction.Rational) ≤ 0
      rewrite [Fraction.Field.mul_zero_direct]
      exact Basic.le_refl 0
  | lower :: upper :: rest =>
      have consecutive : Best.Consecutive.Basic.AreConsecutiveBest source.value lower upper :=
        (List.isChain_cons_cons.mp chain).1
      have tailChain :
          (upper :: rest).IsChain (Best.Consecutive.Basic.AreConsecutiveBest source.value) :=
        (List.isChain_cons_cons.mp chain).2
      have firstBound :=
        IndexOne.Bounds.AreConsecutiveBest.gapThreshold_mul_dirichletWindow_le_one
          gap certificate consecutive
      have tailBound :=

          gapThreshold_mul_dirichletWindowQuadrances_sum_le_length
          gap
          certificate (upper :: rest) tailChain
      simp only [dirichletWindowQuadrances,
        dirichletWindowQuadrancesFromExposed,
        coefficientIndexQuadrances, coefficientIndexQuadrancesFromExposed,
        List.sum_cons, List.length_cons, Fraction.Cast.natCast_add_direct, Nat.cast_one]
      calc
        gap * (SourceBound.dirichletWindowQuadrance source.value lower upper +
            (dirichletWindowQuadrances source.value (upper :: rest)).sum) =
            gap * SourceBound.dirichletWindowQuadrance source.value lower upper +
              gap * (dirichletWindowQuadrances source.value
                (upper :: rest)).sum := by ring1
        _ ≤ 1 +
            ((coefficientIndexQuadrances (upper :: rest)).length :
              Fraction.Rational) :=
          Arithmetic.add_le_add_direct firstBound tailBound
        _ = ((coefficientIndexQuadrances (upper :: rest)).length :
              Fraction.Rational) + 1 := by ring1

/-- Clearing the denominator in the direct chain accumulation gives the
integer-coefficient certificate `15 * sum ≤ 28 * transitionCount`. -/
theorem
  fifteen_mul_dirichletWindowQuadrances_sum_le_twentyEight_mul_length
    {source : GaussianInt.Fraction} (pairs : List Basic.ConvergentPair)
    (chain : pairs.IsChain (Best.Consecutive.Basic.AreConsecutiveBest source.value)) :
    15 * (dirichletWindowQuadrances source.value pairs).sum ≤
      (28 * (coefficientIndexQuadrances pairs).length : Nat) := by
  have sumBound :=
    dirichletWindowQuadrances_sum_le_twentyEight_fifteenths_mul_length
      pairs chain
  have scaled :=
    Arithmetic.mul_le_mul_of_nonneg_left_direct sumBound
      (show (0 : Fraction.Rational) ≤ 15 by decide)
  calc
    15 * (dirichletWindowQuadrances source.value pairs).sum ≤
        15 * ((28 / 15 : Fraction.Rational) *
          ((coefficientIndexQuadrances pairs).length : Fraction.Rational)) := scaled
    _ = (28 * (coefficientIndexQuadrances pairs).length : Nat) := by
      rw [Fraction.Cast.natCast_mul_direct, Nat.cast_ofNat]
      have cancellation : (15 : Fraction.Rational) * (28 / 15) = 28 := by decide
      rw [← Fraction.Field.mul_assoc, cancellation]

/-- Compatibility with the earlier parity-sensitive statement.  The new
direct accumulation is strictly stronger and no parity correction is needed. -/
theorem
  fifteen_mul_dirichletWindowQuadrances_sum_le_with_parity
    {source : GaussianInt.Fraction} (pairs : List Basic.ConvergentPair)
    (chain : pairs.IsChain (Best.Consecutive.Basic.AreConsecutiveBest source.value)) :
    15 * (dirichletWindowQuadrances source.value pairs).sum ≤
      (29 * (coefficientIndexQuadrances pairs).length +
        (coefficientIndexQuadrances pairs).length % 2 : Nat) := by
  have direct :=
    fifteen_mul_dirichletWindowQuadrances_sum_le_twentyEight_mul_length
      pairs chain
  have naturalBound :
      28 * (coefficientIndexQuadrances pairs).length ≤
        29 * (coefficientIndexQuadrances pairs).length +
          (coefficientIndexQuadrances pairs).length % 2 := by
    exact (Nat.mul_le_mul_right _ (show 28 ≤ 29 by decide)).trans
      (Nat.le_add_right _ _)
  exact direct.trans
    (Fraction.Cast.Order.natCast_le_direct naturalBound)

/-- The exact universal one-window bound accumulates directly along any
supplied finite chain.  Each transition contributes at most two. -/
theorem dirichletWindowQuadrances_sum_le_two_mul_length
    {source : GaussianInt.Fraction} (pairs : List Basic.ConvergentPair)
    (chain : pairs.IsChain (Best.Consecutive.Basic.AreConsecutiveBest source.value)) :
    (dirichletWindowQuadrances source.value pairs).sum ≤
      2 * ((coefficientIndexQuadrances pairs).length : Fraction.Rational) := by
  match pairs with
  | [] =>
      change (0 : Fraction.Rational) ≤ _ * (0 : Fraction.Rational)
      rewrite [Fraction.Field.mul_zero_direct]
      exact Basic.le_refl 0
  | [_] =>
      change (0 : Fraction.Rational) ≤ _ * (0 : Fraction.Rational)
      rewrite [Fraction.Field.mul_zero_direct]
      exact Basic.le_refl 0
  | lower :: upper :: rest =>
      have consecutive : Best.Consecutive.Basic.AreConsecutiveBest source.value lower upper :=
        (List.isChain_cons_cons.mp chain).1
      have tailChain :
          (upper :: rest).IsChain (Best.Consecutive.Basic.AreConsecutiveBest source.value) :=
        (List.isChain_cons_cons.mp chain).2
      have firstBound :=
        IndexOne.Bounds.AreConsecutiveBest.dirichletWindowQuadrance_le_two
          consecutive
      have tailBound :=
        Chain.dirichletWindowQuadrances_sum_le_two_mul_length
          (upper :: rest) tailChain
      simp only [dirichletWindowQuadrances,
        dirichletWindowQuadrancesFromExposed,
        coefficientIndexQuadrances, coefficientIndexQuadrancesFromExposed,
        List.sum_cons, List.length_cons, Fraction.Cast.natCast_add_direct, Nat.cast_one]
      calc
        SourceBound.dirichletWindowQuadrance source.value lower upper +
            (dirichletWindowQuadrances source.value (upper :: rest)).sum ≤
            2 + 2 *
              ((coefficientIndexQuadrances (upper :: rest)).length :
                Fraction.Rational) :=
          Arithmetic.add_le_add_direct firstBound tailBound
        _ = 2 *
            (((coefficientIndexQuadrances (upper :: rest)).length :
                Fraction.Rational) + 1) := by ring1

end Purelib.NumberTheory.Approximation.Dirichlet.Window.Chain

end
