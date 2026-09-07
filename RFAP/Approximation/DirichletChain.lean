import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import RFAP.Approximation.DirichletBlock

/-!
# Finite chains of Dirichlet windows

This file packages the adjacent-window result over one supplied finite list
of best pairs.  The chain predicate checks only neighbouring records.  Its
computed index and window lists therefore have one entry per transition, and
the exclusion of successive index two gives an explicit alternating-pattern
bound on their finite sums.
-/

namespace RFAP.DirichletChain

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Pair := RFAP.HurwitzRational.ConvergentPair

open RFAP.BestApproximation

/-- Structural tail recursion for adjacent coefficient-index quadrances. -/
@[simp] private def coefficientIndexQuadrancesFrom (lower : Pair) :
    List Pair → List Nat
  | [] => []
  | upper :: rest =>
      coefficientIndexQuadrance lower upper ::
        coefficientIndexQuadrancesFrom upper rest

/-- One coefficient-index quadrance for each adjacent pair in a supplied
finite list. -/
def coefficientIndexQuadrances : List Pair → List Nat
  | [] => []
  | lower :: rest => coefficientIndexQuadrancesFrom lower rest

/-- Structural tail recursion for adjacent squared Dirichlet windows. -/
@[simp] private def dirichletWindowQuadrancesFrom
    (source : RFAP.ConstructiveGaussian.Gaussian) (lower : Pair) :
    List Pair → List Coordinate
  | [] => []
  | upper :: rest =>
      dirichletWindowQuadrance source lower upper ::
        dirichletWindowQuadrancesFrom source upper rest

/-- One exact squared Dirichlet-window product for each adjacent pair in a
supplied finite list. -/
def dirichletWindowQuadrances
    (source : RFAP.ConstructiveGaussian.Gaussian) : List Pair → List Coordinate
  | [] => []
  | lower :: rest => dirichletWindowQuadrancesFrom source lower rest

theorem dirichletWindowQuadrances_length_eq_coefficientIndexQuadrances_length
    (source : RFAP.ConstructiveGaussian.Gaussian) (pairs : List Pair) :
    (dirichletWindowQuadrances source pairs).length =
      (coefficientIndexQuadrances pairs).length := by
  match pairs with
  | [] => simp [dirichletWindowQuadrances, coefficientIndexQuadrances]
  | [_] => simp [dirichletWindowQuadrances, coefficientIndexQuadrances]
  | _ :: upper :: rest =>
      simp only [dirichletWindowQuadrances, dirichletWindowQuadrancesFrom,
        coefficientIndexQuadrances, coefficientIndexQuadrancesFrom,
        List.length_cons]
      exact congrArg Nat.succ
        (dirichletWindowQuadrances_length_eq_coefficientIndexQuadrances_length
          source (upper :: rest))
termination_by pairs.length

/-- Along a finite chain of consecutive best levels, the sum of the
coefficient indices obeys the exact alternating-pattern inequality.  The
parity term records the possible final unpaired index-two transition. -/
theorem two_mul_coefficientIndexQuadrances_sum_le_with_parity
    {source : RFAP.HurwitzRational.Fraction} (pairs : List Pair)
    (chain : pairs.IsChain (AreConsecutiveBest source.value)) :
    2 * (coefficientIndexQuadrances pairs).sum ≤
      3 * (coefficientIndexQuadrances pairs).length +
        (coefficientIndexQuadrances pairs).length % 2 := by
  match pairs with
  | [] => simp [coefficientIndexQuadrances]
  | [_] => simp [coefficientIndexQuadrances]
  | [lower, upper] =>
      have consecutive : AreConsecutiveBest source.value lower upper :=
        (List.isChain_cons_cons.mp chain).1
      have indexBound := consecutive.coefficientIndexQuadrance_le_two
      simp only [coefficientIndexQuadrances, coefficientIndexQuadrancesFrom,
        List.sum_cons, List.sum_nil, Nat.add_zero, List.length_cons,
        List.length_nil]
      simpa only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceMod]
        using Nat.mul_le_mul_left 2 indexBound
  | lower :: middle :: upper :: rest =>
      have first : AreConsecutiveBest source.value lower middle :=
        (List.isChain_cons_cons.mp chain).1
      have middleChain :
          (middle :: upper :: rest).IsChain
            (AreConsecutiveBest source.value) :=
        (List.isChain_cons_cons.mp chain).2
      have second : AreConsecutiveBest source.value middle upper :=
        (List.isChain_cons_cons.mp middleChain).1
      have tailChain :
          (upper :: rest).IsChain (AreConsecutiveBest source.value) :=
        (List.isChain_cons_cons.mp middleChain).2
      have firstTwoBound :=
        RFAP.DirichletBlock.coefficientIndexQuadrance_add_le_three first second
      have tailBound :=
        two_mul_coefficientIndexQuadrances_sum_le_with_parity
          (upper :: rest) tailChain
      simp only [coefficientIndexQuadrances, coefficientIndexQuadrancesFrom,
        List.sum_cons, List.length_cons]
      have firstScaled := Nat.mul_le_mul_left 2 firstTwoBound
      have added := Nat.add_le_add firstScaled tailBound
      calc
        2 * (coefficientIndexQuadrance lower middle +
            (coefficientIndexQuadrance middle upper +
              (coefficientIndexQuadrances (upper :: rest)).sum)) =
            2 * (coefficientIndexQuadrance lower middle +
              coefficientIndexQuadrance middle upper) +
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
            Nat.add_mod_right]
          ring1
termination_by pairs.length

/-- Parity-free consequence of the exact alternating-pattern bound. -/
theorem two_mul_coefficientIndexQuadrances_sum_le
    {source : RFAP.HurwitzRational.Fraction} (pairs : List Pair)
    (chain : pairs.IsChain (AreConsecutiveBest source.value)) :
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
theorem quadraticThreshold_mul_dirichletWindowQuadrances_sum_le_indexSum
    {source : RFAP.HurwitzRational.Fraction} (pairs : List Pair)
    (chain : pairs.IsChain (AreConsecutiveBest source.value))
    (threshold : Coordinate)
    (thresholdLtHalf : threshold < (1 / 2 : Coordinate))
    (thresholdPolynomialNonnegative :
      0 ≤ threshold ^ 2 - 3 * threshold + 1 / 4) :
    threshold * (dirichletWindowQuadrances source.value pairs).sum ≤
      ((coefficientIndexQuadrances pairs).sum : Coordinate) := by
  match pairs with
  | [] => simp [dirichletWindowQuadrances, coefficientIndexQuadrances]
  | [_] => simp [dirichletWindowQuadrances, coefficientIndexQuadrances]
  | lower :: upper :: rest =>
      have consecutive : AreConsecutiveBest source.value lower upper :=
        (List.isChain_cons_cons.mp chain).1
      have tailChain :
          (upper :: rest).IsChain (AreConsecutiveBest source.value) :=
        (List.isChain_cons_cons.mp chain).2
      have firstBound :=
        RFAP.DirichletWindow.AreConsecutiveBest.quadraticThreshold_mul_dirichletWindow_le_index
          consecutive threshold thresholdLtHalf
            thresholdPolynomialNonnegative
      have tailBound :=
        quadraticThreshold_mul_dirichletWindowQuadrances_sum_le_indexSum
          (upper :: rest) tailChain threshold thresholdLtHalf
            thresholdPolynomialNonnegative
      have addedBounds :=
        RFAP.ConstructiveFraction.add_le_add_direct firstBound tailBound
      simp only [dirichletWindowQuadrances, dirichletWindowQuadrancesFrom,
        coefficientIndexQuadrances, coefficientIndexQuadrancesFrom,
        List.sum_cons, Nat.cast_add]
      calc
        threshold *
            (dirichletWindowQuadrance source.value lower upper +
              (dirichletWindowQuadrances source.value (upper :: rest)).sum) =
            threshold * dirichletWindowQuadrance source.value lower upper +
              threshold *
                (dirichletWindowQuadrances source.value (upper :: rest)).sum := by
          ring1
        _ ≤ (coefficientIndexQuadrance lower upper : Coordinate) +
              ((coefficientIndexQuadrances (upper :: rest)).sum : Coordinate) :=
          addedBounds
termination_by pairs.length

/-- Division-free finite-chain window certificate.  If a displayed rational
threshold passes the quadratic test, twice that threshold times the sum of
all chain windows is at most `3 * transitionCount + 1`. -/
theorem two_mul_quadraticThreshold_mul_dirichletWindowQuadrances_sum_le
    {source : RFAP.HurwitzRational.Fraction} (pairs : List Pair)
    (chain : pairs.IsChain (AreConsecutiveBest source.value))
    (threshold : Coordinate)
    (thresholdLtHalf : threshold < (1 / 2 : Coordinate))
    (thresholdPolynomialNonnegative :
      0 ≤ threshold ^ 2 - 3 * threshold + 1 / 4) :
    2 * threshold * (dirichletWindowQuadrances source.value pairs).sum ≤
      (3 * (coefficientIndexQuadrances pairs).length + 1 : Nat) := by
  have windowSumBound :=
    quadraticThreshold_mul_dirichletWindowQuadrances_sum_le_indexSum pairs
      chain threshold thresholdLtHalf thresholdPolynomialNonnegative
  have scaledWindowSumBound :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct windowSumBound
      (show (0 : Coordinate) ≤ 2 by decide)
  have indexSumBound :=
    two_mul_coefficientIndexQuadrances_sum_le pairs chain
  have castIndexSumBound :
      ((2 * (coefficientIndexQuadrances pairs).sum : Nat) : Coordinate) ≤
        (3 * (coefficientIndexQuadrances pairs).length + 1 : Nat) :=
    RFAP.ConstructiveFraction.natCast_le_direct indexSumBound
  calc
    2 * threshold * (dirichletWindowQuadrances source.value pairs).sum =
        2 *
          (threshold *
            (dirichletWindowQuadrances source.value pairs).sum) := by
      ring1
    _ ≤ 2 * ((coefficientIndexQuadrances pairs).sum : Coordinate) :=
      scaledWindowSumBound
    _ = ((2 * (coefficientIndexQuadrances pairs).sum : Nat) : Coordinate) := by
      rw [Nat.cast_mul, Nat.cast_ofNat]
    _ ≤ (3 * (coefficientIndexQuadrances pairs).length + 1 : Nat) :=
      castIndexSumBound

/-- Exact parity-sensitive finite-chain window certificate. -/
theorem two_mul_quadraticThreshold_mul_dirichletWindowQuadrances_sum_le_with_parity
    {source : RFAP.HurwitzRational.Fraction} (pairs : List Pair)
    (chain : pairs.IsChain (AreConsecutiveBest source.value))
    (threshold : Coordinate)
    (thresholdLtHalf : threshold < (1 / 2 : Coordinate))
    (thresholdPolynomialNonnegative :
      0 ≤ threshold ^ 2 - 3 * threshold + 1 / 4) :
    2 * threshold * (dirichletWindowQuadrances source.value pairs).sum ≤
      (3 * (coefficientIndexQuadrances pairs).length +
        (coefficientIndexQuadrances pairs).length % 2 : Nat) := by
  have windowSumBound :=
    quadraticThreshold_mul_dirichletWindowQuadrances_sum_le_indexSum pairs
      chain threshold thresholdLtHalf thresholdPolynomialNonnegative
  have scaledWindowSumBound :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct windowSumBound
      (show (0 : Coordinate) ≤ 2 by decide)
  have indexSumBound :=
    two_mul_coefficientIndexQuadrances_sum_le_with_parity pairs chain
  have castIndexSumBound :
      ((2 * (coefficientIndexQuadrances pairs).sum : Nat) : Coordinate) ≤
        (3 * (coefficientIndexQuadrances pairs).length +
          (coefficientIndexQuadrances pairs).length % 2 : Nat) :=
    RFAP.ConstructiveFraction.natCast_le_direct indexSumBound
  calc
    2 * threshold * (dirichletWindowQuadrances source.value pairs).sum =
        2 *
          (threshold *
            (dirichletWindowQuadrances source.value pairs).sum) := by
      ring1
    _ ≤ 2 * ((coefficientIndexQuadrances pairs).sum : Coordinate) :=
      scaledWindowSumBound
    _ = ((2 * (coefficientIndexQuadrances pairs).sum : Nat) : Coordinate) := by
      rw [Nat.cast_mul, Nat.cast_ofNat]
    _ ≤ (3 * (coefficientIndexQuadrances pairs).length +
          (coefficientIndexQuadrances pairs).length % 2 : Nat) :=
      castIndexSumBound

/-- Cancel any quadratic-certified threshold against a displayed nonnegative
reciprocal in the exact finite-chain inequality. -/
theorem two_mul_dirichletWindowQuadrances_sum_le_factor_mul_parityBound_of_quadraticThreshold
    {source : RFAP.HurwitzRational.Fraction} (pairs : List Pair)
    (chain : pairs.IsChain (AreConsecutiveBest source.value))
    (threshold factor : Coordinate)
    (thresholdLtHalf : threshold < (1 / 2 : Coordinate))
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
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct thresholdBound
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
theorem two_mul_dirichletWindowQuadrances_sum_le_refinedIndexFactor_mul_parityBound
    {source : RFAP.HurwitzRational.Fraction} (pairs : List Pair)
    (chain : pairs.IsChain (AreConsecutiveBest source.value)) :
    2 * (dirichletWindowQuadrances source.value pairs).sum ≤
      RFAP.DirichletWindow.refinedIndexFactor *
        (3 * (coefficientIndexQuadrances pairs).length +
          (coefficientIndexQuadrances pairs).length % 2 : Nat) :=
  two_mul_dirichletWindowQuadrances_sum_le_factor_mul_parityBound_of_quadraticThreshold
    pairs chain RFAP.DirichletWindow.refinedGapThreshold
      RFAP.DirichletWindow.refinedIndexFactor
      RFAP.DirichletWindow.refinedGapThreshold_lt_half
      RFAP.DirichletWindow.refinedGapThreshold_quadratic_nonnegative
      RFAP.DirichletWindow.refinedGapThreshold_mul_refinedIndexFactor
      RFAP.DirichletWindow.refinedIndexFactor_nonneg

/-- Sharper concrete finite-chain specialization at threshold `102/1189`. -/
theorem two_mul_dirichletWindowQuadrances_sum_le_quadraticIndexFactor_mul_parityBound
    {source : RFAP.HurwitzRational.Fraction} (pairs : List Pair)
    (chain : pairs.IsChain (AreConsecutiveBest source.value)) :
    2 * (dirichletWindowQuadrances source.value pairs).sum ≤
      RFAP.DirichletWindow.quadraticIndexFactor *
        (3 * (coefficientIndexQuadrances pairs).length +
          (coefficientIndexQuadrances pairs).length % 2 : Nat) :=
  two_mul_dirichletWindowQuadrances_sum_le_factor_mul_parityBound_of_quadraticThreshold
    pairs chain RFAP.DirichletWindow.quadraticGapThreshold
      RFAP.DirichletWindow.quadraticIndexFactor
      RFAP.DirichletWindow.quadraticGapThreshold_lt_half
      RFAP.DirichletWindow.quadraticGapThreshold_quadratic_nonnegative
      RFAP.DirichletWindow.quadraticGapThreshold_mul_quadraticIndexFactor
      RFAP.DirichletWindow.quadraticIndexFactor_nonneg

/-- The index-aware one-window bound accumulates directly along any supplied
finite chain.  Each transition contributes at most `1189/102`, independently
of its determinant index. -/
theorem dirichletWindowQuadrances_sum_le_quadraticIndexFactor_mul_length
    {source : RFAP.HurwitzRational.Fraction} (pairs : List Pair)
    (chain : pairs.IsChain (AreConsecutiveBest source.value)) :
    (dirichletWindowQuadrances source.value pairs).sum ≤
      RFAP.DirichletWindow.quadraticIndexFactor *
        ((coefficientIndexQuadrances pairs).length : Coordinate) := by
  match pairs with
  | [] => simp [dirichletWindowQuadrances, coefficientIndexQuadrances]
  | [_] => simp [dirichletWindowQuadrances, coefficientIndexQuadrances]
  | lower :: upper :: rest =>
      have consecutive : AreConsecutiveBest source.value lower upper :=
        (List.isChain_cons_cons.mp chain).1
      have tailChain :
          (upper :: rest).IsChain (AreConsecutiveBest source.value) :=
        (List.isChain_cons_cons.mp chain).2
      have firstBound :=
        RFAP.IndexTwoWindow.AreConsecutiveBest.dirichletWindowQuadrance_le_quadraticIndexFactorUniversal
          consecutive
      have tailBound :=
        dirichletWindowQuadrances_sum_le_quadraticIndexFactor_mul_length
          (upper :: rest) tailChain
      simp only [dirichletWindowQuadrances, dirichletWindowQuadrancesFrom,
        coefficientIndexQuadrances, coefficientIndexQuadrancesFrom,
        List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
      calc
        dirichletWindowQuadrance source.value lower upper +
            (dirichletWindowQuadrances source.value (upper :: rest)).sum ≤
            RFAP.DirichletWindow.quadraticIndexFactor +
              RFAP.DirichletWindow.quadraticIndexFactor *
                ((coefficientIndexQuadrances (upper :: rest)).length :
                  Coordinate) :=
          RFAP.ConstructiveFraction.add_le_add_direct firstBound tailBound
        _ = RFAP.DirichletWindow.quadraticIndexFactor *
            (((coefficientIndexQuadrances (upper :: rest)).length :
                Coordinate) + 1) := by ring1

/-- The rational universal one-window bound accumulates directly along any
supplied finite chain. -/
theorem dirichletWindowQuadrances_sum_le_twentyEight_fifteenths_mul_length
    {source : RFAP.HurwitzRational.Fraction} (pairs : List Pair)
    (chain : pairs.IsChain (AreConsecutiveBest source.value)) :
    (dirichletWindowQuadrances source.value pairs).sum ≤
      (28 / 15 : Coordinate) *
        ((coefficientIndexQuadrances pairs).length : Coordinate) := by
  match pairs with
  | [] => simp [dirichletWindowQuadrances, coefficientIndexQuadrances]
  | [_] => simp [dirichletWindowQuadrances, coefficientIndexQuadrances]
  | lower :: upper :: rest =>
      have consecutive : AreConsecutiveBest source.value lower upper :=
        (List.isChain_cons_cons.mp chain).1
      have tailChain :
          (upper :: rest).IsChain (AreConsecutiveBest source.value) :=
        (List.isChain_cons_cons.mp chain).2
      have firstBound :=
        RFAP.IndexOneWindow.AreConsecutiveBest.dirichletWindowQuadrance_le_twentyEight_fifteenths
          consecutive
      have tailBound :=
        dirichletWindowQuadrances_sum_le_twentyEight_fifteenths_mul_length
          (upper :: rest) tailChain
      simp only [dirichletWindowQuadrances, dirichletWindowQuadrancesFrom,
        coefficientIndexQuadrances, coefficientIndexQuadrancesFrom,
        List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
      calc
        dirichletWindowQuadrance source.value lower upper +
            (dirichletWindowQuadrances source.value (upper :: rest)).sum ≤
            (28 / 15 : Coordinate) +
              (28 / 15 : Coordinate) *
                ((coefficientIndexQuadrances (upper :: rest)).length :
                  Coordinate) :=
          RFAP.ConstructiveFraction.add_le_add_direct firstBound tailBound
        _ = (28 / 15 : Coordinate) *
            (((coefficientIndexQuadrances (upper :: rest)).length :
                Coordinate) + 1) := by ring1

/-- The norm-two-coefficient universal one-window bound accumulates directly
along any supplied finite chain. -/
theorem dirichletWindowQuadrances_sum_le_normTwoUniversalWindowBound_mul_length
    {source : RFAP.HurwitzRational.Fraction} (pairs : List Pair)
    (chain : pairs.IsChain (AreConsecutiveBest source.value)) :
    (dirichletWindowQuadrances source.value pairs).sum ≤
      RFAP.IndexOneWindow.normTwoIndexOneWindowBound *
        ((coefficientIndexQuadrances pairs).length : Coordinate) := by
  match pairs with
  | [] => simp [dirichletWindowQuadrances, coefficientIndexQuadrances]
  | [_] => simp [dirichletWindowQuadrances, coefficientIndexQuadrances]
  | lower :: upper :: rest =>
      have consecutive : AreConsecutiveBest source.value lower upper :=
        (List.isChain_cons_cons.mp chain).1
      have tailChain :
          (upper :: rest).IsChain (AreConsecutiveBest source.value) :=
        (List.isChain_cons_cons.mp chain).2
      have firstBound :=
        RFAP.IndexOneWindow.AreConsecutiveBest.dirichletWindowQuadrance_le_normTwoUniversalWindowBound
          consecutive
      have tailBound :=
        dirichletWindowQuadrances_sum_le_normTwoUniversalWindowBound_mul_length
          (upper :: rest) tailChain
      simp only [dirichletWindowQuadrances, dirichletWindowQuadrancesFrom,
        coefficientIndexQuadrances, coefficientIndexQuadrancesFrom,
        List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
      calc
        dirichletWindowQuadrance source.value lower upper +
            (dirichletWindowQuadrances source.value (upper :: rest)).sum ≤
            RFAP.IndexOneWindow.normTwoIndexOneWindowBound +
              RFAP.IndexOneWindow.normTwoIndexOneWindowBound *
                ((coefficientIndexQuadrances (upper :: rest)).length :
                  Coordinate) :=
          RFAP.ConstructiveFraction.add_le_add_direct firstBound tailBound
        _ = RFAP.IndexOneWindow.normTwoIndexOneWindowBound *
            (((coefficientIndexQuadrances (upper :: rest)).length :
                Coordinate) + 1) := by ring1

/-- The dyadic near-optimal one-window bound accumulates directly along any
supplied finite chain. -/
theorem dirichletWindowQuadrances_sum_le_sharpDyadicUniversalWindowBound_mul_length
    {source : RFAP.HurwitzRational.Fraction} (pairs : List Pair)
    (chain : pairs.IsChain (AreConsecutiveBest source.value)) :
    (dirichletWindowQuadrances source.value pairs).sum ≤
      RFAP.IndexOneWindow.sharpIndexOneWindowBound *
        ((coefficientIndexQuadrances pairs).length : Coordinate) := by
  match pairs with
  | [] => simp [dirichletWindowQuadrances, coefficientIndexQuadrances]
  | [_] => simp [dirichletWindowQuadrances, coefficientIndexQuadrances]
  | lower :: upper :: rest =>
      have consecutive : AreConsecutiveBest source.value lower upper :=
        (List.isChain_cons_cons.mp chain).1
      have tailChain :
          (upper :: rest).IsChain (AreConsecutiveBest source.value) :=
        (List.isChain_cons_cons.mp chain).2
      have firstBound :=
        RFAP.IndexOneWindow.AreConsecutiveBest.dirichletWindowQuadrance_le_sharpDyadicUniversalWindowBound
          consecutive
      have tailBound :=
        dirichletWindowQuadrances_sum_le_sharpDyadicUniversalWindowBound_mul_length
          (upper :: rest) tailChain
      simp only [dirichletWindowQuadrances, dirichletWindowQuadrancesFrom,
        coefficientIndexQuadrances, coefficientIndexQuadrancesFrom,
        List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
      calc
        dirichletWindowQuadrance source.value lower upper +
            (dirichletWindowQuadrances source.value (upper :: rest)).sum ≤
            RFAP.IndexOneWindow.sharpIndexOneWindowBound +
              RFAP.IndexOneWindow.sharpIndexOneWindowBound *
                ((coefficientIndexQuadrances (upper :: rest)).length :
                  Coordinate) :=
          RFAP.ConstructiveFraction.add_le_add_direct firstBound tailBound
        _ = RFAP.IndexOneWindow.sharpIndexOneWindowBound *
            (((coefficientIndexQuadrances (upper :: rest)).length :
                Coordinate) + 1) := by ring1

/-- Every displayed point of the exact root-free quadratic cut scales the
sum along a supplied finite best chain by at most its transition count. -/
theorem gapThreshold_mul_dirichletWindowQuadrances_sum_le_length
    {source : RFAP.HurwitzRational.Fraction} (gap : Coordinate)
    (certificate : RFAP.OptimalIndexTwoWindow.IsCenteredGapThreshold gap)
    (pairs : List Pair)
    (chain : pairs.IsChain (AreConsecutiveBest source.value)) :
    gap * (dirichletWindowQuadrances source.value pairs).sum ≤
      ((coefficientIndexQuadrances pairs).length : Coordinate) := by
  match pairs with
  | [] => simp [dirichletWindowQuadrances, coefficientIndexQuadrances]
  | [_] => simp [dirichletWindowQuadrances, coefficientIndexQuadrances]
  | lower :: upper :: rest =>
      have consecutive : AreConsecutiveBest source.value lower upper :=
        (List.isChain_cons_cons.mp chain).1
      have tailChain :
          (upper :: rest).IsChain (AreConsecutiveBest source.value) :=
        (List.isChain_cons_cons.mp chain).2
      have firstBound :=
        RFAP.IndexOneWindow.AreConsecutiveBest.gapThreshold_mul_dirichletWindow_le_one
          gap certificate consecutive
      have tailBound :=
        gapThreshold_mul_dirichletWindowQuadrances_sum_le_length gap
          certificate (upper :: rest) tailChain
      simp only [dirichletWindowQuadrances, dirichletWindowQuadrancesFrom,
        coefficientIndexQuadrances, coefficientIndexQuadrancesFrom,
        List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
      calc
        gap * (dirichletWindowQuadrance source.value lower upper +
            (dirichletWindowQuadrances source.value (upper :: rest)).sum) =
            gap * dirichletWindowQuadrance source.value lower upper +
              gap * (dirichletWindowQuadrances source.value
                (upper :: rest)).sum := by ring1
        _ ≤ 1 +
            ((coefficientIndexQuadrances (upper :: rest)).length :
              Coordinate) :=
          RFAP.ConstructiveFraction.add_le_add_direct firstBound tailBound
        _ = ((coefficientIndexQuadrances (upper :: rest)).length :
              Coordinate) + 1 := by ring1

/-- Clearing the denominator in the direct chain accumulation gives the
integer-coefficient certificate `15 * sum ≤ 28 * transitionCount`. -/
theorem fifteen_mul_dirichletWindowQuadrances_sum_le_twentyEight_mul_length
    {source : RFAP.HurwitzRational.Fraction} (pairs : List Pair)
    (chain : pairs.IsChain (AreConsecutiveBest source.value)) :
    15 * (dirichletWindowQuadrances source.value pairs).sum ≤
      (28 * (coefficientIndexQuadrances pairs).length : Nat) := by
  have sumBound :=
    dirichletWindowQuadrances_sum_le_twentyEight_fifteenths_mul_length
      pairs chain
  have scaled :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct sumBound
      (show (0 : Coordinate) ≤ 15 by decide)
  calc
    15 * (dirichletWindowQuadrances source.value pairs).sum ≤
        15 * ((28 / 15 : Coordinate) *
          ((coefficientIndexQuadrances pairs).length : Coordinate)) := scaled
    _ = (28 * (coefficientIndexQuadrances pairs).length : Nat) := by
      rw [Nat.cast_mul, Nat.cast_ofNat]
      have cancellation : (15 : Coordinate) * (28 / 15) = 28 := by decide
      rw [← RFAP.ConstructiveFraction.mul_assoc, cancellation]

/-- Compatibility with the earlier parity-sensitive statement.  The new
direct accumulation is strictly stronger and no parity correction is needed. -/
theorem fifteen_mul_dirichletWindowQuadrances_sum_le_with_parity
    {source : RFAP.HurwitzRational.Fraction} (pairs : List Pair)
    (chain : pairs.IsChain (AreConsecutiveBest source.value)) :
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
    (RFAP.ConstructiveFraction.natCast_le_direct naturalBound)

/-- The exact universal one-window bound accumulates directly along any
supplied finite chain.  Each transition contributes at most two. -/
theorem dirichletWindowQuadrances_sum_le_two_mul_length
    {source : RFAP.HurwitzRational.Fraction} (pairs : List Pair)
    (chain : pairs.IsChain (AreConsecutiveBest source.value)) :
    (dirichletWindowQuadrances source.value pairs).sum ≤
      2 * ((coefficientIndexQuadrances pairs).length : Coordinate) := by
  match pairs with
  | [] => simp [dirichletWindowQuadrances, coefficientIndexQuadrances]
  | [_] => simp [dirichletWindowQuadrances, coefficientIndexQuadrances]
  | lower :: upper :: rest =>
      have consecutive : AreConsecutiveBest source.value lower upper :=
        (List.isChain_cons_cons.mp chain).1
      have tailChain :
          (upper :: rest).IsChain (AreConsecutiveBest source.value) :=
        (List.isChain_cons_cons.mp chain).2
      have firstBound :=
        RFAP.IndexOneWindow.AreConsecutiveBest.dirichletWindowQuadrance_le_two
          consecutive
      have tailBound :=
        dirichletWindowQuadrances_sum_le_two_mul_length
          (upper :: rest) tailChain
      simp only [dirichletWindowQuadrances, dirichletWindowQuadrancesFrom,
        coefficientIndexQuadrances, coefficientIndexQuadrancesFrom,
        List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
      calc
        dirichletWindowQuadrance source.value lower upper +
            (dirichletWindowQuadrances source.value (upper :: rest)).sum ≤
            2 + 2 *
              ((coefficientIndexQuadrances (upper :: rest)).length :
                Coordinate) :=
          RFAP.ConstructiveFraction.add_le_add_direct firstBound tailBound
        _ = 2 *
            (((coefficientIndexQuadrances (upper :: rest)).length :
                Coordinate) + 1) := by ring1

end RFAP.DirichletChain
