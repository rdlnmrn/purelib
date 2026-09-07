import mathlib.Tactic.QuotientFreeRing
import RFAP.Approximation.IndexOneWindow

/-!
# Two-window Dirichlet bounds

This file combines the rational bound for one consecutive Dirichlet window
with the finite exclusion of two successive coefficient indices equal to two.
Thus every adjacent pair of windows contains an index-one window, and their
sum has a smaller bound than two independent applications of the universal
one-window estimate.
-/

namespace RFAP.DirichletBlock

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Pair := RFAP.HurwitzRational.ConvergentPair

open RFAP.BestApproximation

/-- Shallow displayed record for the two-window sum bound `1224/35`. -/
def refinedTwoWindowSumBound : Coordinate :=
  RFAP.ConstructiveFraction.ofFraction ⟨1224, 35, by decide⟩

/-- Shallow displayed record for the sharper two-window sum bound `1189/34`. -/
def quadraticTwoWindowSumBound : Coordinate :=
  RFAP.ConstructiveFraction.ofFraction ⟨1189, 34, by decide⟩

/-- Exact rational sum bound supplied by the finite-octant index-one
certificate and the index-two centered-coset certificate. -/
def finiteOctantTwoWindowSumBound : Coordinate :=
  RFAP.ConstructiveFraction.ofFraction ⟨224, 71, by decide⟩

/-- Near-optimal dyadic bound `512/205` for two successive squared windows. -/
def dyadicTwoWindowSumBound : Coordinate :=
  RFAP.ConstructiveFraction.ofFraction ⟨512, 205, by decide⟩

theorem dyadicTwoWindowSumBound_mul_denominator :
    dyadicTwoWindowSumBound * 205 = 512 := by
  unfold dyadicTwoWindowSumBound
  have clearance := RFAP.ConstructiveFraction.ofFraction_mul_den
    ({ num := 512, den := 205, den_pos := by decide } :
      RFAP.ConstructiveFraction.Fraction)
  simpa only [Int.cast_ofNat] using clearance

theorem finiteOctantTwoWindowSumBound_mul_denominator :
    finiteOctantTwoWindowSumBound * 71 = 224 := by
  unfold finiteOctantTwoWindowSumBound
  have clearance := RFAP.ConstructiveFraction.ofFraction_mul_den
    ({ num := 224, den := 71, den_pos := by decide } :
      RFAP.ConstructiveFraction.Fraction)
  simpa only [Int.cast_ofNat] using clearance

theorem refinedIndexFactor_mul_three :
    RFAP.DirichletWindow.refinedIndexFactor * 3 =
      refinedTwoWindowSumBound := by
  unfold RFAP.DirichletWindow.refinedIndexFactor refinedTwoWindowSumBound
  calc
    RFAP.ConstructiveFraction.ofFraction ⟨408, 35, by decide⟩ * 3 =
        RFAP.ConstructiveFraction.ofFraction ⟨408, 35, by decide⟩ *
          RFAP.ConstructiveFraction.ofFraction ⟨3, 1, by decide⟩ :=
      congrArg
        (fun value : Coordinate =>
          RFAP.ConstructiveFraction.ofFraction ⟨408, 35, by decide⟩ * value)
        (RFAP.ConstructiveFraction.natCast_eq_fraction 3)
    _ = RFAP.ConstructiveFraction.ofFraction ⟨1224, 35, by decide⟩ := by
      rw [RFAP.ConstructiveFraction.ofFraction_mulFraction]
      apply RFAP.ConstructiveFraction.ofFraction_eq_of_equivalent
      change (408 * 3 : Int) * 35 = 1224 * (35 * 1)
      ring1

theorem refinedTwoWindowSumBound_mul_denominator :
    refinedTwoWindowSumBound * 35 = 1224 := by
  unfold refinedTwoWindowSumBound
  have clearance := RFAP.ConstructiveFraction.ofFraction_mul_den
    ({ num := 1224, den := 35, den_pos := by decide } :
      RFAP.ConstructiveFraction.Fraction)
  simpa only [Int.cast_ofNat] using clearance

theorem quadraticIndexFactor_mul_three :
    RFAP.DirichletWindow.quadraticIndexFactor * 3 =
      quadraticTwoWindowSumBound := by
  unfold RFAP.DirichletWindow.quadraticIndexFactor quadraticTwoWindowSumBound
  calc
    RFAP.ConstructiveFraction.ofFraction ⟨1189, 102, by decide⟩ * 3 =
        RFAP.ConstructiveFraction.ofFraction ⟨1189, 102, by decide⟩ *
          RFAP.ConstructiveFraction.ofFraction ⟨3, 1, by decide⟩ :=
      congrArg
        (fun value : Coordinate =>
          RFAP.ConstructiveFraction.ofFraction ⟨1189, 102, by decide⟩ * value)
        (RFAP.ConstructiveFraction.natCast_eq_fraction 3)
    _ = RFAP.ConstructiveFraction.ofFraction ⟨1189, 34, by decide⟩ := by
      rw [RFAP.ConstructiveFraction.ofFraction_mulFraction]
      apply RFAP.ConstructiveFraction.ofFraction_eq_of_equivalent
      change (1189 * 3 : Int) * 34 = 1189 * (102 * 1)
      ring1

theorem quadraticTwoWindowSumBound_mul_denominator :
    quadraticTwoWindowSumBound * 34 = 1189 := by
  unfold quadraticTwoWindowSumBound
  have clearance := RFAP.ConstructiveFraction.ofFraction_mul_den
    ({ num := 1189, den := 34, den_pos := by decide } :
      RFAP.ConstructiveFraction.Fraction)
  simpa only [Int.cast_ofNat] using clearance

/-- The coefficient indices of two successive best transitions have sum at
most three: an index-two transition must be followed by index one. -/
theorem coefficientIndexQuadrance_add_le_three
    {source : RFAP.HurwitzRational.Fraction} {lower middle upper : Pair}
    (first : AreConsecutiveBest source.value lower middle)
    (second : AreConsecutiveBest source.value middle upper) :
    coefficientIndexQuadrance lower middle +
        coefficientIndexQuadrance middle upper ≤ 3 := by
  rcases first.coefficientIndexQuadrance_eq_one_or_two with
      leftIndexOne | leftIndexTwo
  · rw [leftIndexOne]
    simpa only [Nat.one_add, Nat.reduceSucc] using
      Nat.succ_le_succ second.coefficientIndexQuadrance_le_two
  · have rightIndexOne :=
      RFAP.RepeatedIndex.nextCoefficientIndexQuadrance_eq_one_of_eq_two
        first second leftIndexTwo
    rw [leftIndexTwo, rightIndexOne]

/-- For any rational threshold passing the quadratic boundary test, at least
one of two successive windows satisfies the index-one scaled bound. -/
theorem quadraticThreshold_mul_one_dirichletWindow_le_one
    {source : RFAP.HurwitzRational.Fraction} {lower middle upper : Pair}
    (first : AreConsecutiveBest source.value lower middle)
    (second : AreConsecutiveBest source.value middle upper)
    (threshold : Coordinate)
    (thresholdLtHalf : threshold < (1 / 2 : Coordinate))
    (thresholdPolynomialNonnegative :
      0 ≤ threshold ^ 2 - 3 * threshold + 1 / 4) :
    threshold * dirichletWindowQuadrance source.value lower middle ≤ 1 ∨
      threshold * dirichletWindowQuadrance source.value middle upper ≤ 1 := by
  rcases first.coefficientIndexQuadrance_eq_one_or_two with
      leftIndexOne | leftIndexTwo
  · left
    have bound :=
      RFAP.DirichletWindow.AreConsecutiveBest.quadraticThreshold_mul_dirichletWindow_le_index
        first threshold thresholdLtHalf thresholdPolynomialNonnegative
    simpa only [leftIndexOne, Nat.cast_one] using bound
  · right
    have rightIndexOne :=
      RFAP.RepeatedIndex.nextCoefficientIndexQuadrance_eq_one_of_eq_two
        first second leftIndexTwo
    have bound :=
      RFAP.DirichletWindow.AreConsecutiveBest.quadraticThreshold_mul_dirichletWindow_le_index
        second threshold thresholdLtHalf thresholdPolynomialNonnegative
    simpa only [rightIndexOne, Nat.cast_one] using bound

/-- Parameterized two-window form of the quadratic-threshold certificate:
the threshold times the sum of two successive windows is at most three. -/
theorem quadraticThreshold_mul_dirichletWindowSum_le_three
    {source : RFAP.HurwitzRational.Fraction} {lower middle upper : Pair}
    (first : AreConsecutiveBest source.value lower middle)
    (second : AreConsecutiveBest source.value middle upper)
    (threshold : Coordinate)
    (thresholdLtHalf : threshold < (1 / 2 : Coordinate))
    (thresholdPolynomialNonnegative :
      0 ≤ threshold ^ 2 - 3 * threshold + 1 / 4) :
    threshold *
        (dirichletWindowQuadrance source.value lower middle +
          dirichletWindowQuadrance source.value middle upper) ≤ 3 := by
  have firstBound :=
    RFAP.DirichletWindow.AreConsecutiveBest.quadraticThreshold_mul_dirichletWindow_le_index
      first threshold thresholdLtHalf thresholdPolynomialNonnegative
  have secondBound :=
    RFAP.DirichletWindow.AreConsecutiveBest.quadraticThreshold_mul_dirichletWindow_le_index
      second threshold thresholdLtHalf thresholdPolynomialNonnegative
  have addedBounds :=
    RFAP.ConstructiveFraction.add_le_add_direct firstBound secondBound
  have indexSumBound := coefficientIndexQuadrance_add_le_three first second
  have castIndexSumBound :
      ((coefficientIndexQuadrance lower middle +
          coefficientIndexQuadrance middle upper : Nat) : Coordinate) ≤ 3 :=
    RFAP.ConstructiveFraction.natCast_le_direct indexSumBound
  calc
    threshold *
        (dirichletWindowQuadrance source.value lower middle +
          dirichletWindowQuadrance source.value middle upper) =
        threshold * dirichletWindowQuadrance source.value lower middle +
          threshold * dirichletWindowQuadrance source.value middle upper := by
      ring1
    _ ≤ (coefficientIndexQuadrance lower middle : Coordinate) +
          (coefficientIndexQuadrance middle upper : Coordinate) := addedBounds
    _ = ((coefficientIndexQuadrance lower middle +
          coefficientIndexQuadrance middle upper : Nat) : Coordinate) := by
      rw [Nat.cast_add]
    _ ≤ 3 := castIndexSumBound

/-- Among two successive best transitions, at least one squared window is
bounded by the index-one constant `408/35`. -/
theorem one_dirichletWindowQuadrance_le_refinedIndexFactor
    {source : RFAP.HurwitzRational.Fraction} {lower middle upper : Pair}
    (first : AreConsecutiveBest source.value lower middle)
    (second : AreConsecutiveBest source.value middle upper) :
    dirichletWindowQuadrance source.value lower middle ≤
        RFAP.DirichletWindow.refinedIndexFactor ∨
      dirichletWindowQuadrance source.value middle upper ≤
        RFAP.DirichletWindow.refinedIndexFactor := by
  rcases first.coefficientIndexQuadrance_eq_one_or_two with
      leftIndexOne | leftIndexTwo
  · left
    have bound :=
      RFAP.DirichletWindow.AreConsecutiveBest.dirichletWindowQuadrance_le_refinedIndexFactor
        first
    simpa only [leftIndexOne, Nat.cast_one, mul_one] using bound
  · right
    have rightIndexOne :=
      RFAP.RepeatedIndex.nextCoefficientIndexQuadrance_eq_one_of_eq_two
        first second leftIndexTwo
    have bound :=
      RFAP.DirichletWindow.AreConsecutiveBest.dirichletWindowQuadrance_le_refinedIndexFactor
        second
    simpa only [rightIndexOne, Nat.cast_one, mul_one] using bound

/-- Among two successive best transitions, at least one squared window is
bounded by the sharper index-one constant `1189/102`. -/
theorem one_dirichletWindowQuadrance_le_quadraticIndexFactor
    {source : RFAP.HurwitzRational.Fraction} {lower middle upper : Pair}
    (first : AreConsecutiveBest source.value lower middle)
    (second : AreConsecutiveBest source.value middle upper) :
    dirichletWindowQuadrance source.value lower middle ≤
        RFAP.DirichletWindow.quadraticIndexFactor ∨
      dirichletWindowQuadrance source.value middle upper ≤
        RFAP.DirichletWindow.quadraticIndexFactor := by
  rcases first.coefficientIndexQuadrance_eq_one_or_two with
      leftIndexOne | leftIndexTwo
  · left
    have bound :=
      RFAP.DirichletWindow.AreConsecutiveBest.dirichletWindowQuadrance_le_quadraticIndexFactor
        first
    simpa only [leftIndexOne, Nat.cast_one, mul_one] using bound
  · right
    have rightIndexOne :=
      RFAP.RepeatedIndex.nextCoefficientIndexQuadrance_eq_one_of_eq_two
        first second leftIndexTwo
    have bound :=
      RFAP.DirichletWindow.AreConsecutiveBest.dirichletWindowQuadrance_le_quadraticIndexFactor
        second
    simpa only [rightIndexOne, Nat.cast_one, mul_one] using bound

/-- The sum of two successive squared Dirichlet-window products is at most
`1224/35`, improving the sum of two independent universal bounds. -/
theorem dirichletWindowQuadrance_add_le_refinedTwoWindowSumBound
    {source : RFAP.HurwitzRational.Fraction} {lower middle upper : Pair}
    (first : AreConsecutiveBest source.value lower middle)
    (second : AreConsecutiveBest source.value middle upper) :
    dirichletWindowQuadrance source.value lower middle +
        dirichletWindowQuadrance source.value middle upper ≤
      refinedTwoWindowSumBound := by
  have firstBound :=
    RFAP.DirichletWindow.AreConsecutiveBest.dirichletWindowQuadrance_le_refinedIndexFactor
      first
  have secondBound :=
    RFAP.DirichletWindow.AreConsecutiveBest.dirichletWindowQuadrance_le_refinedIndexFactor
      second
  have indexSumBound := coefficientIndexQuadrance_add_le_three first second
  have castIndexSumBound :
      ((coefficientIndexQuadrance lower middle +
          coefficientIndexQuadrance middle upper : Nat) : Coordinate) ≤ 3 :=
    RFAP.ConstructiveFraction.natCast_le_direct indexSumBound
  have scaledIndexSumBound :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      castIndexSumBound RFAP.DirichletWindow.refinedIndexFactor_nonneg
  calc
    dirichletWindowQuadrance source.value lower middle +
        dirichletWindowQuadrance source.value middle upper ≤
        RFAP.DirichletWindow.refinedIndexFactor *
            (coefficientIndexQuadrance lower middle : Coordinate) +
          RFAP.DirichletWindow.refinedIndexFactor *
            (coefficientIndexQuadrance middle upper : Coordinate) :=
      RFAP.ConstructiveFraction.add_le_add_direct firstBound secondBound
    _ = RFAP.DirichletWindow.refinedIndexFactor *
        ((coefficientIndexQuadrance lower middle +
          coefficientIndexQuadrance middle upper : Nat) : Coordinate) := by
      rw [Nat.cast_add]
      ring1
    _ ≤ RFAP.DirichletWindow.refinedIndexFactor * 3 := scaledIndexSumBound
    _ = refinedTwoWindowSumBound := refinedIndexFactor_mul_three

/-- The sum of two successive squared Dirichlet-window products is at most
the sharper rational `1189/34`. -/
theorem dirichletWindowQuadrance_add_le_quadraticTwoWindowSumBound
    {source : RFAP.HurwitzRational.Fraction} {lower middle upper : Pair}
    (first : AreConsecutiveBest source.value lower middle)
    (second : AreConsecutiveBest source.value middle upper) :
    dirichletWindowQuadrance source.value lower middle +
        dirichletWindowQuadrance source.value middle upper ≤
      quadraticTwoWindowSumBound := by
  have firstBound :=
    RFAP.DirichletWindow.AreConsecutiveBest.dirichletWindowQuadrance_le_quadraticIndexFactor
      first
  have secondBound :=
    RFAP.DirichletWindow.AreConsecutiveBest.dirichletWindowQuadrance_le_quadraticIndexFactor
      second
  have indexSumBound := coefficientIndexQuadrance_add_le_three first second
  have castIndexSumBound :
      ((coefficientIndexQuadrance lower middle +
          coefficientIndexQuadrance middle upper : Nat) : Coordinate) ≤ 3 :=
    RFAP.ConstructiveFraction.natCast_le_direct indexSumBound
  have scaledIndexSumBound :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      castIndexSumBound RFAP.DirichletWindow.quadraticIndexFactor_nonneg
  calc
    dirichletWindowQuadrance source.value lower middle +
        dirichletWindowQuadrance source.value middle upper ≤
        RFAP.DirichletWindow.quadraticIndexFactor *
            (coefficientIndexQuadrance lower middle : Coordinate) +
          RFAP.DirichletWindow.quadraticIndexFactor *
            (coefficientIndexQuadrance middle upper : Coordinate) :=
      RFAP.ConstructiveFraction.add_le_add_direct firstBound secondBound
    _ = RFAP.DirichletWindow.quadraticIndexFactor *
        ((coefficientIndexQuadrance lower middle +
          coefficientIndexQuadrance middle upper : Nat) : Coordinate) := by
      rw [Nat.cast_add]
      ring1
    _ ≤ RFAP.DirichletWindow.quadraticIndexFactor * 3 :=
      scaledIndexSumBound
    _ = quadraticTwoWindowSumBound := quadraticIndexFactor_mul_three

/-- The index-aware one-window theorem bounds the sum of any two successive
squared windows by `1189/51`.  This improves the earlier index-sum bound
`1189/34`: determinant index two is now handled by its centered-coset gap
rather than by twice the generic index-one factor. -/
theorem dirichletWindowQuadrance_add_le_quadraticUniversalWindowBound
    {source : RFAP.HurwitzRational.Fraction} {lower middle upper : Pair}
    (first : AreConsecutiveBest source.value lower middle)
    (second : AreConsecutiveBest source.value middle upper) :
    dirichletWindowQuadrance source.value lower middle +
        dirichletWindowQuadrance source.value middle upper ≤
      RFAP.DirichletWindow.quadraticUniversalWindowBound := by
  have firstBound :=
    RFAP.IndexTwoWindow.AreConsecutiveBest.dirichletWindowQuadrance_le_quadraticIndexFactorUniversal
      first
  have secondBound :=
    RFAP.IndexTwoWindow.AreConsecutiveBest.dirichletWindowQuadrance_le_quadraticIndexFactorUniversal
      second
  calc
    dirichletWindowQuadrance source.value lower middle +
        dirichletWindowQuadrance source.value middle upper ≤
        RFAP.DirichletWindow.quadraticIndexFactor +
          RFAP.DirichletWindow.quadraticIndexFactor :=
      RFAP.ConstructiveFraction.add_le_add_direct firstBound secondBound
    _ = RFAP.DirichletWindow.quadraticIndexFactor * 2 := by ring1
    _ = RFAP.DirichletWindow.quadraticUniversalWindowBound :=
      RFAP.DirichletWindow.quadraticIndexFactor_mul_two

/-- Two successive windows have sum at most `224/71`, by applying the current
rational universal bound `112/71` to each supplied transition. -/
theorem dirichletWindowQuadrance_add_le_finiteOctantTwoWindowSumBound
    {source : RFAP.HurwitzRational.Fraction} {lower middle upper : Pair}
    (first : AreConsecutiveBest source.value lower middle)
    (second : AreConsecutiveBest source.value middle upper) :
    dirichletWindowQuadrance source.value lower middle +
        dirichletWindowQuadrance source.value middle upper ≤
      finiteOctantTwoWindowSumBound := by
  have firstBound :=
    RFAP.IndexOneWindow.AreConsecutiveBest.dirichletWindowQuadrance_le_normTwoUniversalWindowBound
      first
  have secondBound :=
    RFAP.IndexOneWindow.AreConsecutiveBest.dirichletWindowQuadrance_le_normTwoUniversalWindowBound
      second
  calc
    dirichletWindowQuadrance source.value lower middle +
        dirichletWindowQuadrance source.value middle upper ≤
        RFAP.IndexOneWindow.normTwoIndexOneWindowBound +
          RFAP.IndexOneWindow.normTwoIndexOneWindowBound :=
      RFAP.ConstructiveFraction.add_le_add_direct firstBound secondBound
    _ = finiteOctantTwoWindowSumBound := by
      unfold finiteOctantTwoWindowSumBound
      unfold RFAP.IndexOneWindow.normTwoIndexOneWindowBound
      rw [RFAP.ConstructiveFraction.ofFraction_addFraction]
      apply RFAP.ConstructiveFraction.ofFraction_eq_of_equivalent
      change ((112 * 71 + 112 * 71) * 71 : Int) = 224 * (71 * 71)
      ring1

/-- Two successive squared windows have sum at most `512/205`, by applying
the dyadic five-obstruction/centered-coset bound to both transitions. -/
theorem dirichletWindowQuadrance_add_le_dyadicTwoWindowSumBound
    {source : RFAP.HurwitzRational.Fraction} {lower middle upper : Pair}
    (first : AreConsecutiveBest source.value lower middle)
    (second : AreConsecutiveBest source.value middle upper) :
    dirichletWindowQuadrance source.value lower middle +
        dirichletWindowQuadrance source.value middle upper ≤
      dyadicTwoWindowSumBound := by
  have firstBound :=
    RFAP.IndexOneWindow.AreConsecutiveBest.dirichletWindowQuadrance_le_sharpDyadicUniversalWindowBound
      first
  have secondBound :=
    RFAP.IndexOneWindow.AreConsecutiveBest.dirichletWindowQuadrance_le_sharpDyadicUniversalWindowBound
      second
  calc
    dirichletWindowQuadrance source.value lower middle +
        dirichletWindowQuadrance source.value middle upper ≤
        RFAP.IndexOneWindow.sharpIndexOneWindowBound +
          RFAP.IndexOneWindow.sharpIndexOneWindowBound :=
      RFAP.ConstructiveFraction.add_le_add_direct firstBound secondBound
    _ = dyadicTwoWindowSumBound := by
      unfold dyadicTwoWindowSumBound
        RFAP.IndexOneWindow.sharpIndexOneWindowBound
        RFAP.SharpIndexOneWindow.firstRegionWindowBound
      rw [RFAP.ConstructiveFraction.ofFraction_addFraction]
      apply RFAP.ConstructiveFraction.ofFraction_eq_of_equivalent
      change ((256 * 205 + 256 * 205) * 205 : Int) =
        512 * (205 * 205)
      ring1

/-- Every displayed point of the exact root-free quadratic cut scales the
sum of two successive windows by at most two. -/
theorem gapThreshold_mul_dirichletWindowQuadrance_add_le_two
    {source : RFAP.HurwitzRational.Fraction} {lower middle upper : Pair}
    (gap : Coordinate)
    (certificate : RFAP.OptimalIndexTwoWindow.IsCenteredGapThreshold gap)
    (first : AreConsecutiveBest source.value lower middle)
    (second : AreConsecutiveBest source.value middle upper) :
    gap * (dirichletWindowQuadrance source.value lower middle +
      dirichletWindowQuadrance source.value middle upper) ≤ 2 := by
  have firstBound :=
    RFAP.IndexOneWindow.AreConsecutiveBest.gapThreshold_mul_dirichletWindow_le_one
      gap certificate first
  have secondBound :=
    RFAP.IndexOneWindow.AreConsecutiveBest.gapThreshold_mul_dirichletWindow_le_one
      gap certificate second
  calc
    gap * (dirichletWindowQuadrance source.value lower middle +
        dirichletWindowQuadrance source.value middle upper) =
        gap * dirichletWindowQuadrance source.value lower middle +
          gap * dirichletWindowQuadrance source.value middle upper := by ring1
    _ ≤ 1 + 1 :=
      RFAP.ConstructiveFraction.add_le_add_direct firstBound secondBound
    _ = 2 := by ring1

/-- The finite-octant one-window theorem bounds two successive squared
windows by four. -/
theorem dirichletWindowQuadrance_add_le_four
    {source : RFAP.HurwitzRational.Fraction} {lower middle upper : Pair}
    (first : AreConsecutiveBest source.value lower middle)
    (second : AreConsecutiveBest source.value middle upper) :
    dirichletWindowQuadrance source.value lower middle +
        dirichletWindowQuadrance source.value middle upper ≤ 4 := by
  have firstBound :=
    RFAP.IndexOneWindow.AreConsecutiveBest.dirichletWindowQuadrance_le_two
      first
  have secondBound :=
    RFAP.IndexOneWindow.AreConsecutiveBest.dirichletWindowQuadrance_le_two
      second
  calc
    dirichletWindowQuadrance source.value lower middle +
        dirichletWindowQuadrance source.value middle upper ≤ 2 + 2 :=
      RFAP.ConstructiveFraction.add_le_add_direct firstBound secondBound
    _ = 4 := by ring1

end RFAP.DirichletBlock
