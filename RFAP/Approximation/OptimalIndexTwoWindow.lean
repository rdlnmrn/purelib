import mathlib.Tactic.QuotientFreeRing
import RFAP.Approximation.IndexTwoWindow
import RFAP.Approximation.OptimalIndexOneWindow

/-!
# Root-free optimal determinant-index-two window

The centered index-two chamber has the same optimal window boundary as the
index-one chamber, but its determinant gap is twice as large.  This module
keeps that boundary entirely rational.  For a displayed gap cut `t`, put
`s = t / 3`.  The condition

`t ^ 2 - 12 * t + 9 >= 0`

becomes

`s ^ 2 - 4 * s + 1 >= 0`.

The affine function

`(s / (1 - s ^ 2)) * (X + 1)`

is then a rational minorant for the larger coordinate of a normalized vector
of quadrance `X`.  At the omitted algebraic endpoint it agrees with the usual
square-root expression, but neither the definition nor its proof constructs a
square root or a completed real number.
-/

namespace RFAP.OptimalIndexTwoWindow

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianInt := RFAP.ConstructiveGaussianHeight.GaussianInt

open RFAP.ConstructiveGaussian.Gaussian
open RFAP.ConstructiveGaussianHeight.GaussianInt

/-- The norm polynomial obtained from the optimal gap polynomial by the
substitution `t = 3 * s`. -/
def normPolynomial (value : Coordinate) : Coordinate :=
  value ^ 2 - 4 * value + 1

/-- The displayed norm cut corresponding to a displayed determinant-gap cut. -/
def normCut (gap : Coordinate) : Coordinate := gap / 3

/-- The rational slope of the endpoint-exact affine coordinate minorant. -/
def componentSlope (gap : Coordinate) : Coordinate :=
  let cut := normCut gap
  cut / (1 - cut ^ 2)

/-- The endpoint-exact rational affine minorant for a larger coordinate. -/
def componentLower (gap norm : Coordinate) : Coordinate :=
  componentSlope gap * (norm + 1)

/-- The useful displayed part of the exact centered cut.  The lower bound
`3/4` is internal proof slack: it contains the previous `205/256` cut and all
rational cuts approaching the optimal quadratic boundary. -/
def IsCenteredGapThreshold (gap : Coordinate) : Prop :=
  (3 / 4 : Coordinate) ≤ gap ∧
    RFAP.OptimalIndexOneWindow.IsGapThreshold gap

theorem normCut_mul_three (gap : Coordinate) : normCut gap * 3 = gap := by
  unfold normCut
  exact RFAP.ConstructiveFraction.div_mul_cancel_of_ne gap 3 (by decide)

private theorem normCut_nonnegative
    {gap : Coordinate} (certificate : IsCenteredGapThreshold gap) :
    0 ≤ normCut gap := by
  unfold normCut
  exact RFAP.ConstructiveFraction.div_nonneg_direct
    ((show (0 : Coordinate) ≤ 3 / 4 by decide).trans certificate.1)
    (by decide)

private theorem normCut_lt_oneThird
    {gap : Coordinate} (certificate : IsCenteredGapThreshold gap) :
    normCut gap < 1 / 3 := by
  apply (RFAP.ConstructiveFraction.div_lt_iff_pos
    (show (0 : Coordinate) < 3 by decide)).mpr
  calc
    gap < 1 := certificate.2.1
    _ = (1 / 3 : Coordinate) * 3 :=
      (RFAP.ConstructiveFraction.div_mul_cancel_of_ne 1 3
        (by decide)).symm

private theorem normCut_lt_one
    {gap : Coordinate} (certificate : IsCenteredGapThreshold gap) :
    normCut gap < 1 :=
  (normCut_lt_oneThird certificate).trans (by decide)

private theorem oneFourth_le_normCut
    {gap : Coordinate} (certificate : IsCenteredGapThreshold gap) :
    (1 / 4 : Coordinate) ≤ normCut gap := by
  apply (RFAP.ConstructiveFraction.le_div_iff_pos
    (show (0 : Coordinate) < 3 by decide)).mpr
  calc
    (1 / 4 : Coordinate) * 3 = 3 / 4 := by decide
    _ ≤ gap := certificate.1

private theorem normCut_polynomial_nonnegative
    {gap : Coordinate} (certificate : IsCenteredGapThreshold gap) :
    0 ≤ normPolynomial (normCut gap) := by
  have identity :
      normPolynomial (normCut gap) * 9 =
        RFAP.OptimalIndexOneWindow.gapPolynomial gap := by
    unfold normPolynomial RFAP.OptimalIndexOneWindow.gapPolynomial
    calc
      (normCut gap ^ 2 - 4 * normCut gap + 1) * 9 =
          (normCut gap * 3) ^ 2 - 12 * (normCut gap * 3) + 9 := by
        ring1
      _ = gap ^ 2 - 12 * gap + 9 := by rw [normCut_mul_three]
  apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct (c := 9)
  · calc
      (0 : Coordinate) * 9 = 0 := by ring1
      _ ≤ RFAP.OptimalIndexOneWindow.gapPolynomial gap := certificate.2.2
      _ = normPolynomial (normCut gap) * 9 := identity.symm
  · decide

private theorem normCut_sq_lt_one
    {gap : Coordinate} (certificate : IsCenteredGapThreshold gap) :
    normCut gap ^ 2 < 1 := by
  have cutNonnegative := normCut_nonnegative certificate
  have cutLtOne := normCut_lt_one certificate
  have cutSqLeCut : normCut gap ^ 2 ≤ normCut gap := by
    rw [pow_two]
    calc
      normCut gap * normCut gap ≤ 1 * normCut gap :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          cutLtOne.le cutNonnegative
      _ = normCut gap := by ring1
  exact cutSqLeCut.trans_lt cutLtOne

private theorem slopeDenominator_pos
    {gap : Coordinate} (certificate : IsCenteredGapThreshold gap) :
    0 < 1 - normCut gap ^ 2 :=
  RFAP.ConstructiveFraction.sub_pos_direct
    (normCut_sq_lt_one certificate)

private theorem componentSlope_mul_denominator
    {gap : Coordinate} (certificate : IsCenteredGapThreshold gap) :
    componentSlope gap * (1 - normCut gap ^ 2) = normCut gap := by
  unfold componentSlope
  exact RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ _
    (slopeDenominator_pos certificate).ne'

private theorem componentSlope_nonnegative
    {gap : Coordinate} (certificate : IsCenteredGapThreshold gap) :
    0 ≤ componentSlope gap := by
  unfold componentSlope
  exact RFAP.ConstructiveFraction.div_nonneg_direct
    (normCut_nonnegative certificate)
    (slopeDenominator_pos certificate).le

private theorem twelve_mul_componentSlope_sq_le_one
    {gap : Coordinate} (certificate : IsCenteredGapThreshold gap) :
    12 * componentSlope gap ^ 2 ≤ 1 := by
  let cut := normCut gap
  let denominator := 1 - cut ^ 2
  let slope := componentSlope gap
  have cutNonnegative : (0 : Coordinate) ≤ cut :=
    normCut_nonnegative certificate
  have polynomialNonnegative : 0 ≤ normPolynomial cut :=
    normCut_polynomial_nonnegative certificate
  have companionNonnegative : 0 ≤ cut ^ 2 + 4 * cut + 1 :=
    add_nonneg
      (add_nonneg (RFAP.ConstructiveFraction.sq_nonneg_direct cut)
        (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
          cutNonnegative))
      (by decide)
  have denominatorDifferenceNonnegative :
      0 ≤ denominator ^ 2 - 12 * cut ^ 2 := by
    calc
      0 ≤ (cut ^ 2 + 4 * cut + 1) * normPolynomial cut :=
        RFAP.ConstructiveFraction.mul_nonneg_direct companionNonnegative
          polynomialNonnegative
      _ = denominator ^ 2 - 12 * cut ^ 2 := by
        dsimp only [denominator]
        unfold normPolynomial
        ring1
  have scaledCutBound : 12 * cut ^ 2 ≤ denominator ^ 2 :=
    RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
      denominatorDifferenceNonnegative
  have denominatorPositive : 0 < denominator := by
    dsimp only [denominator, cut]
    exact slopeDenominator_pos certificate
  have denominatorSquarePositive : 0 < denominator ^ 2 :=
    RFAP.ConstructiveFraction.pow_pos_direct denominatorPositive 2
  apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct
    (c := denominator ^ 2)
  · calc
      (12 * slope ^ 2) * denominator ^ 2 =
          12 * (slope * denominator) ^ 2 := by ring1
      _ = 12 * cut ^ 2 := by
        have slopeIdentity : slope * denominator = cut := by
          dsimp only [slope, denominator, cut]
          exact componentSlope_mul_denominator certificate
        rw [slopeIdentity]
      _ ≤ denominator ^ 2 := scaledCutBound
      _ = 1 * denominator ^ 2 := by ring1
  · exact denominatorSquarePositive

private theorem four_mul_componentSlope_sq_le_half
    {gap : Coordinate} (certificate : IsCenteredGapThreshold gap) :
    4 * componentSlope gap ^ 2 ≤ 1 / 2 := by
  have scaled := twelve_mul_componentSlope_sq_le_one certificate
  apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct (c := 3)
  · calc
      (4 * componentSlope gap ^ 2) * 3 =
          12 * componentSlope gap ^ 2 := by ring1
      _ ≤ 1 := scaled
      _ ≤ (1 / 2 : Coordinate) * 3 := by decide
  · decide

private theorem componentLower_nonnegative
    {gap norm : Coordinate} (certificate : IsCenteredGapThreshold gap)
    (normNonnegative : 0 ≤ norm) :
    0 ≤ componentLower gap norm := by
  unfold componentLower
  exact RFAP.ConstructiveFraction.mul_nonneg_direct
    (componentSlope_nonnegative certificate)
    (add_nonneg normNonnegative (by decide))

private theorem componentLower_cut_mul_complement
    {gap : Coordinate} (certificate : IsCenteredGapThreshold gap) :
    componentLower gap (normCut gap) * (1 - normCut gap) = normCut gap := by
  unfold componentLower
  calc
    componentSlope gap * (normCut gap + 1) * (1 - normCut gap) =
        componentSlope gap * (1 - normCut gap ^ 2) := by ring1
    _ = normCut gap := componentSlope_mul_denominator certificate

private theorem two_mul_normCut_le_complement_sq
    {gap : Coordinate} (certificate : IsCenteredGapThreshold gap) :
    2 * normCut gap ≤ (1 - normCut gap) ^ 2 := by
  apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
  calc
    0 ≤ normPolynomial (normCut gap) :=
      normCut_polynomial_nonnegative certificate
    _ = (1 - normCut gap) ^ 2 - 2 * normCut gap := by
      unfold normPolynomial
      ring1

private theorem componentLower_cut_sq_le_half
    {gap : Coordinate} (certificate : IsCenteredGapThreshold gap) :
    componentLower gap (normCut gap) ^ 2 ≤ normCut gap / 2 := by
  let cut := normCut gap
  let complement := 1 - cut
  let lower := componentLower gap cut
  have cutNonnegative : (0 : Coordinate) ≤ cut :=
    normCut_nonnegative certificate
  have complementPositive : 0 < complement := by
    dsimp only [complement, cut]
    exact RFAP.ConstructiveFraction.sub_pos_direct
      (normCut_lt_one certificate)
  have complementSquarePositive : 0 < complement ^ 2 :=
    RFAP.ConstructiveFraction.pow_pos_direct complementPositive 2
  have scaledQuadratic : 2 * cut ^ 2 ≤ cut * complement ^ 2 := by
    have multiplied :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (two_mul_normCut_le_complement_sq certificate) cutNonnegative
    dsimp only [cut, complement] at multiplied ⊢
    convert multiplied using 1
    all_goals ring1
  apply (RFAP.ConstructiveFraction.le_div_iff_pos
    (show (0 : Coordinate) < 2 by decide)).mpr
  apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct
    (c := complement ^ 2)
  · calc
      (lower ^ 2 * 2) * complement ^ 2 =
          2 * (lower * complement) ^ 2 := by ring1
      _ = 2 * cut ^ 2 := by
        have lowerIdentity : lower * complement = cut := by
          dsimp only [lower, complement, cut]
          exact componentLower_cut_mul_complement certificate
        rw [lowerIdentity]
      _ ≤ cut * complement ^ 2 := scaledQuadratic
  · exact complementSquarePositive

/-- On the exact rational norm chamber, the endpoint-dependent affine
minorant has square at most half the quadrance. -/
theorem componentLower_sq_le_half
    {gap norm : Coordinate} (certificate : IsCenteredGapThreshold gap)
    (cutLe : normCut gap ≤ norm) (normLeOne : norm ≤ 1) :
    componentLower gap norm ^ 2 ≤ norm / 2 := by
  let cut := normCut gap
  let slope := componentSlope gap
  have cutLeOne : cut ≤ (1 : Coordinate) :=
    (normCut_lt_one certificate).le
  have normPlusCutPlusTwoLeFour : norm + cut + 2 ≤ (4 : Coordinate) := by
    have first := RFAP.ConstructiveFraction.add_le_add_direct
      normLeOne cutLeOne
    have second := RFAP.ConstructiveFraction.add_le_add_right_direct first 2
    calc
      norm + cut + 2 ≤ (1 : Coordinate) + 1 + 2 := second
      _ = 4 := by ring1
  have slopeSquareNonnegative : 0 ≤ slope ^ 2 :=
    RFAP.ConstructiveFraction.sq_nonneg_direct slope
  have scaledLeHalf :
      slope ^ 2 * (norm + cut + 2) ≤ 1 / 2 := by
    calc
      slope ^ 2 * (norm + cut + 2) ≤ slope ^ 2 * 4 :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          normPlusCutPlusTwoLeFour slopeSquareNonnegative
      _ = 4 * componentSlope gap ^ 2 := by
        dsimp only [slope]
        ring1
      _ ≤ 1 / 2 := four_mul_componentSlope_sq_le_half certificate
  have factorNonnegative :
      0 ≤ (1 / 2 : Coordinate) - slope ^ 2 * (norm + cut + 2) :=
    RFAP.ConstructiveFraction.sub_nonneg_direct scaledLeHalf
  have endpointNonnegative :
      0 ≤ cut / 2 - componentLower gap cut ^ 2 :=
    RFAP.ConstructiveFraction.sub_nonneg_direct
      (componentLower_cut_sq_le_half certificate)
  have offsetNonnegative : 0 ≤ norm - cut :=
    RFAP.ConstructiveFraction.sub_nonneg_direct cutLe
  have certificateNonnegative :
      0 ≤ (cut / 2 - componentLower gap cut ^ 2) +
        (norm - cut) *
          (1 / 2 - slope ^ 2 * (norm + cut + 2)) :=
    add_nonneg endpointNonnegative
      (RFAP.ConstructiveFraction.mul_nonneg_direct offsetNonnegative
        factorNonnegative)
  apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
  calc
    0 ≤ (cut / 2 - componentLower gap cut ^ 2) +
        (norm - cut) *
          (1 / 2 - slope ^ 2 * (norm + cut + 2)) :=
      certificateNonnegative
    _ = norm / 2 - componentLower gap norm ^ 2 := by
      unfold componentLower
      dsimp only [slope]
      rw [RFAP.IndexTwoWindow.div_two_eq_half_mul cut,
        RFAP.IndexTwoWindow.div_two_eq_half_mul norm]
      ring1

private theorem componentLower_le_largerCoordinate
    {gap large small norm : Coordinate}
    (certificate : IsCenteredGapThreshold gap)
    (largeNonnegative : 0 ≤ large) (smallNonnegative : 0 ≤ small)
    (smallLeLarge : small ≤ large)
    (normIdentity : norm = large ^ 2 + small ^ 2)
    (cutLe : normCut gap ≤ norm) (normLeOne : norm ≤ 1) :
    componentLower gap norm ≤ large := by
  have smallSquareLeLargeSquare : small ^ 2 ≤ large ^ 2 := by
    simpa only [pow_two] using
      RFAP.ConstructiveFraction.mul_le_mul_direct smallLeLarge smallLeLarge
        smallNonnegative largeNonnegative
  have halfNormLeLargeSquare : norm / 2 ≤ large ^ 2 := by
    apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct (c := 2)
    · calc
        (norm / 2) * 2 = norm :=
          RFAP.ConstructiveFraction.div_mul_cancel_of_ne norm 2 (by decide)
        _ = large ^ 2 + small ^ 2 := normIdentity
        _ ≤ large ^ 2 + large ^ 2 :=
          RFAP.ConstructiveFraction.add_le_add_direct le_rfl
            smallSquareLeLargeSquare
        _ = large ^ 2 * 2 := by ring1
    · decide
  exact RFAP.ConstructiveFraction.le_of_sq_le_sq_direct largeNonnegative
    ((componentLower_sq_le_half certificate cutLe normLeOne).trans
      halfNormLeLargeSquare)

private theorem componentSlope_le_half
    {gap : Coordinate} (certificate : IsCenteredGapThreshold gap) :
    componentSlope gap ≤ 1 / 2 := by
  have slopeNonnegative := componentSlope_nonnegative certificate
  have slopeSquareLeTwelfth :
      componentSlope gap ^ 2 ≤ 1 / 12 := by
    apply (RFAP.ConstructiveFraction.le_div_iff_pos
      (show (0 : Coordinate) < 12 by decide)).mpr
    calc
      componentSlope gap ^ 2 * 12 =
          12 * componentSlope gap ^ 2 := by ring1
      _ ≤ 1 := twelve_mul_componentSlope_sq_le_one certificate
  have slopeSquareLeQuarter :
      componentSlope gap ^ 2 ≤ (1 / 2 : Coordinate) ^ 2 :=
    slopeSquareLeTwelfth.trans (by decide)
  exact RFAP.ConstructiveFraction.le_of_sq_le_sq_direct (by decide)
    slopeSquareLeQuarter

private theorem normCut_le_componentSlope
    {gap : Coordinate} (certificate : IsCenteredGapThreshold gap) :
    normCut gap ≤ componentSlope gap := by
  let cut := normCut gap
  let denominator := 1 - cut ^ 2
  have cutNonnegative : (0 : Coordinate) ≤ cut :=
    normCut_nonnegative certificate
  have denominatorPositive : 0 < denominator := by
    dsimp only [denominator, cut]
    exact slopeDenominator_pos certificate
  have denominatorLeOne : denominator ≤ (1 : Coordinate) := by
    dsimp only [denominator]
    apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
    calc
      0 ≤ cut ^ 2 := RFAP.ConstructiveFraction.sq_nonneg_direct cut
      _ = 1 - (1 - cut ^ 2) := by ring1
  unfold componentSlope
  apply (RFAP.ConstructiveFraction.le_div_iff_pos denominatorPositive).mpr
  calc
    cut * denominator ≤ cut * 1 :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        denominatorLeOne cutNonnegative
    _ = cut := by ring1

private theorem cutFactor_nonnegative
    {gap : Coordinate} (certificate : IsCenteredGapThreshold gap) :
    0 ≤ normCut gap +
      2 * componentSlope gap ^ 2 * (normCut gap + 1) -
        (1 - normCut gap) / 2 := by
  let cut := normCut gap
  let slope := componentSlope gap
  let base := fun value : Coordinate =>
    value + 2 * value ^ 2 * (value + 1) - (1 - value) / 2
  have cutNonnegative : (0 : Coordinate) ≤ cut :=
    normCut_nonnegative certificate
  have quarterLeCut : (1 / 4 : Coordinate) ≤ cut :=
    oneFourth_le_normCut certificate
  have cutLeSlope : cut ≤ slope := by
    dsimp only [cut, slope]
    exact normCut_le_componentSlope certificate
  have cutSquareLeSlopeSquare : cut ^ 2 ≤ slope ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct cutNonnegative cutLeSlope 2
  have cutPlusOneNonnegative : 0 ≤ cut + 1 :=
    add_nonneg cutNonnegative (by decide)
  have scaledSquareLower :
      2 * cut ^ 2 * (cut + 1) ≤ 2 * slope ^ 2 * (cut + 1) := by
    exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
      (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        cutSquareLeSlopeSquare (by decide)) cutPlusOneNonnegative
  have baseQuarterPositive : (0 : Coordinate) < base (1 / 4) := by
    dsimp only [base]
    decide
  have offsetNonnegative : 0 ≤ cut - 1 / 4 :=
    RFAP.ConstructiveFraction.sub_nonneg_direct quarterLeCut
  have multiplierNonnegative :
      0 ≤ 2 * (cut ^ 2 + cut * (1 / 4) + (1 / 4) ^ 2) +
        2 * (cut + 1 / 4) + 1 + 1 / 2 := by
    exact add_nonneg
      (add_nonneg
        (add_nonneg
          (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
            (add_nonneg
              (add_nonneg (RFAP.ConstructiveFraction.sq_nonneg_direct cut)
                (RFAP.ConstructiveFraction.mul_nonneg_direct cutNonnegative
                  (by decide)))
              (RFAP.ConstructiveFraction.sq_nonneg_direct (1 / 4))))
          (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
            (add_nonneg cutNonnegative (by decide))))
        (by decide))
      (by decide)
  have baseMonotone : base (1 / 4) ≤ base cut := by
    apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
    calc
      0 ≤ (cut - 1 / 4) *
          (2 * (cut ^ 2 + cut * (1 / 4) + (1 / 4) ^ 2) +
            2 * (cut + 1 / 4) + 1 + 1 / 2) :=
        RFAP.ConstructiveFraction.mul_nonneg_direct offsetNonnegative
          multiplierNonnegative
      _ = base cut - base (1 / 4) := by
        dsimp only [base]
        rw [RFAP.IndexTwoWindow.div_two_eq_half_mul (1 - cut),
          RFAP.IndexTwoWindow.div_two_eq_half_mul (1 - 1 / 4)]
        ring1
  calc
    (0 : Coordinate) ≤ base (1 / 4) := baseQuarterPositive.le
    _ ≤ base cut := baseMonotone
    _ ≤ cut + 2 * slope ^ 2 * (cut + 1) - (1 - cut) / 2 := by
      dsimp only [base]
      calc
        cut + 2 * cut ^ 2 * (cut + 1) - (1 - cut) / 2 =
            2 * cut ^ 2 * (cut + 1) +
              (cut - (1 - cut) / 2) := by ring1
        _ ≤ 2 * slope ^ 2 * (cut + 1) +
              (cut - (1 - cut) / 2) :=
          RFAP.ConstructiveFraction.add_le_add_right_direct
            scaledSquareLower _
        _ = cut + 2 * slope ^ 2 * (cut + 1) -
              (1 - cut) / 2 := by ring1

private def alignedExcessFloor
    (gap firstNorm secondNorm : Coordinate) : Coordinate :=
  firstNorm * secondNorm +
    2 * (componentLower gap firstNorm * componentLower gap secondNorm) +
    ((1 - firstNorm) * (1 - secondNorm)) / 2

private def crossExcessFloor
    (gap firstNorm secondNorm : Coordinate) : Coordinate :=
  firstNorm * secondNorm +
    componentLower gap firstNorm * (1 - secondNorm) +
    (1 - firstNorm) * componentLower gap secondNorm

private theorem twice_half_mul_half
    (first second : Coordinate) :
    2 * ((first / 2) * (second / 2)) = (first * second) / 2 := by
  rw [RFAP.IndexTwoWindow.div_two_eq_half_mul first,
    RFAP.IndexTwoWindow.div_two_eq_half_mul second,
    RFAP.IndexTwoWindow.div_two_eq_half_mul (first * second)]
  have halfCertificate :
      (2 : Coordinate) * (1 / 2) * (1 / 2) = 1 / 2 := by decide
  calc
    2 * ((1 / 2 * first) * (1 / 2 * second)) =
        (2 * (1 / 2) * (1 / 2)) * (first * second) := by ring1
    _ = (1 / 2) * (first * second) := by rw [halfCertificate]

private theorem targetExcess_le_crossFloor
    {gap firstNorm secondNorm : Coordinate}
    (certificate : IsCenteredGapThreshold gap)
    (firstLower : normCut gap ≤ firstNorm)
    (secondLower : normCut gap ≤ secondNorm) :
    2 * gap - 1 ≤ crossExcessFloor gap firstNorm secondNorm := by
  let cut := normCut gap
  let slope := componentSlope gap
  have cutNonnegative : (0 : Coordinate) ≤ cut :=
    normCut_nonnegative certificate
  have firstNonnegative : (0 : Coordinate) ≤ firstNorm :=
    cutNonnegative.trans firstLower
  have productLower : cut ^ 2 ≤ firstNorm * secondNorm := by
    rw [pow_two]
    exact RFAP.ConstructiveFraction.mul_le_mul_direct firstLower secondLower
      cutNonnegative firstNonnegative
  have coefficientNonnegative : 0 ≤ (1 : Coordinate) - 2 * slope := by
    apply RFAP.ConstructiveFraction.sub_nonneg_direct
    calc
      2 * slope ≤ 2 * (1 / 2 : Coordinate) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (componentSlope_le_half certificate) (by decide)
      _ = 1 := by decide
  have scaledProductLower :
      (1 - 2 * slope) * cut ^ 2 ≤
        (1 - 2 * slope) * (firstNorm * secondNorm) :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct productLower
      coefficientNonnegative
  have endpointIdentity :
      2 * slope + (1 - 2 * slope) * cut ^ 2 = cut ^ 2 + 2 * cut := by
    have slopeIdentity : slope * (1 - cut ^ 2) = cut := by
      dsimp only [slope, cut]
      exact componentSlope_mul_denominator certificate
    calc
      2 * slope + (1 - 2 * slope) * cut ^ 2 =
          cut ^ 2 + 2 * (slope * (1 - cut ^ 2)) := by ring1
      _ = cut ^ 2 + 2 * cut := by rw [slopeIdentity]
  have thresholdIdentity : gap = cut * 3 := by
    dsimp only [cut]
    exact (normCut_mul_three gap).symm
  have endpointLower : 2 * gap - 1 ≤ cut ^ 2 + 2 * cut := by
    apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
    calc
      0 ≤ normPolynomial cut := normCut_polynomial_nonnegative certificate
      _ = (cut ^ 2 + 2 * cut) - (2 * gap - 1) := by
        rw [thresholdIdentity]
        unfold normPolynomial
        ring1
  calc
    2 * gap - 1 ≤ cut ^ 2 + 2 * cut := endpointLower
    _ = 2 * slope + (1 - 2 * slope) * cut ^ 2 := endpointIdentity.symm
    _ ≤ 2 * slope +
        (1 - 2 * slope) * (firstNorm * secondNorm) :=
      RFAP.ConstructiveFraction.add_le_add_direct le_rfl scaledProductLower
    _ = crossExcessFloor gap firstNorm secondNorm := by
      unfold crossExcessFloor componentLower
      dsimp only [slope]
      ring1

private theorem crossFloor_cut_cut_le_alignedFloor_cut_cut
    {gap : Coordinate} :
    crossExcessFloor gap (normCut gap) (normCut gap) ≤
      alignedExcessFloor gap (normCut gap) (normCut gap) := by
  let cut := normCut gap
  let lower := componentLower gap cut
  have squareNonnegative :
      0 ≤ 2 * (lower - (1 - cut) / 2) ^ 2 :=
    RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
      (RFAP.ConstructiveFraction.sq_nonneg_direct _)
  apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
  calc
    0 ≤ 2 * (lower - (1 - cut) / 2) ^ 2 := squareNonnegative
    _ = 2 * lower ^ 2 - 2 * lower * (1 - cut) +
        2 * ((1 - cut) / 2) ^ 2 := by
      have halfDouble : ((1 - cut) / 2) * 2 = 1 - cut :=
        RFAP.ConstructiveFraction.div_mul_cancel_of_ne (1 - cut) 2
          (by decide)
      calc
        2 * (lower - (1 - cut) / 2) ^ 2 =
            2 * lower ^ 2 -
              2 * lower * (((1 - cut) / 2) * 2) +
              2 * ((1 - cut) / 2) ^ 2 := by ring1
        _ = 2 * lower ^ 2 - 2 * lower * (1 - cut) +
              2 * ((1 - cut) / 2) ^ 2 := by rw [halfDouble]
    _ = alignedExcessFloor gap cut cut - crossExcessFloor gap cut cut := by
      unfold alignedExcessFloor crossExcessFloor
      dsimp only [lower]
      rw [← twice_half_mul_half (1 - cut) (1 - cut)]
      ring1

private theorem targetExcess_le_alignedFloor
    {gap firstNorm secondNorm : Coordinate}
    (certificate : IsCenteredGapThreshold gap)
    (firstLower : normCut gap ≤ firstNorm)
    (secondLower : normCut gap ≤ secondNorm) :
    2 * gap - 1 ≤ alignedExcessFloor gap firstNorm secondNorm := by
  let cut := normCut gap
  let slope := componentSlope gap
  let factor := fun value : Coordinate =>
    value + 2 * slope ^ 2 * (value + 1) - (1 - value) / 2
  have cutFactorNonnegative : 0 ≤ factor cut := by
    dsimp only [factor, slope, cut]
    exact cutFactor_nonnegative certificate
  have factorMonotone : ∀ value : Coordinate, cut ≤ value →
      factor cut ≤ factor value := by
    intro value cutLe
    have offsetNonnegative : 0 ≤ value - cut :=
      RFAP.ConstructiveFraction.sub_nonneg_direct cutLe
    apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
    calc
      0 ≤ (value - cut) * (1 + 2 * slope ^ 2 + 1 / 2) :=
        RFAP.ConstructiveFraction.mul_nonneg_direct offsetNonnegative
          (add_nonneg
            (add_nonneg (by decide)
              (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
                (RFAP.ConstructiveFraction.sq_nonneg_direct slope)))
            (by decide))
      _ = factor value - factor cut := by
        dsimp only [factor]
        rw [RFAP.IndexTwoWindow.div_two_eq_half_mul (1 - value),
          RFAP.IndexTwoWindow.div_two_eq_half_mul (1 - cut)]
        ring1
  have secondFactorNonnegative : 0 ≤ factor secondNorm :=
    cutFactorNonnegative.trans (factorMonotone secondNorm secondLower)
  have firstStep :
      alignedExcessFloor gap cut secondNorm ≤
        alignedExcessFloor gap firstNorm secondNorm := by
    have offsetNonnegative : 0 ≤ firstNorm - cut :=
      RFAP.ConstructiveFraction.sub_nonneg_direct firstLower
    apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
    calc
      0 ≤ (firstNorm - cut) * factor secondNorm :=
        RFAP.ConstructiveFraction.mul_nonneg_direct offsetNonnegative
          secondFactorNonnegative
      _ = alignedExcessFloor gap firstNorm secondNorm -
          alignedExcessFloor gap cut secondNorm := by
        unfold alignedExcessFloor componentLower
        dsimp only [factor, slope]
        rw [RFAP.IndexTwoWindow.div_two_eq_half_mul
            ((1 - firstNorm) * (1 - secondNorm)),
          RFAP.IndexTwoWindow.div_two_eq_half_mul
            ((1 - cut) * (1 - secondNorm)),
          RFAP.IndexTwoWindow.div_two_eq_half_mul (1 - secondNorm)]
        ring1
  have secondStep :
      alignedExcessFloor gap cut cut ≤
        alignedExcessFloor gap cut secondNorm := by
    have offsetNonnegative : 0 ≤ secondNorm - cut :=
      RFAP.ConstructiveFraction.sub_nonneg_direct secondLower
    apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
    calc
      0 ≤ (secondNorm - cut) * factor cut :=
        RFAP.ConstructiveFraction.mul_nonneg_direct offsetNonnegative
          cutFactorNonnegative
      _ = alignedExcessFloor gap cut secondNorm -
          alignedExcessFloor gap cut cut := by
        unfold alignedExcessFloor componentLower
        dsimp only [factor, slope]
        rw [RFAP.IndexTwoWindow.div_two_eq_half_mul
            ((1 - cut) * (1 - secondNorm)),
          RFAP.IndexTwoWindow.div_two_eq_half_mul
            ((1 - cut) * (1 - cut)),
          RFAP.IndexTwoWindow.div_two_eq_half_mul (1 - cut)]
        ring1
  calc
    2 * gap - 1 ≤ crossExcessFloor gap cut cut :=
      targetExcess_le_crossFloor certificate le_rfl le_rfl
    _ ≤ alignedExcessFloor gap cut cut :=
      crossFloor_cut_cut_le_alignedFloor_cut_cut
    _ ≤ alignedExcessFloor gap cut secondNorm := secondStep
    _ ≤ alignedExcessFloor gap firstNorm secondNorm := firstStep

private theorem normCut_le_of_normQuadratic
    {gap value : Coordinate}
    (certificate : IsCenteredGapThreshold gap)
    (valueInside : value < 1)
    (quadraticBound : (1 - value) ^ 2 ≤ 2 * value) :
    normCut gap ≤ value := by
  let cut := normCut gap
  have cutLtOne : cut < (1 : Coordinate) := normCut_lt_one certificate
  have cutPolynomialNonnegative : 0 ≤ normPolynomial cut :=
    normCut_polynomial_nonnegative certificate
  by_cases cutLe : cut ≤ value
  · exact cutLe
  · have valueLtCut : value < cut :=
      RFAP.ConstructiveFraction.lt_of_not_ge_direct cutLe
    have valuePlusCutLtTwo : value + cut < (2 : Coordinate) := by
      exact RFAP.ConstructiveFraction.add_lt_add_direct valueInside cutLtOne
    have valuePlusCutLtFour : value + cut < (4 : Coordinate) :=
      valuePlusCutLtTwo.trans (by decide)
    have firstFactorPositive : (0 : Coordinate) < cut - value :=
      RFAP.ConstructiveFraction.sub_pos_direct valueLtCut
    have secondFactorPositive :
        (0 : Coordinate) < 4 - value - cut := by
      have identity : 4 - value - cut = 4 - (value + cut) := by ring1
      rw [identity]
      exact RFAP.ConstructiveFraction.sub_pos_direct valuePlusCutLtFour
    have productPositive :
        (0 : Coordinate) < (cut - value) * (4 - value - cut) :=
      RFAP.ConstructiveFraction.mul_pos_direct firstFactorPositive
        secondFactorPositive
    have valuePolynomialPositive : 0 < normPolynomial value := by
      calc
        (0 : Coordinate) = 0 + 0 := by ring1
        _ ≤ normPolynomial cut + 0 :=
          RFAP.ConstructiveFraction.add_le_add_direct
            cutPolynomialNonnegative le_rfl
        _ < normPolynomial cut +
            (cut - value) * (4 - value - cut) :=
          RFAP.ConstructiveFraction.add_lt_add_left_direct productPositive _
        _ = normPolynomial value := by
          unfold normPolynomial
          ring1
    have differenceNonnegative :
        0 ≤ 2 * value - (1 - value) ^ 2 :=
      RFAP.ConstructiveFraction.sub_nonneg_direct quadraticBound
    have valuePolynomialNonpositive : normPolynomial value ≤ 0 := by
      calc
        normPolynomial value = -(2 * value - (1 - value) ^ 2) := by
          unfold normPolynomial
          ring1
        _ ≤ -0 :=
          RFAP.ConstructiveFraction.neg_le_neg_direct differenceNonnegative
        _ = 0 := by ring1
    exact (not_lt_of_ge valuePolynomialNonpositive
      valuePolynomialPositive).elim

private theorem half_complement_le_of_projection
    (norm coordinate : Coordinate)
    (projection : 1 - norm ≤ 2 * coordinate) :
    (1 - norm) / 2 ≤ coordinate := by
  apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct (c := 2)
  · calc
      ((1 - norm) / 2) * 2 = 1 - norm :=
        RFAP.ConstructiveFraction.div_mul_cancel_of_ne (1 - norm) 2
          (by decide)
      _ ≤ 2 * coordinate := projection
      _ = coordinate * 2 := by ring1
  · decide

/-- In a displayed first octant, every rational point of the exact centered
cut gives the determinant-gap family `2 * gap <= determinantGap`.  All
hypotheses and all intermediate bounds are rational coordinate inequalities. -/
theorem twice_gapThreshold_le_determinantGap_of_firstOctantObstructions
    (gap : Coordinate) (certificate : IsCenteredGapThreshold gap)
    (errorRatio denominatorRatio : Gaussian)
    (realNonnegative : 0 ≤ errorRatio.re)
    (imaginaryNonnegative : 0 ≤ errorRatio.im)
    (imaginaryLeReal : errorRatio.im ≤ errorRatio.re)
    (errorInside : normSq errorRatio < 1)
    (denominatorInside : normSq denominatorRatio < 1)
    (obstruction : ∀ unit : GaussianInt, normNat unit = 1 →
      (2 : Coordinate) ≤ normSq (errorRatio - toGaussian unit) ∨
        2 ≤ normSq (1 - toGaussian unit * denominatorRatio)) :
    2 * gap ≤ normSq (1 - denominatorRatio * errorRatio) := by
  let a := errorRatio.re
  let b := errorRatio.im
  let u := -denominatorRatio.re
  let v := denominatorRatio.im
  let firstNorm := normSq errorRatio
  let secondNorm := normSq denominatorRatio
  let firstHalfGap := (1 - firstNorm) / 2
  let secondHalfGap := (1 - secondNorm) / 2
  obtain ⟨firstQuadratic, secondQuadratic⟩ :=
    RFAP.IndexTwoWindow.complement_sq_le_two_norms_of_centeredUnitObstructions
      errorRatio denominatorRatio errorInside denominatorInside obstruction
  have firstNormLower : normCut gap ≤ firstNorm :=
    normCut_le_of_normQuadratic certificate errorInside firstQuadratic
  have secondNormLower : normCut gap ≤ secondNorm :=
    normCut_le_of_normQuadratic certificate denominatorInside secondQuadratic
  obtain ⟨bProjection, uProjectionRaw, vProjection⟩ :=
    RFAP.IndexTwoWindow.firstOctant_projectionBounds_of_centeredUnitObstructions
      errorRatio denominatorRatio realNonnegative imaginaryNonnegative
      errorInside denominatorInside obstruction
  have firstNormLeOne : firstNorm ≤ (1 : Coordinate) := errorInside.le
  have secondNormLeOne : secondNorm ≤ (1 : Coordinate) :=
    denominatorInside.le
  have firstNormNonnegative : (0 : Coordinate) ≤ firstNorm :=
    normSq_nonneg errorRatio
  have secondNormNonnegative : (0 : Coordinate) ≤ secondNorm :=
    normSq_nonneg denominatorRatio
  have firstHalfGapNonnegative : (0 : Coordinate) ≤ firstHalfGap := by
    dsimp only [firstHalfGap]
    exact RFAP.ConstructiveFraction.div_nonneg_direct
      (RFAP.ConstructiveFraction.sub_nonneg_direct firstNormLeOne)
      (by decide)
  have secondHalfGapNonnegative : (0 : Coordinate) ≤ secondHalfGap := by
    dsimp only [secondHalfGap]
    exact RFAP.ConstructiveFraction.div_nonneg_direct
      (RFAP.ConstructiveFraction.sub_nonneg_direct secondNormLeOne)
      (by decide)
  have bLower : firstHalfGap ≤ b := by
    dsimp only [firstHalfGap, firstNorm, b]
    exact half_complement_le_of_projection _ _ bProjection
  have uProjection : 1 - secondNorm ≤ 2 * u := by
    dsimp only [secondNorm, u]
    calc
      1 - normSq denominatorRatio ≤ -2 * denominatorRatio.re :=
        uProjectionRaw
      _ = 2 * (-denominatorRatio.re) := by ring1
  have uLower : secondHalfGap ≤ u := by
    dsimp only [secondHalfGap]
    exact half_complement_le_of_projection secondNorm u uProjection
  have vLower : secondHalfGap ≤ v := by
    dsimp only [secondHalfGap, secondNorm, v]
    exact half_complement_le_of_projection _ _ vProjection
  have uNonnegative : (0 : Coordinate) ≤ u :=
    secondHalfGapNonnegative.trans uLower
  have vNonnegative : (0 : Coordinate) ≤ v :=
    secondHalfGapNonnegative.trans vLower
  have firstNormIdentity : firstNorm = a ^ 2 + b ^ 2 := by
    dsimp only [firstNorm, a, b, normSq]
  have secondNormIdentity : secondNorm = u ^ 2 + v ^ 2 := by
    dsimp only [secondNorm, u, v, normSq]
    ring1
  have firstComponentLower : componentLower gap firstNorm ≤ a :=
    componentLower_le_largerCoordinate
      (gap := gap) (large := a) (small := b) (norm := firstNorm) certificate
      realNonnegative imaginaryNonnegative imaginaryLeReal firstNormIdentity
      firstNormLower firstNormLeOne
  have secondAffineNonnegative :
      (0 : Coordinate) ≤ componentLower gap secondNorm :=
    componentLower_nonnegative certificate secondNormNonnegative
  have excessLeCore :
      2 * gap - 1 ≤ firstNorm * secondNorm + 2 * (a * u + b * v) := by
    by_cases uLeV : u ≤ v
    · have secondComponentLower : componentLower gap secondNorm ≤ v :=
        componentLower_le_largerCoordinate
          (gap := gap) (large := v) (small := u) (norm := secondNorm)
          certificate
          vNonnegative uNonnegative uLeV (by
            rw [secondNormIdentity]
            ring1)
          secondNormLower secondNormLeOne
      have firstProductLower :
          componentLower gap firstNorm * secondHalfGap ≤ a * u :=
        RFAP.ConstructiveFraction.mul_le_mul_direct firstComponentLower
          uLower secondHalfGapNonnegative realNonnegative
      have secondProductLower :
          firstHalfGap * componentLower gap secondNorm ≤ b * v :=
        RFAP.ConstructiveFraction.mul_le_mul_direct bLower
          secondComponentLower secondAffineNonnegative imaginaryNonnegative
      have productSumLower :
          componentLower gap firstNorm * secondHalfGap +
              firstHalfGap * componentLower gap secondNorm ≤ a * u + b * v :=
        RFAP.ConstructiveFraction.add_le_add_direct firstProductLower
          secondProductLower
      have twiceProductSumLower :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          productSumLower (show (0 : Coordinate) ≤ 2 by decide)
      calc
        2 * gap - 1 ≤ crossExcessFloor gap firstNorm secondNorm :=
          targetExcess_le_crossFloor certificate firstNormLower secondNormLower
        _ = firstNorm * secondNorm +
            2 * (componentLower gap firstNorm * secondHalfGap +
              firstHalfGap * componentLower gap secondNorm) := by
          have firstDouble : secondHalfGap * 2 = 1 - secondNorm := by
            dsimp only [secondHalfGap]
            exact RFAP.ConstructiveFraction.div_mul_cancel_of_ne
              (1 - secondNorm) 2 (by decide)
          have secondDouble : firstHalfGap * 2 = 1 - firstNorm := by
            dsimp only [firstHalfGap]
            exact RFAP.ConstructiveFraction.div_mul_cancel_of_ne
              (1 - firstNorm) 2 (by decide)
          unfold crossExcessFloor
          rw [← firstDouble, ← secondDouble]
          ring1
        _ ≤ firstNorm * secondNorm + 2 * (a * u + b * v) :=
          RFAP.ConstructiveFraction.add_le_add_direct le_rfl
            twiceProductSumLower
    · have vLeU : v ≤ u := le_of_not_ge uLeV
      have secondComponentLower : componentLower gap secondNorm ≤ u :=
        componentLower_le_largerCoordinate
          (gap := gap) (large := u) (small := v) (norm := secondNorm)
          certificate
          uNonnegative vNonnegative vLeU secondNormIdentity secondNormLower
          secondNormLeOne
      have firstProductLower :
          componentLower gap firstNorm * componentLower gap secondNorm ≤
            a * u :=
        RFAP.ConstructiveFraction.mul_le_mul_direct firstComponentLower
          secondComponentLower secondAffineNonnegative realNonnegative
      have secondProductLower : firstHalfGap * secondHalfGap ≤ b * v :=
        RFAP.ConstructiveFraction.mul_le_mul_direct bLower vLower
          secondHalfGapNonnegative imaginaryNonnegative
      have productSumLower :
          componentLower gap firstNorm * componentLower gap secondNorm +
              firstHalfGap * secondHalfGap ≤ a * u + b * v :=
        RFAP.ConstructiveFraction.add_le_add_direct firstProductLower
          secondProductLower
      have twiceProductSumLower :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          productSumLower (show (0 : Coordinate) ≤ 2 by decide)
      calc
        2 * gap - 1 ≤ alignedExcessFloor gap firstNorm secondNorm :=
          targetExcess_le_alignedFloor certificate firstNormLower
            secondNormLower
        _ = firstNorm * secondNorm +
            2 * (componentLower gap firstNorm *
                componentLower gap secondNorm +
              firstHalfGap * secondHalfGap) := by
          unfold alignedExcessFloor
          rw [← twice_half_mul_half (1 - firstNorm) (1 - secondNorm)]
          dsimp only [firstHalfGap, secondHalfGap]
          ring1
        _ ≤ firstNorm * secondNorm + 2 * (a * u + b * v) :=
          RFAP.ConstructiveFraction.add_le_add_direct le_rfl
            twiceProductSumLower
  calc
    2 * gap = 1 + (2 * gap - 1) := by ring1
    _ ≤ 1 + (firstNorm * secondNorm + 2 * (a * u + b * v)) :=
      RFAP.ConstructiveFraction.add_le_add_direct le_rfl excessLeCore
    _ = normSq (1 - denominatorRatio * errorRatio) := by
      dsimp only [firstNorm, secondNorm, a, b, u, v, normSq]
      simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
        RFAP.ConstructiveGaussian.Gaussian.sub_im,
        RFAP.ConstructiveGaussian.Gaussian.mul_re,
        RFAP.ConstructiveGaussian.Gaussian.mul_im,
        RFAP.ConstructiveGaussian.Gaussian.one_re,
        RFAP.ConstructiveGaussian.Gaussian.one_im]
      ring1

end RFAP.OptimalIndexTwoWindow
