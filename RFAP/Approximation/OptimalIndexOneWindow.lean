import mathlib.Tactic.QuotientFreeRing
import RFAP.Approximation.SharpIndexOneWindow

/-!
# Root-free optimal determinant-index-one window

The extremal first-octant chamber has a one-vector projection whose completed
description would be `3 * sqrt 3 - 5`.  This module does not introduce that
number.  Instead it proves the exact rational cut determined by

`r ^ 2 + 10 * r - 2 = 0`.

Thus every displayed nonnegative rational on the upper side of that
polynomial boundary is an upper bound for the projection.  Complementing the
projection turns the same certificate into the determinant-gap polynomial
`t ^ 2 - 12 * t + 9`; its smaller root would conventionally be written
`6 - 3 * sqrt 3`.
-/

namespace RFAP.OptimalIndexOneWindow

abbrev Coordinate := RFAP.ConstructiveFraction.Rational

/-- The square-root-free polynomial cutting out the optimal one-vector
projection boundary. -/
def projectionPolynomial (value : Coordinate) : Coordinate :=
  value ^ 2 + 10 * value - 2

/-- The complementary polynomial cutting out the optimal index-one
determinant-gap boundary. -/
def gapPolynomial (value : Coordinate) : Coordinate :=
  value ^ 2 - 12 * value + 9

private def largeCoordinateCutFraction :
    RFAP.ConstructiveFraction.Fraction :=
  { num := 3, den := 2 ^ 6, den_pos := by decide }

/-- The rational split `3/64` used only inside the proof of the exact cut. -/
def largeCoordinateCut : Coordinate :=
  RFAP.ConstructiveFraction.ofFraction largeCoordinateCutFraction

private def interiorProjectionBoundFraction :
    RFAP.ConstructiveFraction.Fraction :=
  { num := 25, den := 2 ^ 7, den_pos := by decide }

/-- A convenient strict interior projection bound `25/128`. -/
def interiorProjectionBound : Coordinate :=
  RFAP.ConstructiveFraction.ofFraction interiorProjectionBoundFraction

private def algebraicSeparatorFraction :
    RFAP.ConstructiveFraction.Fraction :=
  { num := 13, den := 6 * 16 + 1, den_pos := by decide }

/-- A rational just above the smaller zero of the coordinate polynomial and
still below the zero required by the tangent certificate. -/
def algebraicSeparator : Coordinate :=
  RFAP.ConstructiveFraction.ofFraction algebraicSeparatorFraction

private def tangentSlopeFraction : RFAP.ConstructiveFraction.Fraction :=
  { num := 6 * 16 + 1, den := 3 * 8 + 4, den_pos := by decide }

/-- The rational slope `97/28` used for the polynomial lower support to the
circle boundary. -/
def tangentSlope : Coordinate :=
  RFAP.ConstructiveFraction.ofFraction tangentSlopeFraction

private theorem tangentSlope_mul_denominator :
    tangentSlope * (3 * 8 + 4) = 6 * 16 + 1 := by
  unfold tangentSlope
  have clearance := RFAP.ConstructiveFraction.ofFraction_mul_den
    tangentSlopeFraction
  simpa only [tangentSlopeFraction, Int.cast_add, QuotientFreeRing.intCast_mul,
    Int.cast_ofNat, Int.cast_one] using clearance

private theorem largeCoordinateCut_mul_denominator :
    largeCoordinateCut * (2 : Coordinate) ^ 6 = 3 := by
  unfold largeCoordinateCut
  have clearance := RFAP.ConstructiveFraction.ofFraction_mul_den
    largeCoordinateCutFraction
  simpa only [largeCoordinateCutFraction, QuotientFreeRing.intCast_pow,
    Int.cast_ofNat] using clearance

private theorem algebraicSeparator_mul_denominator :
    algebraicSeparator * (6 * 16 + 1) = 13 := by
  unfold algebraicSeparator
  have clearance := RFAP.ConstructiveFraction.ofFraction_mul_den
    algebraicSeparatorFraction
  simpa only [algebraicSeparatorFraction, Int.cast_add, QuotientFreeRing.intCast_mul,
    Int.cast_ofNat, Int.cast_one] using clearance

private theorem largeCoordinateCut_le_algebraicSeparator :
    largeCoordinateCut ≤ algebraicSeparator := by
  unfold largeCoordinateCut largeCoordinateCutFraction algebraicSeparator
    algebraicSeparatorFraction
  decide

private theorem algebraicSeparator_le_oneSeventh :
    algebraicSeparator ≤ (1 / 7 : Coordinate) := by
  unfold algebraicSeparator algebraicSeparatorFraction
  decide

private theorem interiorProjectionBound_nonnegative :
    (0 : Coordinate) ≤ interiorProjectionBound := by
  unfold interiorProjectionBound interiorProjectionBoundFraction
  decide

private theorem interiorProjectionBound_polynomial_nonpositive :
    projectionPolynomial interiorProjectionBound ≤ 0 := by
  unfold projectionPolynomial interiorProjectionBound
    interiorProjectionBoundFraction
  decide

private theorem smallProjectionSum_le_interiorProjectionBound :
    largeCoordinateCut + 4 / 27 ≤ interiorProjectionBound := by
  unfold largeCoordinateCut largeCoordinateCutFraction interiorProjectionBound
    interiorProjectionBoundFraction
  decide

private def majorantLinearCoefficient : Coordinate :=
  (2 : Coordinate) ^ 3 * (11 * 8 + 1)

private theorem majorantLinearCoefficient_nonnegative :
    (0 : Coordinate) ≤ majorantLinearCoefficient := by
  unfold majorantLinearCoefficient
  exact RFAP.ConstructiveFraction.mul_nonneg_direct
    (RFAP.ConstructiveFraction.pow_nonneg_direct (by decide) 3)
    (add_nonneg
      (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide) (by decide))
      (by decide))

private def majorantLinearSlack (value : Coordinate) : Coordinate :=
  majorantLinearCoefficient * value -
    (2 : Coordinate) ^ 8 * tangentSlope + (53 * 16 + 7)

private def majorantQuadraticTerm (value : Coordinate) : Coordinate :=
  (19 * 8 + 4) * value ^ 2

private theorem majorantLinearSlack_mul_denominator :
    majorantLinearSlack largeCoordinateCut * (7 * 8) = 10 * 8 + 5 := by
  unfold majorantLinearSlack majorantLinearCoefficient
  calc
    (((2 : Coordinate) ^ 3 * (11 * 8 + 1)) * largeCoordinateCut -
          (2 : Coordinate) ^ 8 * tangentSlope + (53 * 16 + 7)) *
            (7 * 8) =
        (largeCoordinateCut * (2 : Coordinate) ^ 6) * (89 * 7) -
          (tangentSlope * (3 * 8 + 4)) * (2 : Coordinate) ^ 9 +
            (53 * 16 + 7) * (7 * 8) := by ring1
    _ = 3 * (89 * 7) - (6 * 16 + 1) * (2 : Coordinate) ^ 9 +
          (53 * 16 + 7) * (7 * 8) := by
      rw [largeCoordinateCut_mul_denominator,
        tangentSlope_mul_denominator]
    _ = 10 * 8 + 5 := by ring1

private theorem majorantLinearSlack_nonnegative :
    (0 : Coordinate) ≤ majorantLinearSlack largeCoordinateCut := by
  have valueIdentity :
      majorantLinearSlack largeCoordinateCut =
        ((10 * 8 + 5) / (7 * 8) : Coordinate) := by
    apply RFAP.ConstructiveFraction.mul_right_cancel_of_ne
      (c := (7 * 8 : Coordinate)) (by decide)
    calc
      majorantLinearSlack largeCoordinateCut * (7 * 8) = 10 * 8 + 5 :=
        majorantLinearSlack_mul_denominator
      _ = ((10 * 8 + 5) / (7 * 8) : Coordinate) * (7 * 8) :=
        (RFAP.ConstructiveFraction.div_mul_cancel_of_ne (10 * 8 + 5) (7 * 8)
          (by decide)).symm
  rw [valueIdentity]
  exact RFAP.ConstructiveFraction.div_nonneg_direct (by decide) (by decide)

private theorem majorantLinearSlack_mono
    (lower upper : Coordinate) (lowerLeUpper : lower ≤ upper) :
    majorantLinearSlack lower ≤ majorantLinearSlack upper := by
  unfold majorantLinearSlack
  have scaled := RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
    lowerLeUpper majorantLinearCoefficient_nonnegative
  calc
    majorantLinearCoefficient * lower - (2 : Coordinate) ^ 8 * tangentSlope +
          (53 * 16 + 7) =
        majorantLinearCoefficient * lower +
          (-((2 : Coordinate) ^ 8 * tangentSlope) + (53 * 16 + 7)) := by ring1
    _ ≤ majorantLinearCoefficient * upper +
          (-((2 : Coordinate) ^ 8 * tangentSlope) + (53 * 16 + 7)) :=
      RFAP.ConstructiveFraction.add_le_add_right_direct scaled _
    _ = majorantLinearCoefficient * upper -
          (2 : Coordinate) ^ 8 * tangentSlope + (53 * 16 + 7) := by ring1

private theorem majorantLinearSlack_nonnegative_of_cut
    (b : Coordinate) (cutLeB : largeCoordinateCut ≤ b) :
    0 ≤ majorantLinearSlack b :=
  majorantLinearSlack_nonnegative.trans
    (majorantLinearSlack_mono largeCoordinateCut b cutLeB)

/-- Complementing a proposed gap converts its polynomial exactly into the
projection polynomial. -/
theorem projectionPolynomial_one_sub (value : Coordinate) :
    projectionPolynomial (1 - value) = gapPolynomial value := by
  unfold projectionPolynomial gapPolynomial
  ring1

/-- On the nonnegative branch, a nonpositive value of the projection
polynomial lies below every displayed rational whose polynomial value is
nonnegative.  The factorization selects the intended root without constructing
either root. -/
theorem le_of_projectionPolynomial_nonpositive
    (value bound : Coordinate)
    (boundNonnegative : 0 ≤ bound)
    (valuePolynomialNonpositive : projectionPolynomial value ≤ 0)
    (boundPolynomialNonnegative : 0 ≤ projectionPolynomial bound) :
    value ≤ bound := by
  by_cases target : value ≤ bound
  · exact target
  · have boundLtValue : bound < value := lt_of_not_ge target
    have differencePositive : 0 < value - bound :=
      RFAP.ConstructiveFraction.sub_pos_direct boundLtValue
    have valuePositive : 0 < value :=
      lt_of_le_of_lt boundNonnegative boundLtValue
    have sumPositive : 0 < value + bound + 10 := by
      have valuePlusBoundPositive : 0 < value + bound :=
        add_pos_of_pos_of_nonneg valuePositive boundNonnegative
      exact add_pos_of_pos_of_nonneg valuePlusBoundPositive (by decide)
    have productPositive :
        0 < (value - bound) * (value + bound + 10) :=
      RFAP.ConstructiveFraction.mul_pos_direct differencePositive sumPositive
    have polynomialPositive : 0 < projectionPolynomial value := by
      calc
        0 < projectionPolynomial bound +
            (value - bound) * (value + bound + 10) :=
          add_pos_of_nonneg_of_pos boundPolynomialNonnegative productPositive
        _ = projectionPolynomial value := by
          unfold projectionPolynomial
          ring1
    exact ((not_lt_of_ge valuePolynomialNonpositive) polynomialPositive).elim

/-- The rational separator already used by the dyadic proof lies below
`1/7`.  This shallow public form is useful for the exact polynomial
certificate as well. -/
theorem firstRegionSecondBoundary_le_oneSeventh :
    RFAP.SharpIndexOneWindow.firstRegionSecondBoundary ≤
      (1 / 7 : Coordinate) := by
  unfold RFAP.SharpIndexOneWindow.firstRegionSecondBoundary
  decide

/-- The circle-intersection polynomial for the smaller first-octant
coordinate.  Its smaller zero would be `1 - sqrt 3 / 2`. -/
def secondCoordinatePolynomial (value : Coordinate) : Coordinate :=
  value ^ 2 - 2 * value + 1 / 4

/-- Four times the coordinate polynomial.  This integer-coefficient form
keeps the exact chamber calculation within Lean's ordinary elaboration
limits. -/
def scaledCoordinatePolynomial (value : Coordinate) : Coordinate :=
  4 * value ^ 2 - 8 * value + 1

private theorem largeCoordinateCut_scaledPolynomial_le :
    25 * scaledCoordinatePolynomial largeCoordinateCut ≤ 16 := by
  unfold scaledCoordinatePolynomial largeCoordinateCut
    largeCoordinateCutFraction
  decide

/-- A polynomial lower support to the relevant circle arc. -/
def circleLowerSupport (value : Coordinate) : Coordinate :=
  (8 - 5 * scaledCoordinatePolynomial value) / 16

/-- The projection upper expression obtained from `circleLowerSupport`. -/
def supportedProjectionUpper (value : Coordinate) : Coordinate :=
  value + 1 / 4 * (1 - circleLowerSupport value) ^ 2 - value ^ 4

/-- A linear-in-the-coordinate-polynomial majorant.  At the algebraic
endpoint its correction vanishes and the value is `1 - 6b`. -/
def projectionMajorant (value : Coordinate) : Coordinate :=
  1 - 6 * value - tangentSlope * secondCoordinatePolynomial value

private theorem scaledCoordinatePolynomial_eq_four_mul
    (value : Coordinate) :
    scaledCoordinatePolynomial value = 4 * secondCoordinatePolynomial value := by
  unfold scaledCoordinatePolynomial secondCoordinatePolynomial
  calc
    4 * value ^ 2 - 8 * value + 1 =
        4 * value ^ 2 - 8 * value + (1 / 4 : Coordinate) * 4 := by
      rw [show (1 / 4 : Coordinate) * 4 = 1 by decide]
    _ = 4 * (value ^ 2 - 2 * value + 1 / 4) := by ring1

private theorem algebraicSeparator_coordinatePolynomial_negative :
    secondCoordinatePolynomial algebraicSeparator < 0 := by
  unfold secondCoordinatePolynomial algebraicSeparator
    algebraicSeparatorFraction
  decide

/-- The two first-region circle exclusions force the smaller-coordinate
polynomial to be nonnegative.  This is the algebraic content of saying that
the two excluded discs have not yet crossed. -/
theorem secondCoordinatePolynomial_nonnegative_of_firstRegionObstructions
    (a b xNorm : Coordinate)
    (aNonnegative : 0 ≤ a)
    (xNormIdentity : xNorm = a ^ 2 + b ^ 2)
    (xNormLeOne : xNorm ≤ 1)
    (imaginaryObstruction : 2 * b ≤ xNorm)
    (diagonalObstruction : 2 * (a + b) ≤ xNorm + 1) :
    0 ≤ secondCoordinatePolynomial b := by
  have aSquareLeNorm : a ^ 2 ≤ xNorm := by
    rw [xNormIdentity]
    exact le_add_of_nonneg_right
      (RFAP.ConstructiveFraction.sq_nonneg_direct b)
  have aSquareLeOne : a ^ 2 ≤ (1 : Coordinate) ^ 2 := by
    simpa only [one_pow] using aSquareLeNorm.trans xNormLeOne
  have aLeOne : a ≤ 1 :=
    RFAP.ConstructiveFraction.le_of_sq_le_sq_direct (by decide)
      aSquareLeOne
  have twiceBLeOne : 2 * b ≤ 1 := imaginaryObstruction.trans xNormLeOne
  have bLeHalf : b ≤ (1 / 2 : Coordinate) := by
    apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct (c := 2)
    · calc
        b * 2 = 2 * b := by ring1
        _ ≤ 1 := twiceBLeOne
        _ = (1 / 2 : Coordinate) * 2 := by decide
    · decide
  have twiceBMinusSquareLeASquare : 2 * b - b ^ 2 ≤ a ^ 2 := by
    apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
    calc
      0 ≤ xNorm - 2 * b :=
        RFAP.ConstructiveFraction.sub_nonneg_direct imaginaryObstruction
      _ = a ^ 2 - (2 * b - b ^ 2) := by
        rw [xNormIdentity]
        ring1
  have twiceBMinusSquareLeComplementSquare :
      2 * b - b ^ 2 ≤ (1 - a) ^ 2 := by
    apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
    calc
      0 ≤ xNorm + 1 - 2 * (a + b) :=
        RFAP.ConstructiveFraction.sub_nonneg_direct diagonalObstruction
      _ = (1 - a) ^ 2 - (2 * b - b ^ 2) := by
        rw [xNormIdentity]
        ring1
  have twiceBMinusSquareLeQuarter :
      2 * b - b ^ 2 ≤ (1 / 4 : Coordinate) := by
    by_cases aLeHalf : a ≤ (1 / 2 : Coordinate)
    · have aSquareLeQuarter : a ^ 2 ≤ (1 / 2 : Coordinate) ^ 2 :=
        RFAP.ConstructiveFraction.pow_le_pow_direct aNonnegative aLeHalf 2
      calc
        2 * b - b ^ 2 ≤ a ^ 2 := twiceBMinusSquareLeASquare
        _ ≤ (1 / 2 : Coordinate) ^ 2 := aSquareLeQuarter
        _ = 1 / 4 := by decide
    · have halfLeA : (1 / 2 : Coordinate) ≤ a := le_of_not_ge aLeHalf
      have complementNonnegative : 0 ≤ 1 - a :=
        RFAP.ConstructiveFraction.sub_nonneg_direct aLeOne
      have complementLeHalf : 1 - a ≤ (1 / 2 : Coordinate) := by
        apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
        calc
          0 ≤ a - 1 / 2 :=
            RFAP.ConstructiveFraction.sub_nonneg_direct halfLeA
          _ = a + -(1 / 2) := by ring1
          _ = a + ((1 / 2 : Coordinate) - 1) := by
            rw [show -(1 / 2 : Coordinate) = 1 / 2 - 1 by decide]
          _ = (1 / 2 : Coordinate) - (1 - a) := by ring1
      have complementSquareLeQuarter :
          (1 - a) ^ 2 ≤ (1 / 2 : Coordinate) ^ 2 :=
        RFAP.ConstructiveFraction.pow_le_pow_direct complementNonnegative
          complementLeHalf 2
      calc
        2 * b - b ^ 2 ≤ (1 - a) ^ 2 :=
          twiceBMinusSquareLeComplementSquare
        _ ≤ (1 / 2 : Coordinate) ^ 2 := complementSquareLeQuarter
        _ = 1 / 4 := by decide
  unfold secondCoordinatePolynomial
  apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
  calc
    0 ≤ (1 / 4 : Coordinate) - (2 * b - b ^ 2) :=
      RFAP.ConstructiveFraction.sub_nonneg_direct
        twiceBMinusSquareLeQuarter
    _ = (b ^ 2 - 2 * b + 1 / 4) - 0 := by ring1

/-- The first-region inequalities put the smaller coordinate below `1/7`.
The dyadic separator proves this without selecting the algebraic endpoint. -/
theorem second_le_oneSeventh_of_firstRegionObstructions
    (a b xNorm : Coordinate)
    (aNonnegative : 0 ≤ a)
    (xNormIdentity : xNorm = a ^ 2 + b ^ 2)
    (xNormLeOne : xNorm ≤ 1)
    (imaginaryObstruction : 2 * b ≤ xNorm)
    (diagonalObstruction : 2 * (a + b) ≤ xNorm + 1) :
    b ≤ (1 / 7 : Coordinate) :=
  (RFAP.SharpIndexOneWindow.second_le_firstRegionBoundary_of_firstRegionObstructions
        a b xNorm aNonnegative xNormIdentity xNormLeOne
        imaginaryObstruction diagonalObstruction).trans
    firstRegionSecondBoundary_le_oneSeventh

private theorem second_le_algebraicSeparator_of_polynomial
    (b : Coordinate)
    (bLeOneSeventh : b ≤ (1 / 7 : Coordinate))
    (coordinatePolynomialNonnegative :
      0 ≤ secondCoordinatePolynomial b) :
    b ≤ algebraicSeparator := by
  by_cases target : b ≤ algebraicSeparator
  · exact target
  · have separatorLtB : algebraicSeparator < b := lt_of_not_ge target
    have firstFactorPositive : 0 < b - algebraicSeparator :=
      RFAP.ConstructiveFraction.sub_pos_direct separatorLtB
    have sumLeTwoSevenths :
        b + algebraicSeparator ≤ (2 / 7 : Coordinate) := by
      calc
        b + algebraicSeparator ≤ (1 / 7 : Coordinate) + 1 / 7 :=
          RFAP.ConstructiveFraction.add_le_add_direct bLeOneSeventh
            algebraicSeparator_le_oneSeventh
        _ = 2 / 7 := by decide
    have secondFactorNegative : b + algebraicSeparator - 2 < 0 :=
      RFAP.ConstructiveFraction.sub_neg_direct
        (sumLeTwoSevenths.trans_lt (show (2 / 7 : Coordinate) < 2 by decide))
    have productNegative :
        (b - algebraicSeparator) * (b + algebraicSeparator - 2) < 0 :=
      RFAP.ConstructiveFraction.mul_neg_of_pos_of_neg_direct
        firstFactorPositive secondFactorNegative
    have polynomialNegative : secondCoordinatePolynomial b < 0 := by
      calc
        secondCoordinatePolynomial b =
            secondCoordinatePolynomial algebraicSeparator +
              (b - algebraicSeparator) *
                (b + algebraicSeparator - 2) := by
          unfold secondCoordinatePolynomial
          ring1
        _ < 0 + 0 := RFAP.ConstructiveFraction.add_lt_add_direct
          algebraicSeparator_coordinatePolynomial_negative productNegative
        _ = 0 := by ring1
    exact ((not_lt_of_ge coordinatePolynomialNonnegative)
      polynomialNegative).elim

private theorem scaledCoordinatePolynomial_le_supportThreshold
    (b : Coordinate)
    (cutLeB : largeCoordinateCut ≤ b)
    (bLeOneSeventh : b ≤ (1 / 7 : Coordinate)) :
    25 * scaledCoordinatePolynomial b ≤ 16 := by
  have differenceNonnegative : 0 ≤ b - largeCoordinateCut :=
    RFAP.ConstructiveFraction.sub_nonneg_direct cutLeB
  have sumLtTwo : b + largeCoordinateCut < 2 := by
    calc
      b + largeCoordinateCut ≤ (1 / 7 : Coordinate) + 1 / 7 :=
        RFAP.ConstructiveFraction.add_le_add_direct bLeOneSeventh
          (largeCoordinateCut_le_algebraicSeparator.trans
            algebraicSeparator_le_oneSeventh)
      _ = 2 / 7 := by decide
      _ < 2 := by decide
  have secondFactorNonpositive : 4 * (b + largeCoordinateCut) - 8 ≤ 0 := by
    have sumLeTwo : b + largeCoordinateCut ≤ 2 := sumLtTwo.le
    have scaled := RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      sumLeTwo (show (0 : Coordinate) ≤ 4 by decide)
    apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
    calc
      0 ≤ 4 * 2 - 4 * (b + largeCoordinateCut) :=
        RFAP.ConstructiveFraction.sub_nonneg_direct scaled
      _ = 0 - (4 * (b + largeCoordinateCut) - 8) := by ring1
  have productNonpositive :
      (b - largeCoordinateCut) *
          (4 * (b + largeCoordinateCut) - 8) ≤ 0 := by
    have scaled := RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      secondFactorNonpositive differenceNonnegative
    simpa only [mul_zero] using scaled
  have polynomialLeCut :
      scaledCoordinatePolynomial b ≤
        scaledCoordinatePolynomial largeCoordinateCut := by
    apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
    calc
      0 ≤ -((b - largeCoordinateCut) *
          (4 * (b + largeCoordinateCut) - 8)) := by
        have negated := RFAP.ConstructiveFraction.neg_le_neg_direct
          productNonpositive
        simpa only [neg_zero] using negated
      _ = scaledCoordinatePolynomial largeCoordinateCut -
          scaledCoordinatePolynomial b := by
        unfold scaledCoordinatePolynomial
        ring1
  calc
    25 * scaledCoordinatePolynomial b ≤
        25 * scaledCoordinatePolynomial largeCoordinateCut :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        polynomialLeCut (by decide)
    _ ≤ 16 := largeCoordinateCut_scaledPolynomial_le

private theorem circleLowerSupport_sq_le_middle
    (b : Coordinate)
    (scaledPolynomialNonnegative : 0 ≤ scaledCoordinatePolynomial b)
    (scaledPolynomialLe : 25 * scaledCoordinatePolynomial b ≤ 16) :
    circleLowerSupport b ^ 2 ≤ 2 * b - b ^ 2 := by
  let polynomial : Coordinate := scaledCoordinatePolynomial b
  let support : Coordinate := circleLowerSupport b
  let scaledSupport : Coordinate := 8 - 5 * polynomial
  have remainderNonnegative : 0 ≤ 16 - 25 * polynomial := by
    dsimp only [polynomial]
    exact RFAP.ConstructiveFraction.sub_nonneg_direct scaledPolynomialLe
  have productNonnegative : 0 ≤ polynomial * (16 - 25 * polynomial) :=
    RFAP.ConstructiveFraction.mul_nonneg_direct scaledPolynomialNonnegative
      remainderNonnegative
  have supportScale : support * 16 = scaledSupport := by
    dsimp only [support, scaledSupport]
    unfold circleLowerSupport
    exact RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ 16 (by decide)
  apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct
    (c := (2 : Coordinate) ^ 8)
  · calc
      support ^ 2 * (2 : Coordinate) ^ 8 = scaledSupport ^ 2 := by
        calc
          support ^ 2 * (2 : Coordinate) ^ 8 = (support * 16) ^ 2 := by ring1
          _ = scaledSupport ^ 2 := by rw [supportScale]
      _ ≤ (2 * b - b ^ 2) * (2 : Coordinate) ^ 8 := by
        apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
        calc
          0 ≤ polynomial * (16 - 25 * polynomial) := productNonnegative
          _ = (2 * b - b ^ 2) * (2 : Coordinate) ^ 8 -
              scaledSupport ^ 2 := by
            dsimp only [polynomial, scaledSupport]
            unfold scaledCoordinatePolynomial
            ring1
  · decide

private theorem supportedProjectionUpper_le_projectionMajorant
    (b : Coordinate)
    (scaledPolynomialNonnegative : 0 ≤ scaledCoordinatePolynomial b)
    (cutLeB : largeCoordinateCut ≤ b) :
    supportedProjectionUpper b ≤ projectionMajorant b := by
  let bracket : Coordinate :=
    majorantQuadraticTerm b + majorantLinearSlack b
  let scale : Coordinate := 7 * (2 : Coordinate) ^ 10
  have quadraticNonnegative : 0 ≤ majorantQuadraticTerm b := by
    unfold majorantQuadraticTerm
    exact RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
      (RFAP.ConstructiveFraction.sq_nonneg_direct b)
  have linearNonnegative : 0 ≤ majorantLinearSlack b :=
    majorantLinearSlack_nonnegative_of_cut b cutLeB
  have bracketNonnegative : 0 ≤ bracket := by
    dsimp only [bracket]
    exact add_nonneg quadraticNonnegative linearNonnegative
  have scaledBracketNonnegative : 0 ≤ 7 * bracket :=
    RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
      bracketNonnegative
  have productNonnegative :
      0 ≤ scaledCoordinatePolynomial b * (7 * bracket) :=
    RFAP.ConstructiveFraction.mul_nonneg_direct scaledPolynomialNonnegative
      scaledBracketNonnegative
  have supportScale :
      circleLowerSupport b * 16 =
        8 - 5 * scaledCoordinatePolynomial b := by
    unfold circleLowerSupport
    exact RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ 16 (by decide)
  have complementScale :
      (1 - circleLowerSupport b) * 16 =
        8 + 5 * scaledCoordinatePolynomial b := by
    calc
      (1 - circleLowerSupport b) * 16 =
          16 - circleLowerSupport b * 16 := by ring1
      _ = 16 - (8 - 5 * scaledCoordinatePolynomial b) := by
        rw [supportScale]
      _ = 8 + 5 * scaledCoordinatePolynomial b := by ring1
  have supportedScale :
      supportedProjectionUpper b * (2 : Coordinate) ^ 10 =
        (2 : Coordinate) ^ 10 * b +
          (8 + 5 * scaledCoordinatePolynomial b) ^ 2 -
            (2 : Coordinate) ^ 10 * b ^ 4 := by
    unfold supportedProjectionUpper
    calc
      (b + 1 / 4 * (1 - circleLowerSupport b) ^ 2 - b ^ 4) *
            (2 : Coordinate) ^ 10 =
          (2 : Coordinate) ^ 10 * b +
            ((1 / 4 : Coordinate) * (2 : Coordinate) ^ 10) *
              (1 - circleLowerSupport b) ^ 2 -
                (2 : Coordinate) ^ 10 * b ^ 4 := by ring1
      _ =
          (2 : Coordinate) ^ 10 * b +
            (1 - circleLowerSupport b) ^ 2 * (2 : Coordinate) ^ 8 -
              (2 : Coordinate) ^ 10 * b ^ 4 := by
        rw [show (1 / 4 : Coordinate) * (2 : Coordinate) ^ 10 =
          (2 : Coordinate) ^ 8 by decide]
        ring1
      _ = (2 : Coordinate) ^ 10 * b +
            ((1 - circleLowerSupport b) * 16) ^ 2 -
              (2 : Coordinate) ^ 10 * b ^ 4 := by ring1
      _ = (2 : Coordinate) ^ 10 * b +
            (8 + 5 * scaledCoordinatePolynomial b) ^ 2 -
              (2 : Coordinate) ^ 10 * b ^ 4 := by rw [complementScale]
  have majorantScale :
      projectionMajorant b * 4 =
        4 * (1 - 6 * b) -
          tangentSlope * scaledCoordinatePolynomial b := by
    unfold projectionMajorant
    calc
      (1 - 6 * b - tangentSlope * secondCoordinatePolynomial b) * 4 =
          4 * (1 - 6 * b) - tangentSlope *
            (4 * secondCoordinatePolynomial b) := by ring1
      _ = 4 * (1 - 6 * b) -
          tangentSlope * scaledCoordinatePolynomial b := by
        rw [← scaledCoordinatePolynomial_eq_four_mul]
  have scaledDifference :
      (projectionMajorant b - supportedProjectionUpper b) * scale =
        scaledCoordinatePolynomial b * (7 * bracket) := by
    dsimp only [scale, bracket]
    calc
      (projectionMajorant b - supportedProjectionUpper b) *
            (7 * (2 : Coordinate) ^ 10) =
          (projectionMajorant b * 4) * (7 * (2 : Coordinate) ^ 8) -
            (supportedProjectionUpper b * (2 : Coordinate) ^ 10) * 7 := by
        ring1
      _ = (4 * (1 - 6 * b) -
              tangentSlope * scaledCoordinatePolynomial b) *
              (7 * (2 : Coordinate) ^ 8) -
            ((2 : Coordinate) ^ 10 * b +
              (8 + 5 * scaledCoordinatePolynomial b) ^ 2 -
                (2 : Coordinate) ^ 10 * b ^ 4) * 7 := by
        rw [majorantScale, supportedScale]
      _ = scaledCoordinatePolynomial b *
            (7 * (majorantQuadraticTerm b + majorantLinearSlack b)) := by
        unfold majorantQuadraticTerm majorantLinearSlack
          majorantLinearCoefficient scaledCoordinatePolynomial
        ring1
  apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
  apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct (c := scale)
  · calc
      0 * scale = 0 := by ring1
      _ ≤ scaledCoordinatePolynomial b * (7 * bracket) := productNonnegative
      _ = (projectionMajorant b - supportedProjectionUpper b) * scale :=
        scaledDifference.symm
  · dsimp only [scale]
    exact RFAP.ConstructiveFraction.mul_pos_direct (by decide)
      (RFAP.ConstructiveFraction.pow_pos_direct (by decide) 10)

private def majorantPolynomialQuotient (value : Coordinate) : Coordinate :=
  4 * ((6 * 16 + 1) * value) ^ 2 +
    4 * (17 * 8 + 6) * ((6 * 16 + 1) * value) -
      (4 * (5 * 13 * 31) + 3)

private theorem majorantPolynomialQuotient_nonpositive
    (b : Coordinate) (bNonnegative : 0 ≤ b)
    (bLeSeparator : b ≤ algebraicSeparator) :
    majorantPolynomialQuotient b ≤ 0 := by
  let scaledB : Coordinate := (6 * 16 + 1) * b
  have scaleNonnegative : (0 : Coordinate) ≤ 6 * 16 + 1 := by
    exact add_nonneg
      (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide) (by decide))
      (by decide)
  have scaledBNonnegative : 0 ≤ scaledB := by
    dsimp only [scaledB]
    exact RFAP.ConstructiveFraction.mul_nonneg_direct scaleNonnegative
      bNonnegative
  have scaledBLeThirteen : scaledB ≤ 13 := by
    have scaled := RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      bLeSeparator scaleNonnegative
    calc
      scaledB = (6 * 16 + 1) * b := rfl
      _ ≤ (6 * 16 + 1) * algebraicSeparator := scaled
      _ = algebraicSeparator * (6 * 16 + 1) := by ring1
      _ = 13 := algebraicSeparator_mul_denominator
  have squareLe : scaledB ^ 2 ≤ (13 : Coordinate) ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct scaledBNonnegative
      scaledBLeThirteen 2
  have squareTermLe :
      4 * scaledB ^ 2 ≤ 4 * (13 : Coordinate) ^ 2 :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct squareLe
      (by decide)
  have linearCoefficientNonnegative :
      (0 : Coordinate) ≤ 4 * (17 * 8 + 6) := by
    exact RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
      (add_nonneg
        (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide) (by decide))
        (by decide))
  have linearTermLe :
      4 * (17 * 8 + 6) * scaledB ≤
        4 * (17 * 8 + 6) * 13 :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      scaledBLeThirteen linearCoefficientNonnegative
  have sumLe := RFAP.ConstructiveFraction.add_le_add_direct
    squareTermLe linearTermLe
  unfold majorantPolynomialQuotient
  change
    4 * scaledB ^ 2 + 4 * (17 * 8 + 6) * scaledB -
        (4 * (5 * 13 * 31) + 3) ≤ 0
  calc
    4 * scaledB ^ 2 + 4 * (17 * 8 + 6) * scaledB -
          (4 * (5 * 13 * 31) + 3) ≤
        (4 * (13 : Coordinate) ^ 2 + 4 * (17 * 8 + 6) * 13) -
          (4 * (5 * 13 * 31) + 3) := by
      have shifted := RFAP.ConstructiveFraction.add_le_add_right_direct sumLe
        (-(4 * (5 * 13 * 31) + 3))
      simpa only [sub_eq_add_neg] using shifted
    _ = -3 := by ring1
    _ ≤ 0 := by decide

private theorem projectionMajorant_polynomial_nonpositive
    (b : Coordinate) (bNonnegative : 0 ≤ b)
    (coordinatePolynomialNonnegative :
      0 ≤ secondCoordinatePolynomial b)
    (bLeSeparator : b ≤ algebraicSeparator) :
    projectionPolynomial (projectionMajorant b) ≤ 0 := by
  let scale : Coordinate := 7 * 16
  let scaledMajorant : Coordinate :=
    scale * (1 - 6 * b) - (6 * 16 + 1) * scaledCoordinatePolynomial b
  have scaledPolynomialNonnegative : 0 ≤ scaledCoordinatePolynomial b := by
    rw [scaledCoordinatePolynomial_eq_four_mul]
    exact RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
      coordinatePolynomialNonnegative
  have quotientNonpositive : majorantPolynomialQuotient b ≤ 0 :=
    majorantPolynomialQuotient_nonpositive b bNonnegative bLeSeparator
  have productNonpositive :
      scaledCoordinatePolynomial b * majorantPolynomialQuotient b ≤ 0 := by
    have scaled := RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      quotientNonpositive scaledPolynomialNonnegative
    simpa only [mul_zero] using scaled
  have majorantScale : projectionMajorant b * scale = scaledMajorant := by
    dsimp only [scale, scaledMajorant]
    unfold projectionMajorant
    calc
      (1 - 6 * b - tangentSlope * secondCoordinatePolynomial b) *
            (7 * 16) =
          (7 * 16) * (1 - 6 * b) -
            (tangentSlope * (3 * 8 + 4)) *
              (4 * secondCoordinatePolynomial b) := by ring1
      _ = (7 * 16) * (1 - 6 * b) -
            (6 * 16 + 1) * (4 * secondCoordinatePolynomial b) := by
        rw [tangentSlope_mul_denominator]
      _ = (7 * 16) * (1 - 6 * b) -
            (6 * 16 + 1) * scaledCoordinatePolynomial b := by
        rw [scaledCoordinatePolynomial_eq_four_mul]
  have factorization :
      projectionPolynomial (projectionMajorant b) * scale ^ 2 =
        scaledCoordinatePolynomial b * majorantPolynomialQuotient b := by
    calc
      projectionPolynomial (projectionMajorant b) * scale ^ 2 =
          (projectionMajorant b * scale) ^ 2 +
            10 * scale * (projectionMajorant b * scale) -
              2 * scale ^ 2 := by
        unfold projectionPolynomial
        ring1
      _ = scaledMajorant ^ 2 + 10 * scale * scaledMajorant -
            2 * scale ^ 2 := by rw [majorantScale]
      _ = scaledCoordinatePolynomial b * majorantPolynomialQuotient b := by
        dsimp only [scale, scaledMajorant]
        unfold majorantPolynomialQuotient scaledCoordinatePolynomial
        ring1
  apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct (c := scale ^ 2)
  · calc
      projectionPolynomial (projectionMajorant b) * scale ^ 2 =
          scaledCoordinatePolynomial b * majorantPolynomialQuotient b :=
        factorization
      _ ≤ 0 := productNonpositive
      _ = 0 * scale ^ 2 := by ring1
  · dsimp only [scale]
    exact RFAP.ConstructiveFraction.pow_pos_direct
      (RFAP.ConstructiveFraction.mul_pos_direct (by decide) (by decide)) 2

private theorem firstHalfProjectionUpper_le_linearBoundary
    (b : Coordinate) (bNonnegative : 0 ≤ b)
    (coordinatePolynomialNonnegative :
      0 ≤ secondCoordinatePolynomial b) :
    b + 1 / 16 - b ^ 4 ≤ 1 - 6 * b := by
  let upper : Coordinate := b + 1 / 16 - b ^ 4
  let linearBoundary : Coordinate := 1 - 6 * b
  let firstFactor : Coordinate := 4 * b ^ 2 - 8 * b + 1
  let secondFactor : Coordinate := 4 * b ^ 2 + 8 * b + 15
  let scaledUpper : Coordinate := 16 * b + 1 - 16 * b ^ 4
  let scaledLinearBoundary : Coordinate := 16 - 16 * 6 * b
  have firstFactorNonnegative : 0 ≤ firstFactor := by
    have scaled := RFAP.ConstructiveFraction.mul_nonneg_direct
      (show (0 : Coordinate) ≤ 4 by decide)
      coordinatePolynomialNonnegative
    calc
      0 ≤ 4 * secondCoordinatePolynomial b := scaled
      _ = firstFactor := by
        dsimp only [firstFactor]
        unfold secondCoordinatePolynomial
        calc
          4 * (b ^ 2 - 2 * b + 1 / 4) =
              4 * b ^ 2 - 8 * b + (1 / 4 : Coordinate) * 4 := by ring1
          _ = 4 * b ^ 2 - 8 * b + 1 := by
            rw [show (1 / 4 : Coordinate) * 4 = 1 by decide]
  have secondFactorNonnegative : 0 ≤ secondFactor := by
    dsimp only [secondFactor]
    exact add_nonneg
      (add_nonneg
        (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
          (RFAP.ConstructiveFraction.sq_nonneg_direct b))
        (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
          bNonnegative))
      (by decide)
  have productNonnegative : 0 ≤ firstFactor * secondFactor :=
    RFAP.ConstructiveFraction.mul_nonneg_direct firstFactorNonnegative
      secondFactorNonnegative
  have upperScale : upper * 16 = scaledUpper := by
    dsimp only [upper, scaledUpper]
    calc
      (b + 1 / 16 - b ^ 4) * 16 =
          16 * b + (1 / 16 : Coordinate) * 16 - 16 * b ^ 4 := by ring1
      _ = 16 * b + 1 - 16 * b ^ 4 := by
        rw [show (1 / 16 : Coordinate) * 16 = 1 by decide]
  have linearScale : linearBoundary * 16 = scaledLinearBoundary := by
    dsimp only [linearBoundary, scaledLinearBoundary]
    ring1
  apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct (c := 16)
  · rw [upperScale, linearScale]
    apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
    calc
      0 ≤ firstFactor * secondFactor := productNonnegative
      _ = scaledLinearBoundary - scaledUpper := by
        dsimp only [firstFactor, secondFactor, scaledLinearBoundary,
          scaledUpper]
        ring1
  · decide

private theorem firstHalfProjectionUpper_le_boundary
    (b bound : Coordinate)
    (bNonnegative : 0 ≤ b)
    (coordinatePolynomialNonnegative :
      0 ≤ secondCoordinatePolynomial b)
    (boundNonnegative : 0 ≤ bound)
    (boundPolynomialNonnegative : 0 ≤ projectionPolynomial bound) :
    b + 1 / 16 - b ^ 4 ≤ bound := by
  let upper : Coordinate := b + 1 / 16 - b ^ 4
  let linearBoundary : Coordinate := 1 - 6 * b
  have upperLeLinearBoundary : upper ≤ linearBoundary :=
    firstHalfProjectionUpper_le_linearBoundary b bNonnegative
      coordinatePolynomialNonnegative
  by_cases linearLeBound : linearBoundary ≤ bound
  · exact upperLeLinearBoundary.trans linearLeBound
  · have boundLtLinear : bound < linearBoundary := lt_of_not_ge linearLeBound
    let gap : Coordinate := 1 - bound
    let endpoint : Coordinate := gap / 6
    have gapPositive : 0 < gap := by
      dsimp only [gap, linearBoundary] at boundLtLinear ⊢
      have boundLtOne : bound < 1 := by
        calc
          bound < 1 - 6 * b := boundLtLinear
          _ ≤ 1 := by
            apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
            calc
              0 ≤ 6 * b := RFAP.ConstructiveFraction.mul_nonneg_direct
                (show (0 : Coordinate) ≤ 6 by decide) bNonnegative
              _ = 1 - (1 - 6 * b) := by ring1
      exact RFAP.ConstructiveFraction.sub_pos_direct boundLtOne
    have gapLeOne : gap ≤ 1 := by
      dsimp only [gap]
      have negated := RFAP.ConstructiveFraction.neg_le_neg_direct
        boundNonnegative
      calc
        1 - bound = 1 + -bound := rfl
        _ ≤ 1 + -0 := RFAP.ConstructiveFraction.add_le_add_direct le_rfl
          negated
        _ = 1 := by ring1
    have sixBLtGap : 6 * b < gap := by
      dsimp only [gap, linearBoundary] at boundLtLinear ⊢
      apply RFAP.ConstructiveFraction.lt_of_sub_neg_direct
      calc
        6 * b - (1 - bound) = bound - (1 - 6 * b) := by ring1
        _ < 0 := RFAP.ConstructiveFraction.sub_neg_direct boundLtLinear
    have bLeEndpoint : b ≤ endpoint := by
      apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct (c := 6)
      · calc
          b * 6 = 6 * b := by ring1
          _ ≤ gap := sixBLtGap.le
          _ = endpoint * 6 := by
            dsimp only [endpoint]
            rw [show (gap / 6 : Coordinate) * 6 = gap by
              exact RFAP.ConstructiveFraction.div_mul_cancel_of_ne gap 6
                (by decide)]
      · decide
    have endpointNonnegative : 0 ≤ endpoint := by
      dsimp only [endpoint]
      exact RFAP.ConstructiveFraction.div_nonneg_direct gapPositive.le
        (by decide)
    have endpointLeOneSixth : endpoint ≤ (1 / 6 : Coordinate) := by
      apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct (c := 6)
      · calc
          endpoint * 6 = gap := by
            dsimp only [endpoint]
            exact RFAP.ConstructiveFraction.div_mul_cancel_of_ne gap 6
              (by decide)
          _ ≤ 1 := gapLeOne
          _ = (1 / 6 : Coordinate) * 6 := by decide
      · decide
    have upperMonotone :
        upper ≤ endpoint + 1 / 16 - endpoint ^ 4 := by
      have oneSixthSquare :
          (1 / 6 : Coordinate) ^ 2 = 1 / 36 := by
        rw [pow_two, RFAP.ConstructiveFraction.div_mul_div_direct,
          _root_.one_mul]
        have sixSquared : (6 : Coordinate) * 6 = 36 := by
          change ((6 : Int) : Coordinate) * ((6 : Int) : Coordinate) =
            ((36 : Int) : Coordinate)
          rw [← RFAP.ConstructiveFraction.intCast_mul_direct (6 : Int) 6]
          congr 1
        rw [sixSquared]
      have twoThirtySixths :
          (1 / 36 : Coordinate) + 1 / 36 = 1 / 18 := by
        have thirtySixPositive : (0 : Coordinate) < 36 :=
          RFAP.ConstructiveFraction.natCast_pos_direct
            (n := 36) (by decide)
        have eighteenPositive : (0 : Coordinate) < 18 :=
          RFAP.ConstructiveFraction.natCast_pos_direct
            (n := 18) (by decide)
        have eighteenTimesTwo : (18 : Coordinate) * 2 = 36 := by
          change ((18 : Int) : Coordinate) * ((2 : Int) : Coordinate) =
            ((36 : Int) : Coordinate)
          rw [← RFAP.ConstructiveFraction.intCast_mul_direct (18 : Int) 2]
          congr 1
        apply RFAP.ConstructiveFraction.mul_right_cancel_of_ne
          (c := 36) thirtySixPositive.ne'
        rw [_root_.add_mul,
          RFAP.ConstructiveFraction.div_mul_cancel_of_ne 1 36
            thirtySixPositive.ne']
        calc
          (1 : Coordinate) + 1 = 2 := one_add_one_eq_two
          _ = (1 / 18 : Coordinate) * 36 := by
            symm
            calc
              (1 / 18 : Coordinate) * 36 = (1 / 18) * (18 * 2) := by
                rw [eighteenTimesTwo]
              _ = ((1 / 18 : Coordinate) * 18) * 2 :=
                (RFAP.ConstructiveFraction.mul_assoc _ _ _).symm
              _ = 1 * 2 := by
                rw [RFAP.ConstructiveFraction.div_mul_cancel_of_ne 1 18
                  eighteenPositive.ne']
              _ = 2 := _root_.one_mul _
      have differenceNonnegative : 0 ≤ endpoint - b :=
        RFAP.ConstructiveFraction.sub_nonneg_direct bLeEndpoint
      have bPlusEndpointLeOneThird :
          b + endpoint ≤ (1 / 3 : Coordinate) := by
        calc
          b + endpoint ≤ endpoint + endpoint :=
            RFAP.ConstructiveFraction.add_le_add_direct bLeEndpoint le_rfl
          _ ≤ (1 / 6 : Coordinate) + 1 / 6 :=
            RFAP.ConstructiveFraction.add_le_add_direct endpointLeOneSixth
              endpointLeOneSixth
          _ = 1 / 3 := by decide
      have bSquareLeOneThirtySixth : b ^ 2 ≤ (1 / 36 : Coordinate) := by
        have bLeOneSixth := bLeEndpoint.trans endpointLeOneSixth
        have squared := RFAP.ConstructiveFraction.pow_le_pow_direct
          bNonnegative bLeOneSixth 2
        calc
          b ^ 2 ≤ (1 / 6 : Coordinate) ^ 2 := squared
          _ = 1 / 36 := oneSixthSquare
      have endpointSquareLeOneThirtySixth :
          endpoint ^ 2 ≤ (1 / 36 : Coordinate) := by
        have squared := RFAP.ConstructiveFraction.pow_le_pow_direct
          endpointNonnegative endpointLeOneSixth 2
        calc
          endpoint ^ 2 ≤ (1 / 6 : Coordinate) ^ 2 := squared
          _ = 1 / 36 := oneSixthSquare
      have squareSumLeOneEighteenth :
          b ^ 2 + endpoint ^ 2 ≤ (1 / 18 : Coordinate) := by
        calc
          b ^ 2 + endpoint ^ 2 ≤ (1 / 36 : Coordinate) + 1 / 36 :=
            RFAP.ConstructiveFraction.add_le_add_direct
              bSquareLeOneThirtySixth endpointSquareLeOneThirtySixth
          _ = 1 / 18 := twoThirtySixths
      have productLeOne :
          (b + endpoint) * (b ^ 2 + endpoint ^ 2) ≤ 1 := by
        have productLe :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            squareSumLeOneEighteenth
            (by
              exact add_nonneg bNonnegative endpointNonnegative)
        calc
          (b + endpoint) * (b ^ 2 + endpoint ^ 2) ≤
              (b + endpoint) * (1 / 18 : Coordinate) := productLe
          _ ≤ (1 / 3 : Coordinate) * (1 / 18 : Coordinate) :=
            RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
              bPlusEndpointLeOneThird (by decide)
          _ ≤ 1 := by decide
      have remainingFactorNonnegative :
          0 ≤ 1 - (b + endpoint) * (b ^ 2 + endpoint ^ 2) :=
        RFAP.ConstructiveFraction.sub_nonneg_direct productLeOne
      apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
      calc
        0 ≤ (endpoint - b) *
            (1 - (b + endpoint) * (b ^ 2 + endpoint ^ 2)) :=
          RFAP.ConstructiveFraction.mul_nonneg_direct differenceNonnegative
            remainingFactorNonnegative
        _ = (endpoint + 1 / 16 - endpoint ^ 4) - upper := by
          dsimp only [upper]
          ring1
    have gapPolynomialNonnegative : 0 ≤ gapPolynomial gap := by
      calc
        0 ≤ projectionPolynomial bound := boundPolynomialNonnegative
        _ = projectionPolynomial (1 - gap) := by
          congr 1
          dsimp only [gap]
          ring1
        _ = gapPolynomial gap := projectionPolynomial_one_sub gap
    have endpointScale : endpoint * 6 = gap := by
      dsimp only [endpoint]
      exact RFAP.ConstructiveFraction.div_mul_cancel_of_ne gap 6 (by decide)
    have endpointCoordinatePolynomialNonnegative :
        0 ≤ secondCoordinatePolynomial endpoint := by
      have quarterTimesThirtySix : (1 / 4 : Coordinate) * 36 = 9 := by
        have fourPositive : (0 : Coordinate) < 4 :=
          RFAP.ConstructiveFraction.natCast_pos_direct
            (n := 4) (by decide)
        have fourTimesNine : (4 : Coordinate) * 9 = 36 := by
          change ((4 : Int) : Coordinate) * ((9 : Int) : Coordinate) =
            ((36 : Int) : Coordinate)
          rw [← RFAP.ConstructiveFraction.intCast_mul_direct (4 : Int) 9]
          congr 1
        calc
          (1 / 4 : Coordinate) * 36 = (1 / 4) * (4 * 9) := by
            rw [fourTimesNine]
          _ = ((1 / 4 : Coordinate) * 4) * 9 :=
            (RFAP.ConstructiveFraction.mul_assoc _ _ _).symm
          _ = 1 * 9 := by
            rw [RFAP.ConstructiveFraction.div_mul_cancel_of_ne 1 4
              fourPositive.ne']
          _ = 9 := _root_.one_mul _
      apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct (c := 36)
      · calc
          secondCoordinatePolynomial endpoint * 36 = gapPolynomial gap := by
            unfold secondCoordinatePolynomial gapPolynomial
            calc
              (endpoint ^ 2 - 2 * endpoint + 1 / 4) * 36 =
                  (endpoint * 6) ^ 2 - 12 * (endpoint * 6) +
                    (1 / 4 : Coordinate) * 36 := by ring1
              _ = (endpoint * 6) ^ 2 - 12 * (endpoint * 6) + 9 := by
                rw [quarterTimesThirtySix]
              _ = gap ^ 2 - 12 * gap + 9 := by rw [endpointScale]
          _ ≥ 0 := gapPolynomialNonnegative
          _ = 0 * 36 := by ring1
      · exact RFAP.ConstructiveFraction.natCast_pos_direct
          (n := 36) (by decide)
    have endpointBound : endpoint + 1 / 16 - endpoint ^ 4 ≤ bound := by
      calc
        endpoint + 1 / 16 - endpoint ^ 4 ≤ 1 - 6 * endpoint :=
          firstHalfProjectionUpper_le_linearBoundary endpoint
            endpointNonnegative endpointCoordinatePolynomialNonnegative
        _ = bound := by
          rw [show 6 * endpoint = gap by
            calc
              6 * endpoint = endpoint * 6 := by ring1
              _ = gap := endpointScale]
          dsimp only [gap]
          ring1
    exact upperMonotone.trans endpointBound

private theorem projection_le_firstHalfUpper
    (a b xNorm : Coordinate)
    (aNonnegative : 0 ≤ a) (bNonnegative : 0 ≤ b)
    (aLeHalf : a ≤ (1 / 2 : Coordinate))
    (bLeOneSeventh : b ≤ (1 / 7 : Coordinate))
    (xNormIdentity : xNorm = a ^ 2 + b ^ 2) :
    b + xNorm * (a - xNorm) ≤ b + 1 / 16 - b ^ 4 := by
  let firstFactor : Coordinate := 1 - 2 * a
  let secondFactor : Coordinate :=
    1 + 2 * a + 4 * a ^ 2 - 8 * a ^ 3 - 16 * a * b ^ 2
  have twiceALeOne : 2 * a ≤ 1 := by
    calc
      2 * a ≤ 2 * (1 / 2 : Coordinate) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct aLeHalf
          (by decide)
      _ = 1 := by decide
  have firstFactorNonnegative : 0 ≤ firstFactor := by
    dsimp only [firstFactor]
    exact RFAP.ConstructiveFraction.sub_nonneg_direct twiceALeOne
  have bSquareLe : b ^ 2 ≤ (1 / 7 : Coordinate) ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct bNonnegative bLeOneSeventh 2
  have eightBSquareLeOne : 8 * b ^ 2 ≤ 1 := by
    calc
      8 * b ^ 2 ≤ 8 * (1 / 7 : Coordinate) ^ 2 :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct bSquareLe
          (by decide)
      _ ≤ 1 := by decide
  have oneMinusEightBSquareNonnegative : 0 ≤ 1 - 8 * b ^ 2 :=
    RFAP.ConstructiveFraction.sub_nonneg_direct eightBSquareLeOne
  have secondFactorNonnegative : 0 ≤ secondFactor := by
    have middleNonnegative : 0 ≤ 4 * a ^ 2 * (1 - 2 * a) :=
      RFAP.ConstructiveFraction.mul_nonneg_direct
        (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
          (RFAP.ConstructiveFraction.sq_nonneg_direct a))
        firstFactorNonnegative
    have lastNonnegative : 0 ≤ 2 * a * (1 - 8 * b ^ 2) :=
      RFAP.ConstructiveFraction.mul_nonneg_direct
        (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide) aNonnegative)
        oneMinusEightBSquareNonnegative
    calc
      0 ≤ 1 + 4 * a ^ 2 * (1 - 2 * a) +
          2 * a * (1 - 8 * b ^ 2) :=
        add_nonneg (add_nonneg (by decide) middleNonnegative) lastNonnegative
      _ = secondFactor := by
        dsimp only [secondFactor]
        ring1
  have productNonnegative : 0 ≤ firstFactor * secondFactor :=
    RFAP.ConstructiveFraction.mul_nonneg_direct firstFactorNonnegative
      secondFactorNonnegative
  have upperScale :
      (b + 1 / 16 - b ^ 4) * 16 = 16 * b + 1 - 16 * b ^ 4 := by
    calc
      (b + 1 / 16 - b ^ 4) * 16 =
          16 * b + (1 / 16 : Coordinate) * 16 - 16 * b ^ 4 := by ring1
      _ = 16 * b + 1 - 16 * b ^ 4 := by
        rw [show (1 / 16 : Coordinate) * 16 = 1 by decide]
  have scaledDifference :
      ((b + 1 / 16 - b ^ 4) -
          (b + xNorm * (a - xNorm))) * 16 =
        firstFactor * secondFactor := by
    calc
      ((b + 1 / 16 - b ^ 4) -
          (b + xNorm * (a - xNorm))) * 16 =
        (b + 1 / 16 - b ^ 4) * 16 -
          (b + xNorm * (a - xNorm)) * 16 := by ring1
      _ = (16 * b + 1 - 16 * b ^ 4) -
          (b + xNorm * (a - xNorm)) * 16 := by rw [upperScale]
      _ = firstFactor * secondFactor := by
        rw [xNormIdentity]
        dsimp only [firstFactor, secondFactor]
        ring1
  apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
  apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct (c := 16)
  · calc
      0 * 16 = 0 := by ring1
      _ ≤ firstFactor * secondFactor := productNonnegative
      _ = ((b + 1 / 16 - b ^ 4) -
          (b + xNorm * (a - xNorm))) * 16 := scaledDifference.symm
  · decide

private theorem complementCubic_le_fourTwentySeven
    (u : Coordinate) (uLeHalf : u ≤ (1 / 2 : Coordinate)) :
    u * (1 - u) ^ 2 ≤ (4 / 27 : Coordinate) := by
  have firstFactorNonnegative : 0 ≤ 4 - 3 * u :=
    RFAP.ConstructiveFraction.sub_nonneg_direct (by
      calc
        3 * u ≤ 3 * (1 / 2 : Coordinate) :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct uLeHalf
            (by decide)
        _ ≤ 4 := by decide)
  have scaledCubic : 27 * (u * (1 - u) ^ 2) ≤ 4 := by
    apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
    calc
      0 ≤ (4 - 3 * u) * (3 * u - 1) ^ 2 :=
        RFAP.ConstructiveFraction.mul_nonneg_direct firstFactorNonnegative
          (RFAP.ConstructiveFraction.sq_nonneg_direct _)
      _ = 4 - 27 * (u * (1 - u) ^ 2) := by ring1
  apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct (c := 27)
  · calc
      (u * (1 - u) ^ 2) * 27 = 27 * (u * (1 - u) ^ 2) := by ring1
      _ ≤ 4 := scaledCubic
      _ = (4 / 27 : Coordinate) * 27 := by decide
  · decide

private theorem normTerm_le_complementCubic
    (a b xNorm : Coordinate)
    (aNonnegative : 0 ≤ a) (aLeOne : a ≤ 1)
    (xNormIdentity : xNorm = a ^ 2 + b ^ 2) :
    xNorm * (a - xNorm) ≤ (1 - a) * a ^ 2 := by
  have xNormNonnegative : 0 ≤ xNorm := by
    rw [xNormIdentity]
    exact add_nonneg
      (RFAP.ConstructiveFraction.sq_nonneg_direct a)
      (RFAP.ConstructiveFraction.sq_nonneg_direct b)
  have complementNonnegative : 0 ≤ 1 - a :=
    RFAP.ConstructiveFraction.sub_nonneg_direct aLeOne
  by_cases deltaNonnegative : 0 ≤ a - xNorm
  · have xNormLeA := RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
      deltaNonnegative
    have scaled :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        xNormLeA deltaNonnegative
    have aTermLeCubic : a * (a - xNorm) ≤ (1 - a) * a ^ 2 := by
      apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
      calc
        0 ≤ a * b ^ 2 :=
          RFAP.ConstructiveFraction.mul_nonneg_direct aNonnegative
            (RFAP.ConstructiveFraction.sq_nonneg_direct b)
        _ = (1 - a) * a ^ 2 - a * (a - xNorm) := by
          rw [xNormIdentity]
          ring1
    exact scaled.trans aTermLeCubic
  · have deltaNonpositive : a - xNorm ≤ 0 := le_of_not_ge deltaNonnegative
    have productNonpositive : xNorm * (a - xNorm) ≤ 0 := by
      have scaled := RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        deltaNonpositive xNormNonnegative
      simpa only [mul_zero] using scaled
    have cubicNonnegative : 0 ≤ (1 - a) * a ^ 2 :=
      RFAP.ConstructiveFraction.mul_nonneg_direct complementNonnegative
        (RFAP.ConstructiveFraction.sq_nonneg_direct a)
    exact productNonpositive.trans cubicNonnegative

/-- The exact root-free projection certificate for the extremal first-octant
chamber.  Any displayed nonnegative rational on the upper side of
`r^2 + 10r - 2` bounds the projection; the theorem never constructs the
smaller zero of that polynomial. -/
theorem projection_le_of_firstRegionObstructions
    (a b xNorm bound : Coordinate)
    (aNonnegative : 0 ≤ a) (bNonnegative : 0 ≤ b)
    (xNormIdentity : xNorm = a ^ 2 + b ^ 2)
    (xNormLeOne : xNorm ≤ 1)
    (imaginaryObstruction : 2 * b ≤ xNorm)
    (diagonalObstruction : 2 * (a + b) ≤ xNorm + 1)
    (boundNonnegative : 0 ≤ bound)
    (boundPolynomialNonnegative : 0 ≤ projectionPolynomial bound) :
    b + xNorm * (a - xNorm) ≤ bound := by
  have xNormNonnegative : 0 ≤ xNorm := by
    rw [xNormIdentity]
    exact add_nonneg
      (RFAP.ConstructiveFraction.sq_nonneg_direct a)
      (RFAP.ConstructiveFraction.sq_nonneg_direct b)
  have aSquareLeNorm : a ^ 2 ≤ xNorm := by
    rw [xNormIdentity]
    exact le_add_of_nonneg_right
      (RFAP.ConstructiveFraction.sq_nonneg_direct b)
  have aSquareLeOne : a ^ 2 ≤ (1 : Coordinate) ^ 2 := by
    simpa only [one_pow] using aSquareLeNorm.trans xNormLeOne
  have aLeOne : a ≤ 1 :=
    RFAP.ConstructiveFraction.le_of_sq_le_sq_direct (by decide) aSquareLeOne
  have coordinatePolynomialNonnegative :
      0 ≤ secondCoordinatePolynomial b :=
    secondCoordinatePolynomial_nonnegative_of_firstRegionObstructions
      a b xNorm aNonnegative xNormIdentity xNormLeOne
      imaginaryObstruction diagonalObstruction
  have bLeOneSeventh : b ≤ (1 / 7 : Coordinate) :=
    second_le_oneSeventh_of_firstRegionObstructions
      a b xNorm aNonnegative xNormIdentity xNormLeOne
      imaginaryObstruction diagonalObstruction
  have bLeSeparator : b ≤ algebraicSeparator :=
    second_le_algebraicSeparator_of_polynomial b bLeOneSeventh
      coordinatePolynomialNonnegative
  have scaledPolynomialNonnegative : 0 ≤ scaledCoordinatePolynomial b := by
    rw [scaledCoordinatePolynomial_eq_four_mul]
    exact RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
      coordinatePolynomialNonnegative
  have interiorLeBound : interiorProjectionBound ≤ bound :=
    le_of_projectionPolynomial_nonpositive interiorProjectionBound bound
      boundNonnegative interiorProjectionBound_polynomial_nonpositive
      boundPolynomialNonnegative
  by_cases aLeHalf : a ≤ (1 / 2 : Coordinate)
  · calc
      b + xNorm * (a - xNorm) ≤ b + 1 / 16 - b ^ 4 :=
        projection_le_firstHalfUpper a b xNorm aNonnegative bNonnegative
          aLeHalf bLeOneSeventh xNormIdentity
      _ ≤ bound := firstHalfProjectionUpper_le_boundary b bound bNonnegative
        coordinatePolynomialNonnegative boundNonnegative
        boundPolynomialNonnegative
  · have halfLeA : (1 / 2 : Coordinate) ≤ a := le_of_not_ge aLeHalf
    let u : Coordinate := 1 - a
    have uNonnegative : 0 ≤ u := by
      dsimp only [u]
      exact RFAP.ConstructiveFraction.sub_nonneg_direct aLeOne
    have uLeHalf : u ≤ (1 / 2 : Coordinate) := by
      dsimp only [u]
      apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
      calc
        0 ≤ a - 1 / 2 :=
          RFAP.ConstructiveFraction.sub_nonneg_direct halfLeA
        _ = a + -(1 / 2 : Coordinate) := by ring1
        _ = a + ((1 / 2 : Coordinate) - 1) := by
          rw [show -(1 / 2 : Coordinate) = 1 / 2 - 1 by decide]
        _ = (1 / 2 : Coordinate) - (1 - a) := by ring1
    by_cases cutLeB : largeCoordinateCut ≤ b
    · have scaledPolynomialLe : 25 * scaledCoordinatePolynomial b ≤ 16 :=
        scaledCoordinatePolynomial_le_supportThreshold b cutLeB bLeOneSeventh
      have middleLeUSquare : 2 * b - b ^ 2 ≤ u ^ 2 := by
        apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
        calc
          0 ≤ xNorm + 1 - 2 * (a + b) :=
            RFAP.ConstructiveFraction.sub_nonneg_direct diagonalObstruction
          _ = u ^ 2 - (2 * b - b ^ 2) := by
            dsimp only [u]
            rw [xNormIdentity]
            ring1
      have supportSquareLeUSquare : circleLowerSupport b ^ 2 ≤ u ^ 2 :=
        (circleLowerSupport_sq_le_middle b scaledPolynomialNonnegative
          scaledPolynomialLe).trans middleLeUSquare
      have fivePolynomialLeEight :
          5 * scaledCoordinatePolynomial b ≤ 8 := by
        apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct (c := 5)
        · calc
            (5 * scaledCoordinatePolynomial b) * 5 =
                25 * scaledCoordinatePolynomial b := by ring1
            _ ≤ 16 := scaledPolynomialLe
            _ ≤ 8 * 5 := by decide
        · decide
      have supportNonnegative : 0 ≤ circleLowerSupport b := by
        unfold circleLowerSupport
        exact RFAP.ConstructiveFraction.div_nonneg_direct
          (RFAP.ConstructiveFraction.sub_nonneg_direct fivePolynomialLeEight)
          (by decide)
      have supportLeU : circleLowerSupport b ≤ u :=
        RFAP.ConstructiveFraction.le_of_sq_le_sq_direct uNonnegative
          supportSquareLeUSquare
      have aLeSupportComplement : a ≤ 1 - circleLowerSupport b := by
        apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
        calc
          0 ≤ u - circleLowerSupport b :=
            RFAP.ConstructiveFraction.sub_nonneg_direct supportLeU
          _ = (1 - circleLowerSupport b) - a := by
            dsimp only [u]
            ring1
      have supportComplementNonnegative :
          0 ≤ 1 - circleLowerSupport b :=
        aNonnegative.trans aLeSupportComplement
      have aSquareLeSupportComplementSquare :
          a ^ 2 ≤ (1 - circleLowerSupport b) ^ 2 :=
        RFAP.ConstructiveFraction.pow_le_pow_direct aNonnegative
          aLeSupportComplement 2
      have bSquareLeNormMinusHalfA :
          b ^ 2 ≤ xNorm - (1 / 2 : Coordinate) * a := by
        apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
        calc
          0 ≤ a * (a - 1 / 2) :=
            RFAP.ConstructiveFraction.mul_nonneg_direct aNonnegative
              (RFAP.ConstructiveFraction.sub_nonneg_direct halfLeA)
          _ = (xNorm - (1 / 2 : Coordinate) * a) - b ^ 2 := by
            rw [xNormIdentity]
            ring1
      have twiceBSquareLe : 2 * b ^ 2 ≤ 2 * xNorm - a := by
        calc
          2 * b ^ 2 ≤ 2 * (xNorm - (1 / 2 : Coordinate) * a) :=
            RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
              bSquareLeNormMinusHalfA (by decide)
          _ = 2 * xNorm - ((1 / 2 : Coordinate) * 2) * a := by ring1
          _ = 2 * xNorm - a := by
            rw [show (1 / 2 : Coordinate) * 2 = 1 by decide]
            ring1
      have twiceBSquareNonnegative : 0 ≤ 2 * b ^ 2 :=
        RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
          (RFAP.ConstructiveFraction.sq_nonneg_direct b)
      have correctionSquareLe :
          (2 * b ^ 2) ^ 2 ≤ (2 * xNorm - a) ^ 2 :=
        RFAP.ConstructiveFraction.pow_le_pow_direct twiceBSquareNonnegative
          twiceBSquareLe 2
      have combinedLe :
          4 * (xNorm * (a - xNorm) + b ^ 4) ≤
            (1 - circleLowerSupport b) ^ 2 := by
        calc
          4 * (xNorm * (a - xNorm) + b ^ 4) =
              4 * (xNorm * (a - xNorm)) + (2 * b ^ 2) ^ 2 := by ring1
          _ ≤ 4 * (xNorm * (a - xNorm)) + (2 * xNorm - a) ^ 2 := by
            calc
              4 * (xNorm * (a - xNorm)) + (2 * b ^ 2) ^ 2 =
                  (2 * b ^ 2) ^ 2 + 4 * (xNorm * (a - xNorm)) := by ring1
              _ ≤ (2 * xNorm - a) ^ 2 + 4 * (xNorm * (a - xNorm)) :=
                RFAP.ConstructiveFraction.add_le_add_right_direct
                  correctionSquareLe _
              _ = 4 * (xNorm * (a - xNorm)) +
                  (2 * xNorm - a) ^ 2 := by ring1
          _ = a ^ 2 := by ring1
          _ ≤ (1 - circleLowerSupport b) ^ 2 :=
            aSquareLeSupportComplementSquare
      have termPlusFourthLe :
          xNorm * (a - xNorm) + b ^ 4 ≤
            1 / 4 * (1 - circleLowerSupport b) ^ 2 := by
        apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct (c := 4)
        · calc
            (xNorm * (a - xNorm) + b ^ 4) * 4 =
                4 * (xNorm * (a - xNorm) + b ^ 4) := by ring1
            _ ≤ (1 - circleLowerSupport b) ^ 2 := combinedLe
            _ = 1 * (1 - circleLowerSupport b) ^ 2 := by ring1
            _ = ((1 / 4 : Coordinate) * 4) *
                (1 - circleLowerSupport b) ^ 2 := by
              rw [show (1 / 4 : Coordinate) * 4 = 1 by decide]
            _ = (1 / 4 * (1 - circleLowerSupport b) ^ 2) * 4 := by ring1
        · decide
      have normTermLeSupportedCorrection :
          xNorm * (a - xNorm) ≤
            1 / 4 * (1 - circleLowerSupport b) ^ 2 - b ^ 4 := by
        apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
        calc
          0 ≤ 1 / 4 * (1 - circleLowerSupport b) ^ 2 -
              (xNorm * (a - xNorm) + b ^ 4) :=
            RFAP.ConstructiveFraction.sub_nonneg_direct termPlusFourthLe
          _ = (1 / 4 * (1 - circleLowerSupport b) ^ 2 - b ^ 4) -
              xNorm * (a - xNorm) := by ring1
      have projectionLeSupported :
          b + xNorm * (a - xNorm) ≤ supportedProjectionUpper b := by
        calc
          b + xNorm * (a - xNorm) ≤
              b + (1 / 4 * (1 - circleLowerSupport b) ^ 2 - b ^ 4) :=
            RFAP.ConstructiveFraction.add_le_add_direct le_rfl
              normTermLeSupportedCorrection
          _ = supportedProjectionUpper b := by
            unfold supportedProjectionUpper
            ring1
      have supportedLeMajorant :
          supportedProjectionUpper b ≤ projectionMajorant b :=
        supportedProjectionUpper_le_projectionMajorant b
          scaledPolynomialNonnegative cutLeB
      have majorantPolynomialNonpositive :
          projectionPolynomial (projectionMajorant b) ≤ 0 :=
        projectionMajorant_polynomial_nonpositive b bNonnegative
          coordinatePolynomialNonnegative bLeSeparator
      exact projectionLeSupported.trans (supportedLeMajorant.trans
        (le_of_projectionPolynomial_nonpositive (projectionMajorant b) bound
          boundNonnegative majorantPolynomialNonpositive
          boundPolynomialNonnegative))
    · have bLeCut : b ≤ largeCoordinateCut := (lt_of_not_ge cutLeB).le
      have normTermLeCubic :
          xNorm * (a - xNorm) ≤ u * (1 - u) ^ 2 := by
        calc
          xNorm * (a - xNorm) ≤ (1 - a) * a ^ 2 :=
            normTerm_le_complementCubic a b xNorm aNonnegative aLeOne
              xNormIdentity
          _ = u * (1 - u) ^ 2 := by
            dsimp only [u]
            ring1
      have cubicBound : u * (1 - u) ^ 2 ≤ (4 / 27 : Coordinate) :=
        complementCubic_le_fourTwentySeven u uLeHalf
      calc
        b + xNorm * (a - xNorm) ≤ largeCoordinateCut + 4 / 27 :=
          RFAP.ConstructiveFraction.add_le_add_direct bLeCut
            (normTermLeCubic.trans cubicBound)
        _ ≤ interiorProjectionBound := smallProjectionSum_le_interiorProjectionBound
        _ ≤ bound := interiorLeBound

/-- Two displayed vectors in the extremal chamber satisfy the complementary
determinant-gap cut.  The statement is parameterized by a rational projection
bound, so complementing it later gives the exact root-free gap polynomial. -/
theorem one_sub_projectionBound_le_gap_of_two_firstRegionObstructions
    (a b e c xNorm yNorm bound : Coordinate)
    (aNonnegative : 0 ≤ a) (bNonnegative : 0 ≤ b)
    (eNonnegative : 0 ≤ e) (cNonnegative : 0 ≤ c)
    (bLeA : b ≤ a) (cLeE : c ≤ e)
    (xNormIdentity : xNorm = a ^ 2 + b ^ 2)
    (yNormIdentity : yNorm = e ^ 2 + c ^ 2)
    (xNormLeOne : xNorm ≤ 1) (yNormLeOne : yNorm ≤ 1)
    (firstImaginaryObstruction : 2 * b ≤ xNorm)
    (firstDiagonalObstruction : 2 * (a + b) ≤ xNorm + 1)
    (secondImaginaryObstruction : 2 * c ≤ yNorm)
    (secondDiagonalObstruction : 2 * (e + c) ≤ yNorm + 1)
    (boundNonnegative : 0 ≤ bound)
    (boundPolynomialNonnegative : 0 ≤ projectionPolynomial bound) :
    1 - bound ≤ 1 + xNorm * yNorm - 2 * (a * c + b * e) := by
  have xNormNonnegative : 0 ≤ xNorm := by
    rw [xNormIdentity]
    exact add_nonneg
      (RFAP.ConstructiveFraction.sq_nonneg_direct a)
      (RFAP.ConstructiveFraction.sq_nonneg_direct b)
  have yNormNonnegative : 0 ≤ yNorm := by
    rw [yNormIdentity]
    exact add_nonneg
      (RFAP.ConstructiveFraction.sq_nonneg_direct e)
      (RFAP.ConstructiveFraction.sq_nonneg_direct c)
  have firstProjection :
      2 * (a * c + b * e) ≤ a * yNorm + b := by
    have firstScaled :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        secondImaginaryObstruction
        (RFAP.ConstructiveFraction.sub_nonneg_direct bLeA)
    have secondScaled :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        secondDiagonalObstruction bNonnegative
    have added := RFAP.ConstructiveFraction.add_le_add_direct
      firstScaled secondScaled
    calc
      2 * (a * c + b * e) =
          (a - b) * (2 * c) + b * (2 * (e + c)) := by ring1
      _ ≤ (a - b) * yNorm + b * (yNorm + 1) := added
      _ = a * yNorm + b := by ring1
  have secondProjection :
      2 * (a * c + b * e) ≤ e * xNorm + c := by
    have firstScaled :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        firstImaginaryObstruction
        (RFAP.ConstructiveFraction.sub_nonneg_direct cLeE)
    have secondScaled :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        firstDiagonalObstruction cNonnegative
    have added := RFAP.ConstructiveFraction.add_le_add_direct
      firstScaled secondScaled
    calc
      2 * (a * c + b * e) =
          (e - c) * (2 * b) + c * (2 * (a + b)) := by ring1
      _ ≤ (e - c) * xNorm + c * (xNorm + 1) := added
      _ = e * xNorm + c := by ring1
  by_cases yNormLeXNorm : yNorm ≤ xNorm
  · have projectedTermLe : b + yNorm * (a - xNorm) ≤ bound := by
      by_cases deltaNonnegative : 0 ≤ a - xNorm
      · have scaled :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
            yNormLeXNorm deltaNonnegative
        calc
          b + yNorm * (a - xNorm) ≤ b + xNorm * (a - xNorm) :=
            RFAP.ConstructiveFraction.add_le_add_direct le_rfl scaled
          _ ≤ bound := projection_le_of_firstRegionObstructions
            a b xNorm bound aNonnegative bNonnegative xNormIdentity
            xNormLeOne firstImaginaryObstruction firstDiagonalObstruction
            boundNonnegative boundPolynomialNonnegative
      · have deltaNonpositive : a - xNorm ≤ 0 := le_of_not_ge deltaNonnegative
        have productNonpositive : yNorm * (a - xNorm) ≤ 0 := by
          have scaled :=
            RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
              deltaNonpositive yNormNonnegative
          simpa only [mul_zero] using scaled
        have bLeBound : b ≤ bound := by
          calc
            b ≤ (1 / 7 : Coordinate) :=
              second_le_oneSeventh_of_firstRegionObstructions
                a b xNorm aNonnegative xNormIdentity xNormLeOne
                firstImaginaryObstruction firstDiagonalObstruction
            _ ≤ interiorProjectionBound := by
              unfold interiorProjectionBound interiorProjectionBoundFraction
              decide
            _ ≤ bound := le_of_projectionPolynomial_nonpositive
              interiorProjectionBound bound boundNonnegative
              interiorProjectionBound_polynomial_nonpositive
              boundPolynomialNonnegative
        calc
          b + yNorm * (a - xNorm) ≤ b + 0 :=
            RFAP.ConstructiveFraction.add_le_add_direct le_rfl
              productNonpositive
          _ = b := by ring1
          _ ≤ bound := bLeBound
    have negatedProjection := RFAP.ConstructiveFraction.neg_le_neg_direct
      firstProjection
    have shiftedProjection := RFAP.ConstructiveFraction.add_le_add_direct
      (le_refl (1 + xNorm * yNorm)) negatedProjection
    have negatedTerm := RFAP.ConstructiveFraction.neg_le_neg_direct
      projectedTermLe
    calc
      1 - bound ≤ 1 - (b + yNorm * (a - xNorm)) :=
        (show (1 : Coordinate) + -bound ≤
            1 + -(b + yNorm * (a - xNorm)) from
          RFAP.ConstructiveFraction.add_le_add_direct le_rfl negatedTerm)
      _ = 1 + xNorm * yNorm - (a * yNorm + b) := by ring1
      _ ≤ 1 + xNorm * yNorm - 2 * (a * c + b * e) := by
        simpa only [sub_eq_add_neg] using shiftedProjection
  · have xNormLeYNorm : xNorm ≤ yNorm := le_of_not_ge yNormLeXNorm
    have projectedTermLe : c + xNorm * (e - yNorm) ≤ bound := by
      by_cases deltaNonnegative : 0 ≤ e - yNorm
      · have scaled :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
            xNormLeYNorm deltaNonnegative
        calc
          c + xNorm * (e - yNorm) ≤ c + yNorm * (e - yNorm) :=
            RFAP.ConstructiveFraction.add_le_add_direct le_rfl scaled
          _ ≤ bound := projection_le_of_firstRegionObstructions
            e c yNorm bound eNonnegative cNonnegative yNormIdentity
            yNormLeOne secondImaginaryObstruction secondDiagonalObstruction
            boundNonnegative boundPolynomialNonnegative
      · have deltaNonpositive : e - yNorm ≤ 0 := le_of_not_ge deltaNonnegative
        have productNonpositive : xNorm * (e - yNorm) ≤ 0 := by
          have scaled :=
            RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
              deltaNonpositive xNormNonnegative
          simpa only [mul_zero] using scaled
        have cLeBound : c ≤ bound := by
          calc
            c ≤ (1 / 7 : Coordinate) :=
              second_le_oneSeventh_of_firstRegionObstructions
                e c yNorm eNonnegative yNormIdentity yNormLeOne
                secondImaginaryObstruction secondDiagonalObstruction
            _ ≤ interiorProjectionBound := by
              unfold interiorProjectionBound interiorProjectionBoundFraction
              decide
            _ ≤ bound := le_of_projectionPolynomial_nonpositive
              interiorProjectionBound bound boundNonnegative
              interiorProjectionBound_polynomial_nonpositive
              boundPolynomialNonnegative
        calc
          c + xNorm * (e - yNorm) ≤ c + 0 :=
            RFAP.ConstructiveFraction.add_le_add_direct le_rfl
              productNonpositive
          _ = c := by ring1
          _ ≤ bound := cLeBound
    have negatedProjection := RFAP.ConstructiveFraction.neg_le_neg_direct
      secondProjection
    have shiftedProjection := RFAP.ConstructiveFraction.add_le_add_direct
      (le_refl (1 + xNorm * yNorm)) negatedProjection
    have negatedTerm := RFAP.ConstructiveFraction.neg_le_neg_direct
      projectedTermLe
    calc
      1 - bound ≤ 1 - (c + xNorm * (e - yNorm)) :=
        (show (1 : Coordinate) + -bound ≤
            1 + -(c + xNorm * (e - yNorm)) from
          RFAP.ConstructiveFraction.add_le_add_direct le_rfl negatedTerm)
      _ = 1 + xNorm * yNorm - (e * xNorm + c) := by ring1
      _ ≤ 1 + xNorm * yNorm - 2 * (a * c + b * e) := by
        simpa only [sub_eq_add_neg] using shiftedProjection

/-- A displayed rational belongs to the exact determinant-gap cut when it is
below one and lies on the nonnegative side of the defining polynomial. -/
def IsGapThreshold (value : Coordinate) : Prop :=
  value < 1 ∧ 0 ≤ gapPolynomial value

private theorem gapThreshold_le_one_sub_projectionFloor
    (threshold floor : Coordinate)
    (thresholdCertificate : IsGapThreshold threshold)
    (floorPolynomialNonpositive : projectionPolynomial floor ≤ 0) :
    threshold ≤ 1 - floor := by
  let projectionBound : Coordinate := 1 - threshold
  have projectionBoundNonnegative : 0 ≤ projectionBound := by
    dsimp only [projectionBound]
    exact RFAP.ConstructiveFraction.sub_nonneg_direct
      thresholdCertificate.1.le
  have projectionBoundPolynomialNonnegative :
      0 ≤ projectionPolynomial projectionBound := by
    dsimp only [projectionBound]
    rw [projectionPolynomial_one_sub]
    exact thresholdCertificate.2
  have floorLeProjectionBound : floor ≤ projectionBound :=
    le_of_projectionPolynomial_nonpositive floor projectionBound
      projectionBoundNonnegative floorPolynomialNonpositive
      projectionBoundPolynomialNonnegative
  apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
  calc
    0 ≤ projectionBound - floor :=
      RFAP.ConstructiveFraction.sub_nonneg_direct floorLeProjectionBound
    _ = (1 - floor) - threshold := by
      dsimp only [projectionBound]
      ring1

private theorem gapThreshold_le_sixSevenths
    (threshold : Coordinate)
    (thresholdCertificate : IsGapThreshold threshold) :
    threshold ≤ (6 / 7 : Coordinate) := by
  calc
    threshold ≤ 1 - (1 / 7 : Coordinate) :=
      gapThreshold_le_one_sub_projectionFloor threshold (1 / 7)
        thresholdCertificate (by
          unfold projectionPolynomial
          decide)
    _ = 6 / 7 := by decide

private theorem gapThreshold_le_thirteenFourteenths
    (threshold : Coordinate)
    (thresholdCertificate : IsGapThreshold threshold) :
    threshold ≤ (13 / 14 : Coordinate) := by
  calc
    threshold ≤ 1 - (1 / 14 : Coordinate) :=
      gapThreshold_le_one_sub_projectionFloor threshold (1 / 14)
        thresholdCertificate (by
          unfold projectionPolynomial
          decide)
    _ = 13 / 14 := by decide

private theorem gapThreshold_le_one
    (threshold : Coordinate)
    (thresholdCertificate : IsGapThreshold threshold) :
    threshold ≤ 1 := thresholdCertificate.1.le

private theorem gapThreshold_le_gap_of_greenRegion_of_real_nonnegative
    (a b c d xNorm yNorm threshold : Coordinate)
    (aNonnegative : 0 ≤ a) (bNonnegative : 0 ≤ b)
    (bLeA : b ≤ a) (cNonnegative : 0 ≤ c)
    (xNormIdentity : xNorm = a ^ 2 + b ^ 2)
    (yNormIdentity : yNorm = c ^ 2 + d ^ 2)
    (xNormLeOne : xNorm ≤ 1) (yNormLeOne : yNorm ≤ 1)
    (errorImaginaryObstruction : 2 * b ≤ xNorm)
    (errorDiagonalObstruction : 2 * (a + b) ≤ xNorm + 1)
    (denominatorRealObstruction : 2 * c ≤ yNorm)
    (denominatorDiagonalObstruction : 2 * (c - d) ≤ yNorm + 1)
    (greenRegion : yNorm < c - d)
    (thresholdCertificate : IsGapThreshold threshold) :
    threshold ≤ 1 + xNorm * yNorm - 2 * (a * c - b * d) := by
  have twiceCLtDifference : 2 * c < c - d :=
    lt_of_le_of_lt denominatorRealObstruction greenRegion
  have cPlusDNegative : c + d < 0 := by
    calc
      c + d = 2 * c - (c - d) := by ring1
      _ < 0 := RFAP.ConstructiveFraction.sub_neg_direct twiceCLtDifference
  have dNegative : d < 0 := by
    have dLeSum : d ≤ c + d := by
      calc
        d ≤ d + c := le_add_of_nonneg_right cNonnegative
        _ = c + d := by ring1
    exact lt_of_le_of_lt dLeSum cPlusDNegative
  have negDNonnegative : 0 ≤ -d := by
    have negated := RFAP.ConstructiveFraction.neg_le_neg_direct dNegative.le
    simpa only [neg_zero] using negated
  have cLeNegD : c ≤ -d := by
    apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
    have negated := RFAP.ConstructiveFraction.neg_le_neg_direct
      cPlusDNegative.le
    calc
      0 ≤ -(c + d) := by simpa only [neg_zero] using negated
      _ = -d - c := by ring1
  have transformedNormIdentity : yNorm = (-d) ^ 2 + c ^ 2 := by
    rw [yNormIdentity]
    ring1
  have transformedDiagonalObstruction :
      2 * (-d + c) ≤ yNorm + 1 := by
    calc
      2 * (-d + c) = 2 * (c - d) := by ring1
      _ ≤ yNorm + 1 := denominatorDiagonalObstruction
  let projectionBound : Coordinate := 1 - threshold
  have projectionBoundNonnegative : 0 ≤ projectionBound := by
    dsimp only [projectionBound]
    exact RFAP.ConstructiveFraction.sub_nonneg_direct
      thresholdCertificate.1.le
  have projectionBoundPolynomialNonnegative :
      0 ≤ projectionPolynomial projectionBound := by
    dsimp only [projectionBound]
    rw [projectionPolynomial_one_sub]
    exact thresholdCertificate.2
  have bound := one_sub_projectionBound_le_gap_of_two_firstRegionObstructions
    a b (-d) c xNorm yNorm projectionBound aNonnegative bNonnegative
    negDNonnegative cNonnegative bLeA cLeNegD xNormIdentity
    transformedNormIdentity xNormLeOne yNormLeOne
    errorImaginaryObstruction errorDiagonalObstruction
    denominatorRealObstruction transformedDiagonalObstruction
    projectionBoundNonnegative projectionBoundPolynomialNonnegative
  calc
    threshold = 1 - projectionBound := by
      dsimp only [projectionBound]
      ring1
    _ ≤ 1 + xNorm * yNorm - 2 * (a * c + b * (-d)) := bound
    _ = 1 + xNorm * yNorm - 2 * (a * c - b * d) := by ring1

private theorem gapThreshold_le_gap_of_greenRegion
    (a b c d xNorm yNorm threshold : Coordinate)
    (aNonnegative : 0 ≤ a) (bNonnegative : 0 ≤ b)
    (bLeA : b ≤ a)
    (xNormIdentity : xNorm = a ^ 2 + b ^ 2)
    (yNormIdentity : yNorm = c ^ 2 + d ^ 2)
    (xNormLeOne : xNorm ≤ 1) (yNormLeOne : yNorm ≤ 1)
    (errorImaginaryObstruction : 2 * b ≤ xNorm)
    (errorDiagonalObstruction : 2 * (a + b) ≤ xNorm + 1)
    (denominatorRealObstruction : 2 * c ≤ yNorm)
    (denominatorDiagonalObstruction : 2 * (c - d) ≤ yNorm + 1)
    (greenRegion : yNorm < c - d)
    (thresholdCertificate : IsGapThreshold threshold) :
    threshold ≤ 1 + xNorm * yNorm - 2 * (a * c - b * d) := by
  by_cases cNonnegative : 0 ≤ c
  · exact gapThreshold_le_gap_of_greenRegion_of_real_nonnegative
      a b c d xNorm yNorm threshold aNonnegative bNonnegative bLeA
      cNonnegative xNormIdentity yNormIdentity xNormLeOne yNormLeOne
      errorImaginaryObstruction errorDiagonalObstruction
      denominatorRealObstruction denominatorDiagonalObstruction greenRegion
      thresholdCertificate
  · exact (gapThreshold_le_thirteenFourteenths threshold
      thresholdCertificate).trans
        (RFAP.SharpIndexOneWindow.thirteenFourteenths_le_gap_of_real_nonpositive
          a b c d xNorm yNorm aNonnegative bNonnegative
          (le_of_not_ge cNonnegative) xNormIdentity yNormIdentity xNormLeOne
          errorImaginaryObstruction errorDiagonalObstruction)

/-- The exact rational-cut gap theorem for all five-obstruction configurations
in the normalized first octant.  The four-region split is finite; only its
green chamber uses the quadratic boundary. -/
theorem gapThreshold_le_gap_of_firstOctantFiveObstructions
    (a b c d xNorm yNorm threshold : Coordinate)
    (aNonnegative : 0 ≤ a) (bNonnegative : 0 ≤ b)
    (bLeA : b ≤ a)
    (xNormIdentity : xNorm = a ^ 2 + b ^ 2)
    (yNormIdentity : yNorm = c ^ 2 + d ^ 2)
    (xNormLeOne : xNorm ≤ 1) (yNormLeOne : yNorm ≤ 1)
    (denominatorOne : 2 * c ≤ yNorm)
    (denominatorOneMinusI : 2 * (c - d) ≤ yNorm + 1)
    (imaginaryObstruction : 2 * b ≤ xNorm ∨ -2 * d ≤ yNorm)
    (diagonalObstruction :
      2 * (a + b) ≤ xNorm + 1 ∨ c - d ≤ yNorm)
    (oppositeDiagonalObstruction :
      a - b ≤ xNorm ∨ 2 * (c + d) ≤ yNorm + 1)
    (thresholdCertificate : IsGapThreshold threshold) :
    threshold ≤ 1 + xNorm * yNorm - 2 * (a * c - b * d) := by
  rcases (RFAP.SharpIndexOneWindow.fourRegionSplit_of_fiveCoefficientObstructions
      a b c d xNorm yNorm denominatorOne denominatorOneMinusI
      imaginaryObstruction diagonalObstruction
      oppositeDiagonalObstruction).2 with green | redOrExteriorOrBlue
  · exact gapThreshold_le_gap_of_greenRegion
      a b c d xNorm yNorm threshold aNonnegative bNonnegative bLeA
      xNormIdentity yNormIdentity xNormLeOne yNormLeOne green.2.1 green.2.2
      denominatorOne denominatorOneMinusI green.1 thresholdCertificate
  · rcases redOrExteriorOrBlue with red | exteriorOrBlue
    · exact (gapThreshold_le_one threshold thresholdCertificate).trans
        (RFAP.SharpIndexOneWindow.one_le_gap_of_redRegion
          a b c d xNorm yNorm bNonnegative bLeA xNormIdentity
          yNormIdentity yNormLeOne red.2.2 red.1 red.2.1)
    · rcases exteriorOrBlue with exterior | blue
      · exact (gapThreshold_le_sixSevenths threshold
          thresholdCertificate).trans
          (RFAP.SharpIndexOneWindow.sixSevenths_le_gap_of_exteriorRegion
            a b c d xNorm yNorm aNonnegative bNonnegative bLeA
            xNormIdentity yNormIdentity yNormLeOne denominatorOne
            exterior.1 exterior.2)
      · exact (gapThreshold_le_one threshold thresholdCertificate).trans
          (RFAP.SharpIndexOneWindow.one_le_gap_of_blueRegion
            a b c d xNorm yNorm aNonnegative bNonnegative xNormIdentity
            yNormIdentity yNormLeOne blue.2 denominatorOne blue.1)

end RFAP.OptimalIndexOneWindow
