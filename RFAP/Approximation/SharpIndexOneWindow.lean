import mathlib.Tactic.QuotientFreeRing
import mathlib.RFAP.ConstructiveFraction

/-!
# Finite chamber data for the sharp determinant-index-one window

The optimal index-one calculation uses five small Gaussian coefficient
pairs.  This module records the rational semialgebraic structure exposed by
those pairs.  No circle, angle, square root, or completed lattice is used:
the four regions are simply a case split on three displayed polynomial
comparisons.
-/

namespace RFAP.SharpIndexOneWindow

abbrev Coordinate := RFAP.ConstructiveFraction.Rational

private def firstRegionSecondBoundaryFraction :
    RFAP.ConstructiveFraction.Fraction :=
  { num := 35, den := 2 ^ 8, den_pos := by decide }

/-- A dyadic rational just above the smaller root of
`b² - 2b + 1/4`. -/
def firstRegionSecondBoundary : Coordinate :=
  RFAP.ConstructiveFraction.ofFraction firstRegionSecondBoundaryFraction

private def firstRegionProjectionBoundFraction :
    RFAP.ConstructiveFraction.Fraction :=
  { num := 51, den := 2 ^ 8, den_pos := by decide }

/-- The dyadic one-vector projection bound used by the sharp chamber proof. -/
def firstRegionProjectionBound : Coordinate :=
  RFAP.ConstructiveFraction.ofFraction firstRegionProjectionBoundFraction

/-- The resulting dyadic determinant-gap bound, written as a complement so
the proof never has to name an algebraic root.  It is exactly `205/256`. -/
def firstRegionGapBound : Coordinate :=
  1 - firstRegionProjectionBound

private def firstRegionWindowBoundFraction :
    RFAP.ConstructiveFraction.Fraction :=
  { num := 2 ^ 8, den := 13 * 16 - 3, den_pos := by decide }

/-- The reciprocal dyadic window bound `256/205`.  It is kept as an explicit
reduced fraction so later window proofs need no square root or division by an
unnamed algebraic boundary. -/
def firstRegionWindowBound : Coordinate :=
  RFAP.ConstructiveFraction.ofFraction firstRegionWindowBoundFraction

private theorem fiftyOne_nonnegative : (0 : Coordinate) ≤ 51 := by
  calc
    (0 : Coordinate) ≤ 6 * 8 + 3 := add_nonneg
      (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide) (by decide))
      (by decide)
    _ = 51 := by ring1

private theorem firstRegionSecondBoundary_mul_denominator :
    firstRegionSecondBoundary * (2 : Coordinate) ^ 8 = 35 := by
  unfold firstRegionSecondBoundary
  have clearance := RFAP.ConstructiveFraction.ofFraction_mul_den
    firstRegionSecondBoundaryFraction
  simpa only [firstRegionSecondBoundaryFraction, QuotientFreeRing.intCast_pow,
    Int.cast_ofNat] using clearance

private theorem firstRegionProjectionBound_mul_denominator :
    firstRegionProjectionBound * (2 : Coordinate) ^ 8 = 51 := by
  unfold firstRegionProjectionBound
  have clearance := RFAP.ConstructiveFraction.ofFraction_mul_den
    firstRegionProjectionBoundFraction
  simpa only [firstRegionProjectionBoundFraction, QuotientFreeRing.intCast_pow,
    Int.cast_ofNat] using clearance

/-- The gap bound is exactly `205/256`, recorded without asking the elaborator
to expand a large rational literal. -/
theorem firstRegionGapBound_mul_denominator :
    firstRegionGapBound * (2 : Coordinate) ^ 8 = 13 * 16 - 3 := by
  calc
    firstRegionGapBound * (2 : Coordinate) ^ 8 =
        (1 - firstRegionProjectionBound) * (2 : Coordinate) ^ 8 := rfl
    _ = (2 : Coordinate) ^ 8 -
          firstRegionProjectionBound * (2 : Coordinate) ^ 8 := by ring1
    _ = (2 : Coordinate) ^ 8 - 51 := by
      rw [firstRegionProjectionBound_mul_denominator]
    _ = 13 * 16 - 3 := by ring1

/-- The displayed window bound is exactly `256/205`. -/
theorem firstRegionWindowBound_mul_denominator :
    firstRegionWindowBound * (13 * 16 - 3 : Coordinate) =
      (2 : Coordinate) ^ 8 := by
  unfold firstRegionWindowBound
  have clearance := RFAP.ConstructiveFraction.ofFraction_mul_den
    firstRegionWindowBoundFraction
  simpa only [firstRegionWindowBoundFraction, QuotientFreeRing.intCast_pow,
    QuotientFreeRing.intCast_mul, Int.cast_sub, Int.cast_ofNat] using clearance

/-- The displayed window and gap bounds multiply to one. -/
theorem firstRegionWindowBound_mul_gapBound :
    firstRegionWindowBound * firstRegionGapBound = 1 := by
  apply RFAP.ConstructiveFraction.mul_right_cancel_of_ne
    (show (2 : Coordinate) ^ 8 ≠ 0 by
      exact ne_of_gt
        (RFAP.ConstructiveFraction.pow_pos_direct (by decide) 8))
  calc
    (firstRegionWindowBound * firstRegionGapBound) * (2 : Coordinate) ^ 8 =
        firstRegionWindowBound *
          (firstRegionGapBound * (2 : Coordinate) ^ 8) := by ring1
    _ = firstRegionWindowBound * (13 * 16 - 3) := by
      rw [firstRegionGapBound_mul_denominator]
    _ = (2 : Coordinate) ^ 8 := firstRegionWindowBound_mul_denominator
    _ = (1 : Coordinate) * (2 : Coordinate) ^ 8 := by ring1

private theorem firstRegionSecondBoundary_le_half :
    firstRegionSecondBoundary ≤ (1 / 2 : Coordinate) := by
  unfold firstRegionSecondBoundary firstRegionSecondBoundaryFraction
  decide

private theorem firstRegionSecondBoundary_polynomial_negative :
    firstRegionSecondBoundary ^ 2 -
      2 * firstRegionSecondBoundary + 1 / 4 < 0 := by
  unfold firstRegionSecondBoundary firstRegionSecondBoundaryFraction
  decide

private theorem firstRegionSecondBoundary_add_sixteenth :
    firstRegionSecondBoundary + 1 / ((2 : Coordinate) ^ 4) =
      firstRegionProjectionBound := by
  apply RFAP.ConstructiveFraction.mul_right_cancel_of_ne
    (show (2 : Coordinate) ^ 8 ≠ 0 by
      exact ne_of_gt
        (RFAP.ConstructiveFraction.pow_pos_direct (by decide) 8))
  calc
    (firstRegionSecondBoundary + 1 / ((2 : Coordinate) ^ 4)) *
          (2 : Coordinate) ^ 8 =
        firstRegionSecondBoundary * (2 : Coordinate) ^ 8 +
          (1 / ((2 : Coordinate) ^ 4) : Coordinate) *
            (2 : Coordinate) ^ 8 := by ring1
    _ = firstRegionSecondBoundary * (2 : Coordinate) ^ 8 +
          (2 : Coordinate) ^ 4 := by
      rw [show (1 / ((2 : Coordinate) ^ 4) : Coordinate) *
        (2 : Coordinate) ^ 8 = (2 : Coordinate) ^ 4 by decide]
    _ = 35 + (2 : Coordinate) ^ 4 := by
      rw [firstRegionSecondBoundary_mul_denominator]
    _ = 51 := by ring1
    _ = firstRegionProjectionBound * (2 : Coordinate) ^ 8 :=
      firstRegionProjectionBound_mul_denominator.symm

private theorem firstRegionProjectionBound_le_oneFifth :
    firstRegionProjectionBound ≤ (1 / 5 : Coordinate) := by
  unfold firstRegionProjectionBound firstRegionProjectionBoundFraction
  decide

private theorem firstRegionProjectionBound_nonnegative :
    (0 : Coordinate) ≤ firstRegionProjectionBound := by
  unfold firstRegionProjectionBound firstRegionProjectionBoundFraction
  decide

theorem firstRegionGapBound_le_one :
    firstRegionGapBound ≤ (1 : Coordinate) := by
  unfold firstRegionGapBound
  have negated := RFAP.ConstructiveFraction.neg_le_neg_direct
    firstRegionProjectionBound_nonnegative
  calc
    1 - firstRegionProjectionBound =
        1 + -firstRegionProjectionBound := rfl
    _ ≤ 1 + -0 := RFAP.ConstructiveFraction.add_le_add_direct
      (le_refl (1 : Coordinate)) negated
    _ = 1 := by ring1

theorem firstRegionGapBound_pos :
    (0 : Coordinate) < firstRegionGapBound := by
  unfold firstRegionGapBound firstRegionProjectionBound
    firstRegionProjectionBoundFraction
  decide

private theorem seven_mul_firstRegionSecondBoundary_le_one :
    7 * firstRegionSecondBoundary ≤ (1 : Coordinate) := by
  unfold firstRegionSecondBoundary firstRegionSecondBoundaryFraction
  decide

/-- A division-free angular form of the dyadic gap estimate.  The hypothesis
is `256P²≤51R`; after multiplication by `51`, the required difference is
the sum of `(256P-51)²` and `256(51R-256P²)`. -/
theorem firstRegionGapBound_le_gap_of_scaled_crossSquare
    (productNorm cross : Coordinate)
    (scaledCrossSquare :
      (2 : Coordinate) ^ 8 * cross ^ 2 ≤ 51 * productNorm) :
    firstRegionGapBound ≤ 1 + productNorm - 2 * cross := by
  let denominator : Coordinate := (2 : Coordinate) ^ 8
  have residualNonnegative :
      0 ≤ 51 * productNorm - denominator * cross ^ 2 :=
    RFAP.ConstructiveFraction.sub_nonneg_direct (by
      simpa only [denominator] using scaledCrossSquare)
  have certificateNonnegative :
      0 ≤ (denominator * cross - 51) ^ 2 +
          denominator * (51 * productNorm - denominator * cross ^ 2) :=
    add_nonneg
      (RFAP.ConstructiveFraction.sq_nonneg_direct _)
      (RFAP.ConstructiveFraction.mul_nonneg_direct
        (RFAP.ConstructiveFraction.pow_nonneg_direct (by decide) 8)
        residualNonnegative)
  have scaledDifferenceNonnegative :
      0 ≤ 51 * (51 + denominator * productNorm - 2 * denominator * cross) := by
    calc
      0 ≤ (denominator * cross - 51) ^ 2 +
          denominator * (51 * productNorm - denominator * cross ^ 2) :=
        certificateNonnegative
      _ = 51 * (51 + denominator * productNorm -
          2 * denominator * cross) := by ring1
  have fiftyOnePositive : (0 : Coordinate) < 51 := by
    calc
      (0 : Coordinate) < 3 := by decide
      _ ≤ 6 * 8 + 3 := le_add_of_nonneg_left
        (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide) (by decide))
      _ = 51 := by ring1
  have differenceNonnegative :
      0 ≤ 51 + denominator * productNorm - 2 * denominator * cross := by
    apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct (c := 51)
    · calc
        0 * 51 = 0 := by ring1
        _ ≤ 51 * (51 + denominator * productNorm -
            2 * denominator * cross) := scaledDifferenceNonnegative
        _ = (51 + denominator * productNorm -
            2 * denominator * cross) * 51 := by ring1
    · exact fiftyOnePositive
  have unscaledDifferenceNonnegative :
      0 ≤ firstRegionProjectionBound + productNorm - 2 * cross := by
    apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct
      (c := denominator)
    · calc
        0 * denominator = 0 := by ring1
        _ ≤ 51 + denominator * productNorm -
            2 * denominator * cross := differenceNonnegative
        _ = firstRegionProjectionBound * denominator +
            denominator * productNorm - 2 * denominator * cross := by
          dsimp only [denominator]
          rw [firstRegionProjectionBound_mul_denominator]
        _ = (firstRegionProjectionBound + productNorm - 2 * cross) *
            denominator := by ring1
    · exact RFAP.ConstructiveFraction.pow_pos_direct (by decide) 8
  apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
  calc
    0 ≤ firstRegionProjectionBound + productNorm - 2 * cross :=
      unscaledDifferenceNonnegative
    _ = (1 + productNorm - 2 * cross) - firstRegionGapBound := by
      unfold firstRegionGapBound
      ring1

private theorem scaledCrossSquare_of_factor
    (factor productNorm cross : Coordinate)
    (coefficientBound : (2 : Coordinate) ^ 8 ≤ 51 * factor)
    (factorCrossSquare : factor * cross ^ 2 ≤ productNorm) :
    (2 : Coordinate) ^ 8 * cross ^ 2 ≤ 51 * productNorm := by
  calc
    (2 : Coordinate) ^ 8 * cross ^ 2 ≤
        (51 * factor) * cross ^ 2 :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        coefficientBound (RFAP.ConstructiveFraction.sq_nonneg_direct cross)
    _ = 51 * (factor * cross ^ 2) := by ring1
    _ ≤ 51 * productNorm :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        factorCrossSquare fiftyOne_nonnegative

private theorem dyadicDenominator_le_fiftyOne_mul_seven :
    ((2 : Coordinate) ^ 8) ≤ 51 * 7 := by
  apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
  calc
    0 ≤ (12 : Coordinate) * 8 + 5 :=
      add_nonneg
        (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide) (by decide))
        (by decide)
    _ = 51 * 7 - (2 : Coordinate) ^ 8 := by ring1

private theorem dyadicDenominator_le_fiftyOne_mul_eight :
    ((2 : Coordinate) ^ 8) ≤ 51 * 8 := by
  apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
  calc
    0 ≤ (19 : Coordinate) * 8 :=
      RFAP.ConstructiveFraction.mul_nonneg_direct (by decide) (by decide)
    _ = 51 * 8 - (2 : Coordinate) ^ 8 := by ring1

private theorem one_le_gap_of_cross_nonpositive
    (productNorm cross : Coordinate)
    (productNormNonnegative : 0 ≤ productNorm)
    (crossNonpositive : cross ≤ 0) :
    (1 : Coordinate) ≤ 1 + productNorm - 2 * cross := by
  have twiceCrossNonpositive : 2 * cross ≤ 0 := by
    have scaled := RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      crossNonpositive (show (0 : Coordinate) ≤ 2 by decide)
    simpa only [mul_zero] using scaled
  have negated := RFAP.ConstructiveFraction.neg_le_neg_direct
    twiceCrossNonpositive
  have oneLeGap : (1 : Coordinate) ≤ 1 + productNorm - 2 * cross := by
    calc
      (1 : Coordinate) ≤ 1 + productNorm :=
        le_add_of_nonneg_right productNormNonnegative
      _ ≤ 1 + productNorm - 2 * cross := by
        calc
          1 + productNorm = 1 + productNorm + -0 := by ring1
          _ ≤ 1 + productNorm + -(2 * cross) :=
            RFAP.ConstructiveFraction.add_le_add_direct le_rfl negated
          _ = 1 + productNorm - 2 * cross := rfl
  exact oneLeGap

private theorem sixSevenths_le_gap_of_seven_crossSquare
    (productNorm cross : Coordinate)
    (sevenCrossSquare : 7 * cross ^ 2 ≤ productNorm) :
    (6 / 7 : Coordinate) ≤ 1 + productNorm - 2 * cross := by
  have residualNonnegative : 0 ≤ productNorm - 7 * cross ^ 2 :=
    RFAP.ConstructiveFraction.sub_nonneg_direct sevenCrossSquare
  have certificateNonnegative :
      0 ≤ (7 * cross - 1) ^ 2 + 7 * (productNorm - 7 * cross ^ 2) :=
    add_nonneg (RFAP.ConstructiveFraction.sq_nonneg_direct _)
      (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        residualNonnegative)
  have sixLeScaledGap :
      (6 : Coordinate) ≤ 7 * (1 + productNorm - 2 * cross) := by
    apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
    calc
      0 ≤ (7 * cross - 1) ^ 2 +
          7 * (productNorm - 7 * cross ^ 2) := certificateNonnegative
      _ = 7 * (1 + productNorm - 2 * cross) - 6 := by ring1
  apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct (c := 7)
  · calc
      (6 / 7 : Coordinate) * 7 = 6 := by decide
      _ ≤ 7 * (1 + productNorm - 2 * cross) := sixLeScaledGap
      _ = (1 + productNorm - 2 * cross) * 7 := by ring1
  · decide

private theorem firstRegionSecondBoundary_le_projectionBound :
    firstRegionSecondBoundary ≤ firstRegionProjectionBound := by
  calc
    firstRegionSecondBoundary ≤
        firstRegionSecondBoundary + 1 / ((2 : Coordinate) ^ 4) :=
      le_add_of_nonneg_right (by decide)
    _ = firstRegionProjectionBound :=
      firstRegionSecondBoundary_add_sixteenth

/-- The five coefficient obstructions reduce to four rational regions.

The common inequalities are the denominator alternatives for coefficients
`1` and for the leading combination involving `1-i`.  The three disjunctions
come from `i`, `1+i`, and the remaining leading combination involving
`1+i`.  The four conclusions are the coefficientwise versions of the green,
red, exterior, and blue regions, respectively. -/
theorem fourRegionSplit_of_fiveCoefficientObstructions
    (a b c d xNorm yNorm : Coordinate)
    (denominatorOne : 2 * c ≤ yNorm)
    (denominatorOneMinusI : 2 * (c - d) ≤ yNorm + 1)
    (imaginaryObstruction :
      2 * b ≤ xNorm ∨ -2 * d ≤ yNorm)
    (diagonalObstruction :
      2 * (a + b) ≤ xNorm + 1 ∨ c - d ≤ yNorm)
    (oppositeDiagonalObstruction :
      a - b ≤ xNorm ∨ 2 * (c + d) ≤ yNorm + 1) :
    2 * (c - d) ≤ yNorm + 1 ∧
      ((yNorm < c - d ∧
          2 * b ≤ xNorm ∧ 2 * (a + b) ≤ xNorm + 1) ∨
        (c - d ≤ yNorm ∧ yNorm < -2 * d ∧ 2 * b ≤ xNorm) ∨
        (-2 * d ≤ yNorm ∧ 2 * (c + d) ≤ yNorm + 1) ∨
        (yNorm + 1 < 2 * (c + d) ∧ a - b ≤ xNorm)) := by
  refine ⟨denominatorOneMinusI, ?_⟩
  by_cases greenRegion : yNorm < c - d
  · have twiceCLt : 2 * c < c - d :=
      lt_of_le_of_lt denominatorOne greenRegion
    have cPlusDNegative : c + d < 0 := by
      have differenceNegative :=
        RFAP.ConstructiveFraction.sub_neg_direct twiceCLt
      calc
        c + d = 2 * c - (c - d) := by ring1
        _ < 0 := differenceNegative
    have redRegion : yNorm < -2 * d := by
      have shifted :=
        RFAP.ConstructiveFraction.add_lt_add_right_direct greenRegion (2 * d)
      have sumNegative : yNorm + 2 * d < 0 := by
        calc
          yNorm + 2 * d < (c - d) + 2 * d := shifted
          _ = c + d := by ring1
          _ < 0 := cPlusDNegative
      apply RFAP.ConstructiveFraction.lt_of_sub_neg_direct
      calc
        yNorm - (-2 * d) = yNorm + 2 * d := by ring1
        _ < 0 := sumNegative
    have errorImaginary : 2 * b ≤ xNorm := by
      rcases imaginaryObstruction with errorSide | denominatorSide
      · exact errorSide
      · exact (redRegion.2 denominatorSide).elim
    have errorDiagonal : 2 * (a + b) ≤ xNorm + 1 := by
      rcases diagonalObstruction with errorSide | denominatorSide
      · exact errorSide
      · exact (greenRegion.2 denominatorSide).elim
    exact Or.inl ⟨greenRegion, errorImaginary, errorDiagonal⟩
  · have outsideGreen : c - d ≤ yNorm := le_of_not_gt greenRegion
    by_cases redRegion : yNorm < -2 * d
    · have errorImaginary : 2 * b ≤ xNorm := by
        rcases imaginaryObstruction with errorSide | denominatorSide
        · exact errorSide
        · exact (redRegion.2 denominatorSide).elim
      exact Or.inr (Or.inl ⟨outsideGreen, redRegion, errorImaginary⟩)
    · have outsideRed : -2 * d ≤ yNorm := le_of_not_gt redRegion
      by_cases blueRegion : yNorm + 1 < 2 * (c + d)
      · have errorOppositeDiagonal : a - b ≤ xNorm := by
          rcases oppositeDiagonalObstruction with
              errorSide | denominatorSide
          · exact errorSide
          · exact (blueRegion.2 denominatorSide).elim
        exact Or.inr (Or.inr (Or.inr
          ⟨blueRegion, errorOppositeDiagonal⟩))
      · have outsideBlue : 2 * (c + d) ≤ yNorm + 1 :=
          le_of_not_gt blueRegion
        exact Or.inr (Or.inr (Or.inl ⟨outsideRed, outsideBlue⟩))

/-- In the first (extremal) region, the two error-side circle exclusions
force the square-root-free angular inequality
`4ab ≤ a²+b²`.  The proof is a finite split at `2a=1`; both branches expose
an explicit sum of nonnegative products. -/
theorem slopeQuadratic_nonnegative_of_firstRegionObstructions
    (a b xNorm : Coordinate)
    (aNonnegative : 0 ≤ a)
    (bNonnegative : 0 ≤ b)
    (bLeA : b ≤ a)
    (xNormIdentity : xNorm = a ^ 2 + b ^ 2)
    (xNormLeOne : xNorm ≤ 1)
    (imaginaryObstruction : 2 * b ≤ xNorm)
    (diagonalObstruction : 2 * (a + b) ≤ xNorm + 1) :
    0 ≤ xNorm - 4 * a * b := by
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
  by_cases twiceALeOne : 2 * a ≤ 1
  · have twiceANonnegative : 0 ≤ 2 * a :=
      RFAP.ConstructiveFraction.mul_nonneg_direct (by decide) aNonnegative
    have scaledImaginary :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        imaginaryObstruction twiceANonnegative
    have scaledNorm :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        twiceALeOne xNormNonnegative
    apply RFAP.ConstructiveFraction.sub_nonneg_direct
    calc
      4 * a * b = (2 * a) * (2 * b) := by ring1
      _ ≤ (2 * a) * xNorm := scaledImaginary
      _ ≤ 1 * xNorm := scaledNorm
      _ = xNorm := by ring1
  · have oneLeTwiceA : 1 ≤ 2 * a := le_of_not_ge twiceALeOne
    have aSquareLeA : a ^ 2 ≤ a := by
      have scaled :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          aLeOne aNonnegative
      calc
        a ^ 2 = a * a := by ring1
        _ ≤ a * 1 := scaled
        _ = a := by ring1
    have bLeOne : b ≤ 1 := bLeA.trans aLeOne
    have bSquareLeB : b ^ 2 ≤ b := by
      have scaled :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          bLeOne bNonnegative
      calc
        b ^ 2 = b * b := by ring1
        _ ≤ b * 1 := scaled
        _ = b := by ring1
    have xNormLeTwoA : xNorm ≤ 2 * a := by
      have sumBound := RFAP.ConstructiveFraction.add_le_add_direct
        aSquareLeA (bSquareLeB.trans bLeA)
      calc
        xNorm = a ^ 2 + b ^ 2 := xNormIdentity
        _ ≤ a + a := sumBound
        _ = 2 * a := by ring1
    have firstProductNonnegative :
        0 ≤ (2 * a - 1) * (2 * a - xNorm) :=
      RFAP.ConstructiveFraction.mul_nonneg_direct
        (RFAP.ConstructiveFraction.sub_nonneg_direct oneLeTwiceA)
        (RFAP.ConstructiveFraction.sub_nonneg_direct xNormLeTwoA)
    have twiceANonnegative : 0 ≤ 2 * a :=
      RFAP.ConstructiveFraction.mul_nonneg_direct (by decide) aNonnegative
    have secondProductNonnegative :
        0 ≤ (2 * a) * (xNorm + 1 - 2 * (a + b)) :=
      RFAP.ConstructiveFraction.mul_nonneg_direct twiceANonnegative
        (RFAP.ConstructiveFraction.sub_nonneg_direct diagonalObstruction)
    calc
      0 ≤ (2 * a - 1) * (2 * a - xNorm) +
          (2 * a) * (xNorm + 1 - 2 * (a + b)) :=
        add_nonneg firstProductNonnegative secondProductNonnegative
      _ = xNorm - 4 * a * b := by ring1

/-- The lower branch of `a²-4ab+b² ≥ 0` is selected by `0 ≤ b ≤ a`:
the first coordinate is at least twice the second.  This is the rational
form of the fifteen-degree sector bound, without naming an angle. -/
theorem twice_second_le_first_of_slopeQuadratic
    (a b xNorm : Coordinate)
    (aNonnegative : 0 ≤ a)
    (bLeA : b ≤ a)
    (xNormIdentity : xNorm = a ^ 2 + b ^ 2)
    (slopeQuadratic : 0 ≤ xNorm - 4 * a * b) :
    2 * b ≤ a := by
  by_cases target : 2 * b ≤ a
  · exact target
  · have aLtTwiceB : a < 2 * b := lt_of_not_ge target
    have twiceBPositive : 0 < 2 * b := lt_of_le_of_lt aNonnegative aLtTwiceB
    have bPositive : 0 < b := by
      apply RFAP.ConstructiveFraction.pos_of_mul_pos_right_direct
      · exact twiceBPositive
      · decide
    have differencePositive : 0 < 2 * b - a :=
      RFAP.ConstructiveFraction.sub_pos_direct aLtTwiceB
    have differenceLeB : 2 * b - a ≤ b := by
      have negated := RFAP.ConstructiveFraction.neg_le_neg_direct bLeA
      have shifted :=
        RFAP.ConstructiveFraction.add_le_add_right_direct negated (2 * b)
      calc
        2 * b - a = -a + 2 * b := by ring1
        _ ≤ -b + 2 * b := shifted
        _ = b := by ring1
    have differenceSquareLeBSquare : (2 * b - a) ^ 2 ≤ b ^ 2 :=
      RFAP.ConstructiveFraction.pow_le_pow_direct differencePositive.le
        differenceLeB 2
    have bSquarePositive : 0 < b ^ 2 :=
      RFAP.ConstructiveFraction.pow_pos_direct bPositive 2
    have bSquareLtThreeBSquare : b ^ 2 < 3 * b ^ 2 := by
      have scaled :=
        RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
          (show (1 : Coordinate) < 3 by decide) bSquarePositive
      calc
        b ^ 2 = 1 * b ^ 2 := by ring1
        _ < 3 * b ^ 2 := scaled
    have quadraticNegative : xNorm - 4 * a * b < 0 := by
      have squareLt := differenceSquareLeBSquare.trans_lt
        bSquareLtThreeBSquare
      have differenceNegative :=
        RFAP.ConstructiveFraction.sub_neg_direct squareLt
      calc
        xNorm - 4 * a * b = (2 * b - a) ^ 2 - 3 * b ^ 2 := by
          rw [xNormIdentity]
          ring1
        _ < 0 := differenceNegative
    exact ((not_lt_of_ge slopeQuadratic) quadraticNegative).elim

/-- The two first-region exclusions put the smaller coordinate below the
displayed rational `35/256`.  This is a deliberately rational separator for
the smaller root of `b² - 2b + 1/4`; no root is introduced. -/
theorem second_le_firstRegionBoundary_of_firstRegionObstructions
    (a b xNorm : Coordinate)
    (aNonnegative : 0 ≤ a)
    (xNormIdentity : xNorm = a ^ 2 + b ^ 2)
    (xNormLeOne : xNorm ≤ 1)
    (imaginaryObstruction : 2 * b ≤ xNorm)
    (diagonalObstruction : 2 * (a + b) ≤ xNorm + 1) :
    b ≤ firstRegionSecondBoundary := by
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
  have boundaryPolynomialNonnegative :
      0 ≤ b ^ 2 - 2 * b + 1 / 4 := by
    apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
    calc
      0 ≤ (1 / 4 : Coordinate) - (2 * b - b ^ 2) :=
        RFAP.ConstructiveFraction.sub_nonneg_direct
          twiceBMinusSquareLeQuarter
      _ = (b ^ 2 - 2 * b + 1 / 4) - 0 := by ring1
  by_cases target : b ≤ firstRegionSecondBoundary
  · exact target
  · have boundaryLtB : firstRegionSecondBoundary < b :=
      lt_of_not_ge target
    have firstFactorPositive : 0 < b - firstRegionSecondBoundary :=
      RFAP.ConstructiveFraction.sub_pos_direct boundaryLtB
    have sumLeOne : b + firstRegionSecondBoundary ≤
        (1 : Coordinate) := by
      have added := RFAP.ConstructiveFraction.add_le_add_direct bLeHalf
        firstRegionSecondBoundary_le_half
      exact added.trans_eq (show
        (1 / 2 : Coordinate) + 1 / 2 = 1 by decide)
    have secondFactorNegative :
        b + firstRegionSecondBoundary - 2 < 0 :=
      RFAP.ConstructiveFraction.sub_neg_direct
        (sumLeOne.trans_lt (show (1 : Coordinate) < 2 by decide))
    have productNegative :
        (b - firstRegionSecondBoundary) *
          (b + firstRegionSecondBoundary - 2) < 0 :=
      RFAP.ConstructiveFraction.mul_neg_of_pos_of_neg_direct
        firstFactorPositive secondFactorNegative
    have boundaryValueNegative :
        firstRegionSecondBoundary ^ 2 -
          2 * firstRegionSecondBoundary + 1 / 4 < 0 :=
      firstRegionSecondBoundary_polynomial_negative
    have polynomialNegative : b ^ 2 - 2 * b + 1 / 4 < 0 := by
      calc
        b ^ 2 - 2 * b + 1 / 4 =
            (firstRegionSecondBoundary ^ 2 -
              2 * firstRegionSecondBoundary + 1 / 4) +
              (b - firstRegionSecondBoundary) *
                (b + firstRegionSecondBoundary - 2) := by ring1
        _ < 0 + 0 := RFAP.ConstructiveFraction.add_lt_add_direct
          boundaryValueNegative productNegative
        _ = 0 := by ring1
    exact ((not_lt_of_ge boundaryPolynomialNonnegative)
      polynomialNegative).elim


/-- A one-vector projection bound for the extremal chamber.  Multiplying by
`256` turns the conclusion into the integer inequality
`256 * (b + X * (a-X)) ≤ 51`.  The only nonlinear calculation in the
large-coordinate branch is the displayed polynomial
`0 ≤ -29t² + 1228t - 6724`, where `t=256b` and `13 ≤ t ≤ 35`. -/
theorem second_add_norm_mul_first_sub_norm_le_projectionBound
    (a b xNorm : Coordinate)
    (aNonnegative : 0 ≤ a)
    (xNormIdentity : xNorm = a ^ 2 + b ^ 2)
    (xNormLeOne : xNorm ≤ 1)
    (imaginaryObstruction : 2 * b ≤ xNorm)
    (diagonalObstruction : 2 * (a + b) ≤ xNorm + 1) :
    b + xNorm * (a - xNorm) ≤ firstRegionProjectionBound := by
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
    RFAP.ConstructiveFraction.le_of_sq_le_sq_direct (by decide)
      aSquareLeOne
  have bLeBoundary : b ≤ firstRegionSecondBoundary :=
    second_le_firstRegionBoundary_of_firstRegionObstructions
      a b xNorm aNonnegative xNormIdentity xNormLeOne
      imaginaryObstruction diagonalObstruction
  have normTermLeASquareQuarter :
      xNorm * (a - xNorm) ≤ (1 / 4 : Coordinate) * a ^ 2 := by
    have scaledTerm : 4 * (xNorm * (a - xNorm)) ≤ a ^ 2 := by
      apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
      calc
        0 ≤ (2 * xNorm - a) ^ 2 :=
          RFAP.ConstructiveFraction.sq_nonneg_direct _
        _ = a ^ 2 - 4 * (xNorm * (a - xNorm)) := by ring1
    apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct (c := 4)
    · calc
        (xNorm * (a - xNorm)) * 4 =
            4 * (xNorm * (a - xNorm)) := by ring1
        _ ≤ a ^ 2 := scaledTerm
        _ = ((1 / 4 : Coordinate) * a ^ 2) * 4 := by
          symm
          calc
            ((1 / 4 : Coordinate) * a ^ 2) * 4 =
                ((1 / 4 : Coordinate) * 4) * a ^ 2 := by ring1
            _ = 1 * a ^ 2 := by
              rw [show (1 / 4 : Coordinate) * 4 = 1 by decide]
            _ = a ^ 2 := by ring1
    · decide
  by_cases aLeHalf : a ≤ (1 / 2 : Coordinate)
  · have aSquareLeQuarter : a ^ 2 ≤ (1 / 2 : Coordinate) ^ 2 :=
      RFAP.ConstructiveFraction.pow_le_pow_direct aNonnegative aLeHalf 2
    have termLeSixteenth :
        xNorm * (a - xNorm) ≤ (1 / 16 : Coordinate) := by
      calc
        xNorm * (a - xNorm) ≤ (1 / 4 : Coordinate) * a ^ 2 :=
          normTermLeASquareQuarter
        _ ≤ (1 / 4 : Coordinate) * (1 / 2 : Coordinate) ^ 2 :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            aSquareLeQuarter (by decide)
        _ = 1 / 16 := by decide
    calc
      b + xNorm * (a - xNorm) ≤
          firstRegionSecondBoundary + 1 / 16 :=
        RFAP.ConstructiveFraction.add_le_add_direct bLeBoundary
          termLeSixteenth
      _ = firstRegionProjectionBound :=
        firstRegionSecondBoundary_add_sixteenth
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
        _ = a + -(1 / 2) := by ring1
        _ = a + ((1 / 2 : Coordinate) - 1) := by
          rw [show -(1 / 2 : Coordinate) = 1 / 2 - 1 by decide]
        _ = (1 / 2 : Coordinate) - (1 - a) := by ring1
    by_cases bSmall : (2 : Coordinate) ^ 8 * b ≤ 13
    · have bLeSmall :
          b ≤ (13 / ((2 : Coordinate) ^ 8) : Coordinate) := by
        apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct
          (c := (2 : Coordinate) ^ 8)
        · calc
            b * (2 : Coordinate) ^ 8 = (2 : Coordinate) ^ 8 * b := by
              ring1
            _ ≤ 13 := bSmall
            _ = (13 / ((2 : Coordinate) ^ 8) : Coordinate) *
                (2 : Coordinate) ^ 8 := by decide
        · exact RFAP.ConstructiveFraction.pow_pos_direct (by decide) 8
      have cubicBound : u * (1 - u) ^ 2 ≤ (4 / 27 : Coordinate) := by
        have firstFactorNonnegative : 0 ≤ 4 - 3 * u :=
          RFAP.ConstructiveFraction.sub_nonneg_direct (by
            calc
              3 * u ≤ 3 * (1 / 2 : Coordinate) :=
                RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
                  uLeHalf (by decide)
              _ ≤ 4 := by decide)
        have scaledCubic : 27 * (u * (1 - u) ^ 2) ≤ 4 := by
          apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
          calc
            0 ≤ (4 - 3 * u) * (3 * u - 1) ^ 2 :=
              RFAP.ConstructiveFraction.mul_nonneg_direct
                firstFactorNonnegative
                (RFAP.ConstructiveFraction.sq_nonneg_direct _)
            _ = 4 - 27 * (u * (1 - u) ^ 2) := by ring1
        apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct (c := 27)
        · calc
            (u * (1 - u) ^ 2) * 27 =
                27 * (u * (1 - u) ^ 2) := by ring1
            _ ≤ 4 := scaledCubic
            _ = (4 / 27 : Coordinate) * 27 := by decide
        · exact RFAP.ConstructiveFraction.natCast_pos_direct
            (n := 27) (by decide)
      have normTermLeCubic :
          xNorm * (a - xNorm) ≤ u * (1 - u) ^ 2 := by
        by_cases deltaNonnegative : 0 ≤ a - xNorm
        · have xNormLeA :=
            RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
              deltaNonnegative
          have scaled :=
            RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
              xNormLeA deltaNonnegative
          have aTermLeCubic :
              a * (a - xNorm) ≤ u * (1 - u) ^ 2 := by
            apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
            calc
              0 ≤ a * b ^ 2 :=
                RFAP.ConstructiveFraction.mul_nonneg_direct aNonnegative
                  (RFAP.ConstructiveFraction.sq_nonneg_direct b)
              _ = u * (1 - u) ^ 2 - a * (a - xNorm) := by
                dsimp only [u]
                rw [xNormIdentity]
                ring1
          exact scaled.trans aTermLeCubic
        · have deltaNonpositive : a - xNorm ≤ 0 :=
            le_of_not_ge deltaNonnegative
          have productNonpositive : xNorm * (a - xNorm) ≤ 0 := by
            have scaled :=
              RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
                deltaNonpositive xNormNonnegative
            simpa only [mul_zero] using scaled
          have cubicNonnegative : 0 ≤ u * (1 - u) ^ 2 :=
            RFAP.ConstructiveFraction.mul_nonneg_direct uNonnegative
              (RFAP.ConstructiveFraction.sq_nonneg_direct _)
          exact productNonpositive.trans cubicNonnegative
      have smallSumLeProjection :
          (13 / ((2 : Coordinate) ^ 8) : Coordinate) + 4 / 27 ≤
            firstRegionProjectionBound := by
        apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct
          (c := (2 : Coordinate) ^ 8 * 27)
        · calc
            ((13 / ((2 : Coordinate) ^ 8) : Coordinate) + 4 / 27) *
                ((2 : Coordinate) ^ 8 * 27) =
              (13 / ((2 : Coordinate) ^ 8) : Coordinate) *
                  ((2 : Coordinate) ^ 8 * 27) +
                (4 / 27 : Coordinate) *
                  ((2 : Coordinate) ^ 8 * 27) := by ring1
            _ =
              13 * 27 + 4 * (2 : Coordinate) ^ 8 := by
              rw [show (13 / ((2 : Coordinate) ^ 8) : Coordinate) *
                  ((2 : Coordinate) ^ 8 * 27) = 13 * 27 by decide]
              rw [show (4 / 27 : Coordinate) *
                  ((2 : Coordinate) ^ 8 * 27) =
                    4 * (2 : Coordinate) ^ 8 by decide]
            _ ≤ 51 * 27 := by
              apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
              calc
                0 ≤ (2 : Coordinate) := by decide
                _ = 51 * 27 -
                    (13 * 27 + 4 * (2 : Coordinate) ^ 8) := by ring1
            _ = firstRegionProjectionBound *
                ((2 : Coordinate) ^ 8 * 27) := by
              calc
                51 * 27 =
                    (firstRegionProjectionBound * (2 : Coordinate) ^ 8) *
                      27 := by rw [firstRegionProjectionBound_mul_denominator]
                _ = firstRegionProjectionBound *
                    ((2 : Coordinate) ^ 8 * 27) := by ring1
        · exact RFAP.ConstructiveFraction.mul_pos_direct
            (RFAP.ConstructiveFraction.pow_pos_direct (by decide) 8)
            (RFAP.ConstructiveFraction.natCast_pos_direct
              (n := 27) (by decide))
      exact (RFAP.ConstructiveFraction.add_le_add_direct bLeSmall
        (normTermLeCubic.trans cubicBound)).trans smallSumLeProjection
    · let t : Coordinate := (2 : Coordinate) ^ 8 * b
      have thirteenLeT : (13 : Coordinate) ≤ t := by
        dsimp only [t]
        exact le_of_not_ge bSmall
      have tLeThirtyFive : t ≤ 35 := by
        dsimp only [t]
        calc
          (2 : Coordinate) ^ 8 * b ≤
              (2 : Coordinate) ^ 8 * firstRegionSecondBoundary :=
            RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
              bLeBoundary
              (RFAP.ConstructiveFraction.pow_nonneg_direct (by decide) 8)
          _ = 35 := by
            calc
              (2 : Coordinate) ^ 8 * firstRegionSecondBoundary =
                  firstRegionSecondBoundary * (2 : Coordinate) ^ 8 := by ring1
              _ = 35 := firstRegionSecondBoundary_mul_denominator
      let affineNumerator : Coordinate := 5 * t + (10 * 8 + 2)
      let affineLower : Coordinate :=
        (1 / ((2 : Coordinate) ^ 9) : Coordinate) * affineNumerator
      have affineNumeratorNonnegative : 0 ≤ affineNumerator := by
        dsimp only [affineNumerator]
        exact add_nonneg
          (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
            (le_trans (by decide) thirteenLeT))
          (add_nonneg
            (RFAP.ConstructiveFraction.mul_nonneg_direct
              (by decide) (by decide))
            (by decide))
      have affineLowerNonnegative : 0 ≤ affineLower := by
        dsimp only [affineLower]
        exact RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
          affineNumeratorNonnegative
      have qNonnegative :
          0 ≤ 4 * t * ((2 : Coordinate) ^ 9 - t) -
            (5 * t + (10 * 8 + 2)) ^ 2 := by
        by_cases tLeTwentyOne : t ≤ (21 : Coordinate)
        · have firstNonnegative : 0 ≤ t - 13 :=
            RFAP.ConstructiveFraction.sub_nonneg_direct thirteenLeT
          have secondNonnegative : 0 ≤ 23 * 37 - 29 * t :=
            RFAP.ConstructiveFraction.sub_nonneg_direct (by
              calc
                29 * t ≤ 29 * 21 :=
                  RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
                    tLeTwentyOne
                    (RFAP.ConstructiveFraction.natCast_le_direct
                      (m := 0) (n := 29) (by decide))
                _ ≤ 23 * 37 := by
                  apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
                  calc
                    0 ≤ (11 : Coordinate) * 22 :=
                      RFAP.ConstructiveFraction.mul_nonneg_direct
                        (RFAP.ConstructiveFraction.natCast_le_direct
                          (m := 0) (n := 11) (by decide))
                        (RFAP.ConstructiveFraction.natCast_le_direct
                          (m := 0) (n := 22) (by decide))
                    _ = 23 * 37 - 29 * 21 := by ring1)
          have productNonnegative :
              0 ≤ (t - 13) * (23 * 37 - 29 * t) :=
            RFAP.ConstructiveFraction.mul_nonneg_direct firstNonnegative
              secondNonnegative
          calc
            0 ≤ ((2 : Coordinate) ^ 6 * (8 * 8 + 3) + (6 * 8 + 3)) +
                (t - 13) * (23 * 37 - 29 * t) :=
              add_nonneg
                (add_nonneg
                  (RFAP.ConstructiveFraction.mul_nonneg_direct
                    (RFAP.ConstructiveFraction.pow_nonneg_direct (by decide) 6)
                    (add_nonneg
                      (RFAP.ConstructiveFraction.mul_nonneg_direct
                        (by decide) (by decide))
                      (by decide)))
                  (add_nonneg
                    (RFAP.ConstructiveFraction.mul_nonneg_direct
                      (by decide) (by decide))
                    (by decide)))
                productNonnegative
            _ = 4 * t * ((2 : Coordinate) ^ 9 - t) -
                (5 * t + (10 * 8 + 2)) ^ 2 := by ring1
        · have twentyOneLeT : (21 : Coordinate) ≤ t :=
            le_of_not_ge tLeTwentyOne
          have firstNonnegative : 0 ≤ 35 - t :=
            RFAP.ConstructiveFraction.sub_nonneg_direct tLeThirtyFive
          have secondNonnegative : 0 ≤ 29 * t - 3 * (9 * 8 - 1) :=
            RFAP.ConstructiveFraction.sub_nonneg_direct (by
              calc
                3 * (9 * 8 - 1) ≤ 29 * 21 := by
                  apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
                  calc
                    0 ≤ (12 : Coordinate) * 33 :=
                      RFAP.ConstructiveFraction.mul_nonneg_direct
                        (RFAP.ConstructiveFraction.natCast_le_direct
                          (m := 0) (n := 12) (by decide))
                        (RFAP.ConstructiveFraction.natCast_le_direct
                          (m := 0) (n := 33) (by decide))
                    _ = 29 * 21 - 3 * (9 * 8 - 1) := by ring1
                _ ≤ 29 * t :=
                  RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
                    twentyOneLeT
                    (RFAP.ConstructiveFraction.natCast_le_direct
                      (m := 0) (n := 29) (by decide)))
          have productNonnegative :
              0 ≤ (35 - t) * (29 * t - 3 * (9 * 8 - 1)) :=
            RFAP.ConstructiveFraction.mul_nonneg_direct firstNonnegative
              secondNonnegative
          calc
            0 ≤ 17 * (5 * 8 + 3) +
                (35 - t) * (29 * t - 3 * (9 * 8 - 1)) :=
              add_nonneg
                (RFAP.ConstructiveFraction.mul_nonneg_direct
                  (by decide)
                  (add_nonneg
                    (RFAP.ConstructiveFraction.mul_nonneg_direct
                      (by decide) (by decide))
                    (by decide)))
                productNonnegative
            _ = 4 * t * ((2 : Coordinate) ^ 9 - t) -
                (5 * t + (10 * 8 + 2)) ^ 2 := by ring1
      have numeratorSquareLeScaledMiddle :
          affineNumerator ^ 2 ≤
            ((2 : Coordinate) ^ 9) ^ 2 * (2 * b - b ^ 2) := by
        apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
        calc
          0 ≤ 4 * t * ((2 : Coordinate) ^ 9 - t) -
              (5 * t + (10 * 8 + 2)) ^ 2 := qNonnegative
          _ = ((2 : Coordinate) ^ 9) ^ 2 * (2 * b - b ^ 2) -
              affineNumerator ^ 2 := by
            dsimp only [t, affineNumerator]
            ring1
      have middleLeUSquare : 2 * b - b ^ 2 ≤ u ^ 2 := by
        apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
        calc
          0 ≤ xNorm + 1 - 2 * (a + b) :=
            RFAP.ConstructiveFraction.sub_nonneg_direct
              diagonalObstruction
          _ = u ^ 2 - (2 * b - b ^ 2) := by
            dsimp only [u]
            rw [xNormIdentity]
            ring1
      have affineSquareLeUSquare : affineLower ^ 2 ≤ u ^ 2 := by
        apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct
          (c := ((2 : Coordinate) ^ 9) ^ 2)
        · calc
            affineLower ^ 2 * ((2 : Coordinate) ^ 9) ^ 2 =
                affineNumerator ^ 2 := by
              dsimp only [affineLower]
              calc
                ((1 / ((2 : Coordinate) ^ 9) : Coordinate) *
                      affineNumerator) ^ 2 * ((2 : Coordinate) ^ 9) ^ 2 =
                    (((1 / ((2 : Coordinate) ^ 9) : Coordinate) ^ 2) *
                      ((2 : Coordinate) ^ 9) ^ 2) *
                      affineNumerator ^ 2 := by ring1
                _ = 1 * affineNumerator ^ 2 := by
                  rw [show
                    (1 / ((2 : Coordinate) ^ 9) : Coordinate) ^ 2 *
                      ((2 : Coordinate) ^ 9) ^ 2 = 1 by decide]
                _ = affineNumerator ^ 2 := by ring1
            _ ≤ ((2 : Coordinate) ^ 9) ^ 2 * (2 * b - b ^ 2) :=
              numeratorSquareLeScaledMiddle
            _ ≤ ((2 : Coordinate) ^ 9) ^ 2 * u ^ 2 :=
              RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
                middleLeUSquare
                (RFAP.ConstructiveFraction.pow_nonneg_direct
                  (RFAP.ConstructiveFraction.pow_nonneg_direct (by decide) 9)
                  2)
            _ = u ^ 2 * ((2 : Coordinate) ^ 9) ^ 2 := by ring1
        · exact RFAP.ConstructiveFraction.pow_pos_direct
            (RFAP.ConstructiveFraction.pow_pos_direct (by decide) 9) 2
      have affineLowerLeU : affineLower ≤ u :=
        RFAP.ConstructiveFraction.le_of_sq_le_sq_direct uNonnegative
          affineSquareLeUSquare
      have complementOrder : 1 - u ≤ 1 - affineLower := by
        have negated := RFAP.ConstructiveFraction.neg_le_neg_direct
          affineLowerLeU
        calc
          1 - u = -u + 1 := by ring1
          _ ≤ -affineLower + 1 :=
            RFAP.ConstructiveFraction.add_le_add_right_direct negated 1
          _ = 1 - affineLower := by ring1
      have oneMinusUNonnegative : 0 ≤ 1 - u := by
        dsimp only [u]
        simpa only [sub_sub_cancel] using aNonnegative
      have complementSquareOrder :
          (1 - u) ^ 2 ≤ (1 - affineLower) ^ 2 :=
        RFAP.ConstructiveFraction.pow_le_pow_direct oneMinusUNonnegative
          complementOrder 2
      have normTermLeAffineQuarter :
          xNorm * (a - xNorm) ≤
            (1 / 4 : Coordinate) * (1 - affineLower) ^ 2 := by
        calc
          xNorm * (a - xNorm) ≤ (1 / 4 : Coordinate) * a ^ 2 :=
            normTermLeASquareQuarter
          _ = (1 / 4 : Coordinate) * (1 - u) ^ 2 := by
            dsimp only [u]
            ring1
          _ ≤ (1 / 4 : Coordinate) * (1 - affineLower) ^ 2 :=
            RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
              complementSquareOrder (by decide)
      have affineComplementRepresentation :
          1 - affineLower =
            (1 / ((2 : Coordinate) ^ 9) : Coordinate) *
              (2 * (2 : Coordinate) ^ 8 - (10 * 8 + 2) - 5 * t) := by
        dsimp only [affineLower, affineNumerator]
        calc
          1 - (1 / ((2 : Coordinate) ^ 9) : Coordinate) *
                (5 * t + (10 * 8 + 2)) =
              (1 / ((2 : Coordinate) ^ 9) : Coordinate) *
                  ((2 : Coordinate) ^ 9) -
                (1 / ((2 : Coordinate) ^ 9) : Coordinate) *
                  (5 * t + (10 * 8 + 2)) := by
            rw [show (1 / ((2 : Coordinate) ^ 9) : Coordinate) *
              ((2 : Coordinate) ^ 9) = 1 by decide]
          _ = (1 / ((2 : Coordinate) ^ 9) : Coordinate) *
              (2 * (2 : Coordinate) ^ 8 - (10 * 8 + 2) - 5 * t) := by ring1
      have scaledAffineBoundary :
          (16 * ((2 : Coordinate) ^ 8) ^ 2) *
              (b + (1 / 4 : Coordinate) * (1 - affineLower) ^ 2) ≤
            16 * 51 * (2 : Coordinate) ^ 8 := by
        have firstNonnegative : 0 ≤ 35 - t :=
          RFAP.ConstructiveFraction.sub_nonneg_direct tLeThirtyFive
        have secondNonnegative : 0 ≤ 25 * t + 11 * (7 * 8 + 5) :=
          add_nonneg
            (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
              (le_trans (by decide) thirteenLeT))
            (RFAP.ConstructiveFraction.mul_nonneg_direct
              (by decide)
              (add_nonneg
                (RFAP.ConstructiveFraction.mul_nonneg_direct
                  (by decide) (by decide))
                (by decide)))
        have productNonnegative :
            0 ≤ (35 - t) * (25 * t + 11 * (7 * 8 + 5)) :=
          RFAP.ConstructiveFraction.mul_nonneg_direct firstNonnegative
            secondNonnegative
        have endpointSlackNonnegative :
            0 ≤ 2 * (2 : Coordinate) ^ 8 - 1 := by decide
        calc
          (16 * ((2 : Coordinate) ^ 8) ^ 2) *
                (b + (1 / 4 : Coordinate) * (1 - affineLower) ^ 2) =
              16 * (2 : Coordinate) ^ 8 * t +
                (2 * (2 : Coordinate) ^ 8 - (10 * 8 + 2) - 5 * t) ^ 2 := by
            calc
              (16 * ((2 : Coordinate) ^ 8) ^ 2) *
                    (b + (1 / 4 : Coordinate) * (1 - affineLower) ^ 2) =
                  (16 * ((2 : Coordinate) ^ 8) ^ 2) * b +
                    ((16 * ((2 : Coordinate) ^ 8) ^ 2) *
                      (1 / 4 : Coordinate)) *
                      (1 - affineLower) ^ 2 := by ring1
              _ = 16 * (2 : Coordinate) ^ 8 * t +
                    ((2 : Coordinate) ^ 9) ^ 2 *
                      (1 - affineLower) ^ 2 := by
                rw [show
                  (16 * ((2 : Coordinate) ^ 8) ^ 2) *
                    (1 / 4 : Coordinate) = ((2 : Coordinate) ^ 9) ^ 2 by
                      decide]
                dsimp only [t]
                ring1
              _ = 16 * (2 : Coordinate) ^ 8 * t +
                    ((2 : Coordinate) ^ 9) ^ 2 *
                      ((1 / ((2 : Coordinate) ^ 9) : Coordinate) *
                        (2 * (2 : Coordinate) ^ 8 - (10 * 8 + 2) -
                          5 * t)) ^ 2 := by
                rw [affineComplementRepresentation]
              _ = 16 * (2 : Coordinate) ^ 8 * t +
                    (((1 / ((2 : Coordinate) ^ 9) : Coordinate) ^ 2) *
                      ((2 : Coordinate) ^ 9) ^ 2) *
                        (2 * (2 : Coordinate) ^ 8 - (10 * 8 + 2) -
                          5 * t) ^ 2 := by
                ring1
              _ = 16 * (2 : Coordinate) ^ 8 * t +
                    1 * (2 * (2 : Coordinate) ^ 8 - (10 * 8 + 2) -
                      5 * t) ^ 2 := by
                rw [show
                  (1 / ((2 : Coordinate) ^ 9) : Coordinate) ^ 2 *
                    ((2 : Coordinate) ^ 9) ^ 2 = 1 by decide]
              _ = 16 * (2 : Coordinate) ^ 8 * t +
                  (2 * (2 : Coordinate) ^ 8 - (10 * 8 + 2) -
                    5 * t) ^ 2 := by ring1
          _ ≤ 16 * 51 * (2 : Coordinate) ^ 8 := by
            apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
            calc
              0 ≤ (2 * (2 : Coordinate) ^ 8 - 1) +
                  (35 - t) * (25 * t + 11 * (7 * 8 + 5)) :=
                add_nonneg endpointSlackNonnegative productNonnegative
              _ = 16 * 51 * (2 : Coordinate) ^ 8 -
                  (16 * (2 : Coordinate) ^ 8 * t +
                    (2 * (2 : Coordinate) ^ 8 - (10 * 8 + 2) -
                      5 * t) ^ 2) := by
                ring1
      have affineBoundary :
          b + (1 / 4 : Coordinate) * (1 - affineLower) ^ 2 ≤
            firstRegionProjectionBound := by
        apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct
          (c := 16 * ((2 : Coordinate) ^ 8) ^ 2)
        · calc
            (b + (1 / 4 : Coordinate) * (1 - affineLower) ^ 2) *
                (16 * ((2 : Coordinate) ^ 8) ^ 2) =
              (16 * ((2 : Coordinate) ^ 8) ^ 2) *
                (b + (1 / 4 : Coordinate) * (1 - affineLower) ^ 2) := by
                  ring1
            _ ≤ 16 * 51 * (2 : Coordinate) ^ 8 := scaledAffineBoundary
            _ = firstRegionProjectionBound *
                (16 * ((2 : Coordinate) ^ 8) ^ 2) := by
              calc
                16 * 51 * (2 : Coordinate) ^ 8 =
                    16 * (firstRegionProjectionBound *
                      (2 : Coordinate) ^ 8) * (2 : Coordinate) ^ 8 := by
                        rw [firstRegionProjectionBound_mul_denominator]
                _ = firstRegionProjectionBound *
                    (16 * ((2 : Coordinate) ^ 8) ^ 2) := by ring1
        · exact RFAP.ConstructiveFraction.mul_pos_direct (by decide)
            (RFAP.ConstructiveFraction.pow_pos_direct
              (RFAP.ConstructiveFraction.pow_pos_direct (by decide) 8) 2)
      calc
        b + xNorm * (a - xNorm) ≤
            b + (1 / 4 : Coordinate) * (1 - affineLower) ^ 2 := by
          have shifted :=
            RFAP.ConstructiveFraction.add_le_add_right_direct
              normTermLeAffineQuarter b
          calc
            b + xNorm * (a - xNorm) = xNorm * (a - xNorm) + b := by ring1
            _ ≤ (1 / 4 : Coordinate) * (1 - affineLower) ^ 2 + b :=
              shifted
            _ = b + (1 / 4 : Coordinate) * (1 - affineLower) ^ 2 := by
              ring1
        _ ≤ firstRegionProjectionBound := affineBoundary

/-- The dyadic projection bound is strictly stronger than the convenient
decimal-free value `1/5`. -/
theorem second_add_norm_mul_first_sub_norm_le_oneFifth
    (a b xNorm : Coordinate)
    (aNonnegative : 0 ≤ a)
    (xNormIdentity : xNorm = a ^ 2 + b ^ 2)
    (xNormLeOne : xNorm ≤ 1)
    (imaginaryObstruction : 2 * b ≤ xNorm)
    (diagonalObstruction : 2 * (a + b) ≤ xNorm + 1) :
    b + xNorm * (a - xNorm) ≤ (1 / 5 : Coordinate) :=
  (second_add_norm_mul_first_sub_norm_le_projectionBound
    a b xNorm aNonnegative xNormIdentity xNormLeOne
    imaginaryObstruction diagonalObstruction).trans
      firstRegionProjectionBound_le_oneFifth

/-- Two vectors satisfying the extremal chamber inequalities have normalized
determinant gap at least `205/256`.  The proof chooses the smaller of the two
displayed quadrances and uses the corresponding projection; all choices and
comparisons are finite rational calculations. -/
theorem firstRegionGapBound_le_gap_of_two_firstRegionObstructions
    (a b e c xNorm yNorm : Coordinate)
    (aNonnegative : 0 ≤ a)
    (bNonnegative : 0 ≤ b)
    (eNonnegative : 0 ≤ e)
    (cNonnegative : 0 ≤ c)
    (bLeA : b ≤ a)
    (cLeE : c ≤ e)
    (xNormIdentity : xNorm = a ^ 2 + b ^ 2)
    (yNormIdentity : yNorm = e ^ 2 + c ^ 2)
    (xNormLeOne : xNorm ≤ 1)
    (yNormLeOne : yNorm ≤ 1)
    (firstImaginaryObstruction : 2 * b ≤ xNorm)
    (firstDiagonalObstruction : 2 * (a + b) ≤ xNorm + 1)
    (secondImaginaryObstruction : 2 * c ≤ yNorm)
    (secondDiagonalObstruction : 2 * (e + c) ≤ yNorm + 1) :
    firstRegionGapBound ≤
      1 + xNorm * yNorm - 2 * (a * c + b * e) := by
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
    have aMinusBNonnegative : 0 ≤ a - b :=
      RFAP.ConstructiveFraction.sub_nonneg_direct bLeA
    have firstScaled :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        secondImaginaryObstruction aMinusBNonnegative
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
    have eMinusCNonnegative : 0 ≤ e - c :=
      RFAP.ConstructiveFraction.sub_nonneg_direct cLeE
    have firstScaled :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        firstImaginaryObstruction eMinusCNonnegative
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
  · have projectedTermLe :
        b + yNorm * (a - xNorm) ≤ firstRegionProjectionBound := by
      by_cases deltaNonnegative : 0 ≤ a - xNorm
      · have scaled :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
            yNormLeXNorm deltaNonnegative
        calc
          b + yNorm * (a - xNorm) ≤
              b + xNorm * (a - xNorm) :=
            RFAP.ConstructiveFraction.add_le_add_direct le_rfl scaled
          _ ≤ firstRegionProjectionBound :=
            second_add_norm_mul_first_sub_norm_le_projectionBound
              a b xNorm aNonnegative xNormIdentity xNormLeOne
                firstImaginaryObstruction firstDiagonalObstruction
      · have deltaNonpositive : a - xNorm ≤ 0 :=
          le_of_not_ge deltaNonnegative
        have productNonpositive : yNorm * (a - xNorm) ≤ 0 := by
          have scaled :=
            RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
              deltaNonpositive yNormNonnegative
          simpa only [mul_zero] using scaled
        calc
          b + yNorm * (a - xNorm) ≤ b + 0 :=
            RFAP.ConstructiveFraction.add_le_add_direct le_rfl
              productNonpositive
          _ = b := by ring1
          _ ≤ firstRegionSecondBoundary :=
            second_le_firstRegionBoundary_of_firstRegionObstructions
              a b xNorm aNonnegative xNormIdentity xNormLeOne
                firstImaginaryObstruction firstDiagonalObstruction
          _ ≤ firstRegionProjectionBound :=
            firstRegionSecondBoundary_le_projectionBound
    have negatedProjection := RFAP.ConstructiveFraction.neg_le_neg_direct
      firstProjection
    have shiftedProjection := RFAP.ConstructiveFraction.add_le_add_direct
      (le_refl (1 + xNorm * yNorm)) negatedProjection
    have negatedTerm := RFAP.ConstructiveFraction.neg_le_neg_direct
      projectedTermLe
    calc
      firstRegionGapBound = 1 - firstRegionProjectionBound := rfl
      _ ≤ 1 - (b + yNorm * (a - xNorm)) :=
        (show (1 : Coordinate) + -firstRegionProjectionBound ≤
            1 + -(b + yNorm * (a - xNorm)) from
          RFAP.ConstructiveFraction.add_le_add_direct
            (le_refl (1 : Coordinate)) negatedTerm)
      _ = 1 + xNorm * yNorm - (a * yNorm + b) := by ring1
      _ ≤ 1 + xNorm * yNorm - 2 * (a * c + b * e) := by
        simpa only [sub_eq_add_neg] using shiftedProjection
  · have xNormLeYNorm : xNorm ≤ yNorm := le_of_not_ge yNormLeXNorm
    have projectedTermLe :
        c + xNorm * (e - yNorm) ≤ firstRegionProjectionBound := by
      by_cases deltaNonnegative : 0 ≤ e - yNorm
      · have scaled :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
            xNormLeYNorm deltaNonnegative
        calc
          c + xNorm * (e - yNorm) ≤
              c + yNorm * (e - yNorm) :=
            RFAP.ConstructiveFraction.add_le_add_direct le_rfl scaled
          _ ≤ firstRegionProjectionBound :=
            second_add_norm_mul_first_sub_norm_le_projectionBound
              e c yNorm eNonnegative yNormIdentity yNormLeOne
                secondImaginaryObstruction secondDiagonalObstruction
      · have deltaNonpositive : e - yNorm ≤ 0 :=
          le_of_not_ge deltaNonnegative
        have productNonpositive : xNorm * (e - yNorm) ≤ 0 := by
          have scaled :=
            RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
              deltaNonpositive xNormNonnegative
          simpa only [mul_zero] using scaled
        calc
          c + xNorm * (e - yNorm) ≤ c + 0 :=
            RFAP.ConstructiveFraction.add_le_add_direct le_rfl
              productNonpositive
          _ = c := by ring1
          _ ≤ firstRegionSecondBoundary :=
            second_le_firstRegionBoundary_of_firstRegionObstructions
              e c yNorm eNonnegative yNormIdentity yNormLeOne
                secondImaginaryObstruction secondDiagonalObstruction
          _ ≤ firstRegionProjectionBound :=
            firstRegionSecondBoundary_le_projectionBound
    have negatedProjection := RFAP.ConstructiveFraction.neg_le_neg_direct
      secondProjection
    have shiftedProjection := RFAP.ConstructiveFraction.add_le_add_direct
      (le_refl (1 + xNorm * yNorm)) negatedProjection
    have negatedTerm := RFAP.ConstructiveFraction.neg_le_neg_direct
      projectedTermLe
    calc
      firstRegionGapBound = 1 - firstRegionProjectionBound := rfl
      _ ≤ 1 - (c + xNorm * (e - yNorm)) :=
        (show (1 : Coordinate) + -firstRegionProjectionBound ≤
            1 + -(c + xNorm * (e - yNorm)) from
          RFAP.ConstructiveFraction.add_le_add_direct
            (le_refl (1 : Coordinate)) negatedTerm)
      _ = 1 + xNorm * yNorm - (e * xNorm + c) := by ring1
      _ ≤ 1 + xNorm * yNorm - 2 * (a * c + b * e) := by
        simpa only [sub_eq_add_neg] using shiftedProjection

/-- The nonnegative-real half of the actual green chamber is the symmetric
two-vector chamber after the explicit substitution `e=-d`. -/
theorem firstRegionGapBound_le_gap_of_greenRegion_of_real_nonnegative
    (a b c d xNorm yNorm : Coordinate)
    (aNonnegative : 0 ≤ a)
    (bNonnegative : 0 ≤ b)
    (bLeA : b ≤ a)
    (cNonnegative : 0 ≤ c)
    (xNormIdentity : xNorm = a ^ 2 + b ^ 2)
    (yNormIdentity : yNorm = c ^ 2 + d ^ 2)
    (xNormLeOne : xNorm ≤ 1)
    (yNormLeOne : yNorm ≤ 1)
    (errorImaginaryObstruction : 2 * b ≤ xNorm)
    (errorDiagonalObstruction : 2 * (a + b) ≤ xNorm + 1)
    (denominatorRealObstruction : 2 * c ≤ yNorm)
    (denominatorDiagonalObstruction : 2 * (c - d) ≤ yNorm + 1)
    (greenRegion : yNorm < c - d) :
    firstRegionGapBound ≤
      1 + xNorm * yNorm - 2 * (a * c - b * d) := by
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
  have bound := firstRegionGapBound_le_gap_of_two_firstRegionObstructions
    a b (-d) c xNorm yNorm aNonnegative bNonnegative negDNonnegative
      cNonnegative bLeA cLeNegD xNormIdentity transformedNormIdentity
      xNormLeOne yNormLeOne errorImaginaryObstruction
      errorDiagonalObstruction denominatorRealObstruction
      transformedDiagonalObstruction
  calc
    firstRegionGapBound ≤
        1 + xNorm * yNorm - 2 * (a * c + b * (-d)) := bound
    _ = 1 + xNorm * yNorm - 2 * (a * c - b * d) := by ring1

/-- If the denominator real coordinate is nonpositive, the green-chamber
error inequalities give a stronger square certificate directly.  The exact
remainder is a sum of `-2ac`, `Xc²`, `(X-2b)d²`, and
`(b/2)(2d+1)²`. -/
theorem thirteenFourteenths_le_gap_of_real_nonpositive
    (a b c d xNorm yNorm : Coordinate)
    (aNonnegative : 0 ≤ a)
    (bNonnegative : 0 ≤ b)
    (cNonpositive : c ≤ 0)
    (xNormIdentity : xNorm = a ^ 2 + b ^ 2)
    (yNormIdentity : yNorm = c ^ 2 + d ^ 2)
    (xNormLeOne : xNorm ≤ 1)
    (errorImaginaryObstruction : 2 * b ≤ xNorm)
    (errorDiagonalObstruction : 2 * (a + b) ≤ xNorm + 1) :
    (13 / 14 : Coordinate) ≤
      1 + xNorm * yNorm - 2 * (a * c - b * d) := by
  have bLeBoundary : b ≤ firstRegionSecondBoundary :=
    second_le_firstRegionBoundary_of_firstRegionObstructions
      a b xNorm aNonnegative xNormIdentity xNormLeOne
        errorImaginaryObstruction errorDiagonalObstruction
  have sevenBLeOne : 7 * b ≤ 1 := by
    calc
      7 * b ≤ 7 * firstRegionSecondBoundary :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct bLeBoundary
          (by decide)
      _ ≤ 1 := seven_mul_firstRegionSecondBoundary_le_one
  have halfBLeOneFourteenth :
      (1 / 2 : Coordinate) * b ≤ 1 / 14 := by
    apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct (c := 14)
    · calc
        ((1 / 2 : Coordinate) * b) * 14 =
            ((1 / 2 : Coordinate) * 14) * b := by ring1
        _ = 7 * b := by
          rw [show (1 / 2 : Coordinate) * 14 = 7 by decide]
        _ ≤ 1 := sevenBLeOne
        _ = (1 / 14 : Coordinate) * 14 := by decide
    · decide
  have xMinusTwiceBNonnegative : 0 ≤ xNorm - 2 * b :=
    RFAP.ConstructiveFraction.sub_nonneg_direct errorImaginaryObstruction
  have halfSquareExpansion :
      (1 / 2 : Coordinate) * b * (2 * d + 1) ^ 2 =
        2 * b * d ^ 2 + 2 * b * d + (1 / 2 : Coordinate) * b := by
    calc
      (1 / 2 : Coordinate) * b * (2 * d + 1) ^ 2 =
          ((1 / 2 : Coordinate) * 4) * b * d ^ 2 +
            ((1 / 2 : Coordinate) * 4) * b * d +
              (1 / 2 : Coordinate) * b := by ring1
      _ = 2 * b * d ^ 2 + 2 * b * d +
          (1 / 2 : Coordinate) * b := by
        rw [show (1 / 2 : Coordinate) * 4 = 2 by decide]
  have squareCertificate :
      0 ≤ xNorm * yNorm + 2 * b * d + (1 / 2 : Coordinate) * b := by
    calc
      0 ≤ xNorm * c ^ 2 +
          (xNorm - 2 * b) * d ^ 2 +
          (1 / 2 : Coordinate) * b * (2 * d + 1) ^ 2 := by
        repeat apply add_nonneg
        · have xNormNonnegative : 0 ≤ xNorm := by
            rw [xNormIdentity]
            exact add_nonneg
              (RFAP.ConstructiveFraction.sq_nonneg_direct a)
              (RFAP.ConstructiveFraction.sq_nonneg_direct b)
          exact RFAP.ConstructiveFraction.mul_nonneg_direct xNormNonnegative
            (RFAP.ConstructiveFraction.sq_nonneg_direct c)
        · exact RFAP.ConstructiveFraction.mul_nonneg_direct
            xMinusTwiceBNonnegative
            (RFAP.ConstructiveFraction.sq_nonneg_direct d)
        · exact RFAP.ConstructiveFraction.mul_nonneg_direct
            (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
              bNonnegative)
            (RFAP.ConstructiveFraction.sq_nonneg_direct _)
      _ = xNorm * yNorm + 2 * b * d +
          (1 / 2 : Coordinate) * b := by
        rw [yNormIdentity, halfSquareExpansion]
        ring1
  have acNonpositive : a * c ≤ 0 := by
    have scaled :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        cNonpositive aNonnegative
    simpa only [mul_zero] using scaled
  have minusTwiceACNonnegative : 0 ≤ -2 * (a * c) := by
    have negated := RFAP.ConstructiveFraction.neg_le_neg_direct acNonpositive
    have scaled :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct negated
        (show (0 : Coordinate) ≤ 2 by decide)
    calc
      0 = 2 * -0 := by ring1
      _ ≤ 2 * -(a * c) := scaled
      _ = -2 * (a * c) := by ring1
  have gapFromHalfB :
      1 - (1 / 2 : Coordinate) * b ≤
        1 + xNorm * yNorm - 2 * (a * c - b * d) := by
    apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
    calc
      0 ≤ -2 * (a * c) +
          (xNorm * yNorm + 2 * b * d + (1 / 2 : Coordinate) * b) :=
        add_nonneg minusTwiceACNonnegative squareCertificate
      _ = (1 + xNorm * yNorm - 2 * (a * c - b * d)) -
          (1 - (1 / 2 : Coordinate) * b) := by ring1
  have negatedHalfB := RFAP.ConstructiveFraction.neg_le_neg_direct
    halfBLeOneFourteenth
  calc
    (13 / 14 : Coordinate) = 1 - 1 / 14 := by decide
    _ ≤ 1 - (1 / 2 : Coordinate) * b :=
      (show (1 : Coordinate) + -(1 / 14 : Coordinate) ≤
          1 + -((1 / 2 : Coordinate) * b) from
        RFAP.ConstructiveFraction.add_le_add_direct
          (le_refl (1 : Coordinate)) negatedHalfB)
    _ ≤ 1 + xNorm * yNorm - 2 * (a * c - b * d) := gapFromHalfB

/-- The dyadic green-region statement retained for the existing public
interface. -/
theorem firstRegionGapBound_le_gap_of_real_nonpositive
    (a b c d xNorm yNorm : Coordinate)
    (aNonnegative : 0 ≤ a)
    (bNonnegative : 0 ≤ b)
    (cNonpositive : c ≤ 0)
    (xNormIdentity : xNorm = a ^ 2 + b ^ 2)
    (yNormIdentity : yNorm = c ^ 2 + d ^ 2)
    (xNormLeOne : xNorm ≤ 1)
    (errorImaginaryObstruction : 2 * b ≤ xNorm)
    (errorDiagonalObstruction : 2 * (a + b) ≤ xNorm + 1) :
    firstRegionGapBound ≤
      1 + xNorm * yNorm - 2 * (a * c - b * d) := by
  calc
    firstRegionGapBound ≤ (13 / 14 : Coordinate) := by
      unfold firstRegionGapBound firstRegionProjectionBound
        firstRegionProjectionBoundFraction
      decide
    _ ≤ 1 + xNorm * yNorm - 2 * (a * c - b * d) :=
      thirteenFourteenths_le_gap_of_real_nonpositive
        a b c d xNorm yNorm aNonnegative bNonnegative cNonpositive
        xNormIdentity yNormIdentity xNormLeOne errorImaginaryObstruction
        errorDiagonalObstruction

/-- The complete displayed green region has gap at least `205/256`; the
decidable sign of `c` selects one of the two preceding certificates. -/
theorem firstRegionGapBound_le_gap_of_greenRegion
    (a b c d xNorm yNorm : Coordinate)
    (aNonnegative : 0 ≤ a)
    (bNonnegative : 0 ≤ b)
    (bLeA : b ≤ a)
    (xNormIdentity : xNorm = a ^ 2 + b ^ 2)
    (yNormIdentity : yNorm = c ^ 2 + d ^ 2)
    (xNormLeOne : xNorm ≤ 1)
    (yNormLeOne : yNorm ≤ 1)
    (errorImaginaryObstruction : 2 * b ≤ xNorm)
    (errorDiagonalObstruction : 2 * (a + b) ≤ xNorm + 1)
    (denominatorRealObstruction : 2 * c ≤ yNorm)
    (denominatorDiagonalObstruction : 2 * (c - d) ≤ yNorm + 1)
    (greenRegion : yNorm < c - d) :
    firstRegionGapBound ≤
      1 + xNorm * yNorm - 2 * (a * c - b * d) := by
  by_cases cNonnegative : 0 ≤ c
  · exact firstRegionGapBound_le_gap_of_greenRegion_of_real_nonnegative
      a b c d xNorm yNorm aNonnegative bNonnegative bLeA cNonnegative
        xNormIdentity yNormIdentity xNormLeOne yNormLeOne
        errorImaginaryObstruction errorDiagonalObstruction
        denominatorRealObstruction denominatorDiagonalObstruction greenRegion
  · exact firstRegionGapBound_le_gap_of_real_nonpositive
      a b c d xNorm yNorm aNonnegative bNonnegative
        (le_of_not_ge cNonnegative) xNormIdentity yNormIdentity xNormLeOne
        errorImaginaryObstruction errorDiagonalObstruction

/-- In the red region the displayed inequalities force `c≤0`.  Rewriting
the cross term as `(a-b)c+b(c-d)` then gives `2P≤XY`, so the gap is at
least one. -/
theorem one_le_gap_of_redRegion
    (a b c d xNorm yNorm : Coordinate)
    (bNonnegative : 0 ≤ b)
    (bLeA : b ≤ a)
    (xNormIdentity : xNorm = a ^ 2 + b ^ 2)
    (yNormIdentity : yNorm = c ^ 2 + d ^ 2)
    (yNormLeOne : yNorm ≤ 1)
    (errorImaginaryObstruction : 2 * b ≤ xNorm)
    (outsideGreen : c - d ≤ yNorm)
    (redRegion : yNorm < -2 * d) :
    (1 : Coordinate) ≤
      1 + xNorm * yNorm - 2 * (a * c - b * d) := by
  let e : Coordinate := -d
  have xNormNonnegative : 0 ≤ xNorm := by
    rw [xNormIdentity]
    exact add_nonneg
      (RFAP.ConstructiveFraction.sq_nonneg_direct a)
      (RFAP.ConstructiveFraction.sq_nonneg_direct b)
  have yNormNonnegative : 0 ≤ yNorm := by
    rw [yNormIdentity]
    exact add_nonneg
      (RFAP.ConstructiveFraction.sq_nonneg_direct c)
      (RFAP.ConstructiveFraction.sq_nonneg_direct d)
  have transformedNormIdentity : yNorm = c ^ 2 + e ^ 2 := by
    dsimp only [e]
    rw [yNormIdentity]
    ring1
  have yNormLtTwiceE : yNorm < 2 * e := by
    dsimp only [e]
    calc
      yNorm < -2 * d := redRegion
      _ = 2 * -d := by ring1
  have ePositive : 0 < e := by
    have twiceEPositive : 0 < 2 * e :=
      lt_of_le_of_lt yNormNonnegative yNormLtTwiceE
    exact RFAP.ConstructiveFraction.pos_of_mul_pos_right_direct
      twiceEPositive (by decide)
  have eSquareLeYNorm : e ^ 2 ≤ yNorm := by
    rw [transformedNormIdentity]
    exact le_add_of_nonneg_left
      (RFAP.ConstructiveFraction.sq_nonneg_direct c)
  have eLeOne : e ≤ 1 :=
    RFAP.ConstructiveFraction.le_of_sq_le_sq_direct (by decide)
      (by simpa only [one_pow] using eSquareLeYNorm.trans yNormLeOne)
  have cLtE : c < e := by
    have sumLtTwiceE : c + e < 2 * e := by
      calc
        c + e = c - d := by
          dsimp only [e]
          ring1
        _ ≤ yNorm := outsideGreen
        _ < 2 * e := yNormLtTwiceE
    apply RFAP.ConstructiveFraction.lt_of_sub_neg_direct
    calc
      c - e = (c + e) - 2 * e := by ring1
      _ < 0 := RFAP.ConstructiveFraction.sub_neg_direct sumLtTwiceE
  have cNonpositive : c ≤ 0 := by
    by_cases cPositive : 0 < c
    · have cLtOne : c < 1 := cLtE.trans_le eLeOne
      have cSquareLtC : c ^ 2 < c := by
        have scaled :=
          RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
            cPositive cLtOne
        calc
          c ^ 2 = c * c := by ring1
          _ < c * 1 := scaled
          _ = c := by ring1
      have eSquareLeE : e ^ 2 ≤ e := by
        have scaled :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            eLeOne ePositive.le
        calc
          e ^ 2 = e * e := by ring1
          _ ≤ e * 1 := scaled
          _ = e := by ring1
      have normLtSum : yNorm < c + e := by
        rw [transformedNormIdentity]
        have first := RFAP.ConstructiveFraction.add_lt_add_right_direct
          cSquareLtC (e ^ 2)
        have second : c + e ^ 2 ≤ c + e := by
          exact RFAP.ConstructiveFraction.add_le_add_direct le_rfl eSquareLeE
        exact first.trans_le second
      exact ((not_lt_of_ge (show c + e ≤ yNorm by
        simpa only [e, sub_eq_add_neg] using outsideGreen)) normLtSum).elim
    · exact le_of_not_gt cPositive
  have aMinusBNonnegative : 0 ≤ a - b :=
    RFAP.ConstructiveFraction.sub_nonneg_direct bLeA
  have firstTermNonpositive : (a - b) * c ≤ 0 := by
    have scaled :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        cNonpositive aMinusBNonnegative
    simpa only [mul_zero] using scaled
  have secondTermBound : b * (c + e) ≤ b * yNorm := by
    apply RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      (show c + e ≤ yNorm by
        simpa only [e, sub_eq_add_neg] using outsideGreen)
      bNonnegative
  have crossLeBY : a * c - b * d ≤ b * yNorm := by
    calc
      a * c - b * d = (a - b) * c + b * (c + e) := by
        dsimp only [e]
        ring1
      _ ≤ 0 + b * yNorm :=
        RFAP.ConstructiveFraction.add_le_add_direct
          firstTermNonpositive secondTermBound
      _ = b * yNorm := by ring1
  have twiceCrossLeTwiceBY :
      2 * (a * c - b * d) ≤ 2 * b * yNorm := by
    have scaled :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        crossLeBY (show (0 : Coordinate) ≤ 2 by decide)
    simpa only [mul_assoc] using scaled
  have twiceBYLeProduct : 2 * b * yNorm ≤ xNorm * yNorm :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
      errorImaginaryObstruction yNormNonnegative
  have oneLeGap :
      (1 : Coordinate) ≤
        1 + xNorm * yNorm - 2 * (a * c - b * d) := by
    have crossBound := twiceCrossLeTwiceBY.trans twiceBYLeProduct
    have negated := RFAP.ConstructiveFraction.neg_le_neg_direct crossBound
    calc
      (1 : Coordinate) = 1 + xNorm * yNorm - xNorm * yNorm := by ring1
      _ ≤ 1 + xNorm * yNorm - 2 * (a * c - b * d) :=
        RFAP.ConstructiveFraction.add_le_add_direct
          (le_refl (1 + xNorm * yNorm)) negated
  exact oneLeGap

/-- The dyadic red-region statement retained for the existing public
interface. -/
theorem firstRegionGapBound_le_gap_of_redRegion
    (a b c d xNorm yNorm : Coordinate)
    (bNonnegative : 0 ≤ b)
    (bLeA : b ≤ a)
    (xNormIdentity : xNorm = a ^ 2 + b ^ 2)
    (yNormIdentity : yNorm = c ^ 2 + d ^ 2)
    (yNormLeOne : yNorm ≤ 1)
    (errorImaginaryObstruction : 2 * b ≤ xNorm)
    (outsideGreen : c - d ≤ yNorm)
    (redRegion : yNorm < -2 * d) :
    firstRegionGapBound ≤
      1 + xNorm * yNorm - 2 * (a * c - b * d) :=
  firstRegionGapBound_le_one.trans
    (one_le_gap_of_redRegion a b c d xNorm yNorm bNonnegative bLeA
      xNormIdentity yNormIdentity yNormLeOne errorImaginaryObstruction
      outsideGreen redRegion)

/-- In the blue region, either `c≤0` makes the cross term nonpositive, or
the circle exclusions force `0≤c≤d`; in the latter case
`2P≤XY` follows from the displayed `a-b` and `c` projections. -/
theorem one_le_gap_of_blueRegion
    (a b c d xNorm yNorm : Coordinate)
    (aNonnegative : 0 ≤ a)
    (bNonnegative : 0 ≤ b)
    (xNormIdentity : xNorm = a ^ 2 + b ^ 2)
    (yNormIdentity : yNorm = c ^ 2 + d ^ 2)
    (yNormLeOne : yNorm ≤ 1)
    (errorOppositeDiagonalObstruction : a - b ≤ xNorm)
    (denominatorRealObstruction : 2 * c ≤ yNorm)
    (blueRegion : yNorm + 1 < 2 * (c + d)) :
    (1 : Coordinate) ≤
      1 + xNorm * yNorm - 2 * (a * c - b * d) := by
  have xNormNonnegative : 0 ≤ xNorm := by
    rw [xNormIdentity]
    exact add_nonneg
      (RFAP.ConstructiveFraction.sq_nonneg_direct a)
      (RFAP.ConstructiveFraction.sq_nonneg_direct b)
  have yNormNonnegative : 0 ≤ yNorm := by
    rw [yNormIdentity]
    exact add_nonneg
      (RFAP.ConstructiveFraction.sq_nonneg_direct c)
      (RFAP.ConstructiveFraction.sq_nonneg_direct d)
  have dPositive : 0 < d := by
    have oneLtTwiceD : (1 : Coordinate) < 2 * d := by
      have shifted := lt_of_le_of_lt
        (RFAP.ConstructiveFraction.add_le_add_right_direct
          denominatorRealObstruction 1)
        blueRegion
      apply RFAP.ConstructiveFraction.lt_of_sub_neg_direct
      calc
        1 - 2 * d = (2 * c + 1) - 2 * (c + d) := by ring1
        _ < 0 := RFAP.ConstructiveFraction.sub_neg_direct shifted
    have twiceDPositive : 0 < 2 * d :=
      (show (0 : Coordinate) < 1 by decide).trans oneLtTwiceD
    exact RFAP.ConstructiveFraction.pos_of_mul_pos_right_direct
      twiceDPositive (by decide)
  have oneLeGap_of_c_nonpositive (cNonpositive : c ≤ 0) :
      (1 : Coordinate) ≤
        1 + xNorm * yNorm - 2 * (a * c - b * d) := by
    have acNonpositive : a * c ≤ 0 := by
      have scaled :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          cNonpositive aNonnegative
      simpa only [mul_zero] using scaled
    have minusBDNonpositive : -(b * d) ≤ 0 := by
      have productNonnegative :=
        RFAP.ConstructiveFraction.mul_nonneg_direct bNonnegative dPositive.le
      have negated := RFAP.ConstructiveFraction.neg_le_neg_direct
        productNonnegative
      simpa only [neg_zero] using negated
    have crossNonpositive : a * c - b * d ≤ 0 := by
      calc
        a * c - b * d = a * c + -(b * d) := rfl
        _ ≤ 0 + 0 := RFAP.ConstructiveFraction.add_le_add_direct
          acNonpositive minusBDNonpositive
        _ = 0 := by ring1
    have twiceCrossNonpositive : 2 * (a * c - b * d) ≤ 0 := by
      have scaled :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          crossNonpositive (show (0 : Coordinate) ≤ 2 by decide)
      simpa only [mul_zero] using scaled
    have negated := RFAP.ConstructiveFraction.neg_le_neg_direct
      twiceCrossNonpositive
    calc
      (1 : Coordinate) ≤ 1 + xNorm * yNorm :=
        le_add_of_nonneg_right
          (RFAP.ConstructiveFraction.mul_nonneg_direct
            xNormNonnegative yNormNonnegative)
      _ ≤ 1 + xNorm * yNorm - 2 * (a * c - b * d) := by
        calc
          1 + xNorm * yNorm = 1 + xNorm * yNorm + -0 := by ring1
          _ ≤ 1 + xNorm * yNorm + -(2 * (a * c - b * d)) :=
            RFAP.ConstructiveFraction.add_le_add_direct le_rfl negated
          _ = 1 + xNorm * yNorm - 2 * (a * c - b * d) := rfl
  by_cases cNonnegative : 0 ≤ c
  · have cSquareLeYNorm : c ^ 2 ≤ yNorm := by
      rw [yNormIdentity]
      exact le_add_of_nonneg_right
        (RFAP.ConstructiveFraction.sq_nonneg_direct d)
    have cLeOne : c ≤ 1 :=
      RFAP.ConstructiveFraction.le_of_sq_le_sq_direct (by decide)
        (by simpa only [one_pow] using cSquareLeYNorm.trans yNormLeOne)
    have cLeD : c ≤ d := by
      by_cases dLeC : d ≤ c
      · by_cases dEqualsC : d = c
        · exact dEqualsC.ge
        · have dLtC : d < c := lt_of_le_of_ne dLeC dEqualsC
          have cPositive : 0 < c := dPositive.trans dLtC
          have dSquareLtCSquare : d ^ 2 < c ^ 2 := by
            have first :=
              RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
                dPositive dLtC
            have second :=
              RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
                dLtC cPositive
            calc
              d ^ 2 = d * d := by ring1
              _ < d * c := first
              _ < c * c := second
              _ = c ^ 2 := by ring1
          have cSquareLeC : c ^ 2 ≤ c := by
            have scaled :=
              RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
                cLeOne cNonnegative
            calc
              c ^ 2 = c * c := by ring1
              _ ≤ c * 1 := scaled
              _ = c := by ring1
          have normLtTwiceC : yNorm < 2 * c := by
            rw [yNormIdentity]
            calc
              c ^ 2 + d ^ 2 = d ^ 2 + c ^ 2 := by ring1
              _ < c ^ 2 + c ^ 2 :=
                RFAP.ConstructiveFraction.add_lt_add_right_direct
                  dSquareLtCSquare (c ^ 2)
              _ ≤ c + c := RFAP.ConstructiveFraction.add_le_add_direct
                cSquareLeC cSquareLeC
              _ = 2 * c := by ring1
          exact ((not_lt_of_ge denominatorRealObstruction) normLtTwiceC).elim
      · exact le_of_not_ge dLeC
    have secondTermNonpositive : b * (c - d) ≤ 0 := by
      have differenceNonpositive : c - d ≤ 0 := by
        calc
          c - d = c + -d := rfl
          _ ≤ d + -d :=
            RFAP.ConstructiveFraction.add_le_add_right_direct cLeD (-d)
          _ = 0 := by ring1
      have scaled :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          differenceNonpositive bNonnegative
      simpa only [mul_zero] using scaled
    have firstTermBound : (a - b) * c ≤ xNorm * c :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        errorOppositeDiagonalObstruction cNonnegative
    have crossLeXC : a * c - b * d ≤ xNorm * c := by
      calc
        a * c - b * d = (a - b) * c + b * (c - d) := by ring1
        _ ≤ xNorm * c + 0 := RFAP.ConstructiveFraction.add_le_add_direct
          firstTermBound secondTermNonpositive
        _ = xNorm * c := by ring1
    have twiceCrossLeTwiceXC :
        2 * (a * c - b * d) ≤ xNorm * (2 * c) := by
      have scaled :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          crossLeXC (show (0 : Coordinate) ≤ 2 by decide)
      calc
        2 * (a * c - b * d) ≤ 2 * (xNorm * c) := scaled
        _ = xNorm * (2 * c) := by ring1
    have twiceCrossLeProduct :
        2 * (a * c - b * d) ≤ xNorm * yNorm :=
      twiceCrossLeTwiceXC.trans
        (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          denominatorRealObstruction xNormNonnegative)
    have negated := RFAP.ConstructiveFraction.neg_le_neg_direct
      twiceCrossLeProduct
    have oneLeGap :
        (1 : Coordinate) ≤
          1 + xNorm * yNorm - 2 * (a * c - b * d) := by
      calc
        (1 : Coordinate) = 1 + xNorm * yNorm - xNorm * yNorm := by ring1
        _ ≤ 1 + xNorm * yNorm - 2 * (a * c - b * d) :=
          RFAP.ConstructiveFraction.add_le_add_direct
            (le_refl (1 + xNorm * yNorm)) negated
    exact oneLeGap
  · exact oneLeGap_of_c_nonpositive (le_of_not_ge cNonnegative)

/-- The dyadic blue-region statement retained for the existing public
interface. -/
theorem firstRegionGapBound_le_gap_of_blueRegion
    (a b c d xNorm yNorm : Coordinate)
    (aNonnegative : 0 ≤ a)
    (bNonnegative : 0 ≤ b)
    (xNormIdentity : xNorm = a ^ 2 + b ^ 2)
    (yNormIdentity : yNorm = c ^ 2 + d ^ 2)
    (yNormLeOne : yNorm ≤ 1)
    (errorOppositeDiagonalObstruction : a - b ≤ xNorm)
    (denominatorRealObstruction : 2 * c ≤ yNorm)
    (blueRegion : yNorm + 1 < 2 * (c + d)) :
    firstRegionGapBound ≤
      1 + xNorm * yNorm - 2 * (a * c - b * d) :=
  firstRegionGapBound_le_one.trans
    (one_le_gap_of_blueRegion a b c d xNorm yNorm aNonnegative
      bNonnegative xNormIdentity yNormIdentity yNormLeOne
      errorOppositeDiagonalObstruction denominatorRealObstruction blueRegion)

/-- In the exterior region the denominator-side circle exclusions put its
positive projection in a narrow rational cone.  According to the signs of
`c,d`, the proof obtains either `8P²≤XY` or `7P²≤XY`; the latter sharp common
factor gives a gap of at least `6/7`. -/
theorem sixSevenths_le_gap_of_exteriorRegion
    (a b c d xNorm yNorm : Coordinate)
    (aNonnegative : 0 ≤ a)
    (bNonnegative : 0 ≤ b)
    (bLeA : b ≤ a)
    (xNormIdentity : xNorm = a ^ 2 + b ^ 2)
    (yNormIdentity : yNorm = c ^ 2 + d ^ 2)
    (yNormLeOne : yNorm ≤ 1)
    (denominatorRealObstruction : 2 * c ≤ yNorm)
    (denominatorImaginaryObstruction : -2 * d ≤ yNorm)
    (denominatorOppositeDiagonalObstruction :
      2 * (c + d) ≤ yNorm + 1) :
    (6 / 7 : Coordinate) ≤
      1 + xNorm * yNorm - 2 * (a * c - b * d) := by
  let cross : Coordinate := a * c - b * d
  let productNorm : Coordinate := xNorm * yNorm
  have xNormNonnegative : 0 ≤ xNorm := by
    rw [xNormIdentity]
    exact add_nonneg
      (RFAP.ConstructiveFraction.sq_nonneg_direct a)
      (RFAP.ConstructiveFraction.sq_nonneg_direct b)
  have yNormNonnegative : 0 ≤ yNorm := by
    rw [yNormIdentity]
    exact add_nonneg
      (RFAP.ConstructiveFraction.sq_nonneg_direct c)
      (RFAP.ConstructiveFraction.sq_nonneg_direct d)
  have productNormNonnegative : 0 ≤ productNorm :=
    RFAP.ConstructiveFraction.mul_nonneg_direct xNormNonnegative
      yNormNonnegative
  by_cases crossNonpositive : cross ≤ 0
  · calc
      (6 / 7 : Coordinate) ≤ 1 := by decide
      _ ≤ 1 + xNorm * yNorm - 2 * (a * c - b * d) := by
        simpa only [cross, productNorm] using
          one_le_gap_of_cross_nonpositive
            productNorm cross productNormNonnegative crossNonpositive
  · have crossPositive : 0 < cross := lt_of_not_ge crossNonpositive
    by_cases cNonnegative : 0 ≤ c
    · by_cases dNonnegative : 0 ≤ d
      · have cLeBoundary : c ≤ firstRegionSecondBoundary :=
          second_le_firstRegionBoundary_of_firstRegionObstructions
            d c yNorm dNonnegative (by
              rw [yNormIdentity]
              ring1) yNormLeOne denominatorRealObstruction
                (by
                  calc
                    2 * (d + c) = 2 * (c + d) := by ring1
                    _ ≤ yNorm + 1 :=
                      denominatorOppositeDiagonalObstruction)
        have sevenCLeOne : 7 * c ≤ 1 := by
          calc
            7 * c ≤ 7 * firstRegionSecondBoundary :=
              RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
                cLeBoundary (by decide)
            _ ≤ 1 := seven_mul_firstRegionSecondBoundary_le_one
        have sevenCSquareLeC : 7 * c ^ 2 ≤ c := by
          have scaled :=
            RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
              sevenCLeOne cNonnegative
          calc
            7 * c ^ 2 = (7 * c) * c := by ring1
            _ ≤ 1 * c := scaled
            _ = c := by ring1
        have cLeYNorm : c ≤ yNorm := by
          calc
            c ≤ 2 * c := by
              apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
              calc
                0 ≤ c := cNonnegative
                _ = 2 * c - c := by ring1
            _ ≤ yNorm := denominatorRealObstruction
        have sevenCSquareLeYNorm : 7 * c ^ 2 ≤ yNorm :=
          sevenCSquareLeC.trans cLeYNorm
        have aSquareLeXNorm : a ^ 2 ≤ xNorm := by
          rw [xNormIdentity]
          exact le_add_of_nonneg_right
            (RFAP.ConstructiveFraction.sq_nonneg_direct b)
        have minusBDNonpositive : -(b * d) ≤ 0 := by
          have productNonnegative :=
            RFAP.ConstructiveFraction.mul_nonneg_direct
              bNonnegative dNonnegative
          have negated := RFAP.ConstructiveFraction.neg_le_neg_direct
            productNonnegative
          simpa only [neg_zero] using negated
        have crossLeAC : cross ≤ a * c := by
          dsimp only [cross]
          calc
            a * c - b * d = a * c + -(b * d) := rfl
            _ ≤ a * c + 0 :=
              RFAP.ConstructiveFraction.add_le_add_direct le_rfl
                minusBDNonpositive
            _ = a * c := by ring1
        have crossSquareLeACSquare : cross ^ 2 ≤ (a * c) ^ 2 :=
          RFAP.ConstructiveFraction.pow_le_pow_direct crossPositive.le
            crossLeAC 2
        have sevenCrossSquareLeProductNorm :
            7 * cross ^ 2 ≤ productNorm := by
          calc
            7 * cross ^ 2 ≤ 7 * (a * c) ^ 2 :=
              RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
                crossSquareLeACSquare (by decide)
            _ = a ^ 2 * (7 * c ^ 2) := by ring1
            _ ≤ a ^ 2 * yNorm :=
              RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
                sevenCSquareLeYNorm
                (RFAP.ConstructiveFraction.sq_nonneg_direct a)
            _ ≤ xNorm * yNorm :=
              RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
                aSquareLeXNorm yNormNonnegative
            _ = productNorm := rfl
        simpa only [cross, productNorm] using
          sixSevenths_le_gap_of_seven_crossSquare
            productNorm cross sevenCrossSquareLeProductNorm
      · let e : Coordinate := -d
        have ePositive : 0 < e := by
          dsimp only [e]
          calc
            0 < 0 - d := RFAP.ConstructiveFraction.sub_pos_direct
              (lt_of_not_ge dNonnegative)
            _ = -d := by ring1
        have twiceELeYNorm : 2 * e ≤ yNorm := by
          dsimp only [e]
          calc
            2 * -d = -2 * d := by ring1
            _ ≤ yNorm := denominatorImaginaryObstruction
        have cPlusELeYNorm : c + e ≤ yNorm := by
          apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct (c := 2)
          · calc
              (c + e) * 2 = 2 * c + 2 * e := by ring1
              _ ≤ yNorm + yNorm :=
                RFAP.ConstructiveFraction.add_le_add_direct
                  denominatorRealObstruction twiceELeYNorm
              _ = yNorm * 2 := by ring1
          · decide
        have cLeOne : c ≤ 1 := by
          calc
            c ≤ 2 * c := by
              apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
              calc
                0 ≤ c := cNonnegative
                _ = 2 * c - c := by ring1
            _ ≤ yNorm := denominatorRealObstruction
            _ ≤ 1 := yNormLeOne
        have eLeHalf : e ≤ (1 / 2 : Coordinate) := by
          apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct (c := 2)
          · calc
              e * 2 = 2 * e := by ring1
              _ ≤ yNorm := twiceELeYNorm
              _ ≤ 1 := yNormLeOne
              _ = (1 / 2 : Coordinate) * 2 := by decide
          · decide
        have eLtOne : e < 1 :=
          eLeHalf.trans_lt (show (1 / 2 : Coordinate) < 1 by decide)
        have cSquareLeC : c ^ 2 ≤ c := by
          have scaled :=
            RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
              cLeOne cNonnegative
          calc
            c ^ 2 = c * c := by ring1
            _ ≤ c * 1 := scaled
            _ = c := by ring1
        have eSquareLtE : e ^ 2 < e := by
          have scaled :=
            RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
              ePositive eLtOne
          calc
            e ^ 2 = e * e := by ring1
            _ < e * 1 := scaled
            _ = e := by ring1
        have normLtSum : yNorm < c + e := by
          calc
            yNorm = c ^ 2 + e ^ 2 := by
              dsimp only [e]
              rw [yNormIdentity]
              ring1
            _ ≤ c + e ^ 2 :=
              RFAP.ConstructiveFraction.add_le_add_direct cSquareLeC le_rfl
            _ = e ^ 2 + c := by ring1
            _ < e + c :=
              RFAP.ConstructiveFraction.add_lt_add_right_direct eSquareLtE c
            _ = c + e := by ring1
        exact ((not_lt_of_ge cPlusELeYNorm) normLtSum).elim
    · have cNonpositive : c ≤ 0 := le_of_not_ge cNonnegative
      have acNonpositive : a * c ≤ 0 := by
        have scaled :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            cNonpositive aNonnegative
        simpa only [mul_zero] using scaled
      let e : Coordinate := -d
      have crossLeBE : cross ≤ b * e := by
        dsimp only [cross, e]
        calc
          a * c - b * d = a * c + b * (-d) := by ring1
          _ ≤ 0 + b * (-d) :=
            RFAP.ConstructiveFraction.add_le_add_direct acNonpositive le_rfl
          _ = b * (-d) := by ring1
      have bePositive : 0 < b * e := crossPositive.trans_le crossLeBE
      have ePositive : 0 < e :=
        RFAP.ConstructiveFraction.pos_of_mul_pos_right_direct
          bePositive bNonnegative
      have twiceELeYNorm : 2 * e ≤ yNorm := by
        dsimp only [e]
        calc
          2 * -d = -2 * d := by ring1
          _ ≤ yNorm := denominatorImaginaryObstruction
      have bSquareLeASquare : b ^ 2 ≤ a ^ 2 :=
        RFAP.ConstructiveFraction.pow_le_pow_direct bNonnegative bLeA 2
      have twiceBSquareLeXNorm : 2 * b ^ 2 ≤ xNorm := by
        calc
          2 * b ^ 2 = b ^ 2 + b ^ 2 := by ring1
          _ ≤ a ^ 2 + b ^ 2 :=
            RFAP.ConstructiveFraction.add_le_add_direct
              bSquareLeASquare le_rfl
          _ = xNorm := xNormIdentity.symm
      have fourESquareLeYNormSquare : 4 * e ^ 2 ≤ yNorm ^ 2 := by
        have squared := RFAP.ConstructiveFraction.pow_le_pow_direct
          (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
            ePositive.le) twiceELeYNorm 2
        calc
          4 * e ^ 2 = (2 * e) ^ 2 := by ring1
          _ ≤ yNorm ^ 2 := squared
      have yNormSquareLeYNorm : yNorm ^ 2 ≤ yNorm := by
        have scaled :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            yNormLeOne yNormNonnegative
        calc
          yNorm ^ 2 = yNorm * yNorm := by ring1
          _ ≤ yNorm * 1 := scaled
          _ = yNorm := by ring1
      have crossSquareLeBESquare : cross ^ 2 ≤ (b * e) ^ 2 :=
        RFAP.ConstructiveFraction.pow_le_pow_direct crossPositive.le
          crossLeBE 2
      have eightCrossSquareLeProductNorm :
          8 * cross ^ 2 ≤ productNorm := by
        calc
          8 * cross ^ 2 ≤ 8 * (b * e) ^ 2 :=
            RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
              crossSquareLeBESquare (by decide)
          _ = (2 * b ^ 2) * (4 * e ^ 2) := by ring1
          _ ≤ xNorm * (4 * e ^ 2) :=
            RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
              twiceBSquareLeXNorm
              (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
                (RFAP.ConstructiveFraction.sq_nonneg_direct e))
          _ ≤ xNorm * yNorm ^ 2 :=
            RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
              fourESquareLeYNormSquare xNormNonnegative
          _ ≤ xNorm * yNorm :=
            RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
              yNormSquareLeYNorm xNormNonnegative
          _ = productNorm := rfl
      have sevenCrossSquareLeProductNorm :
          7 * cross ^ 2 ≤ productNorm := by
        calc
          7 * cross ^ 2 ≤ 8 * cross ^ 2 :=
            RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
              (show (7 : Coordinate) ≤ 8 by decide)
              (RFAP.ConstructiveFraction.sq_nonneg_direct cross)
          _ ≤ productNorm := eightCrossSquareLeProductNorm
      simpa only [cross, productNorm] using
        sixSevenths_le_gap_of_seven_crossSquare
          productNorm cross sevenCrossSquareLeProductNorm

/-- The dyadic exterior-region statement retained for the existing public
interface. -/
theorem firstRegionGapBound_le_gap_of_exteriorRegion
    (a b c d xNorm yNorm : Coordinate)
    (aNonnegative : 0 ≤ a)
    (bNonnegative : 0 ≤ b)
    (bLeA : b ≤ a)
    (xNormIdentity : xNorm = a ^ 2 + b ^ 2)
    (yNormIdentity : yNorm = c ^ 2 + d ^ 2)
    (yNormLeOne : yNorm ≤ 1)
    (denominatorRealObstruction : 2 * c ≤ yNorm)
    (denominatorImaginaryObstruction : -2 * d ≤ yNorm)
    (denominatorOppositeDiagonalObstruction :
      2 * (c + d) ≤ yNorm + 1) :
    firstRegionGapBound ≤
      1 + xNorm * yNorm - 2 * (a * c - b * d) := by
  calc
    firstRegionGapBound ≤ (6 / 7 : Coordinate) := by
      unfold firstRegionGapBound firstRegionProjectionBound
        firstRegionProjectionBoundFraction
      decide
    _ ≤ 1 + xNorm * yNorm - 2 * (a * c - b * d) :=
      sixSevenths_le_gap_of_exteriorRegion
        a b c d xNorm yNorm aNonnegative bNonnegative bLeA
        xNormIdentity yNormIdentity yNormLeOne denominatorRealObstruction
        denominatorImaginaryObstruction denominatorOppositeDiagonalObstruction

/-- The five displayed coefficient exclusions cover the whole normalized
first octant.  The finite four-way split dispatches to the green, red,
exterior, and blue certificates above. -/
theorem firstRegionGapBound_le_gap_of_firstOctantFiveObstructions
    (a b c d xNorm yNorm : Coordinate)
    (aNonnegative : 0 ≤ a)
    (bNonnegative : 0 ≤ b)
    (bLeA : b ≤ a)
    (xNormIdentity : xNorm = a ^ 2 + b ^ 2)
    (yNormIdentity : yNorm = c ^ 2 + d ^ 2)
    (xNormLeOne : xNorm ≤ 1)
    (yNormLeOne : yNorm ≤ 1)
    (denominatorOne : 2 * c ≤ yNorm)
    (denominatorOneMinusI : 2 * (c - d) ≤ yNorm + 1)
    (imaginaryObstruction :
      2 * b ≤ xNorm ∨ -2 * d ≤ yNorm)
    (diagonalObstruction :
      2 * (a + b) ≤ xNorm + 1 ∨ c - d ≤ yNorm)
    (oppositeDiagonalObstruction :
      a - b ≤ xNorm ∨ 2 * (c + d) ≤ yNorm + 1) :
    firstRegionGapBound ≤
      1 + xNorm * yNorm - 2 * (a * c - b * d) := by
  rcases (fourRegionSplit_of_fiveCoefficientObstructions
      a b c d xNorm yNorm denominatorOne denominatorOneMinusI
        imaginaryObstruction diagonalObstruction
        oppositeDiagonalObstruction).2 with
    green | redOrExteriorOrBlue
  · exact firstRegionGapBound_le_gap_of_greenRegion
      a b c d xNorm yNorm aNonnegative bNonnegative bLeA
        xNormIdentity yNormIdentity xNormLeOne yNormLeOne green.2.1
        green.2.2 denominatorOne denominatorOneMinusI green.1
  · rcases redOrExteriorOrBlue with red | exteriorOrBlue
    · exact firstRegionGapBound_le_gap_of_redRegion
        a b c d xNorm yNorm bNonnegative bLeA xNormIdentity
          yNormIdentity yNormLeOne red.2.2 red.1 red.2.1
    · rcases exteriorOrBlue with exterior | blue
      · exact firstRegionGapBound_le_gap_of_exteriorRegion
          a b c d xNorm yNorm aNonnegative bNonnegative bLeA
            xNormIdentity yNormIdentity yNormLeOne denominatorOne
            exterior.1 exterior.2
      · exact firstRegionGapBound_le_gap_of_blueRegion
          a b c d xNorm yNorm aNonnegative bNonnegative xNormIdentity
            yNormIdentity yNormLeOne blue.2 denominatorOne blue.1

/-- Two first-region vectors have a root-free sixty-degree separation:
if `T = ac+be`, then `4T² ≤ UV`.  The proof is the homogeneous polynomial
certificate obtained by combining the two slope quadratics. -/
theorem four_crossSquare_le_normProduct_of_slopeQuadratics
    (a b e c xNorm yNorm : Coordinate)
    (aNonnegative : 0 ≤ a)
    (bNonnegative : 0 ≤ b)
    (eNonnegative : 0 ≤ e)
    (cNonnegative : 0 ≤ c)
    (bLeA : b ≤ a)
    (cLeE : c ≤ e)
    (xNormIdentity : xNorm = a ^ 2 + b ^ 2)
    (yNormIdentity : yNorm = e ^ 2 + c ^ 2)
    (firstSlopeQuadratic : 0 ≤ xNorm - 4 * a * b)
    (secondSlopeQuadratic : 0 ≤ yNorm - 4 * e * c)
    (twiceBLeA : 2 * b ≤ a)
    (twiceCLeE : 2 * c ≤ e) :
    4 * (a * c + b * e) ^ 2 ≤ xNorm * yNorm := by
  let cross := a * c + b * e
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
  by_cases aZero : a = 0
  · have bZero : b = 0 := by
      apply le_antisymm
      · simpa only [aZero] using bLeA
      · exact bNonnegative
    rw [aZero, bZero]
    simp only [zero_mul, zero_add]
    exact RFAP.ConstructiveFraction.mul_nonneg_direct xNormNonnegative
      yNormNonnegative
  · by_cases eZero : e = 0
    · have cZero : c = 0 := by
        apply le_antisymm
        · simpa only [eZero] using cLeE
        · exact cNonnegative
      rw [eZero, cZero]
      simp only [mul_zero, add_zero]
      exact RFAP.ConstructiveFraction.mul_nonneg_direct xNormNonnegative
        yNormNonnegative
    · have aPositive : 0 < a :=
        lt_of_le_of_ne aNonnegative (Ne.symm aZero)
      have ePositive : 0 < e :=
        lt_of_le_of_ne eNonnegative (Ne.symm eZero)
      have aePositive : 0 < a * e :=
        RFAP.ConstructiveFraction.mul_pos_direct aPositive ePositive
      have crossNonnegative : 0 ≤ cross := by
        dsimp only [cross]
        exact add_nonneg
          (RFAP.ConstructiveFraction.mul_nonneg_direct aNonnegative
            cNonnegative)
          (RFAP.ConstructiveFraction.mul_nonneg_direct bNonnegative
            eNonnegative)
      have twiceBELt : 2 * b * e ≤ a * e := by
        have scaled :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
            twiceBLeA eNonnegative
        simpa only [mul_assoc] using scaled
      have twiceACLe : 2 * a * c ≤ a * e := by
        have scaled :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            twiceCLeE aNonnegative
        calc
          2 * a * c = a * (2 * c) := by ring1
          _ ≤ a * e := scaled
      have twiceCrossLeTwiceAE : 2 * cross ≤ 2 * (a * e) := by
        have added := RFAP.ConstructiveFraction.add_le_add_direct
          twiceACLe twiceBELt
        calc
          2 * cross = 2 * a * c + 2 * b * e := by
            dsimp only [cross]
            ring1
          _ ≤ a * e + a * e := added
          _ = 2 * (a * e) := by ring1
      have crossLeAE : cross ≤ a * e := by
        apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct (c := 2)
        · calc
            cross * 2 = 2 * cross := by ring1
            _ ≤ 2 * (a * e) := twiceCrossLeTwiceAE
            _ = (a * e) * 2 := by ring1
        · decide
      have aeMinusCrossNonnegative : 0 ≤ a * e - cross :=
        RFAP.ConstructiveFraction.sub_nonneg_direct crossLeAE
      have firstMultiplierNonnegative :
          0 ≤ 3 * a * e ^ 3 + 8 * b * e ^ 3 +
            4 * a * c * e ^ 2 + 3 * a * c ^ 2 * e := by
        repeat apply add_nonneg
        · exact RFAP.ConstructiveFraction.mul_nonneg_direct
            (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
              aNonnegative)
            (RFAP.ConstructiveFraction.pow_nonneg_direct eNonnegative 3)
        · exact RFAP.ConstructiveFraction.mul_nonneg_direct
            (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
              bNonnegative)
            (RFAP.ConstructiveFraction.pow_nonneg_direct eNonnegative 3)
        · exact RFAP.ConstructiveFraction.mul_nonneg_direct
            (RFAP.ConstructiveFraction.mul_nonneg_direct
              (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
                aNonnegative) cNonnegative)
            (RFAP.ConstructiveFraction.pow_nonneg_direct eNonnegative 2)
        · exact RFAP.ConstructiveFraction.mul_nonneg_direct
            (RFAP.ConstructiveFraction.mul_nonneg_direct
              (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
                aNonnegative)
              (RFAP.ConstructiveFraction.pow_nonneg_direct cNonnegative 2))
            eNonnegative
      have secondMultiplierNonnegative :
          0 ≤ 3 * e * a ^ 3 + 8 * c * a ^ 3 +
            4 * e * b * a ^ 2 + 3 * e * b ^ 2 * a := by
        repeat apply add_nonneg
        · exact RFAP.ConstructiveFraction.mul_nonneg_direct
            (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
              eNonnegative)
            (RFAP.ConstructiveFraction.pow_nonneg_direct aNonnegative 3)
        · exact RFAP.ConstructiveFraction.mul_nonneg_direct
            (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
              cNonnegative)
            (RFAP.ConstructiveFraction.pow_nonneg_direct aNonnegative 3)
        · exact RFAP.ConstructiveFraction.mul_nonneg_direct
            (RFAP.ConstructiveFraction.mul_nonneg_direct
              (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
                eNonnegative) bNonnegative)
            (RFAP.ConstructiveFraction.pow_nonneg_direct aNonnegative 2)
        · exact RFAP.ConstructiveFraction.mul_nonneg_direct
            (RFAP.ConstructiveFraction.mul_nonneg_direct
              (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
                eNonnegative)
              (RFAP.ConstructiveFraction.pow_nonneg_direct bNonnegative 2))
            aNonnegative
      have certificateNonnegative :
          0 ≤
            (3 * a * e ^ 3 + 8 * b * e ^ 3 +
                4 * a * c * e ^ 2 + 3 * a * c ^ 2 * e) *
                (xNorm - 4 * a * b) +
              (3 * e * a ^ 3 + 8 * c * a ^ 3 +
                4 * e * b * a ^ 2 + 3 * e * b ^ 2 * a) *
                (yNorm - 4 * e * c) +
              8 * (a * e - cross) * (b * e - a * c) ^ 2 := by
        repeat apply add_nonneg
        · exact RFAP.ConstructiveFraction.mul_nonneg_direct
            firstMultiplierNonnegative firstSlopeQuadratic
        · exact RFAP.ConstructiveFraction.mul_nonneg_direct
            secondMultiplierNonnegative secondSlopeQuadratic
        · exact RFAP.ConstructiveFraction.mul_nonneg_direct
            (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
              aeMinusCrossNonnegative)
            (RFAP.ConstructiveFraction.sq_nonneg_direct _)
      have scaledDifferenceNonnegative :
          0 ≤ 6 * (a * e) *
            (xNorm * yNorm - 4 * cross ^ 2) := by
        calc
          0 ≤
              (3 * a * e ^ 3 + 8 * b * e ^ 3 +
                  4 * a * c * e ^ 2 + 3 * a * c ^ 2 * e) *
                  (xNorm - 4 * a * b) +
                (3 * e * a ^ 3 + 8 * c * a ^ 3 +
                  4 * e * b * a ^ 2 + 3 * e * b ^ 2 * a) *
                  (yNorm - 4 * e * c) +
                8 * (a * e - cross) * (b * e - a * c) ^ 2 :=
            certificateNonnegative
          _ = 6 * (a * e) *
              (xNorm * yNorm - 4 * cross ^ 2) := by
            rw [xNormIdentity, yNormIdentity]
            dsimp only [cross]
            ring1
      have sixAEPositive : 0 < 6 * (a * e) :=
        RFAP.ConstructiveFraction.mul_pos_direct (by decide) aePositive
      have differenceNonnegative :
          0 ≤ xNorm * yNorm - 4 * cross ^ 2 := by
        apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct
          (c := 6 * (a * e))
        · calc
            0 * (6 * (a * e)) = 0 := by ring1
            _ ≤ 6 * (a * e) *
                (xNorm * yNorm - 4 * cross ^ 2) :=
              scaledDifferenceNonnegative
            _ = (xNorm * yNorm - 4 * cross ^ 2) *
                (6 * (a * e)) := by ring1
        · exact sixAEPositive
      exact RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
        differenceNonnegative

/-- Packaged first-region consequence: the four displayed circle exclusions
alone imply the homogeneous sixty-degree separation certificate. -/
theorem four_crossSquare_le_normProduct_of_firstRegionObstructions
    (a b e c xNorm yNorm : Coordinate)
    (aNonnegative : 0 ≤ a)
    (bNonnegative : 0 ≤ b)
    (eNonnegative : 0 ≤ e)
    (cNonnegative : 0 ≤ c)
    (bLeA : b ≤ a)
    (cLeE : c ≤ e)
    (xNormIdentity : xNorm = a ^ 2 + b ^ 2)
    (yNormIdentity : yNorm = e ^ 2 + c ^ 2)
    (xNormLeOne : xNorm ≤ 1)
    (yNormLeOne : yNorm ≤ 1)
    (firstImaginaryObstruction : 2 * b ≤ xNorm)
    (firstDiagonalObstruction : 2 * (a + b) ≤ xNorm + 1)
    (secondImaginaryObstruction : 2 * c ≤ yNorm)
    (secondDiagonalObstruction : 2 * (e + c) ≤ yNorm + 1) :
    4 * (a * c + b * e) ^ 2 ≤ xNorm * yNorm := by
  have firstSlope :=
    slopeQuadratic_nonnegative_of_firstRegionObstructions
      a b xNorm aNonnegative bNonnegative bLeA xNormIdentity xNormLeOne
      firstImaginaryObstruction firstDiagonalObstruction
  have secondSlope :=
    slopeQuadratic_nonnegative_of_firstRegionObstructions
      e c yNorm eNonnegative cNonnegative cLeE yNormIdentity yNormLeOne
      secondImaginaryObstruction secondDiagonalObstruction
  have twiceBLeA := twice_second_le_first_of_slopeQuadratic
    a b xNorm aNonnegative bLeA xNormIdentity firstSlope
  have twiceCLeE := twice_second_le_first_of_slopeQuadratic
    e c yNorm eNonnegative cLeE yNormIdentity secondSlope
  exact four_crossSquare_le_normProduct_of_slopeQuadratics
    a b e c xNorm yNorm aNonnegative bNonnegative eNonnegative cNonnegative
    bLeA cLeE xNormIdentity yNormIdentity firstSlope secondSlope twiceBLeA
    twiceCLeE

end RFAP.SharpIndexOneWindow
