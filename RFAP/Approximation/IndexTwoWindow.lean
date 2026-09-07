import mathlib.Tactic.QuotientFreeRing
import RFAP.Approximation.DirichletWindow
import RFAP.Approximation.RepeatedIndex

/-!
# Index-two Dirichlet-window geometry

The centered coefficient coset available when two consecutive best pairs have
determinant quadrance two supplies four explicit unit candidates.  The
opposite-unit alternatives force the real projections of the normalized error
and denominator ratios to have opposite signs, while their imaginary
projections have the same sign.  This file turns those finite alternatives
into the rational gap bound needed for a substantially smaller window
constant.
-/

namespace RFAP.IndexTwoWindow

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianInt := RFAP.ConstructiveGaussianHeight.GaussianInt
abbrev Pair := RFAP.HurwitzRational.ConvergentPair

open RFAP.ConstructiveGaussian.Gaussian
open RFAP.ConstructiveGaussianHeight.GaussianInt
open RFAP.BestApproximation
open RFAP.DirichletWindow
open RFAP.HurwitzApproximation

/-- The two complementary products of the normalized error and denominator
quadrances. -/
def balancedNormProduct (errorRatio denominatorRatio : Gaussian) : Coordinate :=
  normSq errorRatio * normSq denominatorRatio +
    (1 - normSq errorRatio) * (1 - normSq denominatorRatio)

private def centeredNormThresholdFraction :
    RFAP.ConstructiveFraction.Fraction :=
  { num := 15, den := 56, den_pos := by decide }

/-- The displayed rational point `15/56`, chosen just below
`2 - sqrt(3)` without introducing that completed value. -/
def centeredNormThreshold : Coordinate :=
  RFAP.ConstructiveFraction.ofFraction centeredNormThresholdFraction

private def centeredGapThresholdFraction :
    RFAP.ConstructiveFraction.Fraction :=
  { num := 71, den := 56, den_pos := by decide }

/-- The resulting displayed determinant-gap threshold `71/56`. -/
def centeredGapThreshold : Coordinate :=
  RFAP.ConstructiveFraction.ofFraction centeredGapThresholdFraction

private def centeredWindowBoundFraction :
    RFAP.ConstructiveFraction.Fraction :=
  { num := 112, den := 71, den_pos := by decide }

/-- The index-two window bound `112/71` obtained by dividing the exact
coefficient index two by `71/56`. -/
def centeredWindowBound : Coordinate :=
  RFAP.ConstructiveFraction.ofFraction centeredWindowBoundFraction

private def dyadicCenteredGapThresholdFraction :
    RFAP.ConstructiveFraction.Fraction :=
  { num := 13 * 16 - 3, den := 2 ^ 7, den_pos := by decide }

/-- The strengthened index-two gap `205/128`.  Its reciprocal index factor
matches the dyadic index-one window without naming the optimal algebraic
boundary. -/
def dyadicCenteredGapThreshold : Coordinate :=
  RFAP.ConstructiveFraction.ofFraction dyadicCenteredGapThresholdFraction

private def dyadicCenteredWindowBoundFraction :
    RFAP.ConstructiveFraction.Fraction :=
  { num := 2 ^ 8, den := 13 * 16 - 3, den_pos := by decide }

/-- The corresponding index-two squared-window bound `256/205`. -/
def dyadicCenteredWindowBound : Coordinate :=
  RFAP.ConstructiveFraction.ofFraction dyadicCenteredWindowBoundFraction

private def dyadicCenteredExcessThresholdFraction :
    RFAP.ConstructiveFraction.Fraction :=
  { num := 9 * 8 + 5, den := 2 ^ 7, den_pos := by decide }

/-- The amount `77/128` by which the strengthened gap exceeds one. -/
def dyadicCenteredExcessThreshold : Coordinate :=
  RFAP.ConstructiveFraction.ofFraction
    dyadicCenteredExcessThresholdFraction

theorem dyadicCenteredGapThreshold_eq_one_add_excess :
    dyadicCenteredGapThreshold = 1 + dyadicCenteredExcessThreshold := by
  unfold dyadicCenteredGapThreshold dyadicCenteredGapThresholdFraction
    dyadicCenteredExcessThreshold dyadicCenteredExcessThresholdFraction
  rw [show (1 : Coordinate) =
        RFAP.ConstructiveFraction.ofFraction ⟨1, 1, by decide⟩ from
      RFAP.ConstructiveFraction.natCast_eq_fraction 1,
    RFAP.ConstructiveFraction.ofFraction_addFraction]
  apply RFAP.ConstructiveFraction.ofFraction_eq_of_equivalent
  change
    ((13 * 16 - 3 : Nat) : Int) *
        (1 * ((2 ^ 7 : Nat) : Int)) =
      (1 * ((2 ^ 7 : Nat) : Int) +
          ((9 * 8 + 5 : Nat) : Int) * 1) *
        ((2 ^ 7 : Nat) : Int)
  ring1

theorem dyadicCenteredWindowBound_mul_gapThreshold :
    dyadicCenteredWindowBound * dyadicCenteredGapThreshold = 2 := by
  unfold dyadicCenteredWindowBound dyadicCenteredWindowBoundFraction
    dyadicCenteredGapThreshold dyadicCenteredGapThresholdFraction
  rw [RFAP.ConstructiveFraction.ofFraction_mulFraction]
  calc
    _ = RFAP.ConstructiveFraction.ofFraction ⟨2, 1, by decide⟩ := by
      apply RFAP.ConstructiveFraction.ofFraction_eq_of_equivalent
      change
        (((2 ^ 8 : Nat) : Int) * ((13 * 16 - 3 : Nat) : Int)) * 1 =
          2 * (((13 * 16 - 3 : Nat) : Int) * ((2 ^ 7 : Nat) : Int))
      ring1
    _ = 2 := (RFAP.ConstructiveFraction.natCast_eq_fraction 2).symm

theorem dyadicCenteredGapThreshold_pos :
    (0 : Coordinate) < dyadicCenteredGapThreshold := by
  unfold dyadicCenteredGapThreshold dyadicCenteredGapThresholdFraction
  change
    RFAP.ConstructiveFraction.LessEqFraction
        RFAP.ConstructiveFraction.zeroFraction
        ⟨13 * 16 - 3, 2 ^ 7, by decide⟩ ∧
      ¬RFAP.ConstructiveFraction.LessEqFraction
        ⟨13 * 16 - 3, 2 ^ 7, by decide⟩
        RFAP.ConstructiveFraction.zeroFraction
  decide

theorem centeredNormThreshold_mul_denominator :
    centeredNormThreshold * 56 = 15 := by
  unfold centeredNormThreshold centeredNormThresholdFraction
  have clearance := RFAP.ConstructiveFraction.ofFraction_mul_den
    ({ num := 15, den := 56, den_pos := by decide } :
      RFAP.ConstructiveFraction.Fraction)
  simpa only [Int.cast_ofNat] using clearance

theorem centeredGapThreshold_mul_denominator :
    centeredGapThreshold * 56 = 71 := by
  unfold centeredGapThreshold centeredGapThresholdFraction
  have clearance := RFAP.ConstructiveFraction.ofFraction_mul_den
    ({ num := 71, den := 56, den_pos := by decide } :
      RFAP.ConstructiveFraction.Fraction)
  simpa only [Int.cast_ofNat] using clearance

theorem centeredWindowBound_mul_denominator :
    centeredWindowBound * 71 = 112 := by
  unfold centeredWindowBound centeredWindowBoundFraction
  have clearance := RFAP.ConstructiveFraction.ofFraction_mul_den
    ({ num := 112, den := 71, den_pos := by decide } :
      RFAP.ConstructiveFraction.Fraction)
  simpa only [Int.cast_ofNat] using clearance

private theorem error_one_projection
    (value : Gaussian)
    (outside : (2 : Coordinate) ≤
      normSq (value - toGaussian (1 : GaussianInt))) :
    1 - normSq value ≤ -2 * value.re := by
  apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
  calc
    0 ≤ normSq (value - toGaussian (1 : GaussianInt)) - 2 :=
      RFAP.ConstructiveFraction.sub_nonneg_direct outside
    _ = (-2 * value.re) - (1 - normSq value) := by
      dsimp only [normSq, toGaussian]
      simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
        RFAP.ConstructiveGaussian.Gaussian.sub_im,
        RFAP.ConstructiveGaussianHeight.GaussianInt.one_re,
        RFAP.ConstructiveGaussianHeight.GaussianInt.one_im,
        Int.cast_one, Int.cast_zero]
      ring1

private theorem error_negOne_projection
    (value : Gaussian)
    (outside : (2 : Coordinate) ≤
      normSq (value - toGaussian (-1 : GaussianInt))) :
    1 - normSq value ≤ 2 * value.re := by
  apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
  calc
    0 ≤ normSq (value - toGaussian (-1 : GaussianInt)) - 2 :=
      RFAP.ConstructiveFraction.sub_nonneg_direct outside
    _ = 2 * value.re - (1 - normSq value) := by
      dsimp only [normSq, toGaussian]
      simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
        RFAP.ConstructiveGaussian.Gaussian.sub_im,
        RFAP.ConstructiveGaussianHeight.GaussianInt.neg_re,
        RFAP.ConstructiveGaussianHeight.GaussianInt.neg_im,
        RFAP.ConstructiveGaussianHeight.GaussianInt.one_re,
        RFAP.ConstructiveGaussianHeight.GaussianInt.one_im,
        Int.cast_neg, Int.cast_one, Int.cast_zero]
      ring1

private theorem denominator_one_projection
    (value : Gaussian)
    (outside : (2 : Coordinate) ≤
      normSq (1 - toGaussian (1 : GaussianInt) * value)) :
    1 - normSq value ≤ -2 * value.re := by
  apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
  calc
    0 ≤ normSq (1 - toGaussian (1 : GaussianInt) * value) - 2 :=
      RFAP.ConstructiveFraction.sub_nonneg_direct outside
    _ = (-2 * value.re) - (1 - normSq value) := by
      dsimp only [normSq, toGaussian]
      simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
        RFAP.ConstructiveGaussian.Gaussian.sub_im,
        RFAP.ConstructiveGaussian.Gaussian.mul_re,
        RFAP.ConstructiveGaussian.Gaussian.mul_im,
        RFAP.ConstructiveGaussian.Gaussian.one_re,
        RFAP.ConstructiveGaussian.Gaussian.one_im,
        RFAP.ConstructiveGaussianHeight.GaussianInt.one_re,
        RFAP.ConstructiveGaussianHeight.GaussianInt.one_im,
        Int.cast_one, Int.cast_zero]
      ring1

private theorem denominator_negOne_projection
    (value : Gaussian)
    (outside : (2 : Coordinate) ≤
      normSq (1 - toGaussian (-1 : GaussianInt) * value)) :
    1 - normSq value ≤ 2 * value.re := by
  apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
  calc
    0 ≤ normSq (1 - toGaussian (-1 : GaussianInt) * value) - 2 :=
      RFAP.ConstructiveFraction.sub_nonneg_direct outside
    _ = 2 * value.re - (1 - normSq value) := by
      dsimp only [normSq, toGaussian]
      simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
        RFAP.ConstructiveGaussian.Gaussian.sub_im,
        RFAP.ConstructiveGaussian.Gaussian.mul_re,
        RFAP.ConstructiveGaussian.Gaussian.mul_im,
        RFAP.ConstructiveGaussian.Gaussian.one_re,
        RFAP.ConstructiveGaussian.Gaussian.one_im,
        RFAP.ConstructiveGaussianHeight.GaussianInt.neg_re,
        RFAP.ConstructiveGaussianHeight.GaussianInt.neg_im,
        RFAP.ConstructiveGaussianHeight.GaussianInt.one_re,
        RFAP.ConstructiveGaussianHeight.GaussianInt.one_im,
        Int.cast_neg, Int.cast_one, Int.cast_zero]
      ring1

private theorem error_imaginary_projection
    (value : Gaussian)
    (outside : (2 : Coordinate) ≤ normSq
      (value - toGaussian RFAP.HurwitzGeometry.imaginaryUnit)) :
    1 - normSq value ≤ -2 * value.im := by
  apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
  calc
    0 ≤ normSq
        (value - toGaussian RFAP.HurwitzGeometry.imaginaryUnit) - 2 :=
      RFAP.ConstructiveFraction.sub_nonneg_direct outside
    _ = (-2 * value.im) - (1 - normSq value) := by
      dsimp only [normSq, toGaussian, RFAP.HurwitzGeometry.imaginaryUnit]
      simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
        RFAP.ConstructiveGaussian.Gaussian.sub_im, Int.cast_one,
        Int.cast_zero]
      ring1

private theorem error_negImaginary_projection
    (value : Gaussian)
    (outside : (2 : Coordinate) ≤ normSq
      (value - toGaussian (-RFAP.HurwitzGeometry.imaginaryUnit))) :
    1 - normSq value ≤ 2 * value.im := by
  apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
  calc
    0 ≤ normSq
        (value - toGaussian (-RFAP.HurwitzGeometry.imaginaryUnit)) - 2 :=
      RFAP.ConstructiveFraction.sub_nonneg_direct outside
    _ = 2 * value.im - (1 - normSq value) := by
      dsimp only [normSq, toGaussian, RFAP.HurwitzGeometry.imaginaryUnit]
      simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
        RFAP.ConstructiveGaussian.Gaussian.sub_im,
        RFAP.ConstructiveGaussianHeight.GaussianInt.neg_re,
        RFAP.ConstructiveGaussianHeight.GaussianInt.neg_im,
        Int.cast_neg, Int.cast_one, Int.cast_zero]
      ring1

private theorem denominator_imaginary_projection
    (value : Gaussian)
    (outside : (2 : Coordinate) ≤ normSq
      (1 - toGaussian RFAP.HurwitzGeometry.imaginaryUnit * value)) :
    1 - normSq value ≤ 2 * value.im := by
  apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
  calc
    0 ≤ normSq
        (1 - toGaussian RFAP.HurwitzGeometry.imaginaryUnit * value) - 2 :=
      RFAP.ConstructiveFraction.sub_nonneg_direct outside
    _ = 2 * value.im - (1 - normSq value) := by
      dsimp only [normSq, toGaussian, RFAP.HurwitzGeometry.imaginaryUnit]
      simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
        RFAP.ConstructiveGaussian.Gaussian.sub_im,
        RFAP.ConstructiveGaussian.Gaussian.mul_re,
        RFAP.ConstructiveGaussian.Gaussian.mul_im,
        RFAP.ConstructiveGaussian.Gaussian.one_re,
        RFAP.ConstructiveGaussian.Gaussian.one_im, Int.cast_one,
        Int.cast_zero]
      ring1

private theorem denominator_negImaginary_projection
    (value : Gaussian)
    (outside : (2 : Coordinate) ≤ normSq
      (1 - toGaussian (-RFAP.HurwitzGeometry.imaginaryUnit) * value)) :
    1 - normSq value ≤ -2 * value.im := by
  apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
  calc
    0 ≤ normSq
        (1 - toGaussian (-RFAP.HurwitzGeometry.imaginaryUnit) * value) - 2 :=
      RFAP.ConstructiveFraction.sub_nonneg_direct outside
    _ = (-2 * value.im) - (1 - normSq value) := by
      dsimp only [normSq, toGaussian, RFAP.HurwitzGeometry.imaginaryUnit]
      simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
        RFAP.ConstructiveGaussian.Gaussian.sub_im,
        RFAP.ConstructiveGaussian.Gaussian.mul_re,
        RFAP.ConstructiveGaussian.Gaussian.mul_im,
        RFAP.ConstructiveGaussian.Gaussian.one_re,
        RFAP.ConstructiveGaussian.Gaussian.one_im,
        RFAP.ConstructiveGaussianHeight.GaussianInt.neg_re,
        RFAP.ConstructiveGaussianHeight.GaussianInt.neg_im,
        Int.cast_neg, Int.cast_one, Int.cast_zero]
      ring1

/-- The four centered-unit alternatives cross in both coordinate directions.
The displayed disjunctions retain which error exterior is paired with which
denominator exterior; no selection from an unbounded set is involved. -/
private theorem centeredUnit_projectionCrosses
    (errorRatio denominatorRatio : Gaussian)
    (errorInside : normSq errorRatio < 1)
    (denominatorInside : normSq denominatorRatio < 1)
    (obstruction : ∀ unit : GaussianInt, normNat unit = 1 →
      (2 : Coordinate) ≤ normSq (errorRatio - toGaussian unit) ∨
        2 ≤ normSq (1 - toGaussian unit * denominatorRatio)) :
    (((1 - normSq errorRatio ≤ -2 * errorRatio.re ∧
          1 - normSq denominatorRatio ≤ 2 * denominatorRatio.re) ∨
        (1 - normSq denominatorRatio ≤ -2 * denominatorRatio.re ∧
          1 - normSq errorRatio ≤ 2 * errorRatio.re)) ∧
      ((1 - normSq errorRatio ≤ -2 * errorRatio.im ∧
          1 - normSq denominatorRatio ≤ -2 * denominatorRatio.im) ∨
        (1 - normSq denominatorRatio ≤ 2 * denominatorRatio.im ∧
          1 - normSq errorRatio ≤ 2 * errorRatio.im))) := by
  have realCross := RFAP.RepeatedIndex.opposite_self_obstructions_cross
    errorRatio denominatorRatio errorInside denominatorInside 1 rfl
      (obstruction 1 rfl) (obstruction (-1) (by decide))
  have imaginaryCross :=
    RFAP.RepeatedIndex.opposite_self_obstructions_cross
      errorRatio denominatorRatio errorInside denominatorInside
        RFAP.HurwitzGeometry.imaginaryUnit (by decide)
        (obstruction RFAP.HurwitzGeometry.imaginaryUnit (by decide))
        (obstruction (-RFAP.HurwitzGeometry.imaginaryUnit) (by decide))
  constructor
  · rcases realCross with cross | cross
    · exact Or.inl ⟨error_one_projection errorRatio cross.1,
        denominator_negOne_projection denominatorRatio cross.2⟩
    · exact Or.inr ⟨denominator_one_projection denominatorRatio cross.1,
        error_negOne_projection errorRatio cross.2⟩
  · rcases imaginaryCross with cross | cross
    · exact Or.inl ⟨error_imaginary_projection errorRatio cross.1,
        denominator_negImaginary_projection denominatorRatio cross.2⟩
    · exact Or.inr ⟨denominator_imaginary_projection denominatorRatio cross.1,
        error_negImaginary_projection errorRatio cross.2⟩

/-- Once the error ratio is in the closed first octant, the four centered
unit alternatives have a forced orientation.  The error ratio lies outside
the circle centred at `-i`, while the denominator ratio lies outside the
circles centred at `1` and `-i`; these are recorded only as rational
projection inequalities. -/
theorem firstOctant_projectionBounds_of_centeredUnitObstructions
    (errorRatio denominatorRatio : Gaussian)
    (realNonnegative : 0 ≤ errorRatio.re)
    (imaginaryNonnegative : 0 ≤ errorRatio.im)
    (errorInside : normSq errorRatio < 1)
    (denominatorInside : normSq denominatorRatio < 1)
    (obstruction : ∀ unit : GaussianInt, normNat unit = 1 →
      (2 : Coordinate) ≤ normSq (errorRatio - toGaussian unit) ∨
        2 ≤ normSq (1 - toGaussian unit * denominatorRatio)) :
    1 - normSq errorRatio ≤ 2 * errorRatio.im ∧
      1 - normSq denominatorRatio ≤ -2 * denominatorRatio.re ∧
      1 - normSq denominatorRatio ≤ 2 * denominatorRatio.im := by
  have errorComplementPositive :
      (0 : Coordinate) < 1 - normSq errorRatio := by
    exact RFAP.ConstructiveFraction.sub_pos_direct errorInside
  obtain ⟨realCross, imaginaryCross⟩ := centeredUnit_projectionCrosses
    errorRatio denominatorRatio errorInside denominatorInside obstruction
  have denominatorReal :
      1 - normSq denominatorRatio ≤ -2 * denominatorRatio.re := by
    rcases realCross with cross | cross
    · have negativeNonpositive :
          -2 * errorRatio.re ≤ (0 : Coordinate) := by
        have negated := RFAP.ConstructiveFraction.neg_le_neg_direct
          realNonnegative
        calc
          -2 * errorRatio.re = 2 * (-errorRatio.re) := by ring1
          _ ≤ 2 * 0 :=
            RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
              negated (by decide)
          _ = 0 := by ring1
      have complementNonpositive := cross.1.trans negativeNonpositive
      exact ((not_le_of_gt errorComplementPositive)
        complementNonpositive).elim
    · exact cross.1
  have imaginaryBounds :
      1 - normSq errorRatio ≤ 2 * errorRatio.im ∧
        1 - normSq denominatorRatio ≤ 2 * denominatorRatio.im := by
    rcases imaginaryCross with cross | cross
    · have negativeNonpositive :
          -2 * errorRatio.im ≤ (0 : Coordinate) := by
        have negated := RFAP.ConstructiveFraction.neg_le_neg_direct
          imaginaryNonnegative
        calc
          -2 * errorRatio.im = 2 * (-errorRatio.im) := by ring1
          _ ≤ 2 * 0 :=
            RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
              negated (by decide)
          _ = 0 := by ring1
      have complementNonpositive := cross.1.trans negativeNonpositive
      exact ((not_le_of_gt errorComplementPositive)
        complementNonpositive).elim
    · exact ⟨cross.2, cross.1⟩
  exact ⟨imaginaryBounds.1, denominatorReal, imaginaryBounds.2⟩

/-- A rational affine minorant for the larger coordinate of a normalized
first-quadrant vector.  The choice `2(X+1)/7` lies just below
`sqrt(X/2)` throughout the centered norm chamber. -/
def centeredComponentLower (norm : Coordinate) : Coordinate :=
  2 * (norm + 1) / 7

/-- Algebraic form of the affine centered-component minorant. -/
theorem centeredComponentLower_eq (norm : Coordinate) :
    centeredComponentLower norm = (2 / 7) * (norm + 1) := by
  unfold centeredComponentLower
  rw [RFAP.ConstructiveFraction.div_eq_mul_inv_direct,
    RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
  calc
    (2 * (norm + 1)) * (7 : Coordinate)⁻¹ =
        2 * ((norm + 1) * (7 : Coordinate)⁻¹) :=
      RFAP.ConstructiveFraction.mul_assoc _ _ _
    _ = 2 * ((7 : Coordinate)⁻¹ * (norm + 1)) := by
      rw [RFAP.ConstructiveFraction.mul_comm (norm + 1) _]
    _ = (2 * (7 : Coordinate)⁻¹) * (norm + 1) :=
      (RFAP.ConstructiveFraction.mul_assoc _ _ _).symm

/-- Division by two agrees with multiplication by the displayed half. -/
theorem div_two_eq_half_mul (value : Coordinate) :
    value / 2 = (1 / 2) * value := by
  rw [RFAP.ConstructiveFraction.div_eq_mul_inv_direct,
    RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
  rw [RFAP.ConstructiveFraction.one_mul]
  exact RFAP.ConstructiveFraction.mul_comm _ _

private theorem centeredComponentLower_nonnegative
    (normNonnegative : (0 : Coordinate) ≤ norm) :
    0 ≤ centeredComponentLower norm := by
  unfold centeredComponentLower
  exact RFAP.ConstructiveFraction.div_nonneg_direct
    (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
      (add_nonneg normNonnegative (by decide)))
    (by decide)

/-- On `15/56 ≤ X ≤ 1`, the affine minorant has square at most `X/2`.
The proof uses the exact factorization of the difference from the lower
endpoint; it does not select a square root. -/
theorem centeredComponentLower_sq_le_half
    (norm : Coordinate)
    (thresholdLe : centeredNormThreshold ≤ norm)
    (normLeOne : norm ≤ 1) :
    centeredComponentLower norm ^ 2 ≤ norm / 2 := by
  let threshold := centeredNormThreshold
  have thresholdLeOne : threshold ≤ (1 : Coordinate) := by
    dsimp only [threshold]
    unfold centeredNormThreshold centeredNormThresholdFraction
    decide
  have normPlusThresholdPlusTwoLeFour :
      norm + threshold + 2 ≤ (4 : Coordinate) := by
    have first := RFAP.ConstructiveFraction.add_le_add_direct
      normLeOne thresholdLeOne
    have second := RFAP.ConstructiveFraction.add_le_add_right_direct first 2
    calc
      norm + threshold + 2 ≤ (1 : Coordinate) + 1 + 2 := second
      _ = 4 := by ring1
  have scaledLeHalf :
      (2 / 7 : Coordinate) ^ 2 * (norm + threshold + 2) ≤ 1 / 2 := by
    calc
      (2 / 7 : Coordinate) ^ 2 * (norm + threshold + 2) ≤
          (2 / 7) ^ 2 * 4 :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          normPlusThresholdPlusTwoLeFour
          (RFAP.ConstructiveFraction.sq_nonneg_direct _)
      _ ≤ 1 / 2 := by decide
  have factorNonnegative :
      0 ≤ (1 / 2 : Coordinate) -
        (2 / 7) ^ 2 * (norm + threshold + 2) :=
    RFAP.ConstructiveFraction.sub_nonneg_direct scaledLeHalf
  have endpointNonnegative :
      0 ≤ threshold / 2 - centeredComponentLower threshold ^ 2 := by
    dsimp only [threshold]
    unfold centeredNormThreshold centeredNormThresholdFraction
      centeredComponentLower
    decide
  have offsetNonnegative : 0 ≤ norm - threshold :=
    RFAP.ConstructiveFraction.sub_nonneg_direct thresholdLe
  have certificateNonnegative :
      0 ≤
        (threshold / 2 - centeredComponentLower threshold ^ 2) +
          (norm - threshold) *
            (1 / 2 - (2 / 7) ^ 2 * (norm + threshold + 2)) :=
    calc
      (0 : Coordinate) = 0 + 0 := by ring1
      _ ≤
          (threshold / 2 - centeredComponentLower threshold ^ 2) +
            (norm - threshold) *
              (1 / 2 - (2 / 7) ^ 2 * (norm + threshold + 2)) :=
        RFAP.ConstructiveFraction.add_le_add_direct endpointNonnegative
          (RFAP.ConstructiveFraction.mul_nonneg_direct offsetNonnegative
            factorNonnegative)
  apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
  calc
    0 ≤
        (threshold / 2 - centeredComponentLower threshold ^ 2) +
          (norm - threshold) *
            (1 / 2 - (2 / 7) ^ 2 * (norm + threshold + 2)) :=
      certificateNonnegative
    _ = norm / 2 - centeredComponentLower norm ^ 2 := by
      rw [centeredComponentLower_eq threshold,
        centeredComponentLower_eq norm]
      rw [div_two_eq_half_mul threshold, div_two_eq_half_mul norm]
      ring1

private theorem centeredComponentLower_le_largerCoordinate
    (large small norm : Coordinate)
    (largeNonnegative : 0 ≤ large)
    (smallNonnegative : 0 ≤ small)
    (smallLeLarge : small ≤ large)
    (normIdentity : norm = large ^ 2 + small ^ 2)
    (thresholdLe : centeredNormThreshold ≤ norm)
    (normLeOne : norm ≤ 1) :
    centeredComponentLower norm ≤ large := by
  have smallSquareLeLargeSquare : small ^ 2 ≤ large ^ 2 := by
    simpa only [pow_two] using
      RFAP.ConstructiveFraction.mul_le_mul_direct smallLeLarge smallLeLarge
        smallNonnegative largeNonnegative
  have halfNormLeLargeSquare : norm / 2 ≤ large ^ 2 := by
    apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct (c := 2)
    · calc
        (norm / 2) * 2 = norm := by
          exact RFAP.ConstructiveFraction.div_mul_cancel_of_ne norm 2
            (by decide)
        _ = large ^ 2 + small ^ 2 := normIdentity
        _ ≤ large ^ 2 + large ^ 2 :=
          RFAP.ConstructiveFraction.add_le_add_direct le_rfl
            smallSquareLeLargeSquare
        _ = large ^ 2 * 2 := by ring1
    · decide
  exact RFAP.ConstructiveFraction.le_of_sq_le_sq_direct largeNonnegative
    ((centeredComponentLower_sq_le_half norm thresholdLe normLeOne).trans
      halfNormLeLargeSquare)

private theorem half_complement_le_of_projection
    (norm coordinate : Coordinate)
    (projection : 1 - norm ≤ 2 * coordinate) :
    (1 - norm) / 2 ≤ coordinate := by
  apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct (c := 2)
  · calc
      ((1 - norm) / 2) * 2 = 1 - norm := by
        exact RFAP.ConstructiveFraction.div_mul_cancel_of_ne (1 - norm) 2
          (by decide)
      _ ≤ 2 * coordinate := projection
      _ = coordinate * 2 := by ring1
  · decide

private def centeredAlignedExcessFloor
    (firstNorm secondNorm : Coordinate) : Coordinate :=
  firstNorm * secondNorm +
    2 * (centeredComponentLower firstNorm *
      centeredComponentLower secondNorm) +
    2 * (((1 - firstNorm) / 2) * ((1 - secondNorm) / 2))

private theorem twice_half_mul_half
    (first second : Coordinate) :
    2 * ((first / 2) * (second / 2)) = (first * second) / 2 := by
  rw [div_two_eq_half_mul first, div_two_eq_half_mul second,
    div_two_eq_half_mul (first * second)]
  have halfCertificate :
      (2 : Coordinate) * (1 / 2) * (1 / 2) = 1 / 2 := by decide
  calc
    2 * ((1 / 2 * first) * (1 / 2 * second)) =
        (2 * (1 / 2) * (1 / 2)) * (first * second) := by ring1
    _ = (1 / 2) * (first * second) := by rw [halfCertificate]

private theorem centeredAlignedExcessFloor_eq
    (firstNorm secondNorm : Coordinate) :
    centeredAlignedExcessFloor firstNorm secondNorm =
      firstNorm * secondNorm +
        2 * (centeredComponentLower firstNorm *
          centeredComponentLower secondNorm) +
        ((1 - firstNorm) * (1 - secondNorm)) / 2 := by
  unfold centeredAlignedExcessFloor
  rw [twice_half_mul_half]

private theorem dyadicCenteredExcessThreshold_le_alignedFloor
    (firstNorm secondNorm : Coordinate)
    (firstLower : centeredNormThreshold ≤ firstNorm)
    (secondLower : centeredNormThreshold ≤ secondNorm) :
    dyadicCenteredExcessThreshold ≤
      centeredAlignedExcessFloor firstNorm secondNorm := by
  let threshold := centeredNormThreshold
  let slope : Coordinate := 2 / 7
  let factor := fun value : Coordinate =>
    value + 2 * slope ^ 2 * (value + 1) - (1 - value) / 2
  have thresholdFactorNonnegative : 0 ≤ factor threshold := by
    dsimp only [factor, slope, threshold]
    unfold centeredNormThreshold centeredNormThresholdFraction
    decide
  have factorMonotone : ∀ value : Coordinate, threshold ≤ value →
      factor threshold ≤ factor value := by
    intro value thresholdLe
    have offsetNonnegative : 0 ≤ value - threshold :=
      RFAP.ConstructiveFraction.sub_nonneg_direct thresholdLe
    apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
    calc
      0 ≤ (value - threshold) *
          (1 + 2 * slope ^ 2 + 1 / 2) :=
        RFAP.ConstructiveFraction.mul_nonneg_direct offsetNonnegative
          (add_nonneg
            (add_nonneg (by decide)
              (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
                (RFAP.ConstructiveFraction.sq_nonneg_direct slope)))
            (by decide))
      _ = factor value - factor threshold := by
        dsimp only [factor]
        rw [div_two_eq_half_mul (1 - value),
          div_two_eq_half_mul (1 - threshold)]
        ring1
  have secondFactorNonnegative : 0 ≤ factor secondNorm :=
    thresholdFactorNonnegative.trans (factorMonotone secondNorm secondLower)
  have firstStep :
      centeredAlignedExcessFloor threshold secondNorm ≤
        centeredAlignedExcessFloor firstNorm secondNorm := by
    have offsetNonnegative : 0 ≤ firstNorm - threshold :=
      RFAP.ConstructiveFraction.sub_nonneg_direct firstLower
    apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
    calc
      0 ≤ (firstNorm - threshold) * factor secondNorm :=
        RFAP.ConstructiveFraction.mul_nonneg_direct offsetNonnegative
          secondFactorNonnegative
      _ = centeredAlignedExcessFloor firstNorm secondNorm -
          centeredAlignedExcessFloor threshold secondNorm := by
        rw [centeredAlignedExcessFloor_eq,
          centeredAlignedExcessFloor_eq]
        simp only [centeredComponentLower_eq]
        dsimp only [factor, slope]
        rw [div_two_eq_half_mul
            ((1 - firstNorm) * (1 - secondNorm)),
          div_two_eq_half_mul
            ((1 - threshold) * (1 - secondNorm)),
          div_two_eq_half_mul (1 - secondNorm)]
        ring1
  have secondStep :
      centeredAlignedExcessFloor threshold threshold ≤
        centeredAlignedExcessFloor threshold secondNorm := by
    have offsetNonnegative : 0 ≤ secondNorm - threshold :=
      RFAP.ConstructiveFraction.sub_nonneg_direct secondLower
    apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
    calc
      0 ≤ (secondNorm - threshold) * factor threshold :=
        RFAP.ConstructiveFraction.mul_nonneg_direct offsetNonnegative
          thresholdFactorNonnegative
      _ = centeredAlignedExcessFloor threshold secondNorm -
          centeredAlignedExcessFloor threshold threshold := by
        rw [centeredAlignedExcessFloor_eq,
          centeredAlignedExcessFloor_eq]
        simp only [centeredComponentLower_eq]
        dsimp only [factor, slope]
        rw [div_two_eq_half_mul
            ((1 - threshold) * (1 - secondNorm)),
          div_two_eq_half_mul ((1 - threshold) * (1 - threshold)),
          div_two_eq_half_mul (1 - threshold)]
        ring1
  calc
    dyadicCenteredExcessThreshold ≤
        centeredAlignedExcessFloor threshold threshold := by
      dsimp only [threshold]
      unfold dyadicCenteredExcessThreshold
        dyadicCenteredExcessThresholdFraction centeredAlignedExcessFloor
        centeredComponentLower centeredNormThreshold
        centeredNormThresholdFraction
      decide
    _ ≤ centeredAlignedExcessFloor threshold secondNorm := secondStep
    _ ≤ centeredAlignedExcessFloor firstNorm secondNorm := firstStep

private theorem dyadicCenteredExcessThreshold_le_crossFloor
    (firstNorm secondNorm : Coordinate)
    (firstLower : centeredNormThreshold ≤ firstNorm)
    (secondLower : centeredNormThreshold ≤ secondNorm) :
    dyadicCenteredExcessThreshold ≤
      firstNorm * secondNorm +
        centeredComponentLower firstNorm * (1 - secondNorm) +
        (1 - firstNorm) * centeredComponentLower secondNorm := by
  let threshold := centeredNormThreshold
  let slope : Coordinate := 2 / 7
  have thresholdNonnegative : (0 : Coordinate) ≤ threshold := by
    dsimp only [threshold]
    unfold centeredNormThreshold centeredNormThresholdFraction
    decide
  have firstNonnegative : (0 : Coordinate) ≤ firstNorm :=
    thresholdNonnegative.trans firstLower
  have productLower : threshold ^ 2 ≤ firstNorm * secondNorm := by
    simpa only [pow_two] using
      RFAP.ConstructiveFraction.mul_le_mul_direct firstLower secondLower
        thresholdNonnegative firstNonnegative
  have coefficientNonnegative : 0 ≤ (1 : Coordinate) - 2 * slope := by
    dsimp only [slope]
    decide
  have scaledProductLower :
      (1 - 2 * slope) * threshold ^ 2 ≤
        (1 - 2 * slope) * (firstNorm * secondNorm) :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct productLower
      coefficientNonnegative
  calc
    dyadicCenteredExcessThreshold ≤
        2 * slope + (1 - 2 * slope) * threshold ^ 2 := by
      dsimp only [slope, threshold]
      unfold dyadicCenteredExcessThreshold
        dyadicCenteredExcessThresholdFraction centeredNormThreshold
        centeredNormThresholdFraction
      decide
    _ ≤ 2 * slope +
        (1 - 2 * slope) * (firstNorm * secondNorm) :=
      RFAP.ConstructiveFraction.add_le_add_direct le_rfl scaledProductLower
    _ = firstNorm * secondNorm +
        centeredComponentLower firstNorm * (1 - secondNorm) +
        (1 - firstNorm) * centeredComponentLower secondNorm := by
      rw [centeredComponentLower_eq, centeredComponentLower_eq]
      dsimp only [slope]
      ring1

private theorem complement_sq_le_two_normSq_of_projectionBounds
    (value : Gaussian)
    (inside : normSq value < 1)
    (realProjection :
      1 - normSq value ≤ -2 * value.re ∨
        1 - normSq value ≤ 2 * value.re)
    (imaginaryProjection :
      1 - normSq value ≤ -2 * value.im ∨
        1 - normSq value ≤ 2 * value.im) :
    (1 - normSq value) ^ 2 ≤ 2 * normSq value := by
  let complement := 1 - normSq value
  have complementNonnegative : 0 ≤ complement := by
    dsimp only [complement]
    exact RFAP.ConstructiveFraction.sub_nonneg_direct inside.le
  have realSquare : complement ^ 2 ≤ 4 * value.re ^ 2 := by
    rcases realProjection with projection | projection
    · have upperNonnegative : 0 ≤ -2 * value.re :=
        complementNonnegative.trans projection
      have squared := RFAP.ConstructiveFraction.mul_le_mul_direct
        projection projection complementNonnegative upperNonnegative
      dsimp only [complement] at projection ⊢
      calc
        (1 - normSq value) ^ 2 =
            (1 - normSq value) * (1 - normSq value) := by ring1
        _ ≤ (-2 * value.re) * (-2 * value.re) := squared
        _ = 4 * value.re ^ 2 := by ring1
    · have upperNonnegative : 0 ≤ 2 * value.re :=
        complementNonnegative.trans projection
      have squared := RFAP.ConstructiveFraction.mul_le_mul_direct
        projection projection complementNonnegative upperNonnegative
      dsimp only [complement] at projection ⊢
      calc
        (1 - normSq value) ^ 2 =
            (1 - normSq value) * (1 - normSq value) := by ring1
        _ ≤ (2 * value.re) * (2 * value.re) := squared
        _ = 4 * value.re ^ 2 := by ring1
  have imaginarySquare : complement ^ 2 ≤ 4 * value.im ^ 2 := by
    rcases imaginaryProjection with projection | projection
    · have upperNonnegative : 0 ≤ -2 * value.im :=
        complementNonnegative.trans projection
      have squared := RFAP.ConstructiveFraction.mul_le_mul_direct
        projection projection complementNonnegative upperNonnegative
      dsimp only [complement] at projection ⊢
      calc
        (1 - normSq value) ^ 2 =
            (1 - normSq value) * (1 - normSq value) := by ring1
        _ ≤ (-2 * value.im) * (-2 * value.im) := squared
        _ = 4 * value.im ^ 2 := by ring1
    · have upperNonnegative : 0 ≤ 2 * value.im :=
        complementNonnegative.trans projection
      have squared := RFAP.ConstructiveFraction.mul_le_mul_direct
        projection projection complementNonnegative upperNonnegative
      dsimp only [complement] at projection ⊢
      calc
        (1 - normSq value) ^ 2 =
            (1 - normSq value) * (1 - normSq value) := by ring1
        _ ≤ (2 * value.im) * (2 * value.im) := squared
        _ = 4 * value.im ^ 2 := by ring1
  have added := RFAP.ConstructiveFraction.add_le_add_direct
    realSquare imaginarySquare
  apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct (c := 2)
  · dsimp only [complement] at added ⊢
    calc
      (1 - normSq value) ^ 2 * 2 =
          (1 - normSq value) ^ 2 + (1 - normSq value) ^ 2 := by ring1
      _ ≤ 4 * value.re ^ 2 + 4 * value.im ^ 2 := added
      _ = (2 * normSq value) * 2 := by
        dsimp only [normSq]
        ring1
  · decide

/-- Four centered-unit obstructions keep both normalized quadrances away
from zero by the same square-root-free quadratic inequality. -/
theorem complement_sq_le_two_norms_of_centeredUnitObstructions
    (errorRatio denominatorRatio : Gaussian)
    (errorInside : normSq errorRatio < 1)
    (denominatorInside : normSq denominatorRatio < 1)
    (obstruction : ∀ unit : GaussianInt, normNat unit = 1 →
      (2 : Coordinate) ≤ normSq (errorRatio - toGaussian unit) ∨
        2 ≤ normSq (1 - toGaussian unit * denominatorRatio)) :
    (1 - normSq errorRatio) ^ 2 ≤ 2 * normSq errorRatio ∧
      (1 - normSq denominatorRatio) ^ 2 ≤
        2 * normSq denominatorRatio := by
  obtain ⟨realCross, imaginaryCross⟩ := centeredUnit_projectionCrosses
    errorRatio denominatorRatio errorInside denominatorInside obstruction
  have errorReal :
      1 - normSq errorRatio ≤ -2 * errorRatio.re ∨
        1 - normSq errorRatio ≤ 2 * errorRatio.re := by
    rcases realCross with cross | cross
    · exact Or.inl cross.1
    · exact Or.inr cross.2
  have errorImaginary :
      1 - normSq errorRatio ≤ -2 * errorRatio.im ∨
        1 - normSq errorRatio ≤ 2 * errorRatio.im := by
    rcases imaginaryCross with cross | cross
    · exact Or.inl cross.1
    · exact Or.inr cross.2
  have denominatorReal :
      1 - normSq denominatorRatio ≤ -2 * denominatorRatio.re ∨
        1 - normSq denominatorRatio ≤ 2 * denominatorRatio.re := by
    rcases realCross with cross | cross
    · exact Or.inr cross.2
    · exact Or.inl cross.1
  have denominatorImaginary :
      1 - normSq denominatorRatio ≤ -2 * denominatorRatio.im ∨
        1 - normSq denominatorRatio ≤ 2 * denominatorRatio.im := by
    rcases imaginaryCross with cross | cross
    · exact Or.inl cross.2
    · exact Or.inr cross.1
  exact ⟨
    complement_sq_le_two_normSq_of_projectionBounds errorRatio errorInside
      errorReal errorImaginary,
    complement_sq_le_two_normSq_of_projectionBounds denominatorRatio
      denominatorInside denominatorReal denominatorImaginary⟩

private theorem fifteen_fiftySixths_le_of_complement_sq_le_twice
    (value : Coordinate)
    (quadraticBound : (1 - value) ^ 2 ≤ 2 * value) :
    centeredNormThreshold ≤ value := by
  by_cases thresholdLe : centeredNormThreshold ≤ value
  · exact thresholdLe
  · have valueLtThreshold : value < centeredNormThreshold :=
      RFAP.ConstructiveFraction.lt_of_not_ge_direct thresholdLe
    have valueLeThreshold : value ≤ centeredNormThreshold :=
      RFAP.ConstructiveFraction.le_of_lt_direct valueLtThreshold
    have sumLe : value + centeredNormThreshold ≤
        centeredNormThreshold + centeredNormThreshold :=
      RFAP.ConstructiveFraction.add_le_add_direct valueLeThreshold le_rfl
    have sumLtFour : value + centeredNormThreshold < 4 := by
      have rationalGap :
          centeredNormThreshold + centeredNormThreshold < 4 := by
        decide
      exact ⟨sumLe.trans rationalGap.1, fun reverse =>
        rationalGap.2 (reverse.trans sumLe)⟩
    have firstFactorPositive :
        0 < centeredNormThreshold - value :=
      RFAP.ConstructiveFraction.sub_pos_direct valueLtThreshold
    have secondFactorPositive :
        0 < 4 - value - centeredNormThreshold := by
      have rewritten :
          4 - value - centeredNormThreshold =
            4 - (value + centeredNormThreshold) := by ring1
      rw [rewritten]
      exact RFAP.ConstructiveFraction.sub_pos_direct sumLtFour
    have productPositive :
        0 < (centeredNormThreshold - value) *
          (4 - value - centeredNormThreshold) :=
      RFAP.ConstructiveFraction.mul_pos_direct firstFactorPositive
        secondFactorPositive
    have thresholdPolynomialPositive :
        0 < centeredNormThreshold ^ 2 -
          4 * centeredNormThreshold + 1 := by
      decide
    have valuePolynomialPositive : 0 < value ^ 2 - 4 * value + 1 := by
      calc
        0 = 0 + 0 := by ring1
        _ < (centeredNormThreshold ^ 2 -
              4 * centeredNormThreshold + 1) +
            (centeredNormThreshold - value) *
              (4 - value - centeredNormThreshold) :=
          RFAP.ConstructiveFraction.add_lt_add_direct
            thresholdPolynomialPositive productPositive
        _ = value ^ 2 - 4 * value + 1 := by ring1
    have differenceNonnegative :
        0 ≤ 2 * value - (1 - value) ^ 2 :=
      RFAP.ConstructiveFraction.sub_nonneg_direct quadraticBound
    have valuePolynomialNonpositive : value ^ 2 - 4 * value + 1 ≤ 0 := by
      calc
        value ^ 2 - 4 * value + 1 =
            -(2 * value - (1 - value) ^ 2) := by ring1
        _ ≤ -0 :=
          RFAP.ConstructiveFraction.neg_le_neg_direct differenceNonnegative
        _ = 0 := by ring1
    exact (not_lt_of_ge valuePolynomialNonpositive
      valuePolynomialPositive).elim

/-- A rational point just below the smaller root `2 - sqrt(3)` of the
quadratic obstruction works uniformly for both normalized coordinates. -/
theorem fifteen_fiftySixths_le_norms_of_centeredUnitObstructions
    (errorRatio denominatorRatio : Gaussian)
    (errorInside : normSq errorRatio < 1)
    (denominatorInside : normSq denominatorRatio < 1)
    (obstruction : ∀ unit : GaussianInt, normNat unit = 1 →
      (2 : Coordinate) ≤ normSq (errorRatio - toGaussian unit) ∨
        2 ≤ normSq (1 - toGaussian unit * denominatorRatio)) :
    centeredNormThreshold ≤ normSq errorRatio ∧
      centeredNormThreshold ≤ normSq denominatorRatio := by
  obtain ⟨errorQuadratic, denominatorQuadratic⟩ :=
    complement_sq_le_two_norms_of_centeredUnitObstructions errorRatio
      denominatorRatio errorInside denominatorInside obstruction
  exact ⟨
    fifteen_fiftySixths_le_of_complement_sq_le_twice
      (normSq errorRatio) errorQuadratic,
    fifteen_fiftySixths_le_of_complement_sq_le_twice
      (normSq denominatorRatio) denominatorQuadratic⟩

private theorem fifteen_fiftySixths_le_balancedNormProduct
    (errorRatio denominatorRatio : Gaussian)
    (errorInside : normSq errorRatio < 1)
    (denominatorInside : normSq denominatorRatio < 1)
    (errorLower : centeredNormThreshold ≤ normSq errorRatio)
    (denominatorLower :
      centeredNormThreshold ≤ normSq denominatorRatio) :
    centeredNormThreshold ≤
      balancedNormProduct errorRatio denominatorRatio := by
  let x := normSq errorRatio
  let y := normSq denominatorRatio
  have xLeOne : x ≤ 1 := errorInside.le
  have yLeOne : y ≤ 1 := denominatorInside.le
  by_cases yLeHalf : y ≤ (1 / 2 : Coordinate)
  · have twiceYLeOne : 2 * y ≤ (1 : Coordinate) := by
      have scaled :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct yLeHalf
          (show (0 : Coordinate) ≤ 2 by decide)
      calc
        2 * y ≤ 2 * (1 / 2 : Coordinate) := scaled
        _ = 1 := by decide
    have oneMinusXNonnegative : 0 ≤ 1 - x :=
      RFAP.ConstructiveFraction.sub_nonneg_direct xLeOne
    have oneMinusTwiceYNonnegative : 0 ≤ 1 - 2 * y :=
      RFAP.ConstructiveFraction.sub_nonneg_direct twiceYLeOne
    have yLeBalanced : y ≤ balancedNormProduct errorRatio denominatorRatio := by
      apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
      calc
        0 ≤ (1 - x) * (1 - 2 * y) :=
          RFAP.ConstructiveFraction.mul_nonneg_direct
            oneMinusXNonnegative oneMinusTwiceYNonnegative
        _ = balancedNormProduct errorRatio denominatorRatio - y := by
          dsimp only [balancedNormProduct, x, y]
          ring1
    exact denominatorLower.trans yLeBalanced
  · have halfLtY : (1 / 2 : Coordinate) < y :=
      RFAP.ConstructiveFraction.lt_of_not_ge_direct yLeHalf
    have halfLeY : (1 / 2 : Coordinate) ≤ y :=
      RFAP.ConstructiveFraction.le_of_lt_direct halfLtY
    have oneLeTwiceY : (1 : Coordinate) ≤ 2 * y := by
      have scaled :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct halfLeY
          (show (0 : Coordinate) ≤ 2 by decide)
      calc
        (1 : Coordinate) = 2 * (1 / 2 : Coordinate) := by decide
        _ ≤ 2 * y := scaled
    have xMinusThresholdNonnegative :
        0 ≤ x - centeredNormThreshold :=
      RFAP.ConstructiveFraction.sub_nonneg_direct errorLower
    have twiceYMinusOneNonnegative : 0 ≤ 2 * y - 1 :=
      RFAP.ConstructiveFraction.sub_nonneg_direct oneLeTwiceY
    have oneMinusYNonnegative : 0 ≤ 1 - y :=
      RFAP.ConstructiveFraction.sub_nonneg_direct yLeOne
    have rationalFactorNonnegative :
        0 ≤ 1 - 2 * centeredNormThreshold := by
      decide
    apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
    calc
      0 ≤ (x - centeredNormThreshold) * (2 * y - 1) +
          (1 - y) * (1 - 2 * centeredNormThreshold) :=
        add_nonneg
          (RFAP.ConstructiveFraction.mul_nonneg_direct
            xMinusThresholdNonnegative twiceYMinusOneNonnegative)
          (RFAP.ConstructiveFraction.mul_nonneg_direct
            oneMinusYNonnegative rationalFactorNonnegative)
      _ = balancedNormProduct errorRatio denominatorRatio -
          centeredNormThreshold := by
        dsimp only [balancedNormProduct, x, y]
        ring1

/-- Four centered unit obstructions force a lower bound stronger than one:
the determinant gap contains both complementary normalized norm products.
The proof is entirely coordinatewise: opposite real units force a negative
real-coordinate product, and opposite imaginary units force a positive
imaginary-coordinate product. -/
theorem one_add_balancedNormProduct_le_determinantGap_of_centeredUnitObstructions
    (errorRatio denominatorRatio : Gaussian)
    (errorInside : normSq errorRatio < 1)
    (denominatorInside : normSq denominatorRatio < 1)
    (obstruction : ∀ unit : GaussianInt, normNat unit = 1 →
      (2 : Coordinate) ≤ normSq (errorRatio - toGaussian unit) ∨
        2 ≤ normSq (1 - toGaussian unit * denominatorRatio)) :
    1 + balancedNormProduct errorRatio denominatorRatio ≤
      normSq (1 - denominatorRatio * errorRatio) := by
  let errorGap := 1 - normSq errorRatio
  let denominatorGap := 1 - normSq denominatorRatio
  have errorGapNonnegative : 0 ≤ errorGap := by
    dsimp only [errorGap]
    exact RFAP.ConstructiveFraction.sub_nonneg_direct errorInside.le
  have denominatorGapNonnegative : 0 ≤ denominatorGap := by
    dsimp only [denominatorGap]
    exact RFAP.ConstructiveFraction.sub_nonneg_direct denominatorInside.le
  have realCross := RFAP.RepeatedIndex.opposite_self_obstructions_cross
    errorRatio denominatorRatio errorInside denominatorInside 1 rfl
      (obstruction 1 rfl) (obstruction (-1) (by decide))
  have imaginaryCross :=
    RFAP.RepeatedIndex.opposite_self_obstructions_cross
      errorRatio denominatorRatio errorInside denominatorInside
        RFAP.HurwitzGeometry.imaginaryUnit (by decide)
        (obstruction RFAP.HurwitzGeometry.imaginaryUnit (by decide))
        (obstruction (-RFAP.HurwitzGeometry.imaginaryUnit) (by decide))
  have realProductBound :
      4 * errorRatio.re * denominatorRatio.re ≤
        -(errorGap * denominatorGap) := by
    rcases realCross with cross | cross
    · have errorProjection : errorGap ≤ -2 * errorRatio.re := by
        apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
        calc
          0 ≤ normSq (errorRatio - toGaussian (1 : GaussianInt)) - 2 :=
            RFAP.ConstructiveFraction.sub_nonneg_direct cross.1
          _ = (-2 * errorRatio.re) - errorGap := by
            dsimp only [errorGap, normSq, toGaussian]
            simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
              RFAP.ConstructiveGaussian.Gaussian.sub_im,
              RFAP.ConstructiveGaussianHeight.GaussianInt.one_re,
              RFAP.ConstructiveGaussianHeight.GaussianInt.one_im,
              Int.cast_one, Int.cast_zero]
            ring1
      have denominatorProjection :
          denominatorGap ≤ 2 * denominatorRatio.re := by
        apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
        calc
          0 ≤ normSq
              (1 - toGaussian (-1 : GaussianInt) * denominatorRatio) - 2 :=
            RFAP.ConstructiveFraction.sub_nonneg_direct cross.2
          _ = 2 * denominatorRatio.re - denominatorGap := by
            dsimp only [denominatorGap, normSq, toGaussian]
            simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
              RFAP.ConstructiveGaussian.Gaussian.sub_im,
              RFAP.ConstructiveGaussian.Gaussian.mul_re,
              RFAP.ConstructiveGaussian.Gaussian.mul_im,
              RFAP.ConstructiveGaussian.Gaussian.one_re,
              RFAP.ConstructiveGaussian.Gaussian.one_im,
              RFAP.ConstructiveGaussianHeight.GaussianInt.neg_re,
              RFAP.ConstructiveGaussianHeight.GaussianInt.neg_im,
              RFAP.ConstructiveGaussianHeight.GaussianInt.one_re,
              RFAP.ConstructiveGaussianHeight.GaussianInt.one_im,
              Int.cast_neg, Int.cast_one, Int.cast_zero]
            ring1
      have productBound := RFAP.ConstructiveFraction.mul_le_mul_direct
        errorProjection denominatorProjection denominatorGapNonnegative
        (errorGapNonnegative.trans errorProjection)
      have negated := RFAP.ConstructiveFraction.neg_le_neg_direct productBound
      calc
        4 * errorRatio.re * denominatorRatio.re =
            -((-2 * errorRatio.re) * (2 * denominatorRatio.re)) := by ring1
        _ ≤ -(errorGap * denominatorGap) := negated
    · have denominatorProjection :
          denominatorGap ≤ -2 * denominatorRatio.re := by
        apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
        calc
          0 ≤ normSq (1 - toGaussian (1 : GaussianInt) * denominatorRatio) - 2 :=
            RFAP.ConstructiveFraction.sub_nonneg_direct cross.1
          _ = (-2 * denominatorRatio.re) - denominatorGap := by
            dsimp only [denominatorGap, normSq, toGaussian]
            simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
              RFAP.ConstructiveGaussian.Gaussian.sub_im,
              RFAP.ConstructiveGaussian.Gaussian.mul_re,
              RFAP.ConstructiveGaussian.Gaussian.mul_im,
              RFAP.ConstructiveGaussian.Gaussian.one_re,
              RFAP.ConstructiveGaussian.Gaussian.one_im,
              RFAP.ConstructiveGaussianHeight.GaussianInt.one_re,
              RFAP.ConstructiveGaussianHeight.GaussianInt.one_im,
              Int.cast_one, Int.cast_zero]
            ring1
      have errorProjection : errorGap ≤ 2 * errorRatio.re := by
        apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
        calc
          0 ≤ normSq (errorRatio - toGaussian (-1 : GaussianInt)) - 2 :=
            RFAP.ConstructiveFraction.sub_nonneg_direct cross.2
          _ = 2 * errorRatio.re - errorGap := by
            dsimp only [errorGap, normSq, toGaussian]
            simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
              RFAP.ConstructiveGaussian.Gaussian.sub_im,
              RFAP.ConstructiveGaussianHeight.GaussianInt.neg_re,
              RFAP.ConstructiveGaussianHeight.GaussianInt.neg_im,
              RFAP.ConstructiveGaussianHeight.GaussianInt.one_re,
              RFAP.ConstructiveGaussianHeight.GaussianInt.one_im,
              Int.cast_neg, Int.cast_one, Int.cast_zero]
            ring1
      have productBound := RFAP.ConstructiveFraction.mul_le_mul_direct
        errorProjection denominatorProjection denominatorGapNonnegative
        (errorGapNonnegative.trans errorProjection)
      have negated := RFAP.ConstructiveFraction.neg_le_neg_direct productBound
      calc
        4 * errorRatio.re * denominatorRatio.re =
            -((2 * errorRatio.re) * (-2 * denominatorRatio.re)) := by ring1
        _ ≤ -(errorGap * denominatorGap) := negated
  have imaginaryProductBound :
      errorGap * denominatorGap ≤
        4 * errorRatio.im * denominatorRatio.im := by
    rcases imaginaryCross with cross | cross
    · have errorProjection : errorGap ≤ -2 * errorRatio.im := by
        apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
        calc
          0 ≤ normSq
              (errorRatio -
                toGaussian RFAP.HurwitzGeometry.imaginaryUnit) - 2 :=
            RFAP.ConstructiveFraction.sub_nonneg_direct cross.1
          _ = (-2 * errorRatio.im) - errorGap := by
            dsimp only [errorGap, normSq, toGaussian,
              RFAP.HurwitzGeometry.imaginaryUnit]
            simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
              RFAP.ConstructiveGaussian.Gaussian.sub_im, Int.cast_one,
              Int.cast_zero]
            ring1
      have denominatorProjection :
          denominatorGap ≤ -2 * denominatorRatio.im := by
        apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
        calc
          0 ≤ normSq
              (1 -
                toGaussian (-RFAP.HurwitzGeometry.imaginaryUnit) *
                  denominatorRatio) - 2 :=
            RFAP.ConstructiveFraction.sub_nonneg_direct cross.2
          _ = (-2 * denominatorRatio.im) - denominatorGap := by
            dsimp only [denominatorGap, normSq, toGaussian,
              RFAP.HurwitzGeometry.imaginaryUnit]
            simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
              RFAP.ConstructiveGaussian.Gaussian.sub_im,
              RFAP.ConstructiveGaussian.Gaussian.mul_re,
              RFAP.ConstructiveGaussian.Gaussian.mul_im,
              RFAP.ConstructiveGaussian.Gaussian.one_re,
              RFAP.ConstructiveGaussian.Gaussian.one_im,
              RFAP.ConstructiveGaussianHeight.GaussianInt.neg_re,
              RFAP.ConstructiveGaussianHeight.GaussianInt.neg_im,
              Int.cast_neg, Int.cast_one, Int.cast_zero]
            ring1
      have productBound := RFAP.ConstructiveFraction.mul_le_mul_direct
        errorProjection denominatorProjection denominatorGapNonnegative
        (errorGapNonnegative.trans errorProjection)
      calc
        errorGap * denominatorGap ≤
            (-2 * errorRatio.im) * (-2 * denominatorRatio.im) :=
          productBound
        _ = 4 * errorRatio.im * denominatorRatio.im := by ring1
    · have denominatorProjection :
          denominatorGap ≤ 2 * denominatorRatio.im := by
        apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
        calc
          0 ≤ normSq
              (1 - toGaussian RFAP.HurwitzGeometry.imaginaryUnit *
                denominatorRatio) - 2 :=
            RFAP.ConstructiveFraction.sub_nonneg_direct cross.1
          _ = 2 * denominatorRatio.im - denominatorGap := by
            dsimp only [denominatorGap, normSq, toGaussian,
              RFAP.HurwitzGeometry.imaginaryUnit]
            simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
              RFAP.ConstructiveGaussian.Gaussian.sub_im,
              RFAP.ConstructiveGaussian.Gaussian.mul_re,
              RFAP.ConstructiveGaussian.Gaussian.mul_im,
              RFAP.ConstructiveGaussian.Gaussian.one_re,
              RFAP.ConstructiveGaussian.Gaussian.one_im, Int.cast_one,
              Int.cast_zero]
            ring1
      have errorProjection : errorGap ≤ 2 * errorRatio.im := by
        apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
        calc
          0 ≤ normSq
              (errorRatio -
                toGaussian (-RFAP.HurwitzGeometry.imaginaryUnit)) - 2 :=
            RFAP.ConstructiveFraction.sub_nonneg_direct cross.2
          _ = 2 * errorRatio.im - errorGap := by
            dsimp only [errorGap, normSq, toGaussian,
              RFAP.HurwitzGeometry.imaginaryUnit]
            simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
              RFAP.ConstructiveGaussian.Gaussian.sub_im,
              RFAP.ConstructiveGaussianHeight.GaussianInt.neg_re,
              RFAP.ConstructiveGaussianHeight.GaussianInt.neg_im,
              Int.cast_neg, Int.cast_one, Int.cast_zero]
            ring1
      have productBound := RFAP.ConstructiveFraction.mul_le_mul_direct
        errorProjection denominatorProjection denominatorGapNonnegative
        (errorGapNonnegative.trans errorProjection)
      calc
        errorGap * denominatorGap ≤
            (2 * errorRatio.im) * (2 * denominatorRatio.im) := productBound
        _ = 4 * errorRatio.im * denominatorRatio.im := by ring1
  have negatedImaginary :=
    RFAP.ConstructiveFraction.neg_le_neg_direct imaginaryProductBound
  have fourRealPartBound :
      4 * (errorRatio.re * denominatorRatio.re -
          errorRatio.im * denominatorRatio.im) ≤
        -2 * (errorGap * denominatorGap) := by
    calc
      4 * (errorRatio.re * denominatorRatio.re -
          errorRatio.im * denominatorRatio.im) =
          4 * errorRatio.re * denominatorRatio.re +
            -(4 * errorRatio.im * denominatorRatio.im) := by ring1
      _ ≤ -(errorGap * denominatorGap) +
          -(errorGap * denominatorGap) :=
        RFAP.ConstructiveFraction.add_le_add_direct realProductBound
          negatedImaginary
      _ = -2 * (errorGap * denominatorGap) := by ring1
  have twiceRealPartBound :
      2 * (errorRatio.re * denominatorRatio.re -
          errorRatio.im * denominatorRatio.im) ≤
        -(errorGap * denominatorGap) := by
    apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct (c := 2)
    · convert fourRealPartBound using 1 <;> ring1
    · decide
  have gapLeNegatedTwiceRealPart :
      errorGap * denominatorGap ≤
        -(2 * (errorRatio.re * denominatorRatio.re -
          errorRatio.im * denominatorRatio.im)) := by
    simpa only [neg_neg] using
      RFAP.ConstructiveFraction.neg_le_neg_direct twiceRealPartBound
  have coreBound :
      balancedNormProduct errorRatio denominatorRatio ≤
        normSq (1 - denominatorRatio * errorRatio) - 1 := by
    unfold balancedNormProduct
    dsimp only [errorGap, denominatorGap] at gapLeNegatedTwiceRealPart
    calc
      normSq errorRatio * normSq denominatorRatio +
          ((1 - normSq errorRatio) * (1 - normSq denominatorRatio)) ≤
          normSq errorRatio * normSq denominatorRatio -
            2 * (errorRatio.re * denominatorRatio.re -
              errorRatio.im * denominatorRatio.im) := by
        exact RFAP.ConstructiveFraction.add_le_add_direct le_rfl
          gapLeNegatedTwiceRealPart
      _ = normSq (1 - denominatorRatio * errorRatio) - 1 := by
        dsimp only [normSq]
        simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
          RFAP.ConstructiveGaussian.Gaussian.sub_im,
          RFAP.ConstructiveGaussian.Gaussian.mul_re,
          RFAP.ConstructiveGaussian.Gaussian.mul_im,
          RFAP.ConstructiveGaussian.Gaussian.one_re,
          RFAP.ConstructiveGaussian.Gaussian.one_im]
        ring1
  calc
    1 + balancedNormProduct errorRatio denominatorRatio ≤
        1 + (normSq (1 - denominatorRatio * errorRatio) - 1) :=
      RFAP.ConstructiveFraction.add_le_add_direct le_rfl coreBound
    _ = normSq (1 - denominatorRatio * errorRatio) := by ring1

/-- Four centered-unit obstructions give the explicit rational determinant
gap `71/56`.  This uses the balanced-product identity together with the
rational point `15/56 < 2 - sqrt(3)`; no square root is introduced. -/
theorem seventyOne_fiftySixths_le_determinantGap_of_centeredUnitObstructions
    (errorRatio denominatorRatio : Gaussian)
    (errorInside : normSq errorRatio < 1)
    (denominatorInside : normSq denominatorRatio < 1)
    (obstruction : ∀ unit : GaussianInt, normNat unit = 1 →
      (2 : Coordinate) ≤ normSq (errorRatio - toGaussian unit) ∨
        2 ≤ normSq (1 - toGaussian unit * denominatorRatio)) :
    centeredGapThreshold ≤
      normSq (1 - denominatorRatio * errorRatio) := by
  obtain ⟨errorLower, denominatorLower⟩ :=
    fifteen_fiftySixths_le_norms_of_centeredUnitObstructions errorRatio
      denominatorRatio errorInside denominatorInside obstruction
  have balancedLower := fifteen_fiftySixths_le_balancedNormProduct
    errorRatio denominatorRatio errorInside denominatorInside errorLower
      denominatorLower
  calc
    centeredGapThreshold = 1 + centeredNormThreshold := by decide
    _ ≤ 1 + balancedNormProduct errorRatio denominatorRatio :=
      RFAP.ConstructiveFraction.add_le_add_direct le_rfl balancedLower
    _ ≤ normSq (1 - denominatorRatio * errorRatio) :=
      one_add_balancedNormProduct_le_determinantGap_of_centeredUnitObstructions
        errorRatio denominatorRatio errorInside denominatorInside obstruction

/-- In a displayed first octant, the ordinary coordinate order and the four
centered-unit certificates force the stronger dyadic gap `205/128`.  The
proof replaces the two square roots in the geometric arc argument by the
affine minorant `2(X+1)/7` and two exact rational orientation cases. -/
theorem dyadicCenteredGapThreshold_le_determinantGap_of_firstOctantObstructions
    (errorRatio denominatorRatio : Gaussian)
    (realNonnegative : 0 ≤ errorRatio.re)
    (imaginaryNonnegative : 0 ≤ errorRatio.im)
    (imaginaryLeReal : errorRatio.im ≤ errorRatio.re)
    (errorInside : normSq errorRatio < 1)
    (denominatorInside : normSq denominatorRatio < 1)
    (obstruction : ∀ unit : GaussianInt, normNat unit = 1 →
      (2 : Coordinate) ≤ normSq (errorRatio - toGaussian unit) ∨
        2 ≤ normSq (1 - toGaussian unit * denominatorRatio)) :
    dyadicCenteredGapThreshold ≤
      normSq (1 - denominatorRatio * errorRatio) := by
  let a := errorRatio.re
  let b := errorRatio.im
  let u := -denominatorRatio.re
  let v := denominatorRatio.im
  let firstNorm := normSq errorRatio
  let secondNorm := normSq denominatorRatio
  let firstHalfGap := (1 - firstNorm) / 2
  let secondHalfGap := (1 - secondNorm) / 2
  obtain ⟨firstNormLower, secondNormLower⟩ :=
    fifteen_fiftySixths_le_norms_of_centeredUnitObstructions errorRatio
      denominatorRatio errorInside denominatorInside obstruction
  obtain ⟨bProjection, uProjectionRaw, vProjection⟩ :=
    firstOctant_projectionBounds_of_centeredUnitObstructions errorRatio
      denominatorRatio realNonnegative imaginaryNonnegative errorInside
      denominatorInside obstruction
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
      1 - normSq denominatorRatio ≤
          -2 * denominatorRatio.re := uProjectionRaw
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
  have firstComponentLower : centeredComponentLower firstNorm ≤ a :=
    centeredComponentLower_le_largerCoordinate a b firstNorm
      realNonnegative imaginaryNonnegative imaginaryLeReal firstNormIdentity
      firstNormLower firstNormLeOne
  have firstAffineNonnegative :
      (0 : Coordinate) ≤ centeredComponentLower firstNorm :=
    centeredComponentLower_nonnegative firstNormNonnegative
  have secondAffineNonnegative :
      (0 : Coordinate) ≤ centeredComponentLower secondNorm :=
    centeredComponentLower_nonnegative secondNormNonnegative
  have excessLeCore :
      dyadicCenteredExcessThreshold ≤
        firstNorm * secondNorm + 2 * (a * u + b * v) := by
    by_cases uLeV : u ≤ v
    · have secondComponentLower :
          centeredComponentLower secondNorm ≤ v :=
        centeredComponentLower_le_largerCoordinate v u secondNorm
          vNonnegative uNonnegative uLeV (by
            rw [secondNormIdentity]
            ring1)
          secondNormLower secondNormLeOne
      have firstProductLower :
          centeredComponentLower firstNorm * secondHalfGap ≤ a * u :=
        RFAP.ConstructiveFraction.mul_le_mul_direct firstComponentLower
          uLower secondHalfGapNonnegative realNonnegative
      have secondProductLower :
          firstHalfGap * centeredComponentLower secondNorm ≤ b * v :=
        RFAP.ConstructiveFraction.mul_le_mul_direct bLower
          secondComponentLower secondAffineNonnegative
          imaginaryNonnegative
      have productSumLower :
          centeredComponentLower firstNorm * secondHalfGap +
              firstHalfGap * centeredComponentLower secondNorm ≤
            a * u + b * v :=
        RFAP.ConstructiveFraction.add_le_add_direct firstProductLower
          secondProductLower
      have twiceProductSumLower :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          productSumLower (show (0 : Coordinate) ≤ 2 by decide)
      calc
        dyadicCenteredExcessThreshold ≤
            firstNorm * secondNorm +
              centeredComponentLower firstNorm * (1 - secondNorm) +
              (1 - firstNorm) * centeredComponentLower secondNorm :=
          dyadicCenteredExcessThreshold_le_crossFloor firstNorm secondNorm
            firstNormLower secondNormLower
        _ = firstNorm * secondNorm +
            2 * (centeredComponentLower firstNorm * secondHalfGap +
              firstHalfGap * centeredComponentLower secondNorm) := by
          have firstDouble : secondHalfGap * 2 = 1 - secondNorm := by
            dsimp only [secondHalfGap]
            exact RFAP.ConstructiveFraction.div_mul_cancel_of_ne
              (1 - secondNorm) 2 (by decide)
          have secondDouble : firstHalfGap * 2 = 1 - firstNorm := by
            dsimp only [firstHalfGap]
            exact RFAP.ConstructiveFraction.div_mul_cancel_of_ne
              (1 - firstNorm) 2 (by decide)
          rw [← firstDouble, ← secondDouble]
          ring1
        _ ≤ firstNorm * secondNorm + 2 * (a * u + b * v) :=
          RFAP.ConstructiveFraction.add_le_add_direct le_rfl
            twiceProductSumLower
    · have vLeU : v ≤ u := le_of_not_ge uLeV
      have secondComponentLower :
          centeredComponentLower secondNorm ≤ u :=
        centeredComponentLower_le_largerCoordinate u v secondNorm
          uNonnegative vNonnegative vLeU secondNormIdentity
          secondNormLower secondNormLeOne
      have firstProductLower :
          centeredComponentLower firstNorm *
              centeredComponentLower secondNorm ≤ a * u :=
        RFAP.ConstructiveFraction.mul_le_mul_direct firstComponentLower
          secondComponentLower secondAffineNonnegative realNonnegative
      have secondProductLower : firstHalfGap * secondHalfGap ≤ b * v :=
        RFAP.ConstructiveFraction.mul_le_mul_direct bLower vLower
          secondHalfGapNonnegative imaginaryNonnegative
      have productSumLower :
          centeredComponentLower firstNorm *
                centeredComponentLower secondNorm +
              firstHalfGap * secondHalfGap ≤
            a * u + b * v :=
        RFAP.ConstructiveFraction.add_le_add_direct firstProductLower
          secondProductLower
      have twiceProductSumLower :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          productSumLower (show (0 : Coordinate) ≤ 2 by decide)
      calc
        dyadicCenteredExcessThreshold ≤
            centeredAlignedExcessFloor firstNorm secondNorm :=
          dyadicCenteredExcessThreshold_le_alignedFloor firstNorm secondNorm
            firstNormLower secondNormLower
        _ = firstNorm * secondNorm +
            2 * (centeredComponentLower firstNorm *
                centeredComponentLower secondNorm +
              firstHalfGap * secondHalfGap) := by
          unfold centeredAlignedExcessFloor
          ring1
        _ ≤ firstNorm * secondNorm + 2 * (a * u + b * v) :=
          RFAP.ConstructiveFraction.add_le_add_direct le_rfl
            twiceProductSumLower
  calc
    dyadicCenteredGapThreshold =
        1 + dyadicCenteredExcessThreshold :=
      dyadicCenteredGapThreshold_eq_one_add_excess
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

/-- Compatibility consequence retaining the earlier unit lower bound. -/
theorem one_le_determinantGap_of_centeredUnitObstructions
    (errorRatio denominatorRatio : Gaussian)
    (errorInside : normSq errorRatio < 1)
    (denominatorInside : normSq denominatorRatio < 1)
    (obstruction : ∀ unit : GaussianInt, normNat unit = 1 →
      (2 : Coordinate) ≤ normSq (errorRatio - toGaussian unit) ∨
        2 ≤ normSq (1 - toGaussian unit * denominatorRatio)) :
    (1 : Coordinate) ≤ normSq (1 - denominatorRatio * errorRatio) := by
  have errorComplementNonnegative : 0 ≤ 1 - normSq errorRatio :=
    RFAP.ConstructiveFraction.sub_nonneg_direct errorInside.le
  have denominatorComplementNonnegative :
      0 ≤ 1 - normSq denominatorRatio :=
    RFAP.ConstructiveFraction.sub_nonneg_direct denominatorInside.le
  have balancedNonnegative :
      0 ≤ balancedNormProduct errorRatio denominatorRatio := by
    unfold balancedNormProduct
    exact add_nonneg
      (RFAP.ConstructiveFraction.mul_nonneg_direct
        (normSq_nonneg errorRatio) (normSq_nonneg denominatorRatio))
      (RFAP.ConstructiveFraction.mul_nonneg_direct
        errorComplementNonnegative denominatorComplementNonnegative)
  calc
    (1 : Coordinate) ≤
        1 + balancedNormProduct errorRatio denominatorRatio :=
      le_add_of_nonneg_right balancedNonnegative
    _ ≤ normSq (1 - denominatorRatio * errorRatio) :=
      one_add_balancedNormProduct_le_determinantGap_of_centeredUnitObstructions
        errorRatio denominatorRatio errorInside denominatorInside obstruction

/-- The upper-to-lower error ratio of a consecutive best pair lies strictly
inside the unit disk. -/
theorem AreConsecutiveBest.errorRatio_normSq_lt_one
    {source : RFAP.HurwitzRational.Fraction} {lower upper : Pair}
    (consecutive : AreConsecutiveBest source.value lower upper) :
    normSq (errorRatio source.value lower upper) < 1 := by
  have lowerPositive : 0 < normSq (error source.value lower) :=
    normSq_pos (RFAP.DirichletWindow.AreConsecutiveBest.lowerError_nonzero
      consecutive)
  unfold errorRatio
  rw [normSq_mul,
    RFAP.ConstructiveGaussian.Gaussian.normSq_inv _
      (RFAP.DirichletWindow.AreConsecutiveBest.lowerError_nonzero consecutive)]
  change normSq (error source.value upper) /
      normSq (error source.value lower) < 1
  apply (RFAP.ConstructiveFraction.div_lt_iff_pos lowerPositive).mpr
  rw [RFAP.ConstructiveFraction.one_mul]
  exact consecutive.2.1.2.1 lower consecutive.1.1 consecutive.2.2.1

/-- The centered coefficient pair available at determinant index two becomes
an exact normalized unit obstruction after cancelling the positive lower-error
and upper-denominator quadrances. -/
theorem AreConsecutiveBest.normalizedCenteredUnitObstruction
    {source : RFAP.HurwitzRational.Fraction} {lower upper : Pair}
    (consecutive : AreConsecutiveBest source.value lower upper)
    (indexTwo : coefficientIndexQuadrance lower upper = 2)
    (unit : GaussianInt) (unitNorm : normNat unit = 1) :
    (2 : Coordinate) ≤
        normSq (errorRatio source.value lower upper - toGaussian unit) ∨
      2 ≤ normSq
        (1 - toGaussian unit * denominatorRatio lower upper) := by
  let candidate := linearCombination lower upper (-unit) 1
  have obstruction :=
    consecutive.centeredUnit_selfObstruction indexTwo unit unitNorm
  have lowerErrorPositive :
      0 < errorQuadrance source.value lower :=
    normSq_pos (RFAP.DirichletWindow.AreConsecutiveBest.lowerError_nonzero
      consecutive)
  have upperDenominatorPositive :
      (0 : Coordinate) < denominatorQuadrance upper :=
    RFAP.ConstructiveFraction.natCast_pos_direct
      (normNat_pos consecutive.2.1.1)
  have errorIdentity :
      error source.value candidate =
        (errorRatio source.value lower upper - toGaussian unit) *
          error source.value lower := by
    dsimp only [candidate]
    rw [error_linearCombination_negUnit_one]
    have ratioCancel :=
      RFAP.DirichletWindow.AreConsecutiveBest.errorRatio_mul_lowerError
        consecutive
    calc
      error source.value upper -
            toGaussian unit * error source.value lower =
          errorRatio source.value lower upper * error source.value lower -
            toGaussian unit * error source.value lower := by
        rw [ratioCancel]
      _ =
          (errorRatio source.value lower upper - toGaussian unit) *
            error source.value lower := by
        apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
          simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
            RFAP.ConstructiveGaussian.Gaussian.sub_im,
            RFAP.ConstructiveGaussian.Gaussian.mul_re,
            RFAP.ConstructiveGaussian.Gaussian.mul_im] <;>
          ring1
  have denominatorIdentity :
      toGaussian candidate.denominator =
        (1 - toGaussian unit * denominatorRatio lower upper) *
          toGaussian upper.denominator := by
    dsimp only [candidate]
    rw [toGaussian_denominator_linearCombination_negUnit_one]
    have ratioCancel :=
      RFAP.DirichletWindow.AreConsecutiveBest.denominatorRatio_mul_upperDenominator
        consecutive
    calc
      toGaussian upper.denominator -
            toGaussian unit * toGaussian lower.denominator =
          toGaussian upper.denominator -
            toGaussian unit *
              (denominatorRatio lower upper *
                toGaussian upper.denominator) := by
        rw [ratioCancel]
      _ =
          (1 - toGaussian unit * denominatorRatio lower upper) *
            toGaussian upper.denominator := by
        apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
          simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
            RFAP.ConstructiveGaussian.Gaussian.sub_im,
            RFAP.ConstructiveGaussian.Gaussian.mul_re,
            RFAP.ConstructiveGaussian.Gaussian.mul_im,
            RFAP.ConstructiveGaussian.Gaussian.one_re,
            RFAP.ConstructiveGaussian.Gaussian.one_im] <;>
          ring1
  rcases obstruction with errorOutside | denominatorOutside
  · left
    apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct
      (c := errorQuadrance source.value lower)
    · calc
        (2 : Coordinate) * errorQuadrance source.value lower ≤
            errorQuadrance source.value candidate := errorOutside
        _ = normSq
              (errorRatio source.value lower upper - toGaussian unit) *
            errorQuadrance source.value lower := by
          unfold errorQuadrance
          rw [errorIdentity, normSq_mul]
    · exact lowerErrorPositive
  · right
    have castOutside :=
      RFAP.ConstructiveFraction.natCast_le_direct denominatorOutside
    apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct
      (c := (denominatorQuadrance upper : Coordinate))
    · calc
        (2 : Coordinate) * (denominatorQuadrance upper : Coordinate) =
            ((2 * denominatorQuadrance upper : Nat) : Coordinate) := by
          rw [Nat.cast_mul, Nat.cast_ofNat]
        _ ≤ (denominatorQuadrance candidate : Coordinate) := castOutside
        _ = normSq (toGaussian candidate.denominator) :=
          (normSq_toGaussian _).symm
        _ = normSq
              (1 - toGaussian unit * denominatorRatio lower upper) *
            (denominatorQuadrance upper : Coordinate) := by
          rw [denominatorIdentity, normSq_mul, normSq_toGaussian]
          rfl
    · exact upperDenominatorPositive

/-- In the determinant-index-two case, the four centered unit candidates
force the normalized determinant gap to be at least the displayed rational
`71/56`. -/
theorem AreConsecutiveBest.seventyOne_fiftySixths_le_normalizedDeterminantGap_of_indexTwo
    {source : RFAP.HurwitzRational.Fraction} {lower upper : Pair}
    (consecutive : AreConsecutiveBest source.value lower upper)
    (indexTwo : coefficientIndexQuadrance lower upper = 2) :
    centeredGapThreshold ≤
      normSq
        (1 - denominatorRatio lower upper *
          errorRatio source.value lower upper) := by
  exact seventyOne_fiftySixths_le_determinantGap_of_centeredUnitObstructions
    (errorRatio source.value lower upper) (denominatorRatio lower upper)
    (errorRatio_normSq_lt_one consecutive)
    (RFAP.DirichletWindow.AreConsecutiveBest.denominatorRatio_normSq_lt_one
      consecutive)
    (normalizedCenteredUnitObstruction consecutive indexTwo)

/-- Compatibility form of the strengthened determinant-index-two gap. -/
theorem AreConsecutiveBest.one_le_normalizedDeterminantGap_of_indexTwo
    {source : RFAP.HurwitzRational.Fraction} {lower upper : Pair}
    (consecutive : AreConsecutiveBest source.value lower upper)
    (indexTwo : coefficientIndexQuadrance lower upper = 2) :
    (1 : Coordinate) ≤
      normSq
        (1 - denominatorRatio lower upper *
          errorRatio source.value lower upper) := by
  exact (show (1 : Coordinate) ≤ centeredGapThreshold by decide).trans
    (seventyOne_fiftySixths_le_normalizedDeterminantGap_of_indexTwo
      consecutive indexTwo)

/-- A determinant-index-two consecutive window has squared product at most
the displayed rational `112/71`.  The proof multiplies through by the
positive displayed threshold, so it never constructs a reciprocal. -/
theorem AreConsecutiveBest.dirichletWindowQuadrance_le_oneHundredTwelve_seventyFirsts_of_indexTwo
    {source : RFAP.HurwitzRational.Fraction} {lower upper : Pair}
    (consecutive : AreConsecutiveBest source.value lower upper)
    (indexTwo : coefficientIndexQuadrance lower upper = 2) :
    dirichletWindowQuadrance source.value lower upper ≤
      centeredWindowBound := by
  have scaledWindow :=
    RFAP.DirichletWindow.AreConsecutiveBest.threshold_mul_dirichletWindow_le_index
      consecutive centeredGapThreshold
        (seventyOne_fiftySixths_le_normalizedDeterminantGap_of_indexTwo
          consecutive indexTwo)
  rw [indexTwo, Nat.cast_ofNat] at scaledWindow
  apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct
    (c := centeredGapThreshold)
  · calc
      dirichletWindowQuadrance source.value lower upper *
          centeredGapThreshold =
          centeredGapThreshold *
            dirichletWindowQuadrance source.value lower upper := by ring1
      _ ≤ 2 := scaledWindow
      _ = centeredWindowBound * centeredGapThreshold := by decide
  · decide

/-- A determinant-index-two consecutive window has squared product at most
two.  This compatibility statement now follows from the sharper rational
bound `112/71`. -/
theorem AreConsecutiveBest.dirichletWindowQuadrance_le_two_of_indexTwo
    {source : RFAP.HurwitzRational.Fraction} {lower upper : Pair}
    (consecutive : AreConsecutiveBest source.value lower upper)
    (indexTwo : coefficientIndexQuadrance lower upper = 2) :
    dirichletWindowQuadrance source.value lower upper ≤ 2 :=
  (dirichletWindowQuadrance_le_oneHundredTwelve_seventyFirsts_of_indexTwo
      consecutive indexTwo).trans (by decide)

theorem two_le_quadraticIndexFactor :
    (2 : Coordinate) ≤ quadraticIndexFactor := by
  unfold quadraticIndexFactor
  decide

theorem quadraticIndexFactor_mul_denominator :
    quadraticIndexFactor * 102 = 1189 := by
  unfold quadraticIndexFactor
  have clearance := RFAP.ConstructiveFraction.ofFraction_mul_den
    ({ num := 1189, den := 102, den_pos := by decide } :
      RFAP.ConstructiveFraction.Fraction)
  simpa only [Int.cast_ofNat] using clearance

/-- Splitting on the exact determinant index improves the universal squared
window bound from `1189/51` to `1189/102`: index one uses the quadratic gap
factor once, while index two has the independent centered-coset bound `2`. -/
theorem AreConsecutiveBest.dirichletWindowQuadrance_le_quadraticIndexFactorUniversal
    {source : RFAP.HurwitzRational.Fraction} {lower upper : Pair}
    (consecutive : AreConsecutiveBest source.value lower upper) :
    dirichletWindowQuadrance source.value lower upper ≤
      quadraticIndexFactor := by
  rcases consecutive.coefficientIndexQuadrance_eq_one_or_two with
      indexOne | indexTwo
  · have indexed :=
      RFAP.DirichletWindow.AreConsecutiveBest.dirichletWindowQuadrance_le_quadraticIndexFactor
        consecutive
    calc
      dirichletWindowQuadrance source.value lower upper ≤
          quadraticIndexFactor *
            (coefficientIndexQuadrance lower upper : Coordinate) := indexed
      _ = quadraticIndexFactor := by rw [indexOne]; ring1
  · exact
      (dirichletWindowQuadrance_le_two_of_indexTwo consecutive indexTwo).trans
        two_le_quadraticIndexFactor

end RFAP.IndexTwoWindow
