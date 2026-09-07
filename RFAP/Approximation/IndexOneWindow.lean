import mathlib.Tactic.QuotientFreeRing
import RFAP.Approximation.OptimalIndexTwoWindow
import RFAP.Approximation.OptimalIndexOneWindow

/-!
# Determinant-index-one Dirichlet windows

The generic nearest-coefficient argument uses only one Gaussian-integer
candidate.  At determinant index one every ambient coefficient is available,
so three neighbouring coefficients in the octant containing the normalized
error ratio give a stronger finite gap.  This file first proves the exact
first-octant calculation.  Its hypotheses are only rational coordinate
inequalities and three explicit empty-cylinder alternatives.
-/

namespace RFAP.IndexOneWindow

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianInt := RFAP.ConstructiveGaussianHeight.GaussianInt

open RFAP.ConstructiveGaussian.Gaussian
open RFAP.ConstructiveGaussianHeight.GaussianInt

private theorem lt_of_lt_of_le_coordinate
    {a b c : Coordinate} (first : a < b) (second : b ≤ c) : a < c :=
  ⟨first.1.trans second, fun reverse => first.2 (second.trans reverse)⟩

private theorem half_le_of_fourDot_le
    (xNorm yNorm dot : Coordinate)
    (yNormLeOne : yNorm ≤ 1)
    (fourDotBound : 4 * dot ≤ (1 + 2 * xNorm) * yNorm) :
    (1 / 2 : Coordinate) ≤ 1 + xNorm * yNorm - 2 * dot := by
  have oneLeBaseline : (1 : Coordinate) ≤ 2 - yNorm := by
    apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
    calc
      0 ≤ 1 - yNorm :=
        RFAP.ConstructiveFraction.sub_nonneg_direct yNormLeOne
      _ = (2 - yNorm) - 1 := by ring1
  have negated :=
    RFAP.ConstructiveFraction.neg_le_neg_direct fourDotBound
  have oneLeTwiceGap :
      (1 : Coordinate) ≤ 2 * (1 + xNorm * yNorm - 2 * dot) := by
    calc
      (1 : Coordinate) ≤ 2 - yNorm := oneLeBaseline
      _ = 2 + 2 * xNorm * yNorm - (1 + 2 * xNorm) * yNorm := by
        ring1
      _ ≤ 2 + 2 * xNorm * yNorm - 4 * dot := by
        have shifted := RFAP.ConstructiveFraction.add_le_add_right_direct
          negated (2 + 2 * xNorm * yNorm)
        calc
          2 + 2 * xNorm * yNorm - (1 + 2 * xNorm) * yNorm =
              -((1 + 2 * xNorm) * yNorm) +
                (2 + 2 * xNorm * yNorm) := by ring1
          _ ≤ -(4 * dot) + (2 + 2 * xNorm * yNorm) := shifted
          _ = 2 + 2 * xNorm * yNorm - 4 * dot := by ring1
      _ = 2 * (1 + xNorm * yNorm - 2 * dot) := by ring1
  apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct (c := 2)
  · calc
      (1 / 2 : Coordinate) * 2 = 1 := by decide
      _ ≤ 2 * (1 + xNorm * yNorm - 2 * dot) := oneLeTwiceGap
      _ = (1 + xNorm * yNorm - 2 * dot) * 2 := by ring1
  · decide

private theorem half_le_of_fourDot_le_boundary
    (xNorm yNorm dot : Coordinate)
    (xNormLeOne : xNorm ≤ 1)
    (yNormLeOne : yNorm ≤ 1)
    (fourDotBound : 4 * dot ≤ yNorm * (xNorm + 1) + xNorm) :
    (1 / 2 : Coordinate) ≤ 1 + xNorm * yNorm - 2 * dot := by
  have oneMinusXNonnegative : 0 ≤ 1 - xNorm :=
    RFAP.ConstructiveFraction.sub_nonneg_direct xNormLeOne
  have oneMinusYNonnegative : 0 ≤ 1 - yNorm :=
    RFAP.ConstructiveFraction.sub_nonneg_direct yNormLeOne
  have productNonnegative : 0 ≤ (1 - xNorm) * (1 - yNorm) :=
    RFAP.ConstructiveFraction.mul_nonneg_direct oneMinusXNonnegative
      oneMinusYNonnegative
  have oneLeBaseline :
      (1 : Coordinate) ≤ 1 + (1 - xNorm) * (1 - yNorm) :=
    le_add_of_nonneg_right productNonnegative
  have negated :=
    RFAP.ConstructiveFraction.neg_le_neg_direct fourDotBound
  have oneLeTwiceGap :
      (1 : Coordinate) ≤ 2 * (1 + xNorm * yNorm - 2 * dot) := by
    calc
      (1 : Coordinate) ≤ 1 + (1 - xNorm) * (1 - yNorm) := oneLeBaseline
      _ = 2 + 2 * xNorm * yNorm -
          (yNorm * (xNorm + 1) + xNorm) := by ring1
      _ ≤ 2 + 2 * xNorm * yNorm - 4 * dot := by
        have shifted := RFAP.ConstructiveFraction.add_le_add_right_direct
          negated (2 + 2 * xNorm * yNorm)
        calc
          2 + 2 * xNorm * yNorm -
                (yNorm * (xNorm + 1) + xNorm) =
              -(yNorm * (xNorm + 1) + xNorm) +
                (2 + 2 * xNorm * yNorm) := by ring1
          _ ≤ -(4 * dot) + (2 + 2 * xNorm * yNorm) := shifted
          _ = 2 + 2 * xNorm * yNorm - 4 * dot := by ring1
      _ = 2 * (1 + xNorm * yNorm - 2 * dot) := by ring1
  apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct (c := 2)
  · calc
      (1 / 2 : Coordinate) * 2 = 1 := by decide
      _ ≤ 2 * (1 + xNorm * yNorm - 2 * dot) := oneLeTwiceGap
      _ = (1 + xNorm * yNorm - 2 * dot) * 2 := by ring1
  · decide

private theorem three_quarters_le_of_twiceDot_le
    (xNorm yNorm dot : Coordinate)
    (twiceDotBound : 2 * dot ≤ xNorm * yNorm + 1 / 4) :
    (3 / 4 : Coordinate) ≤ 1 + xNorm * yNorm - 2 * dot := by
  have negated := RFAP.ConstructiveFraction.neg_le_neg_direct twiceDotBound
  calc
    (3 / 4 : Coordinate) =
        1 + xNorm * yNorm - (xNorm * yNorm + 1 / 4) := by
      rw [show (3 / 4 : Coordinate) = 1 - 1 / 4 by decide]
      ring1
    _ = -(xNorm * yNorm + 1 / 4) + (1 + xNorm * yNorm) := by
      ring1
    _ ≤ -(2 * dot) + (1 + xNorm * yNorm) :=
      RFAP.ConstructiveFraction.add_le_add_right_direct
        negated (1 + xNorm * yNorm)
    _ = 1 + xNorm * yNorm - 2 * dot := by ring1

private theorem component_mul_norm_le_product_add_quarter
    (component other firstNorm secondNorm : Coordinate)
    (firstNormIdentity : firstNorm = component ^ 2 + other ^ 2)
    (secondNormNonnegative : 0 ≤ secondNorm)
    (secondNormLeOne : secondNorm ≤ 1) :
    component * secondNorm ≤ firstNorm * secondNorm + 1 / 4 := by
  have squareSumNonnegative :
      0 ≤ (component - 1 / 2) ^ 2 + other ^ 2 :=
    add_nonneg
      (RFAP.ConstructiveFraction.sq_nonneg_direct _)
      (RFAP.ConstructiveFraction.sq_nonneg_direct _)
  have weightedSquaresNonnegative :
      0 ≤ secondNorm * ((component - 1 / 2) ^ 2 + other ^ 2) :=
    RFAP.ConstructiveFraction.mul_nonneg_direct secondNormNonnegative
      squareSumNonnegative
  have complementNonnegative : 0 ≤ 1 - secondNorm :=
    RFAP.ConstructiveFraction.sub_nonneg_direct secondNormLeOne
  have weightedComplementNonnegative :
      0 ≤ (1 - secondNorm) * (1 / 4) :=
    RFAP.ConstructiveFraction.mul_nonneg_direct complementNonnegative
      (by decide)
  have shiftedSquareIdentity :
      (component - 1 / 2) ^ 2 =
        component ^ 2 - component + 1 / 4 := by
    calc
      (component - 1 / 2) ^ 2 =
          component ^ 2 - component * (1 / 2 + 1 / 2) +
            (1 / 2) ^ 2 := by ring1
      _ = component ^ 2 - component * 1 + (1 / 2) ^ 2 := by
        rw [show (1 / 2 : Coordinate) + 1 / 2 = 1 by decide]
      _ = component ^ 2 - component + 1 / 4 := by
        rw [show (1 / 2 : Coordinate) ^ 2 = 1 / 4 by decide]
        ring1
  apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
  calc
    0 ≤ secondNorm * ((component - 1 / 2) ^ 2 + other ^ 2) +
        (1 - secondNorm) * (1 / 4) :=
      add_nonneg weightedSquaresNonnegative weightedComplementNonnegative
    _ = (firstNorm * secondNorm + 1 / 4) -
        component * secondNorm := by
      rw [firstNormIdentity, shiftedSquareIdentity]
      ring1

private theorem real_nonpositive_or_imaginary_nonnegative_of_axisObstructions
    (value : Gaussian)
    (inside : normSq value < 1)
    (realObstruction : 2 * value.re ≤ normSq value)
    (imaginaryObstruction : -2 * value.im ≤ normSq value) :
    value.re ≤ 0 ∨ 0 ≤ value.im := by
  by_cases realNonpositive : value.re ≤ 0
  · exact Or.inl realNonpositive
  · have realPositive : 0 < value.re :=
      RFAP.ConstructiveFraction.lt_of_not_ge_direct realNonpositive
    by_cases imaginaryNonnegative : 0 ≤ value.im
    · exact Or.inr imaginaryNonnegative
    · have imaginaryNegative : value.im < 0 :=
        RFAP.ConstructiveFraction.lt_of_not_ge_direct imaginaryNonnegative
      have negImaginaryPositive : 0 < -value.im := by
        have positive :=
          RFAP.ConstructiveFraction.sub_pos_direct imaginaryNegative
        calc
          0 < 0 - value.im := positive
          _ = -value.im := by ring1
      have twiceNegImaginaryLeNorm :
          2 * (-value.im) ≤ normSq value := by
        calc
          2 * (-value.im) = -2 * value.im := by ring1
          _ ≤ normSq value := imaginaryObstruction
      have twiceSumLeNorm :
          2 * (value.re + -value.im) ≤ 2 * normSq value := by
        have added := RFAP.ConstructiveFraction.add_le_add_direct
          realObstruction twiceNegImaginaryLeNorm
        calc
          2 * (value.re + -value.im) =
              2 * value.re + 2 * (-value.im) := by ring1
          _ ≤ normSq value + normSq value := added
          _ = 2 * normSq value := by ring1
      have sumLeNorm : value.re + -value.im ≤ normSq value := by
        apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct (c := 2)
        · calc
            (value.re + -value.im) * 2 =
                2 * (value.re + -value.im) := by ring1
            _ ≤ 2 * normSq value := twiceSumLeNorm
            _ = normSq value * 2 := by ring1
        · decide
      have realLtOne : value.re < 1 :=
        lt_of_lt_of_le_coordinate
          (by
            have shifted :=
              RFAP.ConstructiveFraction.add_lt_add_left_direct
                negImaginaryPositive value.re
            calc
              value.re = value.re + 0 := by ring1
              _ < value.re + -value.im := shifted)
          (sumLeNorm.trans
            (RFAP.ConstructiveFraction.le_of_lt_direct inside))
      have negImaginaryLtOne : -value.im < 1 :=
        lt_of_lt_of_le_coordinate
          (by
            have shifted :=
              RFAP.ConstructiveFraction.add_lt_add_right_direct
                realPositive (-value.im)
            calc
              -value.im = 0 + -value.im := by ring1
              _ < value.re + -value.im := shifted)
          (sumLeNorm.trans
            (RFAP.ConstructiveFraction.le_of_lt_direct inside))
      have realSquareLtReal : value.re ^ 2 < value.re := by
        have scaled :=
          RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
            realPositive realLtOne
        calc
          value.re ^ 2 = value.re * value.re := by ring1
          _ < value.re * 1 := scaled
          _ = value.re := by ring1
      have negImaginarySquareLtNegImaginary :
          (-value.im) ^ 2 < -value.im := by
        have scaled :=
          RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
            negImaginaryPositive negImaginaryLtOne
        calc
          (-value.im) ^ 2 = (-value.im) * (-value.im) := by ring1
          _ < (-value.im) * 1 := scaled
          _ = -value.im := by ring1
      have normLtSum : normSq value < value.re + -value.im := by
        have added := RFAP.ConstructiveFraction.add_lt_add_direct
          realSquareLtReal negImaginarySquareLtNegImaginary
        dsimp only [normSq]
        calc
          value.re ^ 2 + value.im ^ 2 =
              value.re ^ 2 + (-value.im) ^ 2 := by ring1
          _ < value.re + -value.im := added
      exact (normLtSum.2 sumLeNorm).elim

private theorem real_nonpositive_or_imaginary_nonnegative_of_diagonalObstructions
    (value : Gaussian)
    (inside : normSq value < 1)
    (diagonalObstruction : value.re - value.im ≤ normSq value) :
    value.re ≤ 0 ∨ 0 ≤ value.im := by
  by_cases realNonpositive : value.re ≤ 0
  · exact Or.inl realNonpositive
  · have realPositive : 0 < value.re :=
      RFAP.ConstructiveFraction.lt_of_not_ge_direct realNonpositive
    by_cases imaginaryNonnegative : 0 ≤ value.im
    · exact Or.inr imaginaryNonnegative
    · have imaginaryNegative : value.im < 0 :=
        RFAP.ConstructiveFraction.lt_of_not_ge_direct imaginaryNonnegative
      have negImaginaryPositive : 0 < -value.im := by
        have positive :=
          RFAP.ConstructiveFraction.sub_pos_direct imaginaryNegative
        calc
          0 < 0 - value.im := positive
          _ = -value.im := by ring1
      have sumLeNorm : value.re + -value.im ≤ normSq value := by
        calc
          value.re + -value.im = value.re - value.im := by ring1
          _ ≤ normSq value := diagonalObstruction
      have realLtOne : value.re < 1 :=
        lt_of_lt_of_le_coordinate
          (by
            have shifted :=
              RFAP.ConstructiveFraction.add_lt_add_left_direct
                negImaginaryPositive value.re
            calc
              value.re = value.re + 0 := by ring1
              _ < value.re + -value.im := shifted)
          (sumLeNorm.trans
            (RFAP.ConstructiveFraction.le_of_lt_direct inside))
      have negImaginaryLtOne : -value.im < 1 :=
        lt_of_lt_of_le_coordinate
          (by
            have shifted :=
              RFAP.ConstructiveFraction.add_lt_add_right_direct
                realPositive (-value.im)
            calc
              -value.im = 0 + -value.im := by ring1
              _ < value.re + -value.im := shifted)
          (sumLeNorm.trans
            (RFAP.ConstructiveFraction.le_of_lt_direct inside))
      have realSquareLtReal : value.re ^ 2 < value.re := by
        have scaled :=
          RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
            realPositive realLtOne
        calc
          value.re ^ 2 = value.re * value.re := by ring1
          _ < value.re * 1 := scaled
          _ = value.re := by ring1
      have negImaginarySquareLtNegImaginary :
          (-value.im) ^ 2 < -value.im := by
        have scaled :=
          RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
            negImaginaryPositive negImaginaryLtOne
        calc
          (-value.im) ^ 2 = (-value.im) * (-value.im) := by ring1
          _ < (-value.im) * 1 := scaled
          _ = -value.im := by ring1
      have normLtSum : normSq value < value.re + -value.im := by
        have added := RFAP.ConstructiveFraction.add_lt_add_direct
          realSquareLtReal negImaginarySquareLtNegImaginary
        dsimp only [normSq]
        calc
          value.re ^ 2 + value.im ^ 2 =
              value.re ^ 2 + (-value.im) ^ 2 := by ring1
          _ < value.re + -value.im := added
      exact (normLtSum.2 sumLeNorm).elim

private theorem three_quarters_le_of_axisChamber
    (errorRatio denominatorRatio : Gaussian)
    (errorRealNonnegative : 0 ≤ errorRatio.re)
    (errorImaginaryNonnegative : 0 ≤ errorRatio.im)
    (denominatorInside : normSq denominatorRatio < 1)
    (denominatorRealObstruction :
      2 * denominatorRatio.re ≤ normSq denominatorRatio)
    (denominatorImaginaryObstruction :
      -2 * denominatorRatio.im ≤ normSq denominatorRatio) :
    (3 / 4 : Coordinate) ≤
      normSq (1 - denominatorRatio * errorRatio) := by
  let xNorm := normSq errorRatio
  let yNorm := normSq denominatorRatio
  let dot := errorRatio.re * denominatorRatio.re -
    errorRatio.im * denominatorRatio.im
  have yNormNonnegative : 0 ≤ yNorm := by
    dsimp only [yNorm]
    exact normSq_nonneg denominatorRatio
  have yNormLeOne : yNorm ≤ 1 := denominatorInside.le
  have realComponentBound :
      errorRatio.re * yNorm ≤ xNorm * yNorm + 1 / 4 := by
    apply component_mul_norm_le_product_add_quarter
        errorRatio.re errorRatio.im xNorm yNorm
    · rfl
    · exact yNormNonnegative
    · exact yNormLeOne
  have imaginaryComponentBound :
      errorRatio.im * yNorm ≤ xNorm * yNorm + 1 / 4 := by
    apply component_mul_norm_le_product_add_quarter
        errorRatio.im errorRatio.re xNorm yNorm
    · dsimp only [xNorm, normSq]
      ring1
    · exact yNormNonnegative
    · exact yNormLeOne
  have gapExpansion :
      normSq (1 - denominatorRatio * errorRatio) =
        1 + xNorm * yNorm - 2 * dot := by
    dsimp only [xNorm, yNorm, dot, normSq]
    simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
      RFAP.ConstructiveGaussian.Gaussian.sub_im,
      RFAP.ConstructiveGaussian.Gaussian.mul_re,
      RFAP.ConstructiveGaussian.Gaussian.mul_im,
      RFAP.ConstructiveGaussian.Gaussian.one_re,
      RFAP.ConstructiveGaussian.Gaussian.one_im]
    ring1
  have signAlternative :=
    real_nonpositive_or_imaginary_nonnegative_of_axisObstructions
      denominatorRatio denominatorInside denominatorRealObstruction
        denominatorImaginaryObstruction
  rw [gapExpansion]
  apply three_quarters_le_of_twiceDot_le xNorm yNorm dot
  rcases signAlternative with realNonpositive | imaginaryNonnegative
  · have realProductNonpositive :
        errorRatio.re * denominatorRatio.re ≤ 0 := by
      have scaled :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          realNonpositive errorRealNonnegative
      calc
        errorRatio.re * denominatorRatio.re ≤ errorRatio.re * 0 := scaled
        _ = 0 := by ring1
    have dotLeImaginaryProduct :
        dot ≤ errorRatio.im * (-denominatorRatio.im) := by
      apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
      dsimp only [dot]
      calc
        0 ≤ -(errorRatio.re * denominatorRatio.re) :=
          neg_nonneg.mpr realProductNonpositive
        _ = errorRatio.im * (-denominatorRatio.im) -
            (errorRatio.re * denominatorRatio.re -
              errorRatio.im * denominatorRatio.im) := by ring1
    have twiceDotLeImaginary :
        2 * dot ≤ errorRatio.im * yNorm := by
      have doubled :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          dotLeImaginaryProduct (show (0 : Coordinate) ≤ 2 by decide)
      have scaled :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          denominatorImaginaryObstruction errorImaginaryNonnegative
      calc
        2 * dot ≤ 2 * (errorRatio.im * (-denominatorRatio.im)) := doubled
        _ = errorRatio.im * (-2 * denominatorRatio.im) := by ring1
        _ ≤ errorRatio.im * yNorm := scaled
    exact twiceDotLeImaginary.trans imaginaryComponentBound
  · have imaginaryProductNonnegative :
        0 ≤ errorRatio.im * denominatorRatio.im :=
      RFAP.ConstructiveFraction.mul_nonneg_direct
        errorImaginaryNonnegative imaginaryNonnegative
    have dotLeRealProduct :
        dot ≤ errorRatio.re * denominatorRatio.re := by
      apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
      dsimp only [dot]
      calc
        0 ≤ errorRatio.im * denominatorRatio.im :=
          imaginaryProductNonnegative
        _ = errorRatio.re * denominatorRatio.re -
            (errorRatio.re * denominatorRatio.re -
              errorRatio.im * denominatorRatio.im) := by ring1
    have twiceDotLeReal : 2 * dot ≤ errorRatio.re * yNorm := by
      have doubled :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          dotLeRealProduct (show (0 : Coordinate) ≤ 2 by decide)
      have scaled :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          denominatorRealObstruction errorRealNonnegative
      calc
        2 * dot ≤ 2 * (errorRatio.re * denominatorRatio.re) := doubled
        _ = errorRatio.re * (2 * denominatorRatio.re) := by ring1
        _ ≤ errorRatio.re * yNorm := scaled
    exact twiceDotLeReal.trans realComponentBound

private theorem three_quarters_le_of_diagonalDenominatorChamber
    (errorRatio denominatorRatio : Gaussian)
    (errorRealNonnegative : 0 ≤ errorRatio.re)
    (errorImaginaryNonnegative : 0 ≤ errorRatio.im)
    (errorInside : normSq errorRatio < 1)
    (denominatorInside : normSq denominatorRatio < 1)
    (errorImaginaryObstruction :
      2 * errorRatio.im ≤ normSq errorRatio)
    (denominatorRealObstruction :
      2 * denominatorRatio.re ≤ normSq denominatorRatio)
    (denominatorDiagonalObstruction :
      denominatorRatio.re - denominatorRatio.im ≤
        normSq denominatorRatio) :
    (3 / 4 : Coordinate) ≤
      normSq (1 - denominatorRatio * errorRatio) := by
  let xNorm := normSq errorRatio
  let yNorm := normSq denominatorRatio
  let dot := errorRatio.re * denominatorRatio.re -
    errorRatio.im * denominatorRatio.im
  have xNormNonnegative : 0 ≤ xNorm := by
    dsimp only [xNorm]
    exact normSq_nonneg errorRatio
  have xNormLeOne : xNorm ≤ 1 := errorInside.le
  have yNormNonnegative : 0 ≤ yNorm := by
    dsimp only [yNorm]
    exact normSq_nonneg denominatorRatio
  have yNormLeOne : yNorm ≤ 1 := denominatorInside.le
  have realComponentBound :
      errorRatio.re * yNorm ≤ xNorm * yNorm + 1 / 4 := by
    apply component_mul_norm_le_product_add_quarter
        errorRatio.re errorRatio.im xNorm yNorm
    · rfl
    · exact yNormNonnegative
    · exact yNormLeOne
  have negativeImaginaryComponentBound :
      xNorm * (-denominatorRatio.im) ≤
        xNorm * yNorm + 1 / 4 := by
    have swapped := component_mul_norm_le_product_add_quarter
      (-denominatorRatio.im) denominatorRatio.re yNorm xNorm
      (by
        dsimp only [yNorm, normSq]
        ring1)
      xNormNonnegative xNormLeOne
    calc
      xNorm * (-denominatorRatio.im) =
          (-denominatorRatio.im) * xNorm := by ring1
      _ ≤ yNorm * xNorm + 1 / 4 := swapped
      _ = xNorm * yNorm + 1 / 4 := by ring1
  have gapExpansion :
      normSq (1 - denominatorRatio * errorRatio) =
        1 + xNorm * yNorm - 2 * dot := by
    dsimp only [xNorm, yNorm, dot, normSq]
    simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
      RFAP.ConstructiveGaussian.Gaussian.sub_im,
      RFAP.ConstructiveGaussian.Gaussian.mul_re,
      RFAP.ConstructiveGaussian.Gaussian.mul_im,
      RFAP.ConstructiveGaussian.Gaussian.one_re,
      RFAP.ConstructiveGaussian.Gaussian.one_im]
    ring1
  have signAlternative :=
    real_nonpositive_or_imaginary_nonnegative_of_diagonalObstructions
      denominatorRatio denominatorInside denominatorDiagonalObstruction
  rw [gapExpansion]
  apply three_quarters_le_of_twiceDot_le xNorm yNorm dot
  by_cases denominatorImaginaryNonnegative : 0 ≤ denominatorRatio.im
  · have imaginaryProductNonnegative :
        0 ≤ errorRatio.im * denominatorRatio.im :=
      RFAP.ConstructiveFraction.mul_nonneg_direct
        errorImaginaryNonnegative denominatorImaginaryNonnegative
    have dotLeRealProduct :
        dot ≤ errorRatio.re * denominatorRatio.re := by
      apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
      dsimp only [dot]
      calc
        0 ≤ errorRatio.im * denominatorRatio.im :=
          imaginaryProductNonnegative
        _ = errorRatio.re * denominatorRatio.re -
            (errorRatio.re * denominatorRatio.re -
              errorRatio.im * denominatorRatio.im) := by ring1
    have twiceDotLeReal : 2 * dot ≤ errorRatio.re * yNorm := by
      have doubled :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          dotLeRealProduct (show (0 : Coordinate) ≤ 2 by decide)
      have scaled :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          denominatorRealObstruction errorRealNonnegative
      calc
        2 * dot ≤ 2 * (errorRatio.re * denominatorRatio.re) := doubled
        _ = errorRatio.re * (2 * denominatorRatio.re) := by ring1
        _ ≤ errorRatio.re * yNorm := scaled
    exact twiceDotLeReal.trans realComponentBound
  · have denominatorImaginaryNegative : denominatorRatio.im < 0 :=
      RFAP.ConstructiveFraction.lt_of_not_ge_direct
        denominatorImaginaryNonnegative
    have denominatorRealNonpositive : denominatorRatio.re ≤ 0 := by
      rcases signAlternative with realNonpositive | imaginaryNonnegative
      · exact realNonpositive
      · exact (denominatorImaginaryNonnegative imaginaryNonnegative).elim
    have negativeImaginaryNonnegative : 0 ≤ -denominatorRatio.im := by
      calc
        0 ≤ 0 - denominatorRatio.im :=
          (RFAP.ConstructiveFraction.sub_pos_direct
            denominatorImaginaryNegative).le
        _ = -denominatorRatio.im := by ring1
    have realProductNonpositive :
        errorRatio.re * denominatorRatio.re ≤ 0 := by
      have scaled :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          denominatorRealNonpositive errorRealNonnegative
      calc
        errorRatio.re * denominatorRatio.re ≤ errorRatio.re * 0 := scaled
        _ = 0 := by ring1
    have dotLeImaginaryProduct :
        dot ≤ errorRatio.im * (-denominatorRatio.im) := by
      apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
      dsimp only [dot]
      calc
        0 ≤ -(errorRatio.re * denominatorRatio.re) :=
          neg_nonneg.mpr realProductNonpositive
        _ = errorRatio.im * (-denominatorRatio.im) -
            (errorRatio.re * denominatorRatio.re -
              errorRatio.im * denominatorRatio.im) := by ring1
    have twiceDotLeNegativeImaginary :
        2 * dot ≤ xNorm * (-denominatorRatio.im) := by
      have doubled :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          dotLeImaginaryProduct (show (0 : Coordinate) ≤ 2 by decide)
      have scaled :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          errorImaginaryObstruction negativeImaginaryNonnegative
      calc
        2 * dot ≤ 2 * (errorRatio.im * (-denominatorRatio.im)) :=
          doubled
        _ = (2 * errorRatio.im) * (-denominatorRatio.im) := by ring1
        _ ≤ xNorm * (-denominatorRatio.im) := scaled
    exact twiceDotLeNegativeImaginary.trans
      negativeImaginaryComponentBound

private def diagonalErrorBoundaryFraction :
    RFAP.ConstructiveFraction.Fraction :=
  { num := 13, den := 97, den_pos := by decide }

private def diagonalErrorBoundary : Coordinate :=
  RFAP.ConstructiveFraction.ofFraction diagonalErrorBoundaryFraction

private theorem diagonalErrorBoundary_mul_denominator :
    diagonalErrorBoundary * 97 = 13 := by
  have numeratorCast :
      (((13 : Nat) : Int) : Coordinate) = (13 : Coordinate) := by
    calc
      (((13 : Nat) : Int) : Coordinate) = ((13 : Nat) : Coordinate) :=
        Int.cast_natCast 13
      _ = (13 : Coordinate) := Nat.cast_ofNat
  calc
    diagonalErrorBoundary * 97 =
        RFAP.ConstructiveFraction.ofFraction diagonalErrorBoundaryFraction *
          ((diagonalErrorBoundaryFraction.den : Int) : Coordinate) := by
      unfold diagonalErrorBoundary
      dsimp only [diagonalErrorBoundaryFraction]
      congr 1
    _ = ((diagonalErrorBoundaryFraction.num : Int) : Coordinate) :=
      RFAP.ConstructiveFraction.ofFraction_mul_den
        diagonalErrorBoundaryFraction
    _ = 13 := by
      dsimp only [diagonalErrorBoundaryFraction]
      exact numeratorCast

private def diagonalErrorLinearCoefficientFraction :
    RFAP.ConstructiveFraction.Fraction :=
  { num := 97, den := 56, den_pos := by decide }

private def diagonalErrorLinearCoefficient : Coordinate :=
  RFAP.ConstructiveFraction.ofFraction
    diagonalErrorLinearCoefficientFraction

private theorem diagonalErrorLinearCoefficient_mul_denominator :
    diagonalErrorLinearCoefficient * 56 = 97 := by
  have numeratorCast :
      (((97 : Nat) : Int) : Coordinate) = (97 : Coordinate) := by
    calc
      (((97 : Nat) : Int) : Coordinate) = ((97 : Nat) : Coordinate) :=
        Int.cast_natCast 97
      _ = (97 : Coordinate) := Nat.cast_ofNat
  calc
    diagonalErrorLinearCoefficient * 56 =
        RFAP.ConstructiveFraction.ofFraction
          diagonalErrorLinearCoefficientFraction *
            ((diagonalErrorLinearCoefficientFraction.den : Int) :
              Coordinate) := by
      unfold diagonalErrorLinearCoefficient
      dsimp only [diagonalErrorLinearCoefficientFraction]
      congr 1
    _ = ((diagonalErrorLinearCoefficientFraction.num : Int) : Coordinate) :=
      RFAP.ConstructiveFraction.ofFraction_mul_den
        diagonalErrorLinearCoefficientFraction
    _ = 97 := by
      dsimp only [diagonalErrorLinearCoefficientFraction]
      exact numeratorCast

private theorem diagonalErrorBoundary_le_half :
    diagonalErrorBoundary ≤ (1 / 2 : Coordinate) := by decide

private theorem diagonalErrorBoundary_polynomial_negative :
    diagonalErrorBoundary ^ 2 - 2 * diagonalErrorBoundary + 1 / 4 < 0 := by
  decide

private theorem twice_diagonalErrorBoundary_le_linearCoefficient :
    diagonalErrorBoundary + diagonalErrorBoundary ≤
      diagonalErrorLinearCoefficient := by
  decide

private theorem diagonalErrorBoundary_quadratic_positive :
    0 < diagonalErrorBoundary ^ 2 -
      diagonalErrorLinearCoefficient * diagonalErrorBoundary + 3 / 14 := by
  decide

private def normTwoIndexOneGapThresholdFraction :
    RFAP.ConstructiveFraction.Fraction :=
  { num := 71, den := 112, den_pos := by decide }

/-- The displayed index-one determinant-gap threshold `71/112` obtained by
adding the first norm-two leading coefficient test. -/
def normTwoIndexOneGapThreshold : Coordinate :=
  RFAP.ConstructiveFraction.ofFraction
    normTwoIndexOneGapThresholdFraction

private def normTwoIndexOneWindowBoundFraction :
    RFAP.ConstructiveFraction.Fraction :=
  { num := 112, den := 71, den_pos := by decide }

/-- The corresponding determinant-index-one squared-window bound `112/71`. -/
def normTwoIndexOneWindowBound : Coordinate :=
  RFAP.ConstructiveFraction.ofFraction
    normTwoIndexOneWindowBoundFraction

/-- The strengthened root-free index-one gap `205/256`. -/
def sharpIndexOneGapBound : Coordinate :=
  RFAP.SharpIndexOneWindow.firstRegionGapBound

/-- The corresponding strengthened squared-window bound `256/205`. -/
def sharpIndexOneWindowBound : Coordinate :=
  RFAP.SharpIndexOneWindow.firstRegionWindowBound

theorem sharpIndexOneGapBound_pos :
    (0 : Coordinate) < sharpIndexOneGapBound :=
  RFAP.SharpIndexOneWindow.firstRegionGapBound_pos

theorem sharpIndexOneWindowBound_mul_gapBound :
    sharpIndexOneWindowBound * sharpIndexOneGapBound = 1 :=
  RFAP.SharpIndexOneWindow.firstRegionWindowBound_mul_gapBound

theorem sharpIndexOneGapBound_mul_denominator :
    sharpIndexOneGapBound * (2 : Coordinate) ^ 8 = 13 * 16 - 3 := by
  simpa only [sharpIndexOneGapBound] using
    RFAP.SharpIndexOneWindow.firstRegionGapBound_mul_denominator

theorem sharpIndexOneWindowBound_mul_denominator :
    sharpIndexOneWindowBound * (13 * 16 - 3 : Coordinate) =
      (2 : Coordinate) ^ 8 := by
  simpa only [sharpIndexOneWindowBound] using
    RFAP.SharpIndexOneWindow.firstRegionWindowBound_mul_denominator

theorem sharpIndexOneWindowBound_eq_dyadicCenteredWindowBound :
    sharpIndexOneWindowBound =
      RFAP.IndexTwoWindow.dyadicCenteredWindowBound := by
  unfold sharpIndexOneWindowBound
    RFAP.SharpIndexOneWindow.firstRegionWindowBound
    RFAP.IndexTwoWindow.dyadicCenteredWindowBound
  apply RFAP.ConstructiveFraction.ofFraction_eq_of_equivalent
  change
    ((2 ^ 8 : Nat) : Int) * ((13 * 16 - 3 : Nat) : Int) =
      ((2 ^ 8 : Nat) : Int) * ((13 * 16 - 3 : Nat) : Int)
  rfl

theorem normTwoIndexOneGapThreshold_mul_denominator :
    normTwoIndexOneGapThreshold * 112 = 71 := by
  unfold normTwoIndexOneGapThreshold normTwoIndexOneGapThresholdFraction
  have clearance := RFAP.ConstructiveFraction.ofFraction_mul_den
    ({ num := 71, den := 112, den_pos := by decide } :
      RFAP.ConstructiveFraction.Fraction)
  simpa only [Int.cast_ofNat] using clearance

theorem normTwoIndexOneWindowBound_mul_denominator :
    normTwoIndexOneWindowBound * 71 = 112 := by
  unfold normTwoIndexOneWindowBound normTwoIndexOneWindowBoundFraction
  have clearance := RFAP.ConstructiveFraction.ofFraction_mul_den
    ({ num := 112, den := 71, den_pos := by decide } :
      RFAP.ConstructiveFraction.Fraction)
  simpa only [Int.cast_ofNat] using clearance

theorem normTwoIndexOneGapThreshold_pos :
    (0 : Coordinate) < normTwoIndexOneGapThreshold := by
  unfold normTwoIndexOneGapThreshold normTwoIndexOneGapThresholdFraction
  change
    RFAP.ConstructiveFraction.LessEqFraction
        RFAP.ConstructiveFraction.zeroFraction ⟨71, 112, by decide⟩ ∧
      ¬RFAP.ConstructiveFraction.LessEqFraction
        ⟨71, 112, by decide⟩ RFAP.ConstructiveFraction.zeroFraction
  decide

theorem normTwoIndexOneWindowBound_mul_gapThreshold :
    normTwoIndexOneWindowBound * normTwoIndexOneGapThreshold = 1 := by
  unfold normTwoIndexOneWindowBound normTwoIndexOneWindowBoundFraction
  unfold normTwoIndexOneGapThreshold normTwoIndexOneGapThresholdFraction
  rw [RFAP.ConstructiveFraction.ofFraction_mulFraction]
  calc
    _ = RFAP.ConstructiveFraction.ofFraction ⟨1, 1, by decide⟩ := by
      apply RFAP.ConstructiveFraction.ofFraction_eq_of_equivalent
      change (112 * 71 : Int) * 1 = 1 * (71 * 112)
      ring1
    _ = 1 := (RFAP.ConstructiveFraction.natCast_eq_fraction 1).symm

theorem normTwoIndexOneWindowBound_eq_centeredIndexTwoWindowBound :
    normTwoIndexOneWindowBound = RFAP.IndexTwoWindow.centeredWindowBound := by
  unfold normTwoIndexOneWindowBound normTwoIndexOneWindowBoundFraction
  unfold RFAP.IndexTwoWindow.centeredWindowBound
  apply RFAP.ConstructiveFraction.ofFraction_eq_of_equivalent
  change (112 * 71 : Int) = 112 * 71
  rfl

private theorem normTwoIndexOneGapThreshold_le_one :
    normTwoIndexOneGapThreshold ≤ 1 := by
  unfold normTwoIndexOneGapThreshold
  rw [show (1 : Coordinate) =
      RFAP.ConstructiveFraction.ofFraction
        RFAP.ConstructiveFraction.oneFraction from
    RFAP.ConstructiveFraction.natCast_eq_fraction 1]
  exact (RFAP.ConstructiveFraction.ofFraction_le_iff _ _).2 (by decide)

private theorem normTwoIndexOneGapThreshold_le_threeQuarters :
    normTwoIndexOneGapThreshold ≤ (3 / 4 : Coordinate) := by
  let threeQuarters : RFAP.ConstructiveFraction.Fraction :=
    ⟨3, 4, by decide⟩
  have threeQuartersDisplay :
      RFAP.ConstructiveFraction.ofFraction threeQuarters =
        (3 / 4 : Coordinate) := by
    simpa only [threeQuarters, Int.cast_ofNat] using
      RFAP.ConstructiveFraction.ofFraction_eq_div threeQuarters
  rw [← threeQuartersDisplay]
  unfold normTwoIndexOneGapThreshold
  exact (RFAP.ConstructiveFraction.ofFraction_le_iff _ _).2 (by decide)

theorem normTwoIndexOneWindowBound_le_two :
    normTwoIndexOneWindowBound ≤ 2 := by
  apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct (c := 71)
  · rw [normTwoIndexOneWindowBound_mul_denominator]
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      RFAP.ConstructiveFraction.natCast_le_direct
        (show 112 ≤ 2 * 71 by decide)
  · exact RFAP.ConstructiveFraction.natCast_pos_direct (by decide)

theorem normTwoIndexOneWindowBound_le_twentyEight_fifteenths :
    normTwoIndexOneWindowBound ≤ (28 / 15 : Coordinate) := by
  apply (RFAP.ConstructiveFraction.le_div_iff_pos
    (RFAP.ConstructiveFraction.natCast_pos_direct
      (show 0 < 15 by decide))).2
  apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct (c := 71)
  · calc
      (normTwoIndexOneWindowBound * 15) * 71 =
          (normTwoIndexOneWindowBound * 71) * 15 := by ring1
      _ = 112 * 15 := by rw [normTwoIndexOneWindowBound_mul_denominator]
      _ ≤ 28 * 71 := by
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using
          RFAP.ConstructiveFraction.natCast_le_direct
            (show 112 * 15 ≤ 28 * 71 by decide)
  · exact RFAP.ConstructiveFraction.natCast_pos_direct (by decide)

private def diagonalErrorBoundaryScalarFraction :
    RFAP.ConstructiveFraction.Fraction :=
  { num := 23859, den := 37636, den_pos := by decide }

private def diagonalErrorBoundaryComplementFraction :
    RFAP.ConstructiveFraction.Fraction :=
  { num := 84, den := 97, den_pos := by decide }

private theorem diagonalErrorBoundaryScalar_representation :
    3 / 4 + diagonalErrorBoundary ^ 2 - diagonalErrorBoundary =
      RFAP.ConstructiveFraction.ofFraction
        diagonalErrorBoundaryScalarFraction := by
  unfold diagonalErrorBoundary diagonalErrorBoundaryFraction
    diagonalErrorBoundaryScalarFraction
  decide

private theorem diagonalErrorBoundaryComplement_representation :
    1 - diagonalErrorBoundary =
      RFAP.ConstructiveFraction.ofFraction
        diagonalErrorBoundaryComplementFraction := by
  unfold diagonalErrorBoundary diagonalErrorBoundaryFraction
    diagonalErrorBoundaryComplementFraction
  decide

private theorem seventyOne_oneHundredTwelfths_le_boundaryScalar :
    normTwoIndexOneGapThreshold ≤
      3 / 4 + diagonalErrorBoundary ^ 2 - diagonalErrorBoundary := by
  rw [diagonalErrorBoundaryScalar_representation]
  unfold normTwoIndexOneGapThreshold
  exact (RFAP.ConstructiveFraction.ofFraction_le_iff _ _).2 (by decide)

private theorem seventyOne_oneHundredTwelfths_le_one_sub_boundary :
    normTwoIndexOneGapThreshold ≤ 1 - diagonalErrorBoundary := by
  rw [diagonalErrorBoundaryComplement_representation]
  unfold normTwoIndexOneGapThreshold
  exact (RFAP.ConstructiveFraction.ofFraction_le_iff _ _).2 (by decide)

/-- The two error-side circle exclusions in the critical first-octant chamber
force the imaginary coordinate below the displayed rational `13/97`.  This is
the square-root-free replacement for locating the smaller root of
`b² - 2b + 1/4`. -/
private theorem imaginary_le_diagonalErrorBoundary_of_diagonalErrorChamber
    (errorRatio : Gaussian)
    (errorRealNonnegative : 0 ≤ errorRatio.re)
    (errorImaginaryNonnegative : 0 ≤ errorRatio.im)
    (errorInside : normSq errorRatio < 1)
    (errorImaginaryObstruction :
      2 * errorRatio.im ≤ normSq errorRatio)
    (errorDiagonalObstruction :
      2 * (errorRatio.re + errorRatio.im) ≤ normSq errorRatio + 1) :
    errorRatio.im ≤ diagonalErrorBoundary := by
  let a := errorRatio.re
  let b := errorRatio.im
  let xNorm := normSq errorRatio
  have aNonnegative : 0 ≤ a := errorRealNonnegative
  have bNonnegative : 0 ≤ b := errorImaginaryNonnegative
  have xNormIdentity : xNorm = a ^ 2 + b ^ 2 := rfl
  have xNormLeOne : xNorm ≤ 1 := errorInside.le
  have aSquareLeNorm : a ^ 2 ≤ xNorm := by
    rw [xNormIdentity]
    exact le_add_of_nonneg_right
      (RFAP.ConstructiveFraction.sq_nonneg_direct b)
  have aSquareLeOne : a ^ 2 ≤ (1 : Coordinate) ^ 2 := by
    simpa only [one_pow] using aSquareLeNorm.trans xNormLeOne
  have aLeOne : a ≤ 1 :=
    RFAP.ConstructiveFraction.le_of_sq_le_sq_direct (by decide) aSquareLeOne
  have twiceBLeOne : 2 * b ≤ 1 :=
    (show 2 * b ≤ xNorm from errorImaginaryObstruction).trans xNormLeOne
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
        RFAP.ConstructiveFraction.sub_nonneg_direct errorImaginaryObstruction
      _ = a ^ 2 - (2 * b - b ^ 2) := by
        rw [xNormIdentity]
        ring1
  have twiceBMinusSquareLeComplementSquare :
      2 * b - b ^ 2 ≤ (1 - a) ^ 2 := by
    apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
    calc
      0 ≤ (xNorm + 1) - 2 * (a + b) :=
        RFAP.ConstructiveFraction.sub_nonneg_direct errorDiagonalObstruction
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
          _ = (1 / 2 : Coordinate) - (1 - a) := by
            calc
              a - 1 / 2 = a + -(1 / 2) := by ring1
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
  by_cases bLe : b ≤ diagonalErrorBoundary
  · exact bLe
  · have boundaryLtB : diagonalErrorBoundary < b := lt_of_not_ge bLe
    have positiveFactor : 0 < b - diagonalErrorBoundary :=
      RFAP.ConstructiveFraction.sub_pos_direct boundaryLtB
    have sumLeOne : b + diagonalErrorBoundary ≤ 1 := by
      have added := RFAP.ConstructiveFraction.add_le_add_direct bLeHalf
        diagonalErrorBoundary_le_half
      exact added.trans_eq (show
        (1 / 2 : Coordinate) + 1 / 2 = 1 by decide)
    have secondFactorNegative : b + diagonalErrorBoundary - 2 < 0 :=
      RFAP.ConstructiveFraction.sub_neg_direct
        (sumLeOne.trans_lt (show (1 : Coordinate) < 2 by decide))
    have productNegative :
        (b - diagonalErrorBoundary) *
          (b + diagonalErrorBoundary - 2) < 0 :=
      RFAP.ConstructiveFraction.mul_neg_of_pos_of_neg_direct
        positiveFactor secondFactorNegative
    have polynomialNegative : b ^ 2 - 2 * b + 1 / 4 < 0 := by
      calc
        b ^ 2 - 2 * b + 1 / 4 =
            (diagonalErrorBoundary ^ 2 -
              2 * diagonalErrorBoundary + 1 / 4) +
              (b - diagonalErrorBoundary) *
                (b + diagonalErrorBoundary - 2) := by ring1
        _ < 0 + 0 := RFAP.ConstructiveFraction.add_lt_add_direct
          diagonalErrorBoundary_polynomial_negative productNegative
        _ = 0 := by ring1
    exact (not_lt_of_ge boundaryPolynomialNonnegative polynomialNegative).elim

private theorem fifteen_twenty_eighths_le_of_diagonalErrorChamber
    (errorRatio denominatorRatio : Gaussian)
    (errorRealNonnegative : 0 ≤ errorRatio.re)
    (errorImaginaryNonnegative : 0 ≤ errorRatio.im)
    (errorImaginaryLeReal : errorRatio.im ≤ errorRatio.re)
    (errorInside : normSq errorRatio < 1)
    (denominatorInside : normSq denominatorRatio < 1)
    (errorImaginaryObstruction :
      2 * errorRatio.im ≤ normSq errorRatio)
    (errorDiagonalObstruction :
      2 * (errorRatio.re + errorRatio.im) ≤ normSq errorRatio + 1)
    (denominatorRealObstruction :
      2 * denominatorRatio.re ≤ normSq denominatorRatio) :
    (15 / 28 : Coordinate) ≤
      normSq (1 - denominatorRatio * errorRatio) := by
  let a := errorRatio.re
  let b := errorRatio.im
  let c := denominatorRatio.re
  let d := denominatorRatio.im
  let xNorm := normSq errorRatio
  let yNorm := normSq denominatorRatio
  let dot := a * c - b * d
  have aNonnegative : 0 ≤ a := errorRealNonnegative
  have bNonnegative : 0 ≤ b := errorImaginaryNonnegative
  have xNormIdentity : xNorm = a ^ 2 + b ^ 2 := rfl
  have yNormIdentity : yNorm = c ^ 2 + d ^ 2 := rfl
  have xNormNonnegative : 0 ≤ xNorm := by
    dsimp only [xNorm]
    exact normSq_nonneg errorRatio
  have yNormNonnegative : 0 ≤ yNorm := by
    dsimp only [yNorm]
    exact normSq_nonneg denominatorRatio
  have xNormLeOne : xNorm ≤ 1 := errorInside.le
  have yNormLeOne : yNorm ≤ 1 := denominatorInside.le
  have oneMinusYNonnegative : 0 ≤ 1 - yNorm :=
    RFAP.ConstructiveFraction.sub_nonneg_direct yNormLeOne
  have yMinusTwiceCNonnegative : 0 ≤ yNorm - 2 * c :=
    RFAP.ConstructiveFraction.sub_nonneg_direct denominatorRealObstruction
  have aSquareLeNorm : a ^ 2 ≤ xNorm := by
    rw [xNormIdentity]
    exact le_add_of_nonneg_right
      (RFAP.ConstructiveFraction.sq_nonneg_direct b)
  have aSquareLeOne : a ^ 2 ≤ (1 : Coordinate) ^ 2 := by
    simpa only [one_pow] using aSquareLeNorm.trans xNormLeOne
  have aLeOne : a ≤ 1 :=
    RFAP.ConstructiveFraction.le_of_sq_le_sq_direct (by decide) aSquareLeOne
  have twiceBLeOne : 2 * b ≤ 1 :=
    (show 2 * b ≤ xNorm from errorImaginaryObstruction).trans xNormLeOne
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
        RFAP.ConstructiveFraction.sub_nonneg_direct errorImaginaryObstruction
      _ = a ^ 2 - (2 * b - b ^ 2) := by
        rw [xNormIdentity]
        ring1
  have twiceBMinusSquareLeComplementSquare :
      2 * b - b ^ 2 ≤ (1 - a) ^ 2 := by
    apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
    calc
      0 ≤ (xNorm + 1) - 2 * (a + b) :=
        RFAP.ConstructiveFraction.sub_nonneg_direct errorDiagonalObstruction
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
          _ = (1 / 2 : Coordinate) - (1 - a) := by
            calc
              a - 1 / 2 = a + -(1 / 2) := by ring1
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
  have bLeRationalBoundary : b ≤ diagonalErrorBoundary := by
    by_cases bLe : b ≤ diagonalErrorBoundary
    · exact bLe
    · have boundaryLtB : diagonalErrorBoundary < b := lt_of_not_ge bLe
      have positiveFactor : 0 < b - diagonalErrorBoundary :=
        RFAP.ConstructiveFraction.sub_pos_direct boundaryLtB
      have sumLeOne : b + diagonalErrorBoundary ≤ 1 := by
        have added := RFAP.ConstructiveFraction.add_le_add_direct bLeHalf
          diagonalErrorBoundary_le_half
        exact added.trans_eq (show
          (1 / 2 : Coordinate) + 1 / 2 = 1 by decide)
      have secondFactorNegative : b + diagonalErrorBoundary - 2 < 0 :=
        RFAP.ConstructiveFraction.sub_neg_direct
          (sumLeOne.trans_lt (show (1 : Coordinate) < 2 by decide))
      have productNegative :
          (b - diagonalErrorBoundary) *
            (b + diagonalErrorBoundary - 2) < 0 :=
        RFAP.ConstructiveFraction.mul_neg_of_pos_of_neg_direct
          positiveFactor secondFactorNegative
      have boundaryValueNegative :
          diagonalErrorBoundary ^ 2 -
            2 * diagonalErrorBoundary + 1 / 4 < 0 :=
        diagonalErrorBoundary_polynomial_negative
      have polynomialNegative : b ^ 2 - 2 * b + 1 / 4 < 0 := by
        calc
          b ^ 2 - 2 * b + 1 / 4 =
              (diagonalErrorBoundary ^ 2 -
                2 * diagonalErrorBoundary + 1 / 4) +
                (b - diagonalErrorBoundary) *
                  (b + diagonalErrorBoundary - 2) := by ring1
          _ < 0 + 0 := RFAP.ConstructiveFraction.add_lt_add_direct
            boundaryValueNegative productNegative
          _ = 0 := by ring1
      exact (not_lt_of_ge boundaryPolynomialNonnegative polynomialNegative).elim
  have decreasingFactorNonnegative :
      0 ≤ diagonalErrorLinearCoefficient - b -
        diagonalErrorBoundary := by
    have sumLe : b + diagonalErrorBoundary ≤
        diagonalErrorLinearCoefficient := by
      calc
      b + diagonalErrorBoundary ≤
          diagonalErrorBoundary + diagonalErrorBoundary :=
        RFAP.ConstructiveFraction.add_le_add_right_direct
          bLeRationalBoundary diagonalErrorBoundary
      _ ≤ diagonalErrorLinearCoefficient :=
        twice_diagonalErrorBoundary_le_linearCoefficient
    apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
    calc
      0 ≤ diagonalErrorLinearCoefficient -
          (b + diagonalErrorBoundary) :=
        RFAP.ConstructiveFraction.sub_nonneg_direct sumLe
      _ = (diagonalErrorLinearCoefficient - b -
          diagonalErrorBoundary) - 0 := by ring1
  have boundaryDifferenceNonnegative : 0 ≤ diagonalErrorBoundary - b :=
    RFAP.ConstructiveFraction.sub_nonneg_direct bLeRationalBoundary
  have boundaryProductNonnegative :
      0 ≤ (diagonalErrorBoundary - b) *
        (diagonalErrorLinearCoefficient - b - diagonalErrorBoundary) :=
    RFAP.ConstructiveFraction.mul_nonneg_direct
      boundaryDifferenceNonnegative decreasingFactorNonnegative
  have boundaryQuadraticPositive :
      0 < diagonalErrorBoundary ^ 2 -
        diagonalErrorLinearCoefficient * diagonalErrorBoundary + 3 / 14 :=
    diagonalErrorBoundary_quadratic_positive
  have bQuadraticNonnegative :
      0 ≤ b ^ 2 - diagonalErrorLinearCoefficient * b + 3 / 14 := by
    calc
      0 ≤ (diagonalErrorBoundary - b) *
          (diagonalErrorLinearCoefficient - b - diagonalErrorBoundary) +
            (diagonalErrorBoundary ^ 2 -
              diagonalErrorLinearCoefficient * diagonalErrorBoundary +
                3 / 14) :=
        add_nonneg boundaryProductNonnegative boundaryQuadraticPositive.le
      _ = b ^ 2 - diagonalErrorLinearCoefficient * b + 3 / 14 := by ring1
  have shiftedSquareIdentity :
      (a - 1 / 2) ^ 2 = a ^ 2 - a + 1 / 4 := by
    calc
      (a - 1 / 2) ^ 2 =
          a ^ 2 - a * (1 / 2 + 1 / 2) + (1 / 2) ^ 2 := by ring1
      _ = a ^ 2 - a * 1 + (1 / 2) ^ 2 := by
        rw [show (1 / 2 : Coordinate) + 1 / 2 = 1 by decide]
      _ = a ^ 2 - a + 1 / 4 := by
        rw [show (1 / 2 : Coordinate) ^ 2 = 1 / 4 by decide]
        ring1
  have scalarLowerBound :
      (15 / 28 : Coordinate) ≤
        1 + xNorm - a - diagonalErrorLinearCoefficient * b := by
    have constantIdentity :
        (1 / 4 : Coordinate) + 3 / 14 = 1 - 15 / 28 := by decide
    apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
    calc
      0 ≤ (a - 1 / 2) ^ 2 +
          (b ^ 2 - diagonalErrorLinearCoefficient * b + 3 / 14) :=
        add_nonneg (RFAP.ConstructiveFraction.sq_nonneg_direct _)
          bQuadraticNonnegative
      _ = a ^ 2 + b ^ 2 - a -
          diagonalErrorLinearCoefficient * b + (1 / 4 + 3 / 14) := by
        rw [shiftedSquareIdentity]
        ring1
      _ = a ^ 2 + b ^ 2 - a -
          diagonalErrorLinearCoefficient * b + (1 - 15 / 28) := by
        rw [constantIdentity]
      _ = (1 + xNorm - a - diagonalErrorLinearCoefficient * b) -
          15 / 28 := by
        rw [xNormIdentity]
        ring1
  have aSquareLeA : a ^ 2 ≤ a := by
    have scaled :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        aLeOne aNonnegative
    calc
      a ^ 2 = a * a := by ring1
      _ ≤ a * 1 := scaled
      _ = a := by ring1
  have sevenBLeFour : 7 * b ≤ 4 := by
    have scaled :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        bLeHalf (show (0 : Coordinate) ≤ 7 by decide)
    calc
      7 * b ≤ 7 * (1 / 2) := scaled
      _ ≤ 4 := by decide
  have sevenBSquareLeFourB : 7 * b ^ 2 ≤ 4 * b := by
    have scaled :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        sevenBLeFour bNonnegative
    calc
      7 * b ^ 2 = b * (7 * b) := by ring1
      _ ≤ b * 4 := scaled
      _ = 4 * b := by ring1
  have sevenASquareLeSevenA : 7 * a ^ 2 ≤ 7 * a :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      aSquareLeA (show (0 : Coordinate) ≤ 7 by decide)
  have sevenNormLeLinear : 7 * xNorm ≤ 7 * a + 4 * b := by
    have added := RFAP.ConstructiveFraction.add_le_add_direct
      sevenASquareLeSevenA sevenBSquareLeFourB
    calc
      7 * xNorm = 7 * a ^ 2 + 7 * b ^ 2 := by
        rw [xNormIdentity]
        ring1
      _ ≤ 7 * a + 4 * b := added
  have sevenAMinusFourBNonnegative : 0 ≤ 7 * a - 4 * b := by
    apply RFAP.ConstructiveFraction.sub_nonneg_direct
    have fourBLeFourA :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (show b ≤ a from errorImaginaryLeReal)
        (show (0 : Coordinate) ≤ 4 by decide)
    exact fourBLeFourA.trans
      (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        (show (4 : Coordinate) ≤ 7 by decide) aNonnegative)
  have sevenAPlusFourBNonnegative : 0 ≤ 7 * a + 4 * b :=
    add_nonneg
      (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide) aNonnegative)
      (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide) bNonnegative)
  let certificate :=
    8 * (7 * a + 4 * b) * (1 - yNorm) +
      8 * (7 * a - 4 * b) * (yNorm - 2 * c) +
      16 * b * (2 * c - 1) ^ 2 +
      b * (8 * d + 7) ^ 2
  have firstTermNonnegative :
      0 ≤ 8 * (7 * a + 4 * b) * (1 - yNorm) :=
    RFAP.ConstructiveFraction.mul_nonneg_direct
      (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        sevenAPlusFourBNonnegative)
      oneMinusYNonnegative
  have secondTermNonnegative :
      0 ≤ 8 * (7 * a - 4 * b) * (yNorm - 2 * c) :=
    RFAP.ConstructiveFraction.mul_nonneg_direct
      (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        sevenAMinusFourBNonnegative)
      yMinusTwiceCNonnegative
  have thirdTermNonnegative :
      0 ≤ 16 * b * (2 * c - 1) ^ 2 :=
    RFAP.ConstructiveFraction.mul_nonneg_direct
      (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide) bNonnegative)
      (RFAP.ConstructiveFraction.sq_nonneg_direct _)
  have fourthTermNonnegative : 0 ≤ b * (8 * d + 7) ^ 2 :=
    RFAP.ConstructiveFraction.mul_nonneg_direct bNonnegative
      (RFAP.ConstructiveFraction.sq_nonneg_direct _)
  have remainingTermsNonnegative :
      0 ≤ 8 * (7 * a - 4 * b) * (yNorm - 2 * c) +
        16 * b * (2 * c - 1) ^ 2 +
        b * (8 * d + 7) ^ 2 :=
    add_nonneg (add_nonneg secondTermNonnegative thirdTermNonnegative)
      fourthTermNonnegative
  have certificateIdentity :
      certificate = 56 * a + 97 * b - 112 * dot := by
    dsimp only [certificate]
    rw [yNormIdentity]
    dsimp only [dot]
    ring1
  have scaledFirstTerm :
      8 * (7 * xNorm) * (1 - yNorm) ≤
        8 * (7 * a + 4 * b) * (1 - yNorm) := by
    have complementScaled :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        sevenNormLeLinear oneMinusYNonnegative
    have eightScaled :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        complementScaled (show (0 : Coordinate) ≤ 8 by decide)
    calc
      8 * (7 * xNorm) * (1 - yNorm) =
          8 * ((7 * xNorm) * (1 - yNorm)) := by ring1
      _ ≤ 8 * ((7 * a + 4 * b) * (1 - yNorm)) := eightScaled
      _ = 8 * (7 * a + 4 * b) * (1 - yNorm) := by ring1
  have scaledNormComplementLeCertificate :
      56 * xNorm * (1 - yNorm) ≤ certificate := by
    calc
      56 * xNorm * (1 - yNorm) =
          8 * (7 * xNorm) * (1 - yNorm) := by ring1
      _ ≤ 8 * (7 * a + 4 * b) * (1 - yNorm) := scaledFirstTerm
      _ ≤ 8 * (7 * a + 4 * b) * (1 - yNorm) +
          (8 * (7 * a - 4 * b) * (yNorm - 2 * c) +
            16 * b * (2 * c - 1) ^ 2 +
            b * (8 * d + 7) ^ 2) :=
        le_add_of_nonneg_right remainingTermsNonnegative
      _ = certificate := by
        dsimp only [certificate]
        ring1
  have scaledNormComplementBound :
      56 * xNorm * (1 - yNorm) ≤
        56 * a + 97 * b - 112 * dot := by
    rw [← certificateIdentity]
    exact scaledNormComplementLeCertificate
  have normComplementBound :
      xNorm * (1 - yNorm) ≤
        a + diagonalErrorLinearCoefficient * b - 2 * dot := by
    apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct (c := 56)
    · calc
        (xNorm * (1 - yNorm)) * 56 =
            56 * xNorm * (1 - yNorm) := by ring1
        _ ≤ 56 * a + 97 * b - 112 * dot :=
          scaledNormComplementBound
        _ = (a + diagonalErrorLinearCoefficient * b - 2 * dot) * 56 := by
          rw [← diagonalErrorLinearCoefficient_mul_denominator]
          ring1
    · calc
        (0 : Coordinate) < 7 * 8 :=
          RFAP.ConstructiveFraction.mul_pos_direct (by decide) (by decide)
        _ = 56 := by ring1
  have algebraicGapLower :
      1 + xNorm - a - diagonalErrorLinearCoefficient * b ≤
        1 + xNorm * yNorm - 2 * dot := by
    have shifted := RFAP.ConstructiveFraction.add_le_add_right_direct
      normComplementBound
      (1 + xNorm * yNorm -
        (a + diagonalErrorLinearCoefficient * b))
    calc
      1 + xNorm - a - diagonalErrorLinearCoefficient * b =
          xNorm * (1 - yNorm) +
            (1 + xNorm * yNorm -
              (a + diagonalErrorLinearCoefficient * b)) := by
        ring1
      _ ≤ (a + diagonalErrorLinearCoefficient * b - 2 * dot) +
          (1 + xNorm * yNorm -
            (a + diagonalErrorLinearCoefficient * b)) := shifted
      _ = 1 + xNorm * yNorm - 2 * dot := by ring1
  have gapExpansion :
      normSq (1 - denominatorRatio * errorRatio) =
        1 + xNorm * yNorm - 2 * dot := by
    dsimp only [xNorm, yNorm, dot, a, b, c, d, normSq]
    simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
      RFAP.ConstructiveGaussian.Gaussian.sub_im,
      RFAP.ConstructiveGaussian.Gaussian.mul_re,
      RFAP.ConstructiveGaussian.Gaussian.mul_im,
      RFAP.ConstructiveGaussian.Gaussian.one_re,
      RFAP.ConstructiveGaussian.Gaussian.one_im]
    ring1
  rw [gapExpansion]
  exact scalarLowerBound.trans algebraicGapLower

/-- Adding the norm-two leading combination supplies the missing second
denominator projection in the critical chamber.  Together with the existing
`13/97` error-coordinate boundary it raises the normalized gap to
`71/112`, without naming the quadratic boundary's irrational root. -/
private theorem seventyOne_oneHundredTwelfths_le_of_diagonalErrorChamber
    (errorRatio denominatorRatio : Gaussian)
    (errorRealNonnegative : 0 ≤ errorRatio.re)
    (errorImaginaryNonnegative : 0 ≤ errorRatio.im)
    (errorImaginaryLeReal : errorRatio.im ≤ errorRatio.re)
    (errorInside : normSq errorRatio < 1)
    (denominatorInside : normSq denominatorRatio < 1)
    (errorImaginaryObstruction :
      2 * errorRatio.im ≤ normSq errorRatio)
    (errorDiagonalObstruction :
      2 * (errorRatio.re + errorRatio.im) ≤ normSq errorRatio + 1)
    (denominatorRealObstruction :
      2 * denominatorRatio.re ≤ normSq denominatorRatio)
    (denominatorDiagonalObstruction :
      2 * (denominatorRatio.re - denominatorRatio.im) ≤
        normSq denominatorRatio + 1) :
    normTwoIndexOneGapThreshold ≤
      normSq (1 - denominatorRatio * errorRatio) := by
  let a := errorRatio.re
  let b := errorRatio.im
  let c := denominatorRatio.re
  let d := denominatorRatio.im
  let xNorm := normSq errorRatio
  let yNorm := normSq denominatorRatio
  let dot := a * c - b * d
  have aNonnegative : 0 ≤ a := errorRealNonnegative
  have bNonnegative : 0 ≤ b := errorImaginaryNonnegative
  have bLeA : b ≤ a := errorImaginaryLeReal
  have xNormIdentity : xNorm = a ^ 2 + b ^ 2 := rfl
  have yNormIdentity : yNorm = c ^ 2 + d ^ 2 := rfl
  have yNormNonnegative : 0 ≤ yNorm := by
    dsimp only [yNorm]
    exact normSq_nonneg denominatorRatio
  have yNormLeOne : yNorm ≤ 1 := denominatorInside.le
  have bLeBoundary : b ≤ diagonalErrorBoundary :=
    imaginary_le_diagonalErrorBoundary_of_diagonalErrorChamber errorRatio
      errorRealNonnegative errorImaginaryNonnegative errorInside
      errorImaginaryObstruction errorDiagonalObstruction
  have boundaryPlusBLeOne : diagonalErrorBoundary + b ≤ 1 := by
    calc
      diagonalErrorBoundary + b ≤
          diagonalErrorBoundary + diagonalErrorBoundary :=
        calc
          diagonalErrorBoundary + b = b + diagonalErrorBoundary := by ring1
          _ ≤ diagonalErrorBoundary + diagonalErrorBoundary :=
            RFAP.ConstructiveFraction.add_le_add_right_direct bLeBoundary
              diagonalErrorBoundary
      _ ≤ (1 / 2 : Coordinate) + 1 / 2 :=
        RFAP.ConstructiveFraction.add_le_add_direct
          diagonalErrorBoundary_le_half diagonalErrorBoundary_le_half
      _ = 1 := by decide
  have firstBoundaryFactorNonnegative :
      0 ≤ diagonalErrorBoundary - b :=
    RFAP.ConstructiveFraction.sub_nonneg_direct bLeBoundary
  have secondBoundaryFactorNonnegative :
      0 ≤ 1 - diagonalErrorBoundary - b := by
    apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
    calc
      0 ≤ 1 - (diagonalErrorBoundary + b) :=
        RFAP.ConstructiveFraction.sub_nonneg_direct boundaryPlusBLeOne
      _ = (1 - diagonalErrorBoundary - b) - 0 := by ring1
  have boundaryProductNonnegative :
      0 ≤ (diagonalErrorBoundary - b) *
        (1 - diagonalErrorBoundary - b) :=
    RFAP.ConstructiveFraction.mul_nonneg_direct
      firstBoundaryFactorNonnegative secondBoundaryFactorNonnegative
  have boundaryQuadraticLe :
      diagonalErrorBoundary ^ 2 - diagonalErrorBoundary ≤ b ^ 2 - b := by
    apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
    calc
      0 ≤ (diagonalErrorBoundary - b) *
          (1 - diagonalErrorBoundary - b) := boundaryProductNonnegative
      _ = (b ^ 2 - b) -
          (diagonalErrorBoundary ^ 2 - diagonalErrorBoundary) := by ring1
  have displayedBoundaryLower :
      normTwoIndexOneGapThreshold ≤
        3 / 4 + diagonalErrorBoundary ^ 2 - diagonalErrorBoundary :=
    seventyOne_oneHundredTwelfths_le_boundaryScalar
  have scalarLowerBound :
      normTwoIndexOneGapThreshold ≤ 1 + xNorm - a - b := by
    have shiftedSquareNonnegative : 0 ≤ (a - 1 / 2) ^ 2 :=
      RFAP.ConstructiveFraction.sq_nonneg_direct _
    have shiftedBoundary :=
      RFAP.ConstructiveFraction.add_le_add_right_direct boundaryQuadraticLe
        (3 / 4 : Coordinate)
    calc
      normTwoIndexOneGapThreshold ≤
          3 / 4 + diagonalErrorBoundary ^ 2 - diagonalErrorBoundary :=
        displayedBoundaryLower
      _ = 3 / 4 +
          (diagonalErrorBoundary ^ 2 - diagonalErrorBoundary) := by ring1
      _ ≤ 3 / 4 + (b ^ 2 - b) := by
        calc
          3 / 4 +
              (diagonalErrorBoundary ^ 2 - diagonalErrorBoundary) =
            (diagonalErrorBoundary ^ 2 - diagonalErrorBoundary) + 3 / 4 := by
              ring1
          _ ≤ (b ^ 2 - b) + 3 / 4 := shiftedBoundary
          _ = 3 / 4 + (b ^ 2 - b) := by ring1
      _ ≤ (a - 1 / 2) ^ 2 + (3 / 4 + (b ^ 2 - b)) :=
        le_add_of_nonneg_left shiftedSquareNonnegative
      _ = 1 + xNorm - a - b := by
        rw [xNormIdentity]
        calc
          (a - 1 / 2) ^ 2 + (3 / 4 + (b ^ 2 - b)) =
              (a ^ 2 - a + 1 / 4) + (3 / 4 + (b ^ 2 - b)) := by
            congr 1
            calc
              (a - 1 / 2) ^ 2 =
                  a ^ 2 - 2 * a * (1 / 2) + (1 / 2) ^ 2 := by
                ring1
              _ = a ^ 2 - a * (2 * (1 / 2)) + (1 / 2) ^ 2 := by
                ring1
              _ = a ^ 2 - a + 1 / 4 := by
                rw [show (2 : Coordinate) * (1 / 2) = 1 by decide,
                  show (1 / 2 : Coordinate) ^ 2 = 1 / 4 by decide]
                ring1
          _ = a ^ 2 + b ^ 2 - a - b + (1 / 4 + 3 / 4) := by
            ring1
          _ = 1 + (a ^ 2 + b ^ 2) - a - b := by
            rw [show (1 / 4 : Coordinate) + 3 / 4 = 1 by decide]
            ring1
  have aMinusBNonnegative : 0 ≤ a - b :=
    RFAP.ConstructiveFraction.sub_nonneg_direct bLeA
  have realProjectionScaled :
      2 * (a - b) * c ≤ (a - b) * yNorm := by
    have scaled :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        denominatorRealObstruction aMinusBNonnegative
    calc
      2 * (a - b) * c = (a - b) * (2 * c) := by ring1
      _ ≤ (a - b) * yNorm := scaled
  have diagonalProjectionScaled :
      2 * b * (c - d) ≤ b * (yNorm + 1) := by
    have scaled :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        denominatorDiagonalObstruction bNonnegative
    calc
      2 * b * (c - d) = b * (2 * (c - d)) := by ring1
      _ ≤ b * (yNorm + 1) := scaled
  have twiceDotLe : 2 * dot ≤ a * yNorm + b := by
    have added := RFAP.ConstructiveFraction.add_le_add_direct
      realProjectionScaled diagonalProjectionScaled
    calc
      2 * dot = 2 * (a - b) * c + 2 * b * (c - d) := by
        dsimp only [dot]
        ring1
      _ ≤ (a - b) * yNorm + b * (yNorm + 1) := added
      _ = a * yNorm + b := by ring1
  have projectedGapLower :
      1 + xNorm * yNorm - a * yNorm - b ≤
        1 + xNorm * yNorm - 2 * dot := by
    apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
    calc
      0 ≤ (a * yNorm + b) - 2 * dot :=
        RFAP.ConstructiveFraction.sub_nonneg_direct twiceDotLe
      _ = (1 + xNorm * yNorm - 2 * dot) -
          (1 + xNorm * yNorm - a * yNorm - b) := by ring1
  have targetLeProjected :
      normTwoIndexOneGapThreshold ≤
        1 + xNorm * yNorm - a * yNorm - b := by
    by_cases xNormLeA : xNorm ≤ a
    · have aMinusXNonnegative : 0 ≤ a - xNorm :=
        RFAP.ConstructiveFraction.sub_nonneg_direct xNormLeA
      have oneMinusYNonnegative : 0 ≤ 1 - yNorm :=
        RFAP.ConstructiveFraction.sub_nonneg_direct yNormLeOne
      have correctionNonnegative :
          0 ≤ (1 - yNorm) * (a - xNorm) :=
        RFAP.ConstructiveFraction.mul_nonneg_direct
          oneMinusYNonnegative aMinusXNonnegative
      calc
        normTwoIndexOneGapThreshold ≤ 1 + xNorm - a - b :=
          scalarLowerBound
        _ ≤ 1 + xNorm * yNorm - a * yNorm - b := by
          apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
          calc
            0 ≤ (1 - yNorm) * (a - xNorm) := correctionNonnegative
            _ = (1 + xNorm * yNorm - a * yNorm - b) -
                (1 + xNorm - a - b) := by ring1
    · have aLeXNorm : a ≤ xNorm := le_of_not_ge xNormLeA
      have xMinusANonnegative : 0 ≤ xNorm - a :=
        RFAP.ConstructiveFraction.sub_nonneg_direct aLeXNorm
      have correctionNonnegative : 0 ≤ yNorm * (xNorm - a) :=
        RFAP.ConstructiveFraction.mul_nonneg_direct yNormNonnegative
          xMinusANonnegative
      have targetLeOneMinusB :
          normTwoIndexOneGapThreshold ≤ 1 - b := by
        calc
          normTwoIndexOneGapThreshold ≤ 1 - diagonalErrorBoundary := by
            exact seventyOne_oneHundredTwelfths_le_one_sub_boundary
          _ ≤ 1 - b := by
            have negated :=
              RFAP.ConstructiveFraction.neg_le_neg_direct bLeBoundary
            have shifted :=
              RFAP.ConstructiveFraction.add_le_add_right_direct negated 1
            calc
              1 - diagonalErrorBoundary =
                  -diagonalErrorBoundary + 1 := by ring1
              _ ≤ -b + 1 := shifted
              _ = 1 - b := by ring1
      calc
        normTwoIndexOneGapThreshold ≤ 1 - b := targetLeOneMinusB
        _ ≤ 1 + xNorm * yNorm - a * yNorm - b := by
          apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
          calc
            0 ≤ yNorm * (xNorm - a) := correctionNonnegative
            _ = (1 + xNorm * yNorm - a * yNorm - b) -
                (1 - b) := by ring1
  have gapExpansion :
      normSq (1 - denominatorRatio * errorRatio) =
        1 + xNorm * yNorm - 2 * dot := by
    dsimp only [xNorm, yNorm, dot, a, b, c, d, normSq]
    simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
      RFAP.ConstructiveGaussian.Gaussian.sub_im,
      RFAP.ConstructiveGaussian.Gaussian.mul_re,
      RFAP.ConstructiveGaussian.Gaussian.mul_im,
      RFAP.ConstructiveGaussian.Gaussian.one_re,
      RFAP.ConstructiveGaussian.Gaussian.one_im]
    ring1
  rw [gapExpansion]
  exact targetLeProjected.trans projectedGapLower

private theorem coefficientExterior_of_linearCombinationExterior
    (errorRatio denominatorRatio : Gaussian)
    (linearCombinationExterior :
      ∀ leftCoefficient rightCoefficient : GaussianInt,
        leftCoefficient ≠ 0 ∨ rightCoefficient ≠ 0 →
          (1 : Coordinate) ≤
              normSq
                (toGaussian leftCoefficient +
                  toGaussian rightCoefficient * errorRatio) ∨
            1 ≤
              normSq
                (toGaussian leftCoefficient * denominatorRatio +
                  toGaussian rightCoefficient)) :
    ∀ coefficient : GaussianInt,
      (1 : Coordinate) ≤ normSq (errorRatio - toGaussian coefficient) ∨
        1 ≤ normSq (1 - toGaussian coefficient * denominatorRatio) := by
  intro coefficient
  rcases linearCombinationExterior (-coefficient) 1
      (Or.inr (by decide)) with errorExterior | denominatorExterior
  · left
    have identity :
        toGaussian (-coefficient) + toGaussian (1 : GaussianInt) * errorRatio =
          errorRatio - toGaussian coefficient := by
      rw [toGaussian_neg, toGaussian_one,
        RFAP.ConstructiveGaussian.Gaussian.one_mul]
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
          RFAP.ConstructiveGaussian.Gaussian.add_im,
          RFAP.ConstructiveGaussian.Gaussian.sub_re,
          RFAP.ConstructiveGaussian.Gaussian.sub_im,
          RFAP.ConstructiveGaussian.Gaussian.neg_re,
          RFAP.ConstructiveGaussian.Gaussian.neg_im] <;>
        ring1
    rw [← identity]
    exact errorExterior
  · right
    have identity :
        toGaussian (-coefficient) * denominatorRatio +
            toGaussian (1 : GaussianInt) =
          1 - toGaussian coefficient * denominatorRatio := by
      rw [toGaussian_neg, toGaussian_one]
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
          RFAP.ConstructiveGaussian.Gaussian.add_im,
          RFAP.ConstructiveGaussian.Gaussian.sub_re,
          RFAP.ConstructiveGaussian.Gaussian.sub_im,
          RFAP.ConstructiveGaussian.Gaussian.mul_re,
          RFAP.ConstructiveGaussian.Gaussian.mul_im,
          RFAP.ConstructiveGaussian.Gaussian.neg_re,
          RFAP.ConstructiveGaussian.Gaussian.neg_im,
          RFAP.ConstructiveGaussian.Gaussian.one_re,
          RFAP.ConstructiveGaussian.Gaussian.one_im] <;>
        ring1
    rw [← identity]
    exact denominatorExterior

private theorem firstOctant_errorRatio_eq_zero_of_normTwoExterior
    (errorRatio : Gaussian)
    (realNonnegative : 0 ≤ errorRatio.re)
    (imaginaryNonnegative : 0 ≤ errorRatio.im)
    (imaginaryLeReal : errorRatio.im ≤ errorRatio.re)
    (errorInside : normSq errorRatio < 1)
    (normTwoErrorExterior :
      (1 : Coordinate) ≤
        normSq
          (1 - toGaussian
            (1 - RFAP.HurwitzGeometry.imaginaryUnit) * errorRatio)) :
    errorRatio = 0 := by
  let a := errorRatio.re
  let b := errorRatio.im
  let xNorm := normSq errorRatio
  have aNonnegative : 0 ≤ a := realNonnegative
  have bNonnegative : 0 ≤ b := imaginaryNonnegative
  have bLeA : b ≤ a := imaginaryLeReal
  have xNormIdentity : xNorm = a ^ 2 + b ^ 2 := rfl
  have sumLeNorm : a + b ≤ xNorm := by
    have twiceSumLeTwiceNorm :
        2 * (a + b) ≤ 2 * xNorm := by
      apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
      calc
        0 ≤ normSq
              (1 - toGaussian
                (1 - RFAP.HurwitzGeometry.imaginaryUnit) * errorRatio) - 1 :=
          RFAP.ConstructiveFraction.sub_nonneg_direct normTwoErrorExterior
        _ = 2 * xNorm - 2 * (a + b) := by
          dsimp only [xNorm, normSq, toGaussian,
            RFAP.HurwitzGeometry.imaginaryUnit]
          simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
            RFAP.ConstructiveGaussian.Gaussian.sub_im,
            RFAP.ConstructiveGaussian.Gaussian.mul_re,
            RFAP.ConstructiveGaussian.Gaussian.mul_im,
            RFAP.ConstructiveGaussian.Gaussian.one_re,
            RFAP.ConstructiveGaussian.Gaussian.one_im,
            RFAP.ConstructiveGaussianHeight.GaussianInt.sub_re,
            RFAP.ConstructiveGaussianHeight.GaussianInt.sub_im,
            RFAP.ConstructiveGaussianHeight.GaussianInt.one_re,
            RFAP.ConstructiveGaussianHeight.GaussianInt.one_im,
            Int.cast_sub, Int.cast_one, Int.cast_zero]
          ring1
    apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct (c := 2)
    · calc
        (a + b) * 2 = 2 * (a + b) := by ring1
        _ ≤ 2 * xNorm := twiceSumLeTwiceNorm
        _ = xNorm * 2 := by ring1
    · decide
  have aNonpositive : a ≤ 0 := by
    by_cases aPositive : 0 < a
    · have aSquareLeNorm : a ^ 2 ≤ xNorm := by
        rw [xNormIdentity]
        exact le_add_of_nonneg_right
          (RFAP.ConstructiveFraction.sq_nonneg_direct b)
      have aSquareLtOne : a ^ 2 < 1 :=
        lt_of_le_of_lt aSquareLeNorm errorInside
      have aLtOne : a < 1 := by
        by_cases oneLeA : 1 ≤ a
        · have oneLeASquare : (1 : Coordinate) ≤ a ^ 2 := by
            calc
              (1 : Coordinate) = 1 ^ 2 := by ring1
              _ ≤ a ^ 2 :=
                RFAP.ConstructiveFraction.pow_le_pow_direct (by decide)
                  oneLeA 2
          exact ((not_lt_of_ge oneLeASquare) aSquareLtOne).elim
        · exact lt_of_not_ge oneLeA
      have aSquareLtA : a ^ 2 < a := by
        have scaled :=
          RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
            aPositive aLtOne
        calc
          a ^ 2 = a * a := by ring1
          _ < a * 1 := scaled
          _ = a := by ring1
      have bLeOne : b ≤ 1 := bLeA.trans aLtOne.le
      have bSquareLeB : b ^ 2 ≤ b := by
        have scaled :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            bLeOne bNonnegative
        calc
          b ^ 2 = b * b := by ring1
          _ ≤ b * 1 := scaled
          _ = b := by ring1
      have normLtSum : xNorm < a + b := by
        rw [xNormIdentity]
        have firstStep :=
          RFAP.ConstructiveFraction.add_lt_add_right_direct aSquareLtA
            (b ^ 2)
        have secondStep : a + b ^ 2 ≤ a + b := by
          calc
            a + b ^ 2 = b ^ 2 + a := by ring1
            _ ≤ b + a :=
              RFAP.ConstructiveFraction.add_le_add_right_direct bSquareLeB a
            _ = a + b := by ring1
        exact firstStep.trans_le secondStep
      exact ((not_lt_of_ge sumLeNorm) normLtSum).elim
    · exact le_of_not_gt aPositive
  have aZero : a = 0 := le_antisymm aNonpositive aNonnegative
  have bZero : b = 0 := by
    apply le_antisymm
    · simpa only [aZero] using bLeA
    · exact bNonnegative
  apply RFAP.ConstructiveGaussian.Gaussian.ext
  · exact aZero
  · exact bZero

/-- Three neighbouring coefficient exclusions in the first octant force a
half-unit normalized determinant gap.  The proof is entirely coordinatewise.
The alternatives correspond respectively to coefficients `1`, `i`, and
`1+i`.
-/
theorem half_le_determinantGap_of_firstOctantObstructions
    (errorRatio denominatorRatio : Gaussian)
    (realNonnegative : 0 ≤ errorRatio.re)
    (imaginaryNonnegative : 0 ≤ errorRatio.im)
    (imaginaryLeReal : errorRatio.im ≤ errorRatio.re)
    (errorInside : normSq errorRatio < 1)
    (denominatorInside : normSq denominatorRatio < 1)
    (coefficientExterior : ∀ coefficient : GaussianInt,
      (1 : Coordinate) ≤ normSq (errorRatio - toGaussian coefficient) ∨
        1 ≤ normSq (1 - toGaussian coefficient * denominatorRatio)) :
    (1 / 2 : Coordinate) ≤
      normSq (1 - denominatorRatio * errorRatio) := by
  let xNorm := normSq errorRatio
  let yNorm := normSq denominatorRatio
  let dot := errorRatio.re * denominatorRatio.re -
    errorRatio.im * denominatorRatio.im
  have xNormLeOne : xNorm ≤ 1 := (show xNorm < 1 from errorInside).le
  have yNormLeOne : yNorm ≤ 1 :=
    (show yNorm < 1 from denominatorInside).le
  have yNormNonnegative : 0 ≤ yNorm := by
    dsimp only [yNorm]
    exact normSq_nonneg denominatorRatio
  have realSquareLeNorm : errorRatio.re ^ 2 ≤ xNorm := by
    dsimp only [xNorm, normSq]
    exact le_add_of_nonneg_right
      (RFAP.ConstructiveFraction.sq_nonneg_direct errorRatio.im)
  have realSquareLeOne : errorRatio.re ^ 2 ≤ (1 : Coordinate) ^ 2 := by
    simpa only [one_pow] using realSquareLeNorm.trans xNormLeOne
  have realLeOne : errorRatio.re ≤ 1 :=
    RFAP.ConstructiveFraction.le_of_sq_le_sq_direct (by decide)
      realSquareLeOne
  have realLtOne : errorRatio.re < 1 := by
    by_cases realEqualsOne : errorRatio.re = 1
    · have oneLeXNorm : (1 : Coordinate) ≤ xNorm := by
        calc
          (1 : Coordinate) = errorRatio.re ^ 2 := by rw [realEqualsOne]; ring1
          _ ≤ xNorm := realSquareLeNorm
      exact ((not_lt_of_ge oneLeXNorm) errorInside).elim
    · exact lt_of_le_of_ne realLeOne realEqualsOne
  have twiceRealLeOnePlusNorm :
      2 * errorRatio.re ≤ 1 + xNorm := by
    apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
    calc
      0 ≤ (1 - errorRatio.re) ^ 2 + errorRatio.im ^ 2 :=
        add_nonneg
          (RFAP.ConstructiveFraction.sq_nonneg_direct _)
          (RFAP.ConstructiveFraction.sq_nonneg_direct _)
      _ = (1 + xNorm) - 2 * errorRatio.re := by
        dsimp only [xNorm, normSq]
        ring1
  have twiceSumLeOnePlusTwiceNorm :
      2 * (errorRatio.re + errorRatio.im) ≤ 1 + 2 * xNorm := by
    have squareSumNonnegative :
        0 ≤ (2 * errorRatio.re - 1) ^ 2 +
          (2 * errorRatio.im - 1) ^ 2 :=
      add_nonneg
        (RFAP.ConstructiveFraction.sq_nonneg_direct _)
        (RFAP.ConstructiveFraction.sq_nonneg_direct _)
    have scaledDifferenceNonnegative :
        0 ≤ ((1 + 2 * xNorm) -
          2 * (errorRatio.re + errorRatio.im)) * 2 := by
      calc
        0 ≤ (2 * errorRatio.re - 1) ^ 2 +
            (2 * errorRatio.im - 1) ^ 2 := squareSumNonnegative
        _ = ((1 + 2 * xNorm) -
            2 * (errorRatio.re + errorRatio.im)) * 2 := by
          dsimp only [xNorm, normSq]
          ring1
    have differenceNonnegative :
        0 ≤ (1 + 2 * xNorm) -
          2 * (errorRatio.re + errorRatio.im) := by
      apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct (c := 2)
      · calc
          (0 : Coordinate) * 2 = 0 := by ring1
          _ ≤ ((1 + 2 * xNorm) -
              2 * (errorRatio.re + errorRatio.im)) * 2 :=
            scaledDifferenceNonnegative
      · decide
    exact RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
      differenceNonnegative
  have negTwiceImagLeNormPlusOne :
      -2 * denominatorRatio.im ≤ yNorm + 1 := by
    apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
    calc
      0 ≤ (denominatorRatio.im + 1) ^ 2 +
          denominatorRatio.re ^ 2 :=
        add_nonneg
          (RFAP.ConstructiveFraction.sq_nonneg_direct _)
          (RFAP.ConstructiveFraction.sq_nonneg_direct _)
      _ = (yNorm + 1) - (-2 * denominatorRatio.im) := by
        dsimp only [yNorm, normSq]
        ring1
  have gapExpansion :
      normSq (1 - denominatorRatio * errorRatio) =
        1 + xNorm * yNorm - 2 * dot := by
    dsimp only [xNorm, yNorm, dot, normSq]
    simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
      RFAP.ConstructiveGaussian.Gaussian.sub_im,
      RFAP.ConstructiveGaussian.Gaussian.mul_re,
      RFAP.ConstructiveGaussian.Gaussian.mul_im,
      RFAP.ConstructiveGaussian.Gaussian.one_re,
      RFAP.ConstructiveGaussian.Gaussian.one_im]
    ring1
  rcases coefficientExterior 1 with errorOneExterior | denominatorOneExterior
  · have twiceRealLeNorm : 2 * errorRatio.re ≤ xNorm := by
      apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
      calc
        0 ≤ normSq (errorRatio - toGaussian (1 : GaussianInt)) - 1 :=
          RFAP.ConstructiveFraction.sub_nonneg_direct errorOneExterior
        _ = xNorm - 2 * errorRatio.re := by
          dsimp only [xNorm, normSq, toGaussian]
          simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
            RFAP.ConstructiveGaussian.Gaussian.sub_im,
            RFAP.ConstructiveGaussianHeight.GaussianInt.one_re,
            RFAP.ConstructiveGaussianHeight.GaussianInt.one_im,
            Int.cast_one, Int.cast_zero]
          ring1
    have imaginarySquareLeRealSquare :
        errorRatio.im ^ 2 ≤ errorRatio.re ^ 2 :=
      RFAP.ConstructiveFraction.pow_le_pow_direct imaginaryNonnegative
        imaginaryLeReal 2
    have normLeTwiceRealSquare :
        xNorm ≤ 2 * errorRatio.re ^ 2 := by
      dsimp only [xNorm, normSq]
      calc
        errorRatio.re ^ 2 + errorRatio.im ^ 2 ≤
            errorRatio.re ^ 2 + errorRatio.re ^ 2 :=
          RFAP.ConstructiveFraction.add_le_add_direct le_rfl
            imaginarySquareLeRealSquare
        _ = 2 * errorRatio.re ^ 2 := by ring1
    have twiceRealLeTwiceRealSquare :
        2 * errorRatio.re ≤ 2 * errorRatio.re ^ 2 :=
      twiceRealLeNorm.trans normLeTwiceRealSquare
    have realLeRealSquare :
        errorRatio.re ≤ errorRatio.re ^ 2 := by
      apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct (c := 2)
      · calc
          errorRatio.re * 2 = 2 * errorRatio.re := by ring1
          _ ≤ 2 * errorRatio.re ^ 2 := twiceRealLeTwiceRealSquare
          _ = errorRatio.re ^ 2 * 2 := by ring1
      · decide
    have oneMinusRealPositive : 0 < 1 - errorRatio.re :=
      RFAP.ConstructiveFraction.sub_pos_direct realLtOne
    have realTimesGapNonpositive :
        errorRatio.re * (1 - errorRatio.re) ≤
          0 * (1 - errorRatio.re) := by
      apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
      calc
        0 ≤ errorRatio.re ^ 2 - errorRatio.re :=
          RFAP.ConstructiveFraction.sub_nonneg_direct realLeRealSquare
        _ = 0 * (1 - errorRatio.re) -
            errorRatio.re * (1 - errorRatio.re) := by ring1
    have realNonpositive : errorRatio.re ≤ 0 :=
      RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct
        realTimesGapNonpositive oneMinusRealPositive
    have realZero : errorRatio.re = 0 :=
      le_antisymm realNonpositive realNonnegative
    have imaginaryZero : errorRatio.im = 0 := by
      apply le_antisymm
      · simpa only [realZero] using imaginaryLeReal
      · exact imaginaryNonnegative
    have errorRatioZero : errorRatio = 0 := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext
      · exact realZero
      · exact imaginaryZero
    rw [errorRatioZero, RFAP.ConstructiveGaussian.Gaussian.mul_zero,
      RFAP.ConstructiveGaussian.Gaussian.sub_zero, normSq_one]
    decide
  · have twiceDenominatorRealLeNorm :
        2 * denominatorRatio.re ≤ yNorm := by
      apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
      calc
        0 ≤ normSq (1 - toGaussian (1 : GaussianInt) * denominatorRatio) - 1 :=
          RFAP.ConstructiveFraction.sub_nonneg_direct denominatorOneExterior
        _ = yNorm - 2 * denominatorRatio.re := by
          dsimp only [yNorm, normSq, toGaussian]
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
    rcases coefficientExterior RFAP.HurwitzGeometry.imaginaryUnit with
        errorImaginaryExterior | denominatorImaginaryExterior
    · have twiceImaginaryLeNorm : 2 * errorRatio.im ≤ xNorm := by
        apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
        calc
          0 ≤ normSq
              (errorRatio -
                toGaussian RFAP.HurwitzGeometry.imaginaryUnit) - 1 :=
            RFAP.ConstructiveFraction.sub_nonneg_direct errorImaginaryExterior
          _ = xNorm - 2 * errorRatio.im := by
            dsimp only [xNorm, normSq, toGaussian,
              RFAP.HurwitzGeometry.imaginaryUnit]
            simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
              RFAP.ConstructiveGaussian.Gaussian.sub_im, Int.cast_one,
              Int.cast_zero]
            ring1
      rcases coefficientExterior
          (1 + RFAP.HurwitzGeometry.imaginaryUnit) with
          errorDiagonalExterior | denominatorDiagonalExterior
      · have twiceSumLeNormPlusOne :
            2 * (errorRatio.re + errorRatio.im) ≤ xNorm + 1 := by
          apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
          calc
            0 ≤ normSq
                (errorRatio - toGaussian
                  (1 + RFAP.HurwitzGeometry.imaginaryUnit)) - 1 :=
              RFAP.ConstructiveFraction.sub_nonneg_direct errorDiagonalExterior
            _ = (xNorm + 1) -
                2 * (errorRatio.re + errorRatio.im) := by
              dsimp only [xNorm, normSq, toGaussian,
                RFAP.HurwitzGeometry.imaginaryUnit]
              simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
                RFAP.ConstructiveGaussian.Gaussian.sub_im,
                RFAP.ConstructiveGaussianHeight.GaussianInt.add_re,
                RFAP.ConstructiveGaussianHeight.GaussianInt.add_im,
                RFAP.ConstructiveGaussianHeight.GaussianInt.one_re,
                RFAP.ConstructiveGaussianHeight.GaussianInt.one_im,
                Int.cast_add, Int.cast_one, Int.cast_zero]
              ring1
        have realScaled :
            2 * errorRatio.re * denominatorRatio.re ≤
              errorRatio.re * yNorm := by
          have scaled :=
            RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
              twiceDenominatorRealLeNorm realNonnegative
          calc
            2 * errorRatio.re * denominatorRatio.re =
                errorRatio.re * (2 * denominatorRatio.re) := by ring1
            _ ≤ errorRatio.re * yNorm := scaled
        have imaginaryScaled :
            -2 * errorRatio.im * denominatorRatio.im ≤
              errorRatio.im * (yNorm + 1) := by
          have scaled :=
            RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
              negTwiceImagLeNormPlusOne imaginaryNonnegative
          calc
            -2 * errorRatio.im * denominatorRatio.im =
                errorRatio.im * (-2 * denominatorRatio.im) := by ring1
            _ ≤ errorRatio.im * (yNorm + 1) := scaled
        have summedDotBound :
            2 * dot ≤
              yNorm * (errorRatio.re + errorRatio.im) + errorRatio.im := by
          have added := RFAP.ConstructiveFraction.add_le_add_direct
            realScaled imaginaryScaled
          dsimp only [dot]
          calc
            2 * (errorRatio.re * denominatorRatio.re -
                errorRatio.im * denominatorRatio.im) =
                2 * errorRatio.re * denominatorRatio.re +
                  (-2 * errorRatio.im * denominatorRatio.im) := by ring1
            _ ≤ errorRatio.re * yNorm +
                errorRatio.im * (yNorm + 1) := added
            _ = yNorm * (errorRatio.re + errorRatio.im) +
                errorRatio.im := by ring1
        have sumScaled :
            2 * (yNorm * (errorRatio.re + errorRatio.im)) ≤
              yNorm * (xNorm + 1) := by
          have scaled :=
            RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
              twiceSumLeNormPlusOne yNormNonnegative
          calc
            2 * (yNorm * (errorRatio.re + errorRatio.im)) =
                yNorm * (2 * (errorRatio.re + errorRatio.im)) := by ring1
            _ ≤ yNorm * (xNorm + 1) := scaled
        have doubledDotBound :
            4 * dot ≤
              2 * (yNorm * (errorRatio.re + errorRatio.im) +
                errorRatio.im) := by
          have scaled :=
            RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
              summedDotBound (show (0 : Coordinate) ≤ 2 by decide)
          calc
            4 * dot = (2 * dot) * 2 := by ring1
            _ ≤ (yNorm * (errorRatio.re + errorRatio.im) +
                errorRatio.im) * 2 := scaled
            _ = 2 * (yNorm * (errorRatio.re + errorRatio.im) +
                errorRatio.im) := by ring1
        have boundaryDotBound :
            4 * dot ≤ yNorm * (xNorm + 1) + xNorm := by
          calc
            4 * dot ≤
                2 * (yNorm * (errorRatio.re + errorRatio.im) +
                  errorRatio.im) := doubledDotBound
            _ = 2 * (yNorm * (errorRatio.re + errorRatio.im)) +
                2 * errorRatio.im := by ring1
            _ ≤ yNorm * (xNorm + 1) + xNorm :=
              RFAP.ConstructiveFraction.add_le_add_direct sumScaled
                twiceImaginaryLeNorm
        rw [gapExpansion]
        exact half_le_of_fourDot_le_boundary xNorm yNorm dot xNormLeOne
          yNormLeOne boundaryDotBound
      · have twiceDiagonalProjection :
            2 * (denominatorRatio.re - denominatorRatio.im) ≤
              2 * yNorm := by
          apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
          calc
            0 ≤ normSq
                (1 - toGaussian
                  (1 + RFAP.HurwitzGeometry.imaginaryUnit) *
                    denominatorRatio) - 1 :=
              RFAP.ConstructiveFraction.sub_nonneg_direct
                denominatorDiagonalExterior
            _ = 2 * yNorm -
                2 * (denominatorRatio.re - denominatorRatio.im) := by
              dsimp only [yNorm, normSq, toGaussian,
                RFAP.HurwitzGeometry.imaginaryUnit]
              simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
                RFAP.ConstructiveGaussian.Gaussian.sub_im,
                RFAP.ConstructiveGaussian.Gaussian.mul_re,
                RFAP.ConstructiveGaussian.Gaussian.mul_im,
                RFAP.ConstructiveGaussian.Gaussian.one_re,
                RFAP.ConstructiveGaussian.Gaussian.one_im,
                RFAP.ConstructiveGaussianHeight.GaussianInt.add_re,
                RFAP.ConstructiveGaussianHeight.GaussianInt.add_im,
                RFAP.ConstructiveGaussianHeight.GaussianInt.one_re,
                RFAP.ConstructiveGaussianHeight.GaussianInt.one_im,
                Int.cast_add, Int.cast_one, Int.cast_zero]
              ring1
        have diagonalProjection :
            denominatorRatio.re - denominatorRatio.im ≤ yNorm := by
          apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct
            (c := 2)
          · calc
              (denominatorRatio.re - denominatorRatio.im) * 2 =
                  2 * (denominatorRatio.re - denominatorRatio.im) := by
                ring1
              _ ≤ 2 * yNorm := twiceDiagonalProjection
              _ = yNorm * 2 := by ring1
          · decide
        have realDifferenceNonnegative :
            0 ≤ errorRatio.re - errorRatio.im :=
          RFAP.ConstructiveFraction.sub_nonneg_direct imaginaryLeReal
        have realScaled :
            2 * (errorRatio.re - errorRatio.im) *
                denominatorRatio.re ≤
              (errorRatio.re - errorRatio.im) * yNorm := by
          have scaled :=
            RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
              twiceDenominatorRealLeNorm realDifferenceNonnegative
          calc
            2 * (errorRatio.re - errorRatio.im) * denominatorRatio.re =
                (errorRatio.re - errorRatio.im) *
                  (2 * denominatorRatio.re) := by ring1
            _ ≤ (errorRatio.re - errorRatio.im) * yNorm := scaled
        have diagonalScaled :
            2 * errorRatio.im *
                (denominatorRatio.re - denominatorRatio.im) ≤
              2 * errorRatio.im * yNorm :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            diagonalProjection
            (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
              imaginaryNonnegative)
        have summedDotBound :
            2 * dot ≤
              (errorRatio.re + errorRatio.im) * yNorm := by
          have added := RFAP.ConstructiveFraction.add_le_add_direct
            realScaled diagonalScaled
          dsimp only [dot]
          calc
            2 * (errorRatio.re * denominatorRatio.re -
                errorRatio.im * denominatorRatio.im) =
                2 * (errorRatio.re - errorRatio.im) *
                    denominatorRatio.re +
                  2 * errorRatio.im *
                    (denominatorRatio.re - denominatorRatio.im) := by
              ring1
            _ ≤ (errorRatio.re - errorRatio.im) * yNorm +
                2 * errorRatio.im * yNorm := added
            _ = (errorRatio.re + errorRatio.im) * yNorm := by ring1
        have twiceSumLeOnePlusTwiceNormFromExterior :
            2 * (errorRatio.re + errorRatio.im) ≤ 1 + 2 * xNorm := by
          have added := RFAP.ConstructiveFraction.add_le_add_direct
            twiceRealLeOnePlusNorm twiceImaginaryLeNorm
          calc
            2 * (errorRatio.re + errorRatio.im) =
                2 * errorRatio.re + 2 * errorRatio.im := by ring1
            _ ≤ (1 + xNorm) + xNorm := added
            _ = 1 + 2 * xNorm := by ring1
        have doubledDotBound :
            4 * dot ≤
              2 * ((errorRatio.re + errorRatio.im) * yNorm) := by
          have scaled :=
            RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
              summedDotBound (show (0 : Coordinate) ≤ 2 by decide)
          calc
            4 * dot = (2 * dot) * 2 := by ring1
            _ ≤ ((errorRatio.re + errorRatio.im) * yNorm) * 2 := scaled
            _ = 2 * ((errorRatio.re + errorRatio.im) * yNorm) := by ring1
        have sumScaled :
            2 * ((errorRatio.re + errorRatio.im) * yNorm) ≤
              (1 + 2 * xNorm) * yNorm := by
          have scaled :=
            RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
              twiceSumLeOnePlusTwiceNormFromExterior yNormNonnegative
          calc
            2 * ((errorRatio.re + errorRatio.im) * yNorm) =
                (2 * (errorRatio.re + errorRatio.im)) * yNorm := by ring1
            _ ≤ (1 + 2 * xNorm) * yNorm := scaled
        rw [gapExpansion]
        exact half_le_of_fourDot_le xNorm yNorm dot yNormLeOne
          (doubledDotBound.trans sumScaled)
    · have negTwiceDenominatorImagLeNorm :
          -2 * denominatorRatio.im ≤ yNorm := by
        apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
        calc
          0 ≤ normSq
              (1 - toGaussian RFAP.HurwitzGeometry.imaginaryUnit *
                denominatorRatio) - 1 :=
            RFAP.ConstructiveFraction.sub_nonneg_direct
              denominatorImaginaryExterior
          _ = yNorm - (-2 * denominatorRatio.im) := by
            dsimp only [yNorm, normSq, toGaussian,
              RFAP.HurwitzGeometry.imaginaryUnit]
            simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
              RFAP.ConstructiveGaussian.Gaussian.sub_im,
              RFAP.ConstructiveGaussian.Gaussian.mul_re,
              RFAP.ConstructiveGaussian.Gaussian.mul_im,
              RFAP.ConstructiveGaussian.Gaussian.one_re,
              RFAP.ConstructiveGaussian.Gaussian.one_im, Int.cast_one,
              Int.cast_zero]
            ring1
      have realScaled :
          2 * errorRatio.re * denominatorRatio.re ≤
            errorRatio.re * yNorm := by
        have scaled :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            twiceDenominatorRealLeNorm realNonnegative
        calc
          2 * errorRatio.re * denominatorRatio.re =
              errorRatio.re * (2 * denominatorRatio.re) := by ring1
          _ ≤ errorRatio.re * yNorm := scaled
      have imaginaryScaled :
          -2 * errorRatio.im * denominatorRatio.im ≤
            errorRatio.im * yNorm := by
        have scaled :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            negTwiceDenominatorImagLeNorm imaginaryNonnegative
        calc
          -2 * errorRatio.im * denominatorRatio.im =
              errorRatio.im * (-2 * denominatorRatio.im) := by ring1
          _ ≤ errorRatio.im * yNorm := scaled
      have summedDotBound :
          2 * dot ≤ (errorRatio.re + errorRatio.im) * yNorm := by
        have added := RFAP.ConstructiveFraction.add_le_add_direct
          realScaled imaginaryScaled
        dsimp only [dot]
        calc
          2 * (errorRatio.re * denominatorRatio.re -
              errorRatio.im * denominatorRatio.im) =
              2 * errorRatio.re * denominatorRatio.re +
                (-2 * errorRatio.im * denominatorRatio.im) := by ring1
          _ ≤ errorRatio.re * yNorm + errorRatio.im * yNorm := added
          _ = (errorRatio.re + errorRatio.im) * yNorm := by ring1
      have doubledDotBound :
          4 * dot ≤ 2 * ((errorRatio.re + errorRatio.im) * yNorm) := by
        have scaled :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
            summedDotBound (show (0 : Coordinate) ≤ 2 by decide)
        calc
          4 * dot = (2 * dot) * 2 := by ring1
          _ ≤ ((errorRatio.re + errorRatio.im) * yNorm) * 2 := scaled
          _ = 2 * ((errorRatio.re + errorRatio.im) * yNorm) := by ring1
      have sumScaled :
          2 * ((errorRatio.re + errorRatio.im) * yNorm) ≤
            (1 + 2 * xNorm) * yNorm := by
        have scaled :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
            twiceSumLeOnePlusTwiceNorm yNormNonnegative
        calc
          2 * ((errorRatio.re + errorRatio.im) * yNorm) =
              (2 * (errorRatio.re + errorRatio.im)) * yNorm := by ring1
          _ ≤ (1 + 2 * xNorm) * yNorm := scaled
      rw [gapExpansion]
      exact half_le_of_fourDot_le xNorm yNorm dot yNormLeOne
        (doubledDotBound.trans sumScaled)

private theorem firstOctant_errorRatio_eq_zero_of_oneExterior
    (errorRatio : Gaussian)
    (realNonnegative : 0 ≤ errorRatio.re)
    (imaginaryNonnegative : 0 ≤ errorRatio.im)
    (imaginaryLeReal : errorRatio.im ≤ errorRatio.re)
    (errorInside : normSq errorRatio < 1)
    (errorOneExterior :
      (1 : Coordinate) ≤
        normSq (errorRatio - toGaussian (1 : GaussianInt))) :
    errorRatio = 0 := by
  have realSquareLeNorm : errorRatio.re ^ 2 ≤ normSq errorRatio := by
    exact le_add_of_nonneg_right
      (RFAP.ConstructiveFraction.sq_nonneg_direct errorRatio.im)
  have realSquareLeOne : errorRatio.re ^ 2 ≤ (1 : Coordinate) ^ 2 := by
    simpa only [one_pow] using realSquareLeNorm.trans errorInside.le
  have realLeOne : errorRatio.re ≤ 1 :=
    RFAP.ConstructiveFraction.le_of_sq_le_sq_direct (by decide)
      realSquareLeOne
  have realLtOne : errorRatio.re < 1 := by
    by_cases realEqualsOne : errorRatio.re = 1
    · have oneLeNorm : (1 : Coordinate) ≤ normSq errorRatio := by
        calc
          (1 : Coordinate) = errorRatio.re ^ 2 := by
            rw [realEqualsOne]
            ring1
          _ ≤ normSq errorRatio := realSquareLeNorm
      exact ((not_lt_of_ge oneLeNorm) errorInside).elim
    · exact lt_of_le_of_ne realLeOne realEqualsOne
  have twiceRealLeNorm : 2 * errorRatio.re ≤ normSq errorRatio := by
    apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
    calc
      0 ≤ normSq (errorRatio - toGaussian (1 : GaussianInt)) - 1 :=
        RFAP.ConstructiveFraction.sub_nonneg_direct errorOneExterior
      _ = normSq errorRatio - 2 * errorRatio.re := by
        dsimp only [normSq, toGaussian]
        simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
          RFAP.ConstructiveGaussian.Gaussian.sub_im,
          RFAP.ConstructiveGaussianHeight.GaussianInt.one_re,
          RFAP.ConstructiveGaussianHeight.GaussianInt.one_im,
          Int.cast_one, Int.cast_zero]
        ring1
  have imaginarySquareLeRealSquare :
      errorRatio.im ^ 2 ≤ errorRatio.re ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct imaginaryNonnegative
      imaginaryLeReal 2
  have normLeTwiceRealSquare :
      normSq errorRatio ≤ 2 * errorRatio.re ^ 2 := by
    calc
      normSq errorRatio = errorRatio.re ^ 2 + errorRatio.im ^ 2 := rfl
      _ ≤ errorRatio.re ^ 2 + errorRatio.re ^ 2 :=
        RFAP.ConstructiveFraction.add_le_add_direct le_rfl
          imaginarySquareLeRealSquare
      _ = 2 * errorRatio.re ^ 2 := by ring1
  have realLeRealSquare : errorRatio.re ≤ errorRatio.re ^ 2 := by
    apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct (c := 2)
    · calc
        errorRatio.re * 2 = 2 * errorRatio.re := by ring1
        _ ≤ 2 * errorRatio.re ^ 2 := twiceRealLeNorm.trans
          normLeTwiceRealSquare
        _ = errorRatio.re ^ 2 * 2 := by ring1
    · decide
  have oneMinusRealPositive : 0 < 1 - errorRatio.re :=
    RFAP.ConstructiveFraction.sub_pos_direct realLtOne
  have realTimesGapNonpositive :
      errorRatio.re * (1 - errorRatio.re) ≤
        0 * (1 - errorRatio.re) := by
    apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
    calc
      0 ≤ errorRatio.re ^ 2 - errorRatio.re :=
        RFAP.ConstructiveFraction.sub_nonneg_direct realLeRealSquare
      _ = 0 * (1 - errorRatio.re) -
          errorRatio.re * (1 - errorRatio.re) := by ring1
  have realNonpositive : errorRatio.re ≤ 0 :=
    RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct
      realTimesGapNonpositive oneMinusRealPositive
  have realZero : errorRatio.re = 0 :=
    le_antisymm realNonpositive realNonnegative
  have imaginaryZero : errorRatio.im = 0 := by
    apply le_antisymm
    · simpa only [realZero] using imaginaryLeReal
    · exact imaginaryNonnegative
  apply RFAP.ConstructiveGaussian.Gaussian.ext
  · exact realZero
  · exact imaginaryZero

/-- The exact finite first-octant chamber certificate strengthens the
three-coefficient normalized determinant gap from `1/2` to `15/28`.  The
two noncritical chambers actually have gap at least `3/4`; the displayed
rational constant is needed only when both non-real coefficient exclusions
occur on the error side. -/
theorem fifteen_twenty_eighths_le_determinantGap_of_firstOctantObstructions
    (errorRatio denominatorRatio : Gaussian)
    (realNonnegative : 0 ≤ errorRatio.re)
    (imaginaryNonnegative : 0 ≤ errorRatio.im)
    (imaginaryLeReal : errorRatio.im ≤ errorRatio.re)
    (errorInside : normSq errorRatio < 1)
    (denominatorInside : normSq denominatorRatio < 1)
    (coefficientExterior : ∀ coefficient : GaussianInt,
      (1 : Coordinate) ≤ normSq (errorRatio - toGaussian coefficient) ∨
        1 ≤ normSq (1 - toGaussian coefficient * denominatorRatio)) :
    (15 / 28 : Coordinate) ≤
      normSq (1 - denominatorRatio * errorRatio) := by
  rcases coefficientExterior 1 with errorOneExterior | denominatorOneExterior
  · have errorRatioZero := firstOctant_errorRatio_eq_zero_of_oneExterior
      errorRatio realNonnegative imaginaryNonnegative imaginaryLeReal
        errorInside errorOneExterior
    rw [errorRatioZero, RFAP.ConstructiveGaussian.Gaussian.mul_zero,
      RFAP.ConstructiveGaussian.Gaussian.sub_zero, normSq_one]
    decide
  · have denominatorRealObstruction :
        2 * denominatorRatio.re ≤ normSq denominatorRatio := by
      apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
      calc
        0 ≤ normSq (1 - toGaussian (1 : GaussianInt) * denominatorRatio) - 1 :=
          RFAP.ConstructiveFraction.sub_nonneg_direct denominatorOneExterior
        _ = normSq denominatorRatio - 2 * denominatorRatio.re := by
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
    rcases coefficientExterior RFAP.HurwitzGeometry.imaginaryUnit with
        errorImaginaryExterior | denominatorImaginaryExterior
    · have errorImaginaryObstruction :
          2 * errorRatio.im ≤ normSq errorRatio := by
        apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
        calc
          0 ≤ normSq
              (errorRatio -
                toGaussian RFAP.HurwitzGeometry.imaginaryUnit) - 1 :=
            RFAP.ConstructiveFraction.sub_nonneg_direct errorImaginaryExterior
          _ = normSq errorRatio - 2 * errorRatio.im := by
            dsimp only [normSq, toGaussian,
              RFAP.HurwitzGeometry.imaginaryUnit]
            simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
              RFAP.ConstructiveGaussian.Gaussian.sub_im, Int.cast_one,
              Int.cast_zero]
            ring1
      rcases coefficientExterior
          (1 + RFAP.HurwitzGeometry.imaginaryUnit) with
          errorDiagonalExterior | denominatorDiagonalExterior
      · have errorDiagonalObstruction :
            2 * (errorRatio.re + errorRatio.im) ≤
              normSq errorRatio + 1 := by
          apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
          calc
            0 ≤ normSq
                (errorRatio - toGaussian
                  (1 + RFAP.HurwitzGeometry.imaginaryUnit)) - 1 :=
              RFAP.ConstructiveFraction.sub_nonneg_direct errorDiagonalExterior
            _ = (normSq errorRatio + 1) -
                2 * (errorRatio.re + errorRatio.im) := by
              dsimp only [normSq, toGaussian,
                RFAP.HurwitzGeometry.imaginaryUnit]
              simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
                RFAP.ConstructiveGaussian.Gaussian.sub_im,
                RFAP.ConstructiveGaussianHeight.GaussianInt.add_re,
                RFAP.ConstructiveGaussianHeight.GaussianInt.add_im,
                RFAP.ConstructiveGaussianHeight.GaussianInt.one_re,
                RFAP.ConstructiveGaussianHeight.GaussianInt.one_im,
                Int.cast_add, Int.cast_one, Int.cast_zero]
              ring1
        exact fifteen_twenty_eighths_le_of_diagonalErrorChamber
          errorRatio denominatorRatio realNonnegative imaginaryNonnegative
          imaginaryLeReal errorInside denominatorInside
          errorImaginaryObstruction errorDiagonalObstruction
          denominatorRealObstruction
      · have twiceDiagonalProjection :
            2 * (denominatorRatio.re - denominatorRatio.im) ≤
              2 * normSq denominatorRatio := by
          apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
          calc
            0 ≤ normSq
                (1 - toGaussian
                  (1 + RFAP.HurwitzGeometry.imaginaryUnit) *
                    denominatorRatio) - 1 :=
              RFAP.ConstructiveFraction.sub_nonneg_direct
                denominatorDiagonalExterior
            _ = 2 * normSq denominatorRatio -
                2 * (denominatorRatio.re - denominatorRatio.im) := by
              dsimp only [normSq, toGaussian,
                RFAP.HurwitzGeometry.imaginaryUnit]
              simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
                RFAP.ConstructiveGaussian.Gaussian.sub_im,
                RFAP.ConstructiveGaussian.Gaussian.mul_re,
                RFAP.ConstructiveGaussian.Gaussian.mul_im,
                RFAP.ConstructiveGaussian.Gaussian.one_re,
                RFAP.ConstructiveGaussian.Gaussian.one_im,
                RFAP.ConstructiveGaussianHeight.GaussianInt.add_re,
                RFAP.ConstructiveGaussianHeight.GaussianInt.add_im,
                RFAP.ConstructiveGaussianHeight.GaussianInt.one_re,
                RFAP.ConstructiveGaussianHeight.GaussianInt.one_im,
                Int.cast_add, Int.cast_one, Int.cast_zero]
              ring1
        have denominatorDiagonalObstruction :
            denominatorRatio.re - denominatorRatio.im ≤
              normSq denominatorRatio := by
          apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct (c := 2)
          · calc
              (denominatorRatio.re - denominatorRatio.im) * 2 =
                  2 * (denominatorRatio.re - denominatorRatio.im) := by ring1
              _ ≤ 2 * normSq denominatorRatio := twiceDiagonalProjection
              _ = normSq denominatorRatio * 2 := by ring1
          · decide
        have chamberBound :=
          three_quarters_le_of_diagonalDenominatorChamber
            errorRatio denominatorRatio realNonnegative imaginaryNonnegative
            errorInside denominatorInside errorImaginaryObstruction
            denominatorRealObstruction denominatorDiagonalObstruction
        exact (show (15 / 28 : Coordinate) ≤ 3 / 4 by decide).trans
          chamberBound
    · have denominatorImaginaryObstruction :
          -2 * denominatorRatio.im ≤ normSq denominatorRatio := by
        apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
        calc
          0 ≤ normSq
              (1 - toGaussian RFAP.HurwitzGeometry.imaginaryUnit *
                denominatorRatio) - 1 :=
            RFAP.ConstructiveFraction.sub_nonneg_direct
              denominatorImaginaryExterior
          _ = normSq denominatorRatio - (-2 * denominatorRatio.im) := by
            dsimp only [normSq, toGaussian,
              RFAP.HurwitzGeometry.imaginaryUnit]
            simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
              RFAP.ConstructiveGaussian.Gaussian.sub_im,
              RFAP.ConstructiveGaussian.Gaussian.mul_re,
              RFAP.ConstructiveGaussian.Gaussian.mul_im,
              RFAP.ConstructiveGaussian.Gaussian.one_re,
              RFAP.ConstructiveGaussian.Gaussian.one_im, Int.cast_one,
              Int.cast_zero]
            ring1
      have chamberBound := three_quarters_le_of_axisChamber
        errorRatio denominatorRatio realNonnegative imaginaryNonnegative
        denominatorInside denominatorRealObstruction
        denominatorImaginaryObstruction
      exact (show (15 / 28 : Coordinate) ≤ 3 / 4 by decide).trans
        chamberBound

/-- The full two-coefficient exterior condition adds the norm-two leading
combination `(1, -(1-i))` to the three neighbouring coefficient tests.  In
the only first-octant chamber below `3/4`, that combination supplies a second
denominator projection and raises the rational gap to `71/112`. -/
private theorem normTwoIndexOneGapThreshold_le_of_firstOctantLinearObstructions
    (errorRatio denominatorRatio : Gaussian)
    (realNonnegative : 0 ≤ errorRatio.re)
    (imaginaryNonnegative : 0 ≤ errorRatio.im)
    (imaginaryLeReal : errorRatio.im ≤ errorRatio.re)
    (errorInside : normSq errorRatio < 1)
    (denominatorInside : normSq denominatorRatio < 1)
    (linearCombinationExterior :
      ∀ leftCoefficient rightCoefficient : GaussianInt,
        leftCoefficient ≠ 0 ∨ rightCoefficient ≠ 0 →
          (1 : Coordinate) ≤
              normSq
                (toGaussian leftCoefficient +
                  toGaussian rightCoefficient * errorRatio) ∨
            1 ≤
              normSq
                (toGaussian leftCoefficient * denominatorRatio +
                  toGaussian rightCoefficient)) :
    normTwoIndexOneGapThreshold ≤
      normSq (1 - denominatorRatio * errorRatio) := by
  have coefficientExterior :=
    coefficientExterior_of_linearCombinationExterior errorRatio
      denominatorRatio linearCombinationExterior
  rcases coefficientExterior 1 with errorOneExterior | denominatorOneExterior
  · have errorRatioZero := firstOctant_errorRatio_eq_zero_of_oneExterior
      errorRatio realNonnegative imaginaryNonnegative imaginaryLeReal
        errorInside errorOneExterior
    rw [errorRatioZero, RFAP.ConstructiveGaussian.Gaussian.mul_zero,
      RFAP.ConstructiveGaussian.Gaussian.sub_zero, normSq_one]
    exact normTwoIndexOneGapThreshold_le_one
  · have denominatorRealObstruction :
        2 * denominatorRatio.re ≤ normSq denominatorRatio := by
      apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
      calc
        0 ≤ normSq (1 - toGaussian (1 : GaussianInt) * denominatorRatio) - 1 :=
          RFAP.ConstructiveFraction.sub_nonneg_direct denominatorOneExterior
        _ = normSq denominatorRatio - 2 * denominatorRatio.re := by
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
    rcases coefficientExterior RFAP.HurwitzGeometry.imaginaryUnit with
        errorImaginaryExterior | denominatorImaginaryExterior
    · have errorImaginaryObstruction :
          2 * errorRatio.im ≤ normSq errorRatio := by
        apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
        calc
          0 ≤ normSq
              (errorRatio -
                toGaussian RFAP.HurwitzGeometry.imaginaryUnit) - 1 :=
            RFAP.ConstructiveFraction.sub_nonneg_direct errorImaginaryExterior
          _ = normSq errorRatio - 2 * errorRatio.im := by
            dsimp only [normSq, toGaussian,
              RFAP.HurwitzGeometry.imaginaryUnit]
            simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
              RFAP.ConstructiveGaussian.Gaussian.sub_im, Int.cast_one,
              Int.cast_zero]
            ring1
      rcases coefficientExterior
          (1 + RFAP.HurwitzGeometry.imaginaryUnit) with
          errorDiagonalExterior | denominatorDiagonalExterior
      · have errorDiagonalObstruction :
            2 * (errorRatio.re + errorRatio.im) ≤
              normSq errorRatio + 1 := by
          apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
          calc
            0 ≤ normSq
                (errorRatio - toGaussian
                  (1 + RFAP.HurwitzGeometry.imaginaryUnit)) - 1 :=
              RFAP.ConstructiveFraction.sub_nonneg_direct errorDiagonalExterior
            _ = (normSq errorRatio + 1) -
                2 * (errorRatio.re + errorRatio.im) := by
              dsimp only [normSq, toGaussian,
                RFAP.HurwitzGeometry.imaginaryUnit]
              simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
                RFAP.ConstructiveGaussian.Gaussian.sub_im,
                RFAP.ConstructiveGaussianHeight.GaussianInt.add_re,
                RFAP.ConstructiveGaussianHeight.GaussianInt.add_im,
                RFAP.ConstructiveGaussianHeight.GaussianInt.one_re,
                RFAP.ConstructiveGaussianHeight.GaussianInt.one_im,
                Int.cast_add, Int.cast_one, Int.cast_zero]
              ring1
        let diagonalCoefficient : GaussianInt :=
          1 - RFAP.HurwitzGeometry.imaginaryUnit
        rcases linearCombinationExterior 1 (-diagonalCoefficient)
            (Or.inl (by decide)) with
            normTwoErrorExterior | normTwoDenominatorExterior
        · have errorExterior :
              (1 : Coordinate) ≤
                normSq (1 - toGaussian diagonalCoefficient * errorRatio) := by
            have identity :
                toGaussian (1 : GaussianInt) +
                    toGaussian (-diagonalCoefficient) * errorRatio =
                  1 - toGaussian diagonalCoefficient * errorRatio := by
              rw [toGaussian_one, toGaussian_neg]
              apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
                simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
                  RFAP.ConstructiveGaussian.Gaussian.add_im,
                  RFAP.ConstructiveGaussian.Gaussian.sub_re,
                  RFAP.ConstructiveGaussian.Gaussian.sub_im,
                  RFAP.ConstructiveGaussian.Gaussian.mul_re,
                  RFAP.ConstructiveGaussian.Gaussian.mul_im,
                  RFAP.ConstructiveGaussian.Gaussian.neg_re,
                  RFAP.ConstructiveGaussian.Gaussian.neg_im,
                  RFAP.ConstructiveGaussian.Gaussian.one_re,
                  RFAP.ConstructiveGaussian.Gaussian.one_im] <;>
                ring1
            rw [← identity]
            exact normTwoErrorExterior
          have errorRatioZero :=
            firstOctant_errorRatio_eq_zero_of_normTwoExterior errorRatio
              realNonnegative imaginaryNonnegative imaginaryLeReal errorInside
              (by simpa only [diagonalCoefficient] using errorExterior)
          rw [errorRatioZero, RFAP.ConstructiveGaussian.Gaussian.mul_zero,
            RFAP.ConstructiveGaussian.Gaussian.sub_zero, normSq_one]
          exact normTwoIndexOneGapThreshold_le_one
        · have denominatorExterior :
              (1 : Coordinate) ≤
                normSq (denominatorRatio - toGaussian diagonalCoefficient) := by
            have identity :
                toGaussian (1 : GaussianInt) * denominatorRatio +
                    toGaussian (-diagonalCoefficient) =
                  denominatorRatio - toGaussian diagonalCoefficient := by
              rw [toGaussian_one, toGaussian_neg,
                RFAP.ConstructiveGaussian.Gaussian.one_mul]
              apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
                simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
                  RFAP.ConstructiveGaussian.Gaussian.add_im,
                  RFAP.ConstructiveGaussian.Gaussian.sub_re,
                  RFAP.ConstructiveGaussian.Gaussian.sub_im,
                  RFAP.ConstructiveGaussian.Gaussian.neg_re,
                  RFAP.ConstructiveGaussian.Gaussian.neg_im] <;>
                ring1
            rw [← identity]
            exact normTwoDenominatorExterior
          have denominatorDiagonalObstruction :
              2 * (denominatorRatio.re - denominatorRatio.im) ≤
                normSq denominatorRatio + 1 := by
            apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
            calc
              0 ≤ normSq
                    (denominatorRatio - toGaussian diagonalCoefficient) - 1 :=
                RFAP.ConstructiveFraction.sub_nonneg_direct denominatorExterior
              _ = (normSq denominatorRatio + 1) -
                  2 * (denominatorRatio.re - denominatorRatio.im) := by
                dsimp only [diagonalCoefficient, normSq, toGaussian,
                  RFAP.HurwitzGeometry.imaginaryUnit]
                simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
                  RFAP.ConstructiveGaussian.Gaussian.sub_im,
                  RFAP.ConstructiveGaussianHeight.GaussianInt.sub_re,
                  RFAP.ConstructiveGaussianHeight.GaussianInt.sub_im,
                  RFAP.ConstructiveGaussianHeight.GaussianInt.one_re,
                  RFAP.ConstructiveGaussianHeight.GaussianInt.one_im,
                  Int.cast_sub, Int.cast_one, Int.cast_zero]
                ring1
          exact seventyOne_oneHundredTwelfths_le_of_diagonalErrorChamber
            errorRatio denominatorRatio realNonnegative imaginaryNonnegative
            imaginaryLeReal errorInside denominatorInside
            errorImaginaryObstruction errorDiagonalObstruction
            denominatorRealObstruction denominatorDiagonalObstruction
      · have twiceDiagonalProjection :
            2 * (denominatorRatio.re - denominatorRatio.im) ≤
              2 * normSq denominatorRatio := by
          apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
          calc
            0 ≤ normSq
                (1 - toGaussian
                  (1 + RFAP.HurwitzGeometry.imaginaryUnit) *
                    denominatorRatio) - 1 :=
              RFAP.ConstructiveFraction.sub_nonneg_direct
                denominatorDiagonalExterior
            _ = 2 * normSq denominatorRatio -
                2 * (denominatorRatio.re - denominatorRatio.im) := by
              dsimp only [normSq, toGaussian,
                RFAP.HurwitzGeometry.imaginaryUnit]
              simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
                RFAP.ConstructiveGaussian.Gaussian.sub_im,
                RFAP.ConstructiveGaussian.Gaussian.mul_re,
                RFAP.ConstructiveGaussian.Gaussian.mul_im,
                RFAP.ConstructiveGaussian.Gaussian.one_re,
                RFAP.ConstructiveGaussian.Gaussian.one_im,
                RFAP.ConstructiveGaussianHeight.GaussianInt.add_re,
                RFAP.ConstructiveGaussianHeight.GaussianInt.add_im,
                RFAP.ConstructiveGaussianHeight.GaussianInt.one_re,
                RFAP.ConstructiveGaussianHeight.GaussianInt.one_im,
                Int.cast_add, Int.cast_one, Int.cast_zero]
              ring1
        have denominatorDiagonalObstruction :
            denominatorRatio.re - denominatorRatio.im ≤
              normSq denominatorRatio := by
          apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct (c := 2)
          · calc
              (denominatorRatio.re - denominatorRatio.im) * 2 =
                  2 * (denominatorRatio.re - denominatorRatio.im) := by ring1
              _ ≤ 2 * normSq denominatorRatio := twiceDiagonalProjection
              _ = normSq denominatorRatio * 2 := by ring1
          · decide
        have chamberBound :=
          three_quarters_le_of_diagonalDenominatorChamber
            errorRatio denominatorRatio realNonnegative imaginaryNonnegative
            errorInside denominatorInside errorImaginaryObstruction
            denominatorRealObstruction denominatorDiagonalObstruction
        exact normTwoIndexOneGapThreshold_le_threeQuarters.trans chamberBound
    · have denominatorImaginaryObstruction :
          -2 * denominatorRatio.im ≤ normSq denominatorRatio := by
        apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
        calc
          0 ≤ normSq
              (1 - toGaussian RFAP.HurwitzGeometry.imaginaryUnit *
                denominatorRatio) - 1 :=
            RFAP.ConstructiveFraction.sub_nonneg_direct
              denominatorImaginaryExterior
          _ = normSq denominatorRatio - (-2 * denominatorRatio.im) := by
            dsimp only [normSq, toGaussian,
              RFAP.HurwitzGeometry.imaginaryUnit]
            simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
              RFAP.ConstructiveGaussian.Gaussian.sub_im,
              RFAP.ConstructiveGaussian.Gaussian.mul_re,
              RFAP.ConstructiveGaussian.Gaussian.mul_im,
              RFAP.ConstructiveGaussian.Gaussian.one_re,
              RFAP.ConstructiveGaussian.Gaussian.one_im, Int.cast_one,
              Int.cast_zero]
            ring1
      have chamberBound := three_quarters_le_of_axisChamber
        errorRatio denominatorRatio realNonnegative imaginaryNonnegative
        denominatorInside denominatorRealObstruction
        denominatorImaginaryObstruction
      exact normTwoIndexOneGapThreshold_le_threeQuarters.trans chamberBound

/-- All five small linear-combination certificates in the normalized first
octant imply every displayed threshold in the exact root-free gap cut.  This
is the Gaussian-coordinate bridge to the scalar four-region calculation. -/
theorem gapThreshold_le_of_firstOctantLinearObstructions
    (threshold : Coordinate)
    (thresholdCertificate :
      RFAP.OptimalIndexOneWindow.IsGapThreshold threshold)
    (errorRatio denominatorRatio : Gaussian)
    (realNonnegative : 0 ≤ errorRatio.re)
    (imaginaryNonnegative : 0 ≤ errorRatio.im)
    (imaginaryLeReal : errorRatio.im ≤ errorRatio.re)
    (errorInside : normSq errorRatio < 1)
    (denominatorInside : normSq denominatorRatio < 1)
    (linearCombinationExterior :
      ∀ leftCoefficient rightCoefficient : GaussianInt,
        leftCoefficient ≠ 0 ∨ rightCoefficient ≠ 0 →
          (1 : Coordinate) ≤
              normSq
                (toGaussian leftCoefficient +
                  toGaussian rightCoefficient * errorRatio) ∨
            1 ≤
              normSq
                (toGaussian leftCoefficient * denominatorRatio +
                  toGaussian rightCoefficient)) :
    threshold ≤
      normSq (1 - denominatorRatio * errorRatio) := by
  let a := errorRatio.re
  let b := errorRatio.im
  let c := denominatorRatio.re
  let d := denominatorRatio.im
  let xNorm := normSq errorRatio
  let yNorm := normSq denominatorRatio
  have coefficientExterior :=
    coefficientExterior_of_linearCombinationExterior errorRatio
      denominatorRatio linearCombinationExterior
  rcases coefficientExterior 1 with errorOneExterior | denominatorOneExterior
  · have errorRatioZero := firstOctant_errorRatio_eq_zero_of_oneExterior
      errorRatio realNonnegative imaginaryNonnegative imaginaryLeReal
        errorInside errorOneExterior
    rw [errorRatioZero, RFAP.ConstructiveGaussian.Gaussian.mul_zero,
      RFAP.ConstructiveGaussian.Gaussian.sub_zero, normSq_one]
    exact thresholdCertificate.1.le
  · have denominatorOne : 2 * c ≤ yNorm := by
      apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
      calc
        0 ≤ normSq (1 - toGaussian (1 : GaussianInt) * denominatorRatio) - 1 :=
          RFAP.ConstructiveFraction.sub_nonneg_direct denominatorOneExterior
        _ = yNorm - 2 * c := by
          dsimp only [yNorm, c, normSq, toGaussian]
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
    have imaginaryObstruction :
        2 * b ≤ xNorm ∨ -2 * d ≤ yNorm := by
      rcases coefficientExterior RFAP.HurwitzGeometry.imaginaryUnit with
          errorExterior | denominatorExterior
      · left
        apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
        calc
          0 ≤ normSq
                (errorRatio -
                  toGaussian RFAP.HurwitzGeometry.imaginaryUnit) - 1 :=
            RFAP.ConstructiveFraction.sub_nonneg_direct errorExterior
          _ = xNorm - 2 * b := by
            dsimp only [xNorm, b, normSq, toGaussian,
              RFAP.HurwitzGeometry.imaginaryUnit]
            simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
              RFAP.ConstructiveGaussian.Gaussian.sub_im, Int.cast_one,
              Int.cast_zero]
            ring1
      · right
        apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
        calc
          0 ≤ normSq
                (1 - toGaussian RFAP.HurwitzGeometry.imaginaryUnit *
                  denominatorRatio) - 1 :=
            RFAP.ConstructiveFraction.sub_nonneg_direct denominatorExterior
          _ = yNorm - (-2 * d) := by
            dsimp only [yNorm, d, normSq, toGaussian,
              RFAP.HurwitzGeometry.imaginaryUnit]
            simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
              RFAP.ConstructiveGaussian.Gaussian.sub_im,
              RFAP.ConstructiveGaussian.Gaussian.mul_re,
              RFAP.ConstructiveGaussian.Gaussian.mul_im,
              RFAP.ConstructiveGaussian.Gaussian.one_re,
              RFAP.ConstructiveGaussian.Gaussian.one_im, Int.cast_one,
              Int.cast_zero]
            ring1
    have diagonalObstruction :
        2 * (a + b) ≤ xNorm + 1 ∨ c - d ≤ yNorm := by
      rcases coefficientExterior
          (1 + RFAP.HurwitzGeometry.imaginaryUnit) with
          errorExterior | denominatorExterior
      · left
        apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
        calc
          0 ≤ normSq
                (errorRatio - toGaussian
                  (1 + RFAP.HurwitzGeometry.imaginaryUnit)) - 1 :=
            RFAP.ConstructiveFraction.sub_nonneg_direct errorExterior
          _ = (xNorm + 1) - 2 * (a + b) := by
            dsimp only [xNorm, a, b, normSq, toGaussian,
              RFAP.HurwitzGeometry.imaginaryUnit]
            simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
              RFAP.ConstructiveGaussian.Gaussian.sub_im,
              RFAP.ConstructiveGaussianHeight.GaussianInt.add_re,
              RFAP.ConstructiveGaussianHeight.GaussianInt.add_im,
              RFAP.ConstructiveGaussianHeight.GaussianInt.one_re,
              RFAP.ConstructiveGaussianHeight.GaussianInt.one_im,
              Int.cast_add, Int.cast_one, Int.cast_zero]
            ring1
      · right
        have twiceProjection : 2 * (c - d) ≤ 2 * yNorm := by
          apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
          calc
            0 ≤ normSq
                  (1 - toGaussian
                    (1 + RFAP.HurwitzGeometry.imaginaryUnit) *
                      denominatorRatio) - 1 :=
              RFAP.ConstructiveFraction.sub_nonneg_direct denominatorExterior
            _ = 2 * yNorm - 2 * (c - d) := by
              dsimp only [yNorm, c, d, normSq, toGaussian,
                RFAP.HurwitzGeometry.imaginaryUnit]
              simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
                RFAP.ConstructiveGaussian.Gaussian.sub_im,
                RFAP.ConstructiveGaussian.Gaussian.mul_re,
                RFAP.ConstructiveGaussian.Gaussian.mul_im,
                RFAP.ConstructiveGaussian.Gaussian.one_re,
                RFAP.ConstructiveGaussian.Gaussian.one_im,
                RFAP.ConstructiveGaussianHeight.GaussianInt.add_re,
                RFAP.ConstructiveGaussianHeight.GaussianInt.add_im,
                RFAP.ConstructiveGaussianHeight.GaussianInt.one_re,
                RFAP.ConstructiveGaussianHeight.GaussianInt.one_im,
                Int.cast_add, Int.cast_one, Int.cast_zero]
              ring1
        apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct (c := 2)
        · calc
            (c - d) * 2 = 2 * (c - d) := by ring1
            _ ≤ 2 * yNorm := twiceProjection
            _ = yNorm * 2 := by ring1
        · decide
    let minusDiagonalCoefficient : GaussianInt :=
      1 - RFAP.HurwitzGeometry.imaginaryUnit
    rcases linearCombinationExterior 1 (-minusDiagonalCoefficient)
        (Or.inl (by decide)) with
        minusErrorExterior | minusDenominatorExterior
    · have errorExterior :
          (1 : Coordinate) ≤
            normSq (1 - toGaussian minusDiagonalCoefficient * errorRatio) := by
        have identity :
            toGaussian (1 : GaussianInt) +
                toGaussian (-minusDiagonalCoefficient) * errorRatio =
              1 - toGaussian minusDiagonalCoefficient * errorRatio := by
          rw [toGaussian_one, toGaussian_neg]
          apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
            simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
              RFAP.ConstructiveGaussian.Gaussian.add_im,
              RFAP.ConstructiveGaussian.Gaussian.sub_re,
              RFAP.ConstructiveGaussian.Gaussian.sub_im,
              RFAP.ConstructiveGaussian.Gaussian.mul_re,
              RFAP.ConstructiveGaussian.Gaussian.mul_im,
              RFAP.ConstructiveGaussian.Gaussian.neg_re,
              RFAP.ConstructiveGaussian.Gaussian.neg_im,
              RFAP.ConstructiveGaussian.Gaussian.one_re,
              RFAP.ConstructiveGaussian.Gaussian.one_im] <;>
            ring1
        rw [← identity]
        exact minusErrorExterior
      have errorRatioZero :=
        firstOctant_errorRatio_eq_zero_of_normTwoExterior errorRatio
          realNonnegative imaginaryNonnegative imaginaryLeReal errorInside
          (by simpa only [minusDiagonalCoefficient] using errorExterior)
      rw [errorRatioZero, RFAP.ConstructiveGaussian.Gaussian.mul_zero,
        RFAP.ConstructiveGaussian.Gaussian.sub_zero, normSq_one]
      exact thresholdCertificate.1.le
    · have denominatorExterior :
          (1 : Coordinate) ≤
            normSq (denominatorRatio -
              toGaussian minusDiagonalCoefficient) := by
        have identity :
            toGaussian (1 : GaussianInt) * denominatorRatio +
                toGaussian (-minusDiagonalCoefficient) =
              denominatorRatio - toGaussian minusDiagonalCoefficient := by
          rw [toGaussian_one, toGaussian_neg,
            RFAP.ConstructiveGaussian.Gaussian.one_mul]
          apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
            simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
              RFAP.ConstructiveGaussian.Gaussian.add_im,
              RFAP.ConstructiveGaussian.Gaussian.sub_re,
              RFAP.ConstructiveGaussian.Gaussian.sub_im,
              RFAP.ConstructiveGaussian.Gaussian.neg_re,
              RFAP.ConstructiveGaussian.Gaussian.neg_im] <;>
            ring1
        rw [← identity]
        exact minusDenominatorExterior
      have denominatorOneMinusI : 2 * (c - d) ≤ yNorm + 1 := by
        apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
        calc
          0 ≤ normSq (denominatorRatio -
                toGaussian minusDiagonalCoefficient) - 1 :=
            RFAP.ConstructiveFraction.sub_nonneg_direct denominatorExterior
          _ = (yNorm + 1) - 2 * (c - d) := by
            dsimp only [minusDiagonalCoefficient, yNorm, c, d, normSq,
              toGaussian, RFAP.HurwitzGeometry.imaginaryUnit]
            simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
              RFAP.ConstructiveGaussian.Gaussian.sub_im,
              RFAP.ConstructiveGaussianHeight.GaussianInt.sub_re,
              RFAP.ConstructiveGaussianHeight.GaussianInt.sub_im,
              RFAP.ConstructiveGaussianHeight.GaussianInt.one_re,
              RFAP.ConstructiveGaussianHeight.GaussianInt.one_im,
              Int.cast_sub, Int.cast_one, Int.cast_zero]
            ring1
      let plusDiagonalCoefficient : GaussianInt :=
        1 + RFAP.HurwitzGeometry.imaginaryUnit
      have oppositeDiagonalObstruction :
          a - b ≤ xNorm ∨ 2 * (c + d) ≤ yNorm + 1 := by
        rcases linearCombinationExterior 1 (-plusDiagonalCoefficient)
            (Or.inl (by decide)) with
            plusErrorExterior | plusDenominatorExterior
        · left
          have errorExterior :
              (1 : Coordinate) ≤
                normSq (1 - toGaussian plusDiagonalCoefficient * errorRatio) := by
            have identity :
                toGaussian (1 : GaussianInt) +
                    toGaussian (-plusDiagonalCoefficient) * errorRatio =
                  1 - toGaussian plusDiagonalCoefficient * errorRatio := by
              rw [toGaussian_one, toGaussian_neg]
              apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
                simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
                  RFAP.ConstructiveGaussian.Gaussian.add_im,
                  RFAP.ConstructiveGaussian.Gaussian.sub_re,
                  RFAP.ConstructiveGaussian.Gaussian.sub_im,
                  RFAP.ConstructiveGaussian.Gaussian.mul_re,
                  RFAP.ConstructiveGaussian.Gaussian.mul_im,
                  RFAP.ConstructiveGaussian.Gaussian.neg_re,
                  RFAP.ConstructiveGaussian.Gaussian.neg_im,
                  RFAP.ConstructiveGaussian.Gaussian.one_re,
                  RFAP.ConstructiveGaussian.Gaussian.one_im] <;>
                ring1
            rw [← identity]
            exact plusErrorExterior
          have twiceProjection : 2 * (a - b) ≤ 2 * xNorm := by
            apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
            calc
              0 ≤ normSq
                    (1 - toGaussian plusDiagonalCoefficient * errorRatio) - 1 :=
                RFAP.ConstructiveFraction.sub_nonneg_direct errorExterior
              _ = 2 * xNorm - 2 * (a - b) := by
                dsimp only [plusDiagonalCoefficient, xNorm, a, b, normSq,
                  toGaussian, RFAP.HurwitzGeometry.imaginaryUnit]
                simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
                  RFAP.ConstructiveGaussian.Gaussian.sub_im,
                  RFAP.ConstructiveGaussian.Gaussian.mul_re,
                  RFAP.ConstructiveGaussian.Gaussian.mul_im,
                  RFAP.ConstructiveGaussian.Gaussian.one_re,
                  RFAP.ConstructiveGaussian.Gaussian.one_im,
                  RFAP.ConstructiveGaussianHeight.GaussianInt.add_re,
                  RFAP.ConstructiveGaussianHeight.GaussianInt.add_im,
                  RFAP.ConstructiveGaussianHeight.GaussianInt.one_re,
                  RFAP.ConstructiveGaussianHeight.GaussianInt.one_im,
                  Int.cast_add, Int.cast_one, Int.cast_zero]
                ring1
          apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct (c := 2)
          · calc
              (a - b) * 2 = 2 * (a - b) := by ring1
              _ ≤ 2 * xNorm := twiceProjection
              _ = xNorm * 2 := by ring1
          · decide
        · right
          have denominatorExterior :
              (1 : Coordinate) ≤
                normSq (denominatorRatio -
                  toGaussian plusDiagonalCoefficient) := by
            have identity :
                toGaussian (1 : GaussianInt) * denominatorRatio +
                    toGaussian (-plusDiagonalCoefficient) =
                  denominatorRatio - toGaussian plusDiagonalCoefficient := by
              rw [toGaussian_one, toGaussian_neg,
                RFAP.ConstructiveGaussian.Gaussian.one_mul]
              apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
                simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
                  RFAP.ConstructiveGaussian.Gaussian.add_im,
                  RFAP.ConstructiveGaussian.Gaussian.sub_re,
                  RFAP.ConstructiveGaussian.Gaussian.sub_im,
                  RFAP.ConstructiveGaussian.Gaussian.neg_re,
                  RFAP.ConstructiveGaussian.Gaussian.neg_im] <;>
                ring1
            rw [← identity]
            exact plusDenominatorExterior
          apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
          calc
            0 ≤ normSq (denominatorRatio -
                  toGaussian plusDiagonalCoefficient) - 1 :=
              RFAP.ConstructiveFraction.sub_nonneg_direct denominatorExterior
            _ = (yNorm + 1) - 2 * (c + d) := by
              dsimp only [plusDiagonalCoefficient, yNorm, c, d, normSq,
                toGaussian, RFAP.HurwitzGeometry.imaginaryUnit]
              simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
                RFAP.ConstructiveGaussian.Gaussian.sub_im,
                RFAP.ConstructiveGaussianHeight.GaussianInt.add_re,
                RFAP.ConstructiveGaussianHeight.GaussianInt.add_im,
                RFAP.ConstructiveGaussianHeight.GaussianInt.one_re,
                RFAP.ConstructiveGaussianHeight.GaussianInt.one_im,
                Int.cast_add, Int.cast_one, Int.cast_zero]
              ring1
      have scalarBound :=
        RFAP.OptimalIndexOneWindow.gapThreshold_le_gap_of_firstOctantFiveObstructions
          a b c d xNorm yNorm threshold realNonnegative imaginaryNonnegative
            imaginaryLeReal rfl rfl errorInside.le denominatorInside.le
            denominatorOne denominatorOneMinusI imaginaryObstruction
            diagonalObstruction oppositeDiagonalObstruction thresholdCertificate
      have gapExpansion :
          normSq (1 - denominatorRatio * errorRatio) =
            1 + xNorm * yNorm - 2 * (a * c - b * d) := by
        dsimp only [xNorm, yNorm, a, b, c, d, normSq]
        simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
          RFAP.ConstructiveGaussian.Gaussian.sub_im,
          RFAP.ConstructiveGaussian.Gaussian.mul_re,
          RFAP.ConstructiveGaussian.Gaussian.mul_im,
          RFAP.ConstructiveGaussian.Gaussian.one_re,
          RFAP.ConstructiveGaussian.Gaussian.one_im]
        ring1
      rw [gapExpansion]
      exact scalarBound

private theorem firstRegionGapBound_isGapThreshold :
    RFAP.OptimalIndexOneWindow.IsGapThreshold
      RFAP.SharpIndexOneWindow.firstRegionGapBound := by
  constructor
  · unfold RFAP.SharpIndexOneWindow.firstRegionGapBound
      RFAP.SharpIndexOneWindow.firstRegionProjectionBound
    decide
  · unfold RFAP.OptimalIndexOneWindow.gapPolynomial
      RFAP.SharpIndexOneWindow.firstRegionGapBound
      RFAP.SharpIndexOneWindow.firstRegionProjectionBound
    decide

/-- Compatibility form of the exact first-octant bridge at the earlier dyadic
threshold `205/256`. -/
theorem sharpIndexOneGapBound_le_of_firstOctantLinearObstructions
    (errorRatio denominatorRatio : Gaussian)
    (realNonnegative : 0 ≤ errorRatio.re)
    (imaginaryNonnegative : 0 ≤ errorRatio.im)
    (imaginaryLeReal : errorRatio.im ≤ errorRatio.re)
    (errorInside : normSq errorRatio < 1)
    (denominatorInside : normSq denominatorRatio < 1)
    (linearCombinationExterior :
      ∀ leftCoefficient rightCoefficient : GaussianInt,
        leftCoefficient ≠ 0 ∨ rightCoefficient ≠ 0 →
          (1 : Coordinate) ≤
              normSq
                (toGaussian leftCoefficient +
                  toGaussian rightCoefficient * errorRatio) ∨
            1 ≤
              normSq
                (toGaussian leftCoefficient * denominatorRatio +
                  toGaussian rightCoefficient)) :
    RFAP.SharpIndexOneWindow.firstRegionGapBound ≤
      normSq (1 - denominatorRatio * errorRatio) :=
  gapThreshold_le_of_firstOctantLinearObstructions
    RFAP.SharpIndexOneWindow.firstRegionGapBound
    firstRegionGapBound_isGapThreshold errorRatio denominatorRatio
    realNonnegative imaginaryNonnegative imaginaryLeReal errorInside
    denominatorInside linearCombinationExterior

/-- Rotate normalized error data by the inverse of a displayed unit. -/
def rotateErrorRatio (unit : GaussianInt) (value : Gaussian) : Gaussian :=
  toGaussian (RFAP.HurwitzGeometry.conjugate unit) * value

/-- Apply the matching unit rotation to normalized denominator data. -/
def rotateDenominatorRatio
    (unit : GaussianInt) (value : Gaussian) : Gaussian :=
  toGaussian unit * value

private theorem normSq_conj (value : Gaussian) :
    normSq (RFAP.ConstructiveGaussian.Gaussian.conj value) =
      normSq value := by
  dsimp only [normSq, RFAP.ConstructiveGaussian.Gaussian.conj]
  ring1

private theorem normSq_rotateErrorRatio
    (unit : GaussianInt) (unitNorm : normNat unit = 1)
    (value : Gaussian) :
    normSq (rotateErrorRatio unit value) = normSq value := by
  unfold rotateErrorRatio
  rw [normSq_mul, normSq_toGaussian,
    RFAP.HurwitzGeometry.normNat_conjugate, unitNorm]
  ring1

private theorem normSq_rotateDenominatorRatio
    (unit : GaussianInt) (unitNorm : normNat unit = 1)
    (value : Gaussian) :
    normSq (rotateDenominatorRatio unit value) = normSq value := by
  unfold rotateDenominatorRatio
  rw [normSq_mul, normSq_toGaussian, unitNorm]
  ring1

private theorem rotatedProduct
    (unit : GaussianInt) (unitNorm : normNat unit = 1)
    (errorRatio denominatorRatio : Gaussian) :
    rotateDenominatorRatio unit denominatorRatio *
        rotateErrorRatio unit errorRatio =
      denominatorRatio * errorRatio := by
  have unitProperty :=
    RFAP.HurwitzGeometry.isGaussianUnit_of_normNat_eq_one unitNorm
  have unitInverseInteger :
      unit * RFAP.HurwitzGeometry.conjugate unit = 1 :=
    RFAP.HurwitzGeometry.self_mul_conjugate_of_isGaussianUnit unitProperty
  have unitInverse :
      toGaussian unit *
          toGaussian (RFAP.HurwitzGeometry.conjugate unit) =
        (1 : Gaussian) := by
    rw [← toGaussian_mul, unitInverseInteger, toGaussian_one]
  unfold rotateDenominatorRatio rotateErrorRatio
  calc
    (toGaussian unit * denominatorRatio) *
        (toGaussian (RFAP.HurwitzGeometry.conjugate unit) * errorRatio) =
      (toGaussian unit *
          toGaussian (RFAP.HurwitzGeometry.conjugate unit)) *
        (denominatorRatio * errorRatio) := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [RFAP.ConstructiveGaussian.Gaussian.mul_re,
          RFAP.ConstructiveGaussian.Gaussian.mul_im] <;>
        ring1
    _ = denominatorRatio * errorRatio := by
      rw [unitInverse, RFAP.ConstructiveGaussian.Gaussian.one_mul]

private theorem rotatedCoefficientExterior
    (unit : GaussianInt) (unitNorm : normNat unit = 1)
    (errorRatio denominatorRatio : Gaussian)
    (coefficientExterior : ∀ coefficient : GaussianInt,
      (1 : Coordinate) ≤ normSq (errorRatio - toGaussian coefficient) ∨
        1 ≤ normSq (1 - toGaussian coefficient * denominatorRatio)) :
    ∀ coefficient : GaussianInt,
      (1 : Coordinate) ≤
          normSq (rotateErrorRatio unit errorRatio - toGaussian coefficient) ∨
        1 ≤ normSq
          (1 - toGaussian coefficient *
            rotateDenominatorRatio unit denominatorRatio) := by
  intro coefficient
  let inverseUnit := RFAP.HurwitzGeometry.conjugate unit
  let sourceCoefficient := unit * coefficient
  have unitProperty :=
    RFAP.HurwitzGeometry.isGaussianUnit_of_normNat_eq_one unitNorm
  have inverseUnitNorm : normNat inverseUnit = 1 := by
    dsimp only [inverseUnit]
    rw [RFAP.HurwitzGeometry.normNat_conjugate, unitNorm]
  have inverseUnitQuadrance :
      normSq (toGaussian inverseUnit) = (1 : Coordinate) := by
    rw [normSq_toGaussian, inverseUnitNorm]
    rfl
  have inverseUnitIdentity : inverseUnit * unit = 1 := by
    dsimp only [inverseUnit]
    exact RFAP.HurwitzGeometry.conjugate_mul_self_of_isGaussianUnit
      unitProperty
  rcases coefficientExterior sourceCoefficient with
      errorExterior | denominatorExterior
  · left
    have differenceIdentity :
        rotateErrorRatio unit errorRatio - toGaussian coefficient =
          toGaussian inverseUnit *
            (errorRatio - toGaussian sourceCoefficient) := by
      dsimp only [rotateErrorRatio, inverseUnit, sourceCoefficient]
      rw [toGaussian_mul]
      have inverseIdentity :
          toGaussian (RFAP.HurwitzGeometry.conjugate unit) *
              toGaussian unit = (1 : Gaussian) := by
        rw [← toGaussian_mul, inverseUnitIdentity, toGaussian_one]
      calc
        toGaussian (RFAP.HurwitzGeometry.conjugate unit) * errorRatio -
              toGaussian coefficient =
            toGaussian (RFAP.HurwitzGeometry.conjugate unit) * errorRatio -
              (1 : Gaussian) * toGaussian coefficient := by
          rw [RFAP.ConstructiveGaussian.Gaussian.one_mul]
        _ = toGaussian (RFAP.HurwitzGeometry.conjugate unit) * errorRatio -
              (toGaussian (RFAP.HurwitzGeometry.conjugate unit) *
                toGaussian unit) * toGaussian coefficient := by
          rw [inverseIdentity]
        _ = toGaussian (RFAP.HurwitzGeometry.conjugate unit) *
              (errorRatio - toGaussian unit * toGaussian coefficient) := by
          apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
            simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
              RFAP.ConstructiveGaussian.Gaussian.sub_im,
              RFAP.ConstructiveGaussian.Gaussian.mul_re,
              RFAP.ConstructiveGaussian.Gaussian.mul_im] <;>
            ring1
    rw [differenceIdentity, normSq_mul, inverseUnitQuadrance]
    calc
      (1 : Coordinate) ≤
          normSq (errorRatio - toGaussian sourceCoefficient) := errorExterior
      _ = 1 * normSq (errorRatio - toGaussian sourceCoefficient) := by ring1
  · right
    have differenceIdentity :
        1 - toGaussian coefficient *
            rotateDenominatorRatio unit denominatorRatio =
          1 - toGaussian sourceCoefficient * denominatorRatio := by
      dsimp only [rotateDenominatorRatio, sourceCoefficient]
      rw [toGaussian_mul]
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
          RFAP.ConstructiveGaussian.Gaussian.sub_im,
          RFAP.ConstructiveGaussian.Gaussian.mul_re,
          RFAP.ConstructiveGaussian.Gaussian.mul_im,
          RFAP.ConstructiveGaussian.Gaussian.one_re,
          RFAP.ConstructiveGaussian.Gaussian.one_im] <;>
        ring1
    rw [differenceIdentity]
    exact denominatorExterior

private theorem rotatedLinearCombinationExterior
    (unit : GaussianInt) (unitNorm : normNat unit = 1)
    (errorRatio denominatorRatio : Gaussian)
    (linearCombinationExterior :
      ∀ leftCoefficient rightCoefficient : GaussianInt,
        leftCoefficient ≠ 0 ∨ rightCoefficient ≠ 0 →
          (1 : Coordinate) ≤
              normSq
                (toGaussian leftCoefficient +
                  toGaussian rightCoefficient * errorRatio) ∨
            1 ≤
              normSq
                (toGaussian leftCoefficient * denominatorRatio +
                  toGaussian rightCoefficient)) :
    ∀ leftCoefficient rightCoefficient : GaussianInt,
      leftCoefficient ≠ 0 ∨ rightCoefficient ≠ 0 →
        (1 : Coordinate) ≤
            normSq
              (toGaussian leftCoefficient +
                toGaussian rightCoefficient *
                  rotateErrorRatio unit errorRatio) ∨
          1 ≤
            normSq
              (toGaussian leftCoefficient *
                  rotateDenominatorRatio unit denominatorRatio +
                toGaussian rightCoefficient) := by
  intro leftCoefficient rightCoefficient coefficientNonzero
  let sourceLeft := unit * leftCoefficient
  have sourceNonzero : sourceLeft ≠ 0 ∨ rightCoefficient ≠ 0 := by
    rcases coefficientNonzero with leftNonzero | rightNonzero
    · left
      intro sourceZero
      have sourceNormZero : normNat sourceLeft = 0 := by rw [sourceZero]; rfl
      have leftNormZero : normNat leftCoefficient = 0 := by
        dsimp only [sourceLeft] at sourceNormZero
        rw [normNat_mul, unitNorm, Nat.one_mul] at sourceNormZero
        exact sourceNormZero
      exact leftNonzero
        (RFAP.HurwitzGeometry.eq_zero_of_normNat_eq_zero leftNormZero)
    · exact Or.inr rightNonzero
  rcases linearCombinationExterior sourceLeft rightCoefficient sourceNonzero with
      errorExterior | denominatorExterior
  · left
    have unitQuadrance : normSq (toGaussian unit) = (1 : Coordinate) := by
      rw [normSq_toGaussian, unitNorm]
      rfl
    have identity :
        toGaussian sourceLeft + toGaussian rightCoefficient * errorRatio =
          toGaussian unit *
            (toGaussian leftCoefficient +
              toGaussian rightCoefficient *
                rotateErrorRatio unit errorRatio) := by
      have unitProperty :=
        RFAP.HurwitzGeometry.isGaussianUnit_of_normNat_eq_one unitNorm
      have inverseIdentity :
          toGaussian unit *
              toGaussian (RFAP.HurwitzGeometry.conjugate unit) =
            (1 : Gaussian) := by
        rw [← toGaussian_mul,
          RFAP.HurwitzGeometry.self_mul_conjugate_of_isGaussianUnit
            unitProperty,
          toGaussian_one]
      dsimp only [sourceLeft, rotateErrorRatio]
      rw [toGaussian_mul]
      calc
        toGaussian unit * toGaussian leftCoefficient +
              toGaussian rightCoefficient * errorRatio =
            toGaussian unit * toGaussian leftCoefficient +
              toGaussian rightCoefficient *
                ((toGaussian unit *
                    toGaussian (RFAP.HurwitzGeometry.conjugate unit)) *
                  errorRatio) := by
            rw [inverseIdentity,
              RFAP.ConstructiveGaussian.Gaussian.one_mul]
        _ = toGaussian unit *
            (toGaussian leftCoefficient +
              toGaussian rightCoefficient *
                (toGaussian (RFAP.HurwitzGeometry.conjugate unit) *
                  errorRatio)) := by
          apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
            simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
              RFAP.ConstructiveGaussian.Gaussian.add_im,
              RFAP.ConstructiveGaussian.Gaussian.mul_re,
              RFAP.ConstructiveGaussian.Gaussian.mul_im] <;>
            ring1
    rw [identity, normSq_mul, unitQuadrance] at errorExterior
    calc
      (1 : Coordinate) ≤ 1 *
          normSq
            (toGaussian leftCoefficient +
              toGaussian rightCoefficient *
                rotateErrorRatio unit errorRatio) := errorExterior
      _ = normSq
          (toGaussian leftCoefficient +
            toGaussian rightCoefficient *
              rotateErrorRatio unit errorRatio) := by ring1
  · right
    have identity :
        toGaussian sourceLeft * denominatorRatio +
            toGaussian rightCoefficient =
          toGaussian leftCoefficient *
              rotateDenominatorRatio unit denominatorRatio +
            toGaussian rightCoefficient := by
      dsimp only [sourceLeft, rotateDenominatorRatio]
      rw [toGaussian_mul]
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
          RFAP.ConstructiveGaussian.Gaussian.add_im,
          RFAP.ConstructiveGaussian.Gaussian.mul_re,
          RFAP.ConstructiveGaussian.Gaussian.mul_im] <;>
        ring1
    rw [← identity]
    exact denominatorExterior

private theorem conjugatedCoefficientExterior
    (errorRatio denominatorRatio : Gaussian)
    (coefficientExterior : ∀ coefficient : GaussianInt,
      (1 : Coordinate) ≤ normSq (errorRatio - toGaussian coefficient) ∨
        1 ≤ normSq (1 - toGaussian coefficient * denominatorRatio)) :
    ∀ coefficient : GaussianInt,
      (1 : Coordinate) ≤
          normSq (RFAP.ConstructiveGaussian.Gaussian.conj errorRatio -
            toGaussian coefficient) ∨
        1 ≤ normSq
          (1 - toGaussian coefficient *
            RFAP.ConstructiveGaussian.Gaussian.conj denominatorRatio) := by
  intro coefficient
  let sourceCoefficient :=
    RFAP.ConstructiveGaussianHeight.GaussianInt.conj coefficient
  rcases coefficientExterior sourceCoefficient with
      errorExterior | denominatorExterior
  · left
    have differenceIdentity :
        RFAP.ConstructiveGaussian.Gaussian.conj errorRatio -
            toGaussian coefficient =
          RFAP.ConstructiveGaussian.Gaussian.conj
            (errorRatio - toGaussian sourceCoefficient) := by
      dsimp only [sourceCoefficient,
        RFAP.ConstructiveGaussianHeight.GaussianInt.conj, toGaussian,
        RFAP.ConstructiveGaussian.Gaussian.conj]
      apply RFAP.ConstructiveGaussian.Gaussian.ext
      · rfl
      · simp only [RFAP.ConstructiveGaussian.Gaussian.sub_im, Int.cast_neg]
        ring1
    rw [differenceIdentity, normSq_conj]
    exact errorExterior
  · right
    have differenceIdentity :
        1 - toGaussian coefficient *
            RFAP.ConstructiveGaussian.Gaussian.conj denominatorRatio =
          RFAP.ConstructiveGaussian.Gaussian.conj
            (1 - toGaussian sourceCoefficient * denominatorRatio) := by
      dsimp only [sourceCoefficient,
        RFAP.ConstructiveGaussianHeight.GaussianInt.conj, toGaussian,
        RFAP.ConstructiveGaussian.Gaussian.conj]
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
          RFAP.ConstructiveGaussian.Gaussian.sub_im,
          RFAP.ConstructiveGaussian.Gaussian.mul_re,
          RFAP.ConstructiveGaussian.Gaussian.mul_im,
          RFAP.ConstructiveGaussian.Gaussian.one_re,
          RFAP.ConstructiveGaussian.Gaussian.one_im, Int.cast_neg] <;>
        ring1
    rw [differenceIdentity, normSq_conj]
    exact denominatorExterior

private theorem conjugatedLinearCombinationExterior
    (errorRatio denominatorRatio : Gaussian)
    (linearCombinationExterior :
      ∀ leftCoefficient rightCoefficient : GaussianInt,
        leftCoefficient ≠ 0 ∨ rightCoefficient ≠ 0 →
          (1 : Coordinate) ≤
              normSq
                (toGaussian leftCoefficient +
                  toGaussian rightCoefficient * errorRatio) ∨
            1 ≤
              normSq
                (toGaussian leftCoefficient * denominatorRatio +
                  toGaussian rightCoefficient)) :
    ∀ leftCoefficient rightCoefficient : GaussianInt,
      leftCoefficient ≠ 0 ∨ rightCoefficient ≠ 0 →
        (1 : Coordinate) ≤
            normSq
              (toGaussian leftCoefficient +
                toGaussian rightCoefficient *
                  RFAP.ConstructiveGaussian.Gaussian.conj errorRatio) ∨
          1 ≤
            normSq
              (toGaussian leftCoefficient *
                  RFAP.ConstructiveGaussian.Gaussian.conj denominatorRatio +
                toGaussian rightCoefficient) := by
  intro leftCoefficient rightCoefficient coefficientNonzero
  let sourceLeft :=
    RFAP.ConstructiveGaussianHeight.GaussianInt.conj leftCoefficient
  let sourceRight :=
    RFAP.ConstructiveGaussianHeight.GaussianInt.conj rightCoefficient
  have sourceNonzero : sourceLeft ≠ 0 ∨ sourceRight ≠ 0 := by
    rcases coefficientNonzero with leftNonzero | rightNonzero
    · left
      intro sourceZero
      have sourceNormZero : normNat sourceLeft = 0 := by rw [sourceZero]; rfl
      have leftNormZero : normNat leftCoefficient = 0 := by
        dsimp only [sourceLeft] at sourceNormZero
        rw [RFAP.ConstructiveGaussianHeight.GaussianInt.normNat_conj] at sourceNormZero
        exact sourceNormZero
      exact leftNonzero
        (RFAP.HurwitzGeometry.eq_zero_of_normNat_eq_zero leftNormZero)
    · right
      intro sourceZero
      have sourceNormZero : normNat sourceRight = 0 := by rw [sourceZero]; rfl
      have rightNormZero : normNat rightCoefficient = 0 := by
        dsimp only [sourceRight] at sourceNormZero
        rw [RFAP.ConstructiveGaussianHeight.GaussianInt.normNat_conj] at sourceNormZero
        exact sourceNormZero
      exact rightNonzero
        (RFAP.HurwitzGeometry.eq_zero_of_normNat_eq_zero rightNormZero)
  rcases linearCombinationExterior sourceLeft sourceRight sourceNonzero with
      errorExterior | denominatorExterior
  · left
    have identity :
        toGaussian leftCoefficient +
            toGaussian rightCoefficient *
              RFAP.ConstructiveGaussian.Gaussian.conj errorRatio =
          RFAP.ConstructiveGaussian.Gaussian.conj
            (toGaussian sourceLeft +
              toGaussian sourceRight * errorRatio) := by
      dsimp only [sourceLeft, sourceRight]
      rw [RFAP.ConstructiveGaussian.Gaussian.conj_add,
        RFAP.ConstructiveGaussian.Gaussian.conj_mul,
        RFAP.ConstructiveGaussianHeight.GaussianInt.toGaussian_conj,
        RFAP.ConstructiveGaussianHeight.GaussianInt.toGaussian_conj,
        RFAP.ConstructiveGaussian.Gaussian.conj_conj,
        RFAP.ConstructiveGaussian.Gaussian.conj_conj]
    rw [identity, normSq_conj]
    exact errorExterior
  · right
    have identity :
        toGaussian leftCoefficient *
              RFAP.ConstructiveGaussian.Gaussian.conj denominatorRatio +
            toGaussian rightCoefficient =
          RFAP.ConstructiveGaussian.Gaussian.conj
            (toGaussian sourceLeft * denominatorRatio +
              toGaussian sourceRight) := by
      dsimp only [sourceLeft, sourceRight]
      rw [RFAP.ConstructiveGaussian.Gaussian.conj_add,
        RFAP.ConstructiveGaussian.Gaussian.conj_mul,
        RFAP.ConstructiveGaussianHeight.GaussianInt.toGaussian_conj,
        RFAP.ConstructiveGaussianHeight.GaussianInt.toGaussian_conj,
        RFAP.ConstructiveGaussian.Gaussian.conj_conj,
        RFAP.ConstructiveGaussian.Gaussian.conj_conj]
    rw [identity, normSq_conj]
    exact denominatorExterior

private theorem rotatedCenteredUnitObstruction
    (unit : GaussianInt) (unitNorm : normNat unit = 1)
    (errorRatio denominatorRatio : Gaussian)
    (obstruction : ∀ centeredUnit : GaussianInt,
      normNat centeredUnit = 1 →
        (2 : Coordinate) ≤
            normSq (errorRatio - toGaussian centeredUnit) ∨
          2 ≤ normSq
            (1 - toGaussian centeredUnit * denominatorRatio)) :
    ∀ centeredUnit : GaussianInt, normNat centeredUnit = 1 →
      (2 : Coordinate) ≤
          normSq (rotateErrorRatio unit errorRatio -
            toGaussian centeredUnit) ∨
        2 ≤ normSq
          (1 - toGaussian centeredUnit *
            rotateDenominatorRatio unit denominatorRatio) := by
  intro centeredUnit centeredUnitNorm
  let inverseUnit := RFAP.HurwitzGeometry.conjugate unit
  let sourceUnit := unit * centeredUnit
  have sourceUnitNorm : normNat sourceUnit = 1 := by
    dsimp only [sourceUnit]
    rw [normNat_mul, unitNorm, centeredUnitNorm, Nat.one_mul]
  have unitProperty :=
    RFAP.HurwitzGeometry.isGaussianUnit_of_normNat_eq_one unitNorm
  have inverseUnitNorm : normNat inverseUnit = 1 := by
    dsimp only [inverseUnit]
    rw [RFAP.HurwitzGeometry.normNat_conjugate, unitNorm]
  have inverseUnitQuadrance :
      normSq (toGaussian inverseUnit) = (1 : Coordinate) := by
    rw [normSq_toGaussian, inverseUnitNorm]
    rfl
  have inverseUnitIdentity : inverseUnit * unit = 1 := by
    dsimp only [inverseUnit]
    exact RFAP.HurwitzGeometry.conjugate_mul_self_of_isGaussianUnit
      unitProperty
  rcases obstruction sourceUnit sourceUnitNorm with
      errorExterior | denominatorExterior
  · left
    have differenceIdentity :
        rotateErrorRatio unit errorRatio - toGaussian centeredUnit =
          toGaussian inverseUnit *
            (errorRatio - toGaussian sourceUnit) := by
      dsimp only [rotateErrorRatio, inverseUnit, sourceUnit]
      rw [toGaussian_mul]
      have inverseIdentity :
          toGaussian (RFAP.HurwitzGeometry.conjugate unit) *
              toGaussian unit = (1 : Gaussian) := by
        rw [← toGaussian_mul, inverseUnitIdentity, toGaussian_one]
      calc
        toGaussian (RFAP.HurwitzGeometry.conjugate unit) * errorRatio -
              toGaussian centeredUnit =
            toGaussian (RFAP.HurwitzGeometry.conjugate unit) * errorRatio -
              (1 : Gaussian) * toGaussian centeredUnit := by
          rw [RFAP.ConstructiveGaussian.Gaussian.one_mul]
        _ = toGaussian (RFAP.HurwitzGeometry.conjugate unit) * errorRatio -
              (toGaussian (RFAP.HurwitzGeometry.conjugate unit) *
                toGaussian unit) * toGaussian centeredUnit := by
          rw [inverseIdentity]
        _ = toGaussian (RFAP.HurwitzGeometry.conjugate unit) *
              (errorRatio - toGaussian unit * toGaussian centeredUnit) := by
          apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
            simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
              RFAP.ConstructiveGaussian.Gaussian.sub_im,
              RFAP.ConstructiveGaussian.Gaussian.mul_re,
              RFAP.ConstructiveGaussian.Gaussian.mul_im] <;>
            ring1
    rw [differenceIdentity, normSq_mul, inverseUnitQuadrance]
    calc
      (2 : Coordinate) ≤
          normSq (errorRatio - toGaussian sourceUnit) := errorExterior
      _ = 1 * normSq (errorRatio - toGaussian sourceUnit) := by ring1
  · right
    have differenceIdentity :
        1 - toGaussian centeredUnit *
            rotateDenominatorRatio unit denominatorRatio =
          1 - toGaussian sourceUnit * denominatorRatio := by
      dsimp only [rotateDenominatorRatio, sourceUnit]
      rw [toGaussian_mul]
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
          RFAP.ConstructiveGaussian.Gaussian.sub_im,
          RFAP.ConstructiveGaussian.Gaussian.mul_re,
          RFAP.ConstructiveGaussian.Gaussian.mul_im,
          RFAP.ConstructiveGaussian.Gaussian.one_re,
          RFAP.ConstructiveGaussian.Gaussian.one_im] <;>
        ring1
    rw [differenceIdentity]
    exact denominatorExterior

private theorem conjugatedCenteredUnitObstruction
    (errorRatio denominatorRatio : Gaussian)
    (obstruction : ∀ centeredUnit : GaussianInt,
      normNat centeredUnit = 1 →
        (2 : Coordinate) ≤
            normSq (errorRatio - toGaussian centeredUnit) ∨
          2 ≤ normSq
            (1 - toGaussian centeredUnit * denominatorRatio)) :
    ∀ centeredUnit : GaussianInt, normNat centeredUnit = 1 →
      (2 : Coordinate) ≤ normSq
          (RFAP.ConstructiveGaussian.Gaussian.conj errorRatio -
            toGaussian centeredUnit) ∨
        2 ≤ normSq
          (1 - toGaussian centeredUnit *
            RFAP.ConstructiveGaussian.Gaussian.conj denominatorRatio) := by
  intro centeredUnit centeredUnitNorm
  let sourceUnit :=
    RFAP.ConstructiveGaussianHeight.GaussianInt.conj centeredUnit
  have sourceUnitNorm : normNat sourceUnit = 1 := by
    dsimp only [sourceUnit]
    rw [RFAP.ConstructiveGaussianHeight.GaussianInt.normNat_conj,
      centeredUnitNorm]
  rcases obstruction sourceUnit sourceUnitNorm with
      errorExterior | denominatorExterior
  · left
    have differenceIdentity :
        RFAP.ConstructiveGaussian.Gaussian.conj errorRatio -
            toGaussian centeredUnit =
          RFAP.ConstructiveGaussian.Gaussian.conj
            (errorRatio - toGaussian sourceUnit) := by
      dsimp only [sourceUnit,
        RFAP.ConstructiveGaussianHeight.GaussianInt.conj, toGaussian,
        RFAP.ConstructiveGaussian.Gaussian.conj]
      apply RFAP.ConstructiveGaussian.Gaussian.ext
      · rfl
      · simp only [RFAP.ConstructiveGaussian.Gaussian.sub_im,
          Int.cast_neg]
        ring1
    rw [differenceIdentity, normSq_conj]
    exact errorExterior
  · right
    have differenceIdentity :
        1 - toGaussian centeredUnit *
            RFAP.ConstructiveGaussian.Gaussian.conj denominatorRatio =
          RFAP.ConstructiveGaussian.Gaussian.conj
            (1 - toGaussian sourceUnit * denominatorRatio) := by
      dsimp only [sourceUnit,
        RFAP.ConstructiveGaussianHeight.GaussianInt.conj, toGaussian,
        RFAP.ConstructiveGaussian.Gaussian.conj]
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
          RFAP.ConstructiveGaussian.Gaussian.sub_im,
          RFAP.ConstructiveGaussian.Gaussian.mul_re,
          RFAP.ConstructiveGaussian.Gaussian.mul_im,
          RFAP.ConstructiveGaussian.Gaussian.one_re,
          RFAP.ConstructiveGaussian.Gaussian.one_im, Int.cast_neg] <;>
        ring1
    rw [differenceIdentity, normSq_conj]
    exact denominatorExterior

private theorem conjugatedProductGapNorm
    (errorRatio denominatorRatio : Gaussian) :
    normSq (1 - RFAP.ConstructiveGaussian.Gaussian.conj denominatorRatio *
      RFAP.ConstructiveGaussian.Gaussian.conj errorRatio) =
      normSq (1 - denominatorRatio * errorRatio) := by
  have identity :
      1 - RFAP.ConstructiveGaussian.Gaussian.conj denominatorRatio *
          RFAP.ConstructiveGaussian.Gaussian.conj errorRatio =
        RFAP.ConstructiveGaussian.Gaussian.conj
          (1 - denominatorRatio * errorRatio) := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
        RFAP.ConstructiveGaussian.Gaussian.sub_im,
        RFAP.ConstructiveGaussian.Gaussian.mul_re,
        RFAP.ConstructiveGaussian.Gaussian.mul_im,
        RFAP.ConstructiveGaussian.Gaussian.one_re,
        RFAP.ConstructiveGaussian.Gaussian.one_im,
        RFAP.ConstructiveGaussian.Gaussian.conj] <;>
      ring1
  rw [identity, normSq_conj]

private theorem dyadicCenteredGapThreshold_le_of_rotatedFirstOctant
    (unit : GaussianInt) (unitNorm : normNat unit = 1)
    (errorRatio denominatorRatio : Gaussian)
    (realNonnegative : 0 ≤ (rotateErrorRatio unit errorRatio).re)
    (imaginaryNonnegative : 0 ≤ (rotateErrorRatio unit errorRatio).im)
    (imaginaryLeReal :
      (rotateErrorRatio unit errorRatio).im ≤
        (rotateErrorRatio unit errorRatio).re)
    (errorInside : normSq errorRatio < 1)
    (denominatorInside : normSq denominatorRatio < 1)
    (obstruction : ∀ centeredUnit : GaussianInt,
      normNat centeredUnit = 1 →
        (2 : Coordinate) ≤
            normSq (errorRatio - toGaussian centeredUnit) ∨
          2 ≤ normSq
            (1 - toGaussian centeredUnit * denominatorRatio)) :
    RFAP.IndexTwoWindow.dyadicCenteredGapThreshold ≤
      normSq (1 - denominatorRatio * errorRatio) := by
  have rotatedErrorInside : normSq (rotateErrorRatio unit errorRatio) < 1 := by
    rw [normSq_rotateErrorRatio unit unitNorm]
    exact errorInside
  have rotatedDenominatorInside :
      normSq (rotateDenominatorRatio unit denominatorRatio) < 1 := by
    rw [normSq_rotateDenominatorRatio unit unitNorm]
    exact denominatorInside
  have result :=
    RFAP.IndexTwoWindow.dyadicCenteredGapThreshold_le_determinantGap_of_firstOctantObstructions
      (rotateErrorRatio unit errorRatio)
      (rotateDenominatorRatio unit denominatorRatio)
      realNonnegative imaginaryNonnegative imaginaryLeReal rotatedErrorInside
      rotatedDenominatorInside
      (rotatedCenteredUnitObstruction unit unitNorm errorRatio
        denominatorRatio obstruction)
  rw [rotatedProduct unit unitNorm errorRatio denominatorRatio] at result
  exact result

private theorem dyadicCenteredGapThreshold_le_of_reflectedRotatedFirstOctant
    (unit : GaussianInt) (unitNorm : normNat unit = 1)
    (errorRatio denominatorRatio : Gaussian)
    (realNonnegative :
      0 ≤ (RFAP.ConstructiveGaussian.Gaussian.conj
        (rotateErrorRatio unit errorRatio)).re)
    (imaginaryNonnegative :
      0 ≤ (RFAP.ConstructiveGaussian.Gaussian.conj
        (rotateErrorRatio unit errorRatio)).im)
    (imaginaryLeReal :
      (RFAP.ConstructiveGaussian.Gaussian.conj
          (rotateErrorRatio unit errorRatio)).im ≤
        (RFAP.ConstructiveGaussian.Gaussian.conj
          (rotateErrorRatio unit errorRatio)).re)
    (errorInside : normSq errorRatio < 1)
    (denominatorInside : normSq denominatorRatio < 1)
    (obstruction : ∀ centeredUnit : GaussianInt,
      normNat centeredUnit = 1 →
        (2 : Coordinate) ≤
            normSq (errorRatio - toGaussian centeredUnit) ∨
          2 ≤ normSq
            (1 - toGaussian centeredUnit * denominatorRatio)) :
    RFAP.IndexTwoWindow.dyadicCenteredGapThreshold ≤
      normSq (1 - denominatorRatio * errorRatio) := by
  let rotatedError := rotateErrorRatio unit errorRatio
  let rotatedDenominator := rotateDenominatorRatio unit denominatorRatio
  have reflectedErrorInside :
      normSq (RFAP.ConstructiveGaussian.Gaussian.conj rotatedError) < 1 := by
    rw [normSq_conj, normSq_rotateErrorRatio unit unitNorm]
    exact errorInside
  have reflectedDenominatorInside :
      normSq (RFAP.ConstructiveGaussian.Gaussian.conj rotatedDenominator) < 1 := by
    rw [normSq_conj, normSq_rotateDenominatorRatio unit unitNorm]
    exact denominatorInside
  have rotatedObstruction := rotatedCenteredUnitObstruction unit unitNorm
    errorRatio denominatorRatio obstruction
  have result :=
    RFAP.IndexTwoWindow.dyadicCenteredGapThreshold_le_determinantGap_of_firstOctantObstructions
      (RFAP.ConstructiveGaussian.Gaussian.conj rotatedError)
      (RFAP.ConstructiveGaussian.Gaussian.conj rotatedDenominator)
      realNonnegative imaginaryNonnegative imaginaryLeReal
      reflectedErrorInside reflectedDenominatorInside
      (conjugatedCenteredUnitObstruction rotatedError rotatedDenominator
        rotatedObstruction)
  rw [conjugatedProductGapNorm rotatedError rotatedDenominator] at result
  dsimp only [rotatedError, rotatedDenominator] at result
  rw [rotatedProduct unit unitNorm errorRatio denominatorRatio] at result
  exact result

private theorem twice_gapThreshold_le_of_rotatedFirstOctant
    (gap : Coordinate)
    (certificate : RFAP.OptimalIndexTwoWindow.IsCenteredGapThreshold gap)
    (unit : GaussianInt) (unitNorm : normNat unit = 1)
    (errorRatio denominatorRatio : Gaussian)
    (realNonnegative : 0 ≤ (rotateErrorRatio unit errorRatio).re)
    (imaginaryNonnegative : 0 ≤ (rotateErrorRatio unit errorRatio).im)
    (imaginaryLeReal :
      (rotateErrorRatio unit errorRatio).im ≤
        (rotateErrorRatio unit errorRatio).re)
    (errorInside : normSq errorRatio < 1)
    (denominatorInside : normSq denominatorRatio < 1)
    (obstruction : ∀ centeredUnit : GaussianInt,
      normNat centeredUnit = 1 →
        (2 : Coordinate) ≤
            normSq (errorRatio - toGaussian centeredUnit) ∨
          2 ≤ normSq
            (1 - toGaussian centeredUnit * denominatorRatio)) :
    2 * gap ≤ normSq (1 - denominatorRatio * errorRatio) := by
  have rotatedErrorInside : normSq (rotateErrorRatio unit errorRatio) < 1 := by
    rw [normSq_rotateErrorRatio unit unitNorm]
    exact errorInside
  have rotatedDenominatorInside :
      normSq (rotateDenominatorRatio unit denominatorRatio) < 1 := by
    rw [normSq_rotateDenominatorRatio unit unitNorm]
    exact denominatorInside
  have result :=
    RFAP.OptimalIndexTwoWindow.twice_gapThreshold_le_determinantGap_of_firstOctantObstructions
      gap certificate (rotateErrorRatio unit errorRatio)
      (rotateDenominatorRatio unit denominatorRatio) realNonnegative
      imaginaryNonnegative imaginaryLeReal rotatedErrorInside
      rotatedDenominatorInside
      (rotatedCenteredUnitObstruction unit unitNorm errorRatio
        denominatorRatio obstruction)
  rw [rotatedProduct unit unitNorm errorRatio denominatorRatio] at result
  exact result

private theorem twice_gapThreshold_le_of_reflectedRotatedFirstOctant
    (gap : Coordinate)
    (certificate : RFAP.OptimalIndexTwoWindow.IsCenteredGapThreshold gap)
    (unit : GaussianInt) (unitNorm : normNat unit = 1)
    (errorRatio denominatorRatio : Gaussian)
    (realNonnegative :
      0 ≤ (RFAP.ConstructiveGaussian.Gaussian.conj
        (rotateErrorRatio unit errorRatio)).re)
    (imaginaryNonnegative :
      0 ≤ (RFAP.ConstructiveGaussian.Gaussian.conj
        (rotateErrorRatio unit errorRatio)).im)
    (imaginaryLeReal :
      (RFAP.ConstructiveGaussian.Gaussian.conj
          (rotateErrorRatio unit errorRatio)).im ≤
        (RFAP.ConstructiveGaussian.Gaussian.conj
          (rotateErrorRatio unit errorRatio)).re)
    (errorInside : normSq errorRatio < 1)
    (denominatorInside : normSq denominatorRatio < 1)
    (obstruction : ∀ centeredUnit : GaussianInt,
      normNat centeredUnit = 1 →
        (2 : Coordinate) ≤
            normSq (errorRatio - toGaussian centeredUnit) ∨
          2 ≤ normSq
            (1 - toGaussian centeredUnit * denominatorRatio)) :
    2 * gap ≤ normSq (1 - denominatorRatio * errorRatio) := by
  let rotatedError := rotateErrorRatio unit errorRatio
  let rotatedDenominator := rotateDenominatorRatio unit denominatorRatio
  have reflectedErrorInside :
      normSq (RFAP.ConstructiveGaussian.Gaussian.conj rotatedError) < 1 := by
    rw [normSq_conj, normSq_rotateErrorRatio unit unitNorm]
    exact errorInside
  have reflectedDenominatorInside :
      normSq (RFAP.ConstructiveGaussian.Gaussian.conj rotatedDenominator) < 1 := by
    rw [normSq_conj, normSq_rotateDenominatorRatio unit unitNorm]
    exact denominatorInside
  have rotatedObstruction := rotatedCenteredUnitObstruction unit unitNorm
    errorRatio denominatorRatio obstruction
  have result :=
    RFAP.OptimalIndexTwoWindow.twice_gapThreshold_le_determinantGap_of_firstOctantObstructions
      gap certificate
      (RFAP.ConstructiveGaussian.Gaussian.conj rotatedError)
      (RFAP.ConstructiveGaussian.Gaussian.conj rotatedDenominator)
      realNonnegative imaginaryNonnegative imaginaryLeReal
      reflectedErrorInside reflectedDenominatorInside
      (conjugatedCenteredUnitObstruction rotatedError rotatedDenominator
        rotatedObstruction)
  rw [conjugatedProductGapNorm rotatedError rotatedDenominator] at result
  dsimp only [rotatedError, rotatedDenominator] at result
  rw [rotatedProduct unit unitNorm errorRatio denominatorRatio] at result
  exact result

private theorem fifteen_twenty_eighths_le_determinantGap_of_rotatedFirstOctant
    (unit : GaussianInt) (unitNorm : normNat unit = 1)
    (errorRatio denominatorRatio : Gaussian)
    (realNonnegative : 0 ≤ (rotateErrorRatio unit errorRatio).re)
    (imaginaryNonnegative : 0 ≤ (rotateErrorRatio unit errorRatio).im)
    (imaginaryLeReal :
      (rotateErrorRatio unit errorRatio).im ≤
        (rotateErrorRatio unit errorRatio).re)
    (errorInside : normSq errorRatio < 1)
    (denominatorInside : normSq denominatorRatio < 1)
    (coefficientExterior : ∀ coefficient : GaussianInt,
      (1 : Coordinate) ≤ normSq (errorRatio - toGaussian coefficient) ∨
        1 ≤ normSq (1 - toGaussian coefficient * denominatorRatio)) :
    (15 / 28 : Coordinate) ≤
      normSq (1 - denominatorRatio * errorRatio) := by
  have rotatedErrorInside : normSq (rotateErrorRatio unit errorRatio) < 1 := by
    rw [normSq_rotateErrorRatio unit unitNorm]
    exact errorInside
  have rotatedDenominatorInside :
      normSq (rotateDenominatorRatio unit denominatorRatio) < 1 := by
    rw [normSq_rotateDenominatorRatio unit unitNorm]
    exact denominatorInside
  have result := fifteen_twenty_eighths_le_determinantGap_of_firstOctantObstructions
    (rotateErrorRatio unit errorRatio)
    (rotateDenominatorRatio unit denominatorRatio)
    realNonnegative imaginaryNonnegative imaginaryLeReal rotatedErrorInside
    rotatedDenominatorInside
    (rotatedCoefficientExterior unit unitNorm errorRatio denominatorRatio
      coefficientExterior)
  rw [rotatedProduct unit unitNorm errorRatio denominatorRatio] at result
  exact result

private theorem fifteen_twenty_eighths_le_determinantGap_of_reflectedRotatedFirstOctant
    (unit : GaussianInt) (unitNorm : normNat unit = 1)
    (errorRatio denominatorRatio : Gaussian)
    (realNonnegative :
      0 ≤ (RFAP.ConstructiveGaussian.Gaussian.conj
        (rotateErrorRatio unit errorRatio)).re)
    (imaginaryNonnegative :
      0 ≤ (RFAP.ConstructiveGaussian.Gaussian.conj
        (rotateErrorRatio unit errorRatio)).im)
    (imaginaryLeReal :
      (RFAP.ConstructiveGaussian.Gaussian.conj
          (rotateErrorRatio unit errorRatio)).im ≤
        (RFAP.ConstructiveGaussian.Gaussian.conj
          (rotateErrorRatio unit errorRatio)).re)
    (errorInside : normSq errorRatio < 1)
    (denominatorInside : normSq denominatorRatio < 1)
    (coefficientExterior : ∀ coefficient : GaussianInt,
      (1 : Coordinate) ≤ normSq (errorRatio - toGaussian coefficient) ∨
        1 ≤ normSq (1 - toGaussian coefficient * denominatorRatio)) :
    (15 / 28 : Coordinate) ≤
      normSq (1 - denominatorRatio * errorRatio) := by
  let rotatedError := rotateErrorRatio unit errorRatio
  let rotatedDenominator := rotateDenominatorRatio unit denominatorRatio
  have reflectedErrorInside :
      normSq (RFAP.ConstructiveGaussian.Gaussian.conj rotatedError) < 1 := by
    rw [normSq_conj, normSq_rotateErrorRatio unit unitNorm]
    exact errorInside
  have reflectedDenominatorInside :
      normSq (RFAP.ConstructiveGaussian.Gaussian.conj rotatedDenominator) < 1 := by
    rw [normSq_conj, normSq_rotateDenominatorRatio unit unitNorm]
    exact denominatorInside
  have rotatedExterior := rotatedCoefficientExterior unit unitNorm errorRatio
    denominatorRatio coefficientExterior
  have result := fifteen_twenty_eighths_le_determinantGap_of_firstOctantObstructions
    (RFAP.ConstructiveGaussian.Gaussian.conj rotatedError)
    (RFAP.ConstructiveGaussian.Gaussian.conj rotatedDenominator)
    realNonnegative imaginaryNonnegative imaginaryLeReal reflectedErrorInside
    reflectedDenominatorInside
    (conjugatedCoefficientExterior rotatedError rotatedDenominator
      rotatedExterior)
  rw [conjugatedProductGapNorm rotatedError rotatedDenominator] at result
  dsimp only [rotatedError, rotatedDenominator] at result
  rw [rotatedProduct unit unitNorm errorRatio denominatorRatio] at result
  exact result

private abbrev FirstOctantLinearCombinationGapBound
    (gapBound : Coordinate) : Prop :=
  ∀ (errorRatio denominatorRatio : Gaussian),
    0 ≤ errorRatio.re →
    0 ≤ errorRatio.im →
    errorRatio.im ≤ errorRatio.re →
    normSq errorRatio < 1 →
    normSq denominatorRatio < 1 →
    (∀ leftCoefficient rightCoefficient : GaussianInt,
      leftCoefficient ≠ 0 ∨ rightCoefficient ≠ 0 →
        (1 : Coordinate) ≤
            normSq
              (toGaussian leftCoefficient +
                toGaussian rightCoefficient * errorRatio) ∨
          1 ≤
            normSq
              (toGaussian leftCoefficient * denominatorRatio +
                toGaussian rightCoefficient)) →
    gapBound ≤ normSq (1 - denominatorRatio * errorRatio)

private theorem gapBound_le_of_rotatedFirstOctant
    (gapBound : Coordinate)
    (firstOctantBound : FirstOctantLinearCombinationGapBound gapBound)
    (unit : GaussianInt) (unitNorm : normNat unit = 1)
    (errorRatio denominatorRatio : Gaussian)
    (realNonnegative : 0 ≤ (rotateErrorRatio unit errorRatio).re)
    (imaginaryNonnegative : 0 ≤ (rotateErrorRatio unit errorRatio).im)
    (imaginaryLeReal :
      (rotateErrorRatio unit errorRatio).im ≤
        (rotateErrorRatio unit errorRatio).re)
    (errorInside : normSq errorRatio < 1)
    (denominatorInside : normSq denominatorRatio < 1)
    (linearCombinationExterior :
      ∀ leftCoefficient rightCoefficient : GaussianInt,
        leftCoefficient ≠ 0 ∨ rightCoefficient ≠ 0 →
          (1 : Coordinate) ≤
              normSq
                (toGaussian leftCoefficient +
                  toGaussian rightCoefficient * errorRatio) ∨
            1 ≤
              normSq
                (toGaussian leftCoefficient * denominatorRatio +
                  toGaussian rightCoefficient)) :
    gapBound ≤
      normSq (1 - denominatorRatio * errorRatio) := by
  have rotatedErrorInside : normSq (rotateErrorRatio unit errorRatio) < 1 := by
    rw [normSq_rotateErrorRatio unit unitNorm]
    exact errorInside
  have rotatedDenominatorInside :
      normSq (rotateDenominatorRatio unit denominatorRatio) < 1 := by
    rw [normSq_rotateDenominatorRatio unit unitNorm]
    exact denominatorInside
  have result :=
    firstOctantBound
      (rotateErrorRatio unit errorRatio)
      (rotateDenominatorRatio unit denominatorRatio)
      realNonnegative imaginaryNonnegative imaginaryLeReal rotatedErrorInside
      rotatedDenominatorInside
      (rotatedLinearCombinationExterior unit unitNorm errorRatio
        denominatorRatio linearCombinationExterior)
  rw [rotatedProduct unit unitNorm errorRatio denominatorRatio] at result
  exact result

private theorem gapBound_le_of_reflectedRotatedFirstOctant
    (gapBound : Coordinate)
    (firstOctantBound : FirstOctantLinearCombinationGapBound gapBound)
    (unit : GaussianInt) (unitNorm : normNat unit = 1)
    (errorRatio denominatorRatio : Gaussian)
    (realNonnegative :
      0 ≤ (RFAP.ConstructiveGaussian.Gaussian.conj
        (rotateErrorRatio unit errorRatio)).re)
    (imaginaryNonnegative :
      0 ≤ (RFAP.ConstructiveGaussian.Gaussian.conj
        (rotateErrorRatio unit errorRatio)).im)
    (imaginaryLeReal :
      (RFAP.ConstructiveGaussian.Gaussian.conj
          (rotateErrorRatio unit errorRatio)).im ≤
        (RFAP.ConstructiveGaussian.Gaussian.conj
          (rotateErrorRatio unit errorRatio)).re)
    (errorInside : normSq errorRatio < 1)
    (denominatorInside : normSq denominatorRatio < 1)
    (linearCombinationExterior :
      ∀ leftCoefficient rightCoefficient : GaussianInt,
        leftCoefficient ≠ 0 ∨ rightCoefficient ≠ 0 →
          (1 : Coordinate) ≤
              normSq
                (toGaussian leftCoefficient +
                  toGaussian rightCoefficient * errorRatio) ∨
            1 ≤
              normSq
                (toGaussian leftCoefficient * denominatorRatio +
                  toGaussian rightCoefficient)) :
    gapBound ≤
      normSq (1 - denominatorRatio * errorRatio) := by
  let rotatedError := rotateErrorRatio unit errorRatio
  let rotatedDenominator := rotateDenominatorRatio unit denominatorRatio
  have reflectedErrorInside :
      normSq (RFAP.ConstructiveGaussian.Gaussian.conj rotatedError) < 1 := by
    rw [normSq_conj, normSq_rotateErrorRatio unit unitNorm]
    exact errorInside
  have reflectedDenominatorInside :
      normSq (RFAP.ConstructiveGaussian.Gaussian.conj rotatedDenominator) < 1 := by
    rw [normSq_conj, normSq_rotateDenominatorRatio unit unitNorm]
    exact denominatorInside
  have rotatedExterior := rotatedLinearCombinationExterior unit unitNorm
    errorRatio denominatorRatio linearCombinationExterior
  have result :=
    firstOctantBound
      (RFAP.ConstructiveGaussian.Gaussian.conj rotatedError)
      (RFAP.ConstructiveGaussian.Gaussian.conj rotatedDenominator)
      realNonnegative imaginaryNonnegative imaginaryLeReal reflectedErrorInside
      reflectedDenominatorInside
      (conjugatedLinearCombinationExterior rotatedError rotatedDenominator
        rotatedExterior)
  rw [conjugatedProductGapNorm rotatedError rotatedDenominator] at result
  dsimp only [rotatedError, rotatedDenominator] at result
  rw [rotatedProduct unit unitNorm errorRatio denominatorRatio] at result
  exact result

private theorem rotateErrorRatio_one (value : Gaussian) :
    rotateErrorRatio (1 : GaussianInt) value = value := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [rotateErrorRatio, RFAP.HurwitzGeometry.conjugate, toGaussian,
      RFAP.ConstructiveGaussian.Gaussian.mul_re,
      RFAP.ConstructiveGaussian.Gaussian.mul_im,
      RFAP.ConstructiveGaussianHeight.GaussianInt.one_re,
      RFAP.ConstructiveGaussianHeight.GaussianInt.one_im, Int.cast_one] <;>
    ring1

private theorem rotateErrorRatio_imaginaryUnit (value : Gaussian) :
    rotateErrorRatio RFAP.HurwitzGeometry.imaginaryUnit value =
      ⟨value.im, -value.re⟩ := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [rotateErrorRatio, RFAP.HurwitzGeometry.conjugate,
      RFAP.HurwitzGeometry.imaginaryUnit, toGaussian,
      RFAP.ConstructiveGaussian.Gaussian.mul_re,
      RFAP.ConstructiveGaussian.Gaussian.mul_im, Int.cast_neg,
      Int.cast_one, Int.cast_zero] <;>
    ring1

private theorem rotateErrorRatio_negOne (value : Gaussian) :
    rotateErrorRatio (-1 : GaussianInt) value =
      ⟨-value.re, -value.im⟩ := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [rotateErrorRatio, RFAP.HurwitzGeometry.conjugate, toGaussian,
      RFAP.ConstructiveGaussian.Gaussian.mul_re,
      RFAP.ConstructiveGaussian.Gaussian.mul_im,
      RFAP.ConstructiveGaussianHeight.GaussianInt.neg_re,
      RFAP.ConstructiveGaussianHeight.GaussianInt.neg_im,
      RFAP.ConstructiveGaussianHeight.GaussianInt.one_re,
      RFAP.ConstructiveGaussianHeight.GaussianInt.one_im, Int.cast_neg,
      Int.cast_one, Int.cast_zero] <;>
    ring1

private theorem rotateErrorRatio_negImaginaryUnit (value : Gaussian) :
    rotateErrorRatio (-RFAP.HurwitzGeometry.imaginaryUnit) value =
      ⟨-value.im, value.re⟩ := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [rotateErrorRatio, RFAP.HurwitzGeometry.conjugate,
      RFAP.HurwitzGeometry.imaginaryUnit, toGaussian,
      RFAP.ConstructiveGaussian.Gaussian.mul_re,
      RFAP.ConstructiveGaussian.Gaussian.mul_im,
      RFAP.ConstructiveGaussianHeight.GaussianInt.neg_re,
      RFAP.ConstructiveGaussianHeight.GaussianInt.neg_im, Int.cast_neg,
      Int.cast_one, Int.cast_zero] <;>
    ring1

private theorem conj_rotateErrorRatio_one (value : Gaussian) :
    RFAP.ConstructiveGaussian.Gaussian.conj
        (rotateErrorRatio (1 : GaussianInt) value) =
      ⟨value.re, -value.im⟩ := by
  rw [rotateErrorRatio_one]
  rfl

private theorem conj_rotateErrorRatio_imaginaryUnit (value : Gaussian) :
    RFAP.ConstructiveGaussian.Gaussian.conj
        (rotateErrorRatio RFAP.HurwitzGeometry.imaginaryUnit value) =
      ⟨value.im, value.re⟩ := by
  rw [rotateErrorRatio_imaginaryUnit]
  apply RFAP.ConstructiveGaussian.Gaussian.ext
  · rfl
  · change - -value.re = value.re
    ring1

private theorem conj_rotateErrorRatio_negOne (value : Gaussian) :
    RFAP.ConstructiveGaussian.Gaussian.conj
        (rotateErrorRatio (-1 : GaussianInt) value) =
      ⟨-value.re, value.im⟩ := by
  rw [rotateErrorRatio_negOne]
  apply RFAP.ConstructiveGaussian.Gaussian.ext
  · rfl
  · change - -value.im = value.im
    ring1

private theorem conj_rotateErrorRatio_negImaginaryUnit (value : Gaussian) :
    RFAP.ConstructiveGaussian.Gaussian.conj
        (rotateErrorRatio (-RFAP.HurwitzGeometry.imaginaryUnit) value) =
      ⟨-value.im, -value.re⟩ := by
  rw [rotateErrorRatio_negImaginaryUnit]
  rfl

/-- The three-coefficient first-octant estimate covers every normalized pair:
one of four explicit unit rotations, optionally followed by conjugation,
places the displayed error ratio in that octant.  The case split is finite
and decidable on rational coordinates. -/
theorem fifteen_twenty_eighths_le_determinantGap_of_coefficientObstructions
    (errorRatio denominatorRatio : Gaussian)
    (errorInside : normSq errorRatio < 1)
    (denominatorInside : normSq denominatorRatio < 1)
    (coefficientExterior : ∀ coefficient : GaussianInt,
      (1 : Coordinate) ≤ normSq (errorRatio - toGaussian coefficient) ∨
        1 ≤ normSq (1 - toGaussian coefficient * denominatorRatio)) :
    (15 / 28 : Coordinate) ≤
      normSq (1 - denominatorRatio * errorRatio) := by
  by_cases realNonnegative : 0 ≤ errorRatio.re
  · by_cases imaginaryNonnegative : 0 ≤ errorRatio.im
    · by_cases imaginaryLeReal : errorRatio.im ≤ errorRatio.re
      · apply fifteen_twenty_eighths_le_determinantGap_of_rotatedFirstOctant
          (1 : GaussianInt) (by decide) errorRatio denominatorRatio
        · simpa only [rotateErrorRatio_one] using realNonnegative
        · simpa only [rotateErrorRatio_one] using imaginaryNonnegative
        · simpa only [rotateErrorRatio_one] using imaginaryLeReal
        · exact errorInside
        · exact denominatorInside
        · exact coefficientExterior
      · have realLeImaginary : errorRatio.re ≤ errorRatio.im :=
          le_of_not_ge imaginaryLeReal
        apply fifteen_twenty_eighths_le_determinantGap_of_reflectedRotatedFirstOctant
          RFAP.HurwitzGeometry.imaginaryUnit (by decide) errorRatio
          denominatorRatio
        · simpa only [conj_rotateErrorRatio_imaginaryUnit] using
            imaginaryNonnegative
        · simpa only [conj_rotateErrorRatio_imaginaryUnit] using
            realNonnegative
        · simpa only [conj_rotateErrorRatio_imaginaryUnit] using
            realLeImaginary
        · exact errorInside
        · exact denominatorInside
        · exact coefficientExterior
    · have imaginaryNonpositive : errorRatio.im ≤ 0 :=
        le_of_not_ge imaginaryNonnegative
      have negImaginaryNonnegative : 0 ≤ -errorRatio.im := by
        have negated := RFAP.ConstructiveFraction.neg_le_neg_direct
          imaginaryNonpositive
        calc
          (0 : Coordinate) = -0 := by ring1
          _ ≤ -errorRatio.im := negated
      by_cases negImaginaryLeReal : -errorRatio.im ≤ errorRatio.re
      · apply fifteen_twenty_eighths_le_determinantGap_of_reflectedRotatedFirstOctant
          (1 : GaussianInt) (by decide) errorRatio denominatorRatio
        · simpa only [conj_rotateErrorRatio_one] using realNonnegative
        · simpa only [conj_rotateErrorRatio_one] using
            negImaginaryNonnegative
        · simpa only [conj_rotateErrorRatio_one] using negImaginaryLeReal
        · exact errorInside
        · exact denominatorInside
        · exact coefficientExterior
      · have realLeNegImaginary : errorRatio.re ≤ -errorRatio.im :=
          le_of_not_ge negImaginaryLeReal
        apply fifteen_twenty_eighths_le_determinantGap_of_rotatedFirstOctant
          (-RFAP.HurwitzGeometry.imaginaryUnit) (by decide) errorRatio
          denominatorRatio
        · simpa only [rotateErrorRatio_negImaginaryUnit] using
            negImaginaryNonnegative
        · simpa only [rotateErrorRatio_negImaginaryUnit] using realNonnegative
        · simpa only [rotateErrorRatio_negImaginaryUnit] using
            realLeNegImaginary
        · exact errorInside
        · exact denominatorInside
        · exact coefficientExterior
  · have realNonpositive : errorRatio.re ≤ 0 := le_of_not_ge realNonnegative
    have negRealNonnegative : 0 ≤ -errorRatio.re := by
      have negated := RFAP.ConstructiveFraction.neg_le_neg_direct
        realNonpositive
      calc
        (0 : Coordinate) = -0 := by ring1
        _ ≤ -errorRatio.re := negated
    by_cases imaginaryNonnegative : 0 ≤ errorRatio.im
    · by_cases negRealLeImaginary : -errorRatio.re ≤ errorRatio.im
      · apply fifteen_twenty_eighths_le_determinantGap_of_rotatedFirstOctant
          RFAP.HurwitzGeometry.imaginaryUnit (by decide) errorRatio
          denominatorRatio
        · simpa only [rotateErrorRatio_imaginaryUnit] using
            imaginaryNonnegative
        · simpa only [rotateErrorRatio_imaginaryUnit] using
            negRealNonnegative
        · simpa only [rotateErrorRatio_imaginaryUnit] using
            negRealLeImaginary
        · exact errorInside
        · exact denominatorInside
        · exact coefficientExterior
      · have imaginaryLeNegReal : errorRatio.im ≤ -errorRatio.re :=
          le_of_not_ge negRealLeImaginary
        apply fifteen_twenty_eighths_le_determinantGap_of_reflectedRotatedFirstOctant
          (-1 : GaussianInt) (by decide) errorRatio denominatorRatio
        · simpa only [conj_rotateErrorRatio_negOne] using negRealNonnegative
        · simpa only [conj_rotateErrorRatio_negOne] using
            imaginaryNonnegative
        · simpa only [conj_rotateErrorRatio_negOne] using imaginaryLeNegReal
        · exact errorInside
        · exact denominatorInside
        · exact coefficientExterior
    · have imaginaryNonpositive : errorRatio.im ≤ 0 :=
        le_of_not_ge imaginaryNonnegative
      have negImaginaryNonnegative : 0 ≤ -errorRatio.im := by
        have negated := RFAP.ConstructiveFraction.neg_le_neg_direct
          imaginaryNonpositive
        calc
          (0 : Coordinate) = -0 := by ring1
          _ ≤ -errorRatio.im := negated
      by_cases negImaginaryLeNegReal :
          -errorRatio.im ≤ -errorRatio.re
      · apply fifteen_twenty_eighths_le_determinantGap_of_rotatedFirstOctant
          (-1 : GaussianInt) (by decide) errorRatio denominatorRatio
        · simpa only [rotateErrorRatio_negOne] using negRealNonnegative
        · simpa only [rotateErrorRatio_negOne] using negImaginaryNonnegative
        · simpa only [rotateErrorRatio_negOne] using negImaginaryLeNegReal
        · exact errorInside
        · exact denominatorInside
        · exact coefficientExterior
      · have negRealLeNegImaginary :
            -errorRatio.re ≤ -errorRatio.im :=
          le_of_not_ge negImaginaryLeNegReal
        apply fifteen_twenty_eighths_le_determinantGap_of_reflectedRotatedFirstOctant
          (-RFAP.HurwitzGeometry.imaginaryUnit) (by decide) errorRatio
          denominatorRatio
        · simpa only [conj_rotateErrorRatio_negImaginaryUnit] using
            negImaginaryNonnegative
        · simpa only [conj_rotateErrorRatio_negImaginaryUnit] using
            negRealNonnegative
        · simpa only [conj_rotateErrorRatio_negImaginaryUnit] using
            negRealLeNegImaginary
        · exact errorInside
        · exact denominatorInside
        · exact coefficientExterior

/-- A bound supplied in both rotated first-octant forms covers all eight
displayed coordinate octants.  The dispatcher depends only on decidable
rational signs and is shared by the index-one and centered index-two proofs. -/
private theorem gapBound_le_of_eightFirstOctants
    (gapBound : Coordinate)
    (errorRatio denominatorRatio : Gaussian)
    (rotatedCase : ∀ unit : GaussianInt, normNat unit = 1 →
      0 ≤ (rotateErrorRatio unit errorRatio).re →
      0 ≤ (rotateErrorRatio unit errorRatio).im →
      (rotateErrorRatio unit errorRatio).im ≤
        (rotateErrorRatio unit errorRatio).re →
      gapBound ≤ normSq (1 - denominatorRatio * errorRatio))
    (reflectedCase : ∀ unit : GaussianInt, normNat unit = 1 →
      0 ≤ (RFAP.ConstructiveGaussian.Gaussian.conj
        (rotateErrorRatio unit errorRatio)).re →
      0 ≤ (RFAP.ConstructiveGaussian.Gaussian.conj
        (rotateErrorRatio unit errorRatio)).im →
      (RFAP.ConstructiveGaussian.Gaussian.conj
          (rotateErrorRatio unit errorRatio)).im ≤
        (RFAP.ConstructiveGaussian.Gaussian.conj
          (rotateErrorRatio unit errorRatio)).re →
      gapBound ≤ normSq (1 - denominatorRatio * errorRatio)) :
    gapBound ≤
      normSq (1 - denominatorRatio * errorRatio) := by
  by_cases realNonnegative : 0 ≤ errorRatio.re
  · by_cases imaginaryNonnegative : 0 ≤ errorRatio.im
    · by_cases imaginaryLeReal : errorRatio.im ≤ errorRatio.re
      · apply rotatedCase (1 : GaussianInt) (by decide)
        · simpa only [rotateErrorRatio_one] using realNonnegative
        · simpa only [rotateErrorRatio_one] using imaginaryNonnegative
        · simpa only [rotateErrorRatio_one] using imaginaryLeReal
      · have realLeImaginary : errorRatio.re ≤ errorRatio.im :=
          le_of_not_ge imaginaryLeReal
        apply reflectedCase RFAP.HurwitzGeometry.imaginaryUnit (by decide)
        · simpa only [conj_rotateErrorRatio_imaginaryUnit] using
            imaginaryNonnegative
        · simpa only [conj_rotateErrorRatio_imaginaryUnit] using
            realNonnegative
        · simpa only [conj_rotateErrorRatio_imaginaryUnit] using
            realLeImaginary
    · have imaginaryNonpositive : errorRatio.im ≤ 0 :=
        le_of_not_ge imaginaryNonnegative
      have negImaginaryNonnegative : 0 ≤ -errorRatio.im := by
        have negated := RFAP.ConstructiveFraction.neg_le_neg_direct
          imaginaryNonpositive
        calc
          (0 : Coordinate) = -0 := by ring1
          _ ≤ -errorRatio.im := negated
      by_cases negImaginaryLeReal : -errorRatio.im ≤ errorRatio.re
      · apply reflectedCase (1 : GaussianInt) (by decide)
        · simpa only [conj_rotateErrorRatio_one] using realNonnegative
        · simpa only [conj_rotateErrorRatio_one] using
            negImaginaryNonnegative
        · simpa only [conj_rotateErrorRatio_one] using negImaginaryLeReal
      · have realLeNegImaginary : errorRatio.re ≤ -errorRatio.im :=
          le_of_not_ge negImaginaryLeReal
        apply rotatedCase (-RFAP.HurwitzGeometry.imaginaryUnit) (by decide)
        · simpa only [rotateErrorRatio_negImaginaryUnit] using
            negImaginaryNonnegative
        · simpa only [rotateErrorRatio_negImaginaryUnit] using realNonnegative
        · simpa only [rotateErrorRatio_negImaginaryUnit] using
            realLeNegImaginary
  · have realNonpositive : errorRatio.re ≤ 0 := le_of_not_ge realNonnegative
    have negRealNonnegative : 0 ≤ -errorRatio.re := by
      have negated := RFAP.ConstructiveFraction.neg_le_neg_direct
        realNonpositive
      calc
        (0 : Coordinate) = -0 := by ring1
        _ ≤ -errorRatio.re := negated
    by_cases imaginaryNonnegative : 0 ≤ errorRatio.im
    · by_cases negRealLeImaginary : -errorRatio.re ≤ errorRatio.im
      · apply rotatedCase RFAP.HurwitzGeometry.imaginaryUnit (by decide)
        · simpa only [rotateErrorRatio_imaginaryUnit] using
            imaginaryNonnegative
        · simpa only [rotateErrorRatio_imaginaryUnit] using
            negRealNonnegative
        · simpa only [rotateErrorRatio_imaginaryUnit] using
            negRealLeImaginary
      · have imaginaryLeNegReal : errorRatio.im ≤ -errorRatio.re :=
          le_of_not_ge negRealLeImaginary
        apply reflectedCase (-1 : GaussianInt) (by decide)
        · simpa only [conj_rotateErrorRatio_negOne] using negRealNonnegative
        · simpa only [conj_rotateErrorRatio_negOne] using
            imaginaryNonnegative
        · simpa only [conj_rotateErrorRatio_negOne] using imaginaryLeNegReal
    · have imaginaryNonpositive : errorRatio.im ≤ 0 :=
        le_of_not_ge imaginaryNonnegative
      have negImaginaryNonnegative : 0 ≤ -errorRatio.im := by
        have negated := RFAP.ConstructiveFraction.neg_le_neg_direct
          imaginaryNonpositive
        calc
          (0 : Coordinate) = -0 := by ring1
          _ ≤ -errorRatio.im := negated
      by_cases negImaginaryLeNegReal :
          -errorRatio.im ≤ -errorRatio.re
      · apply rotatedCase (-1 : GaussianInt) (by decide)
        · simpa only [rotateErrorRatio_negOne] using negRealNonnegative
        · simpa only [rotateErrorRatio_negOne] using negImaginaryNonnegative
        · simpa only [rotateErrorRatio_negOne] using negImaginaryLeNegReal
      · have negRealLeNegImaginary :
            -errorRatio.re ≤ -errorRatio.im :=
          le_of_not_ge negImaginaryLeNegReal
        apply reflectedCase (-RFAP.HurwitzGeometry.imaginaryUnit) (by decide)
        · simpa only [conj_rotateErrorRatio_negImaginaryUnit] using
            negImaginaryNonnegative
        · simpa only [conj_rotateErrorRatio_negImaginaryUnit] using
            negRealNonnegative
        · simpa only [conj_rotateErrorRatio_negImaginaryUnit] using
            negRealLeNegImaginary

private theorem gapBound_le_of_linearCombinationObstructions
    (gapBound : Coordinate)
    (firstOctantBound : FirstOctantLinearCombinationGapBound gapBound)
    (errorRatio denominatorRatio : Gaussian)
    (errorInside : normSq errorRatio < 1)
    (denominatorInside : normSq denominatorRatio < 1)
    (linearCombinationExterior :
      ∀ leftCoefficient rightCoefficient : GaussianInt,
        leftCoefficient ≠ 0 ∨ rightCoefficient ≠ 0 →
          (1 : Coordinate) ≤
              normSq
                (toGaussian leftCoefficient +
                  toGaussian rightCoefficient * errorRatio) ∨
            1 ≤
              normSq
                (toGaussian leftCoefficient * denominatorRatio +
                  toGaussian rightCoefficient)) :
    gapBound ≤ normSq (1 - denominatorRatio * errorRatio) := by
  apply gapBound_le_of_eightFirstOctants gapBound errorRatio denominatorRatio
  · intro unit unitNorm realNonnegative imaginaryNonnegative imaginaryLeReal
    exact gapBound_le_of_rotatedFirstOctant gapBound firstOctantBound unit
      unitNorm errorRatio denominatorRatio realNonnegative imaginaryNonnegative
      imaginaryLeReal errorInside denominatorInside linearCombinationExterior
  · intro unit unitNorm realNonnegative imaginaryNonnegative imaginaryLeReal
    exact gapBound_le_of_reflectedRotatedFirstOctant gapBound firstOctantBound
      unit unitNorm errorRatio denominatorRatio realNonnegative
      imaginaryNonnegative imaginaryLeReal errorInside denominatorInside
      linearCombinationExterior

/-- The centered index-two chamber is invariant under the same eight finite
coordinate symmetries.  Combining the forced centered orientation with the
affine first-octant calculation gives the global gap `205/128`. -/
theorem dyadicCenteredGapThreshold_le_of_centeredUnitObstructions
    (errorRatio denominatorRatio : Gaussian)
    (errorInside : normSq errorRatio < 1)
    (denominatorInside : normSq denominatorRatio < 1)
    (obstruction : ∀ centeredUnit : GaussianInt,
      normNat centeredUnit = 1 →
        (2 : Coordinate) ≤
            normSq (errorRatio - toGaussian centeredUnit) ∨
          2 ≤ normSq
            (1 - toGaussian centeredUnit * denominatorRatio)) :
    RFAP.IndexTwoWindow.dyadicCenteredGapThreshold ≤
      normSq (1 - denominatorRatio * errorRatio) := by
  apply gapBound_le_of_eightFirstOctants
    RFAP.IndexTwoWindow.dyadicCenteredGapThreshold errorRatio denominatorRatio
  · intro unit unitNorm realNonnegative imaginaryNonnegative imaginaryLeReal
    exact dyadicCenteredGapThreshold_le_of_rotatedFirstOctant unit unitNorm
      errorRatio denominatorRatio realNonnegative imaginaryNonnegative
      imaginaryLeReal errorInside denominatorInside obstruction
  · intro unit unitNorm realNonnegative imaginaryNonnegative imaginaryLeReal
    exact dyadicCenteredGapThreshold_le_of_reflectedRotatedFirstOctant unit
      unitNorm errorRatio denominatorRatio realNonnegative
      imaginaryNonnegative imaginaryLeReal errorInside denominatorInside
      obstruction

/-- Every displayed threshold in the exact centered cut survives the eight
rational coordinate symmetries. -/
theorem twice_gapThreshold_le_of_centeredUnitObstructions
    (gap : Coordinate)
    (certificate : RFAP.OptimalIndexTwoWindow.IsCenteredGapThreshold gap)
    (errorRatio denominatorRatio : Gaussian)
    (errorInside : normSq errorRatio < 1)
    (denominatorInside : normSq denominatorRatio < 1)
    (obstruction : ∀ centeredUnit : GaussianInt,
      normNat centeredUnit = 1 →
        (2 : Coordinate) ≤
            normSq (errorRatio - toGaussian centeredUnit) ∨
          2 ≤ normSq
            (1 - toGaussian centeredUnit * denominatorRatio)) :
    2 * gap ≤ normSq (1 - denominatorRatio * errorRatio) := by
  apply gapBound_le_of_eightFirstOctants
    (2 * gap) errorRatio denominatorRatio
  · intro unit unitNorm realNonnegative imaginaryNonnegative imaginaryLeReal
    exact twice_gapThreshold_le_of_rotatedFirstOctant gap certificate unit
      unitNorm errorRatio denominatorRatio realNonnegative
      imaginaryNonnegative imaginaryLeReal errorInside denominatorInside
      obstruction
  · intro unit unitNorm realNonnegative imaginaryNonnegative imaginaryLeReal
    exact twice_gapThreshold_le_of_reflectedRotatedFirstOctant gap certificate
      unit unitNorm errorRatio denominatorRatio realNonnegative
      imaginaryNonnegative imaginaryLeReal errorInside denominatorInside
      obstruction

/-- The earlier norm-two first-octant certificate, lifted through the shared
eight-symmetry dispatcher. -/
private theorem normTwoIndexOneGapThreshold_le_of_linearCombinationObstructions
    (errorRatio denominatorRatio : Gaussian)
    (errorInside : normSq errorRatio < 1)
    (denominatorInside : normSq denominatorRatio < 1)
    (linearCombinationExterior :
      ∀ leftCoefficient rightCoefficient : GaussianInt,
        leftCoefficient ≠ 0 ∨ rightCoefficient ≠ 0 →
          (1 : Coordinate) ≤
              normSq
                (toGaussian leftCoefficient +
                  toGaussian rightCoefficient * errorRatio) ∨
            1 ≤
              normSq
                (toGaussian leftCoefficient * denominatorRatio +
                  toGaussian rightCoefficient)) :
    normTwoIndexOneGapThreshold ≤
      normSq (1 - denominatorRatio * errorRatio) := by
  exact gapBound_le_of_linearCombinationObstructions
    normTwoIndexOneGapThreshold
    normTwoIndexOneGapThreshold_le_of_firstOctantLinearObstructions
    errorRatio denominatorRatio errorInside denominatorInside
    linearCombinationExterior

/-- Every displayed threshold in the exact root-free gap cut survives the
eight rational coordinate symmetries. -/
theorem gapThreshold_le_of_linearCombinationObstructions
    (threshold : Coordinate)
    (thresholdCertificate :
      RFAP.OptimalIndexOneWindow.IsGapThreshold threshold)
    (errorRatio denominatorRatio : Gaussian)
    (errorInside : normSq errorRatio < 1)
    (denominatorInside : normSq denominatorRatio < 1)
    (linearCombinationExterior :
      ∀ leftCoefficient rightCoefficient : GaussianInt,
        leftCoefficient ≠ 0 ∨ rightCoefficient ≠ 0 →
          (1 : Coordinate) ≤
              normSq
                (toGaussian leftCoefficient +
                  toGaussian rightCoefficient * errorRatio) ∨
            1 ≤
              normSq
                (toGaussian leftCoefficient * denominatorRatio +
                  toGaussian rightCoefficient)) :
    threshold ≤ normSq (1 - denominatorRatio * errorRatio) := by
  exact gapBound_le_of_linearCombinationObstructions threshold
    (gapThreshold_le_of_firstOctantLinearObstructions threshold
      thresholdCertificate)
    errorRatio denominatorRatio errorInside denominatorInside
    linearCombinationExterior

/-- The dyadic first-octant chamber certificate is stable under the same
eight finite coordinate symmetries.  Thus every normalized pair satisfying
the full coefficient exterior predicate has gap at least `205/256`. -/
theorem sharpIndexOneGapBound_le_of_linearCombinationObstructions
    (errorRatio denominatorRatio : Gaussian)
    (errorInside : normSq errorRatio < 1)
    (denominatorInside : normSq denominatorRatio < 1)
    (linearCombinationExterior :
      ∀ leftCoefficient rightCoefficient : GaussianInt,
        leftCoefficient ≠ 0 ∨ rightCoefficient ≠ 0 →
          (1 : Coordinate) ≤
              normSq
                (toGaussian leftCoefficient +
                  toGaussian rightCoefficient * errorRatio) ∨
            1 ≤
              normSq
                (toGaussian leftCoefficient * denominatorRatio +
                  toGaussian rightCoefficient)) :
    RFAP.SharpIndexOneWindow.firstRegionGapBound ≤
      normSq (1 - denominatorRatio * errorRatio) := by
  exact gapBound_le_of_linearCombinationObstructions
    RFAP.SharpIndexOneWindow.firstRegionGapBound
    sharpIndexOneGapBound_le_of_firstOctantLinearObstructions
    errorRatio denominatorRatio errorInside denominatorInside
    linearCombinationExterior

/-- Compatibility form of the finite octant certificate with the earlier
half-gap constant. -/
theorem half_le_determinantGap_of_coefficientObstructions
    (errorRatio denominatorRatio : Gaussian)
    (errorInside : normSq errorRatio < 1)
    (denominatorInside : normSq denominatorRatio < 1)
    (coefficientExterior : ∀ coefficient : GaussianInt,
      (1 : Coordinate) ≤ normSq (errorRatio - toGaussian coefficient) ∨
        1 ≤ normSq (1 - toGaussian coefficient * denominatorRatio)) :
    (1 / 2 : Coordinate) ≤
      normSq (1 - denominatorRatio * errorRatio) := by
  exact (show (1 / 2 : Coordinate) ≤ 15 / 28 by decide).trans
    (fifteen_twenty_eighths_le_determinantGap_of_coefficientObstructions
      errorRatio denominatorRatio errorInside denominatorInside
      coefficientExterior)

/-- Every consecutive normalized pair has determinant gap at least `15/28`.
Unlike the earlier nearest-coefficient quadratic estimate, this uses all
three neighbouring coefficients in the finite octant containing the error
ratio. -/
theorem AreConsecutiveBest.fifteen_twenty_eighths_le_normalizedDeterminantGap
    {source : RFAP.HurwitzRational.Fraction}
    {lower upper : RFAP.HurwitzRational.ConvergentPair}
    (consecutive : RFAP.BestApproximation.AreConsecutiveBest
      source.value lower upper) :
    (15 / 28 : Coordinate) ≤
      normSq
        (1 - RFAP.DirichletWindow.denominatorRatio lower upper *
          RFAP.DirichletWindow.errorRatio source.value lower upper) := by
  exact fifteen_twenty_eighths_le_determinantGap_of_coefficientObstructions
    (RFAP.DirichletWindow.errorRatio source.value lower upper)
    (RFAP.DirichletWindow.denominatorRatio lower upper)
    (RFAP.IndexTwoWindow.AreConsecutiveBest.errorRatio_normSq_lt_one
      consecutive)
    (RFAP.DirichletWindow.AreConsecutiveBest.denominatorRatio_normSq_lt_one
      consecutive)
    (RFAP.DirichletWindow.AreConsecutiveBest.normalizedCoefficientExterior
      consecutive)

/-- Every consecutive normalized pair has determinant gap at least the
displayed `71/112`.  The proof uses arbitrary nontrivial two-coefficient
combinations, including the norm-two leading combination that is unavailable
to the one-coefficient normalization. -/
theorem AreConsecutiveBest.normTwoIndexOneGapThreshold_le_normalizedDeterminantGap
    {source : RFAP.HurwitzRational.Fraction}
    {lower upper : RFAP.HurwitzRational.ConvergentPair}
    (consecutive : RFAP.BestApproximation.AreConsecutiveBest
      source.value lower upper) :
    normTwoIndexOneGapThreshold ≤
      normSq
        (1 - RFAP.DirichletWindow.denominatorRatio lower upper *
          RFAP.DirichletWindow.errorRatio source.value lower upper) := by
  exact normTwoIndexOneGapThreshold_le_of_linearCombinationObstructions
    (RFAP.DirichletWindow.errorRatio source.value lower upper)
    (RFAP.DirichletWindow.denominatorRatio lower upper)
    (RFAP.IndexTwoWindow.AreConsecutiveBest.errorRatio_normSq_lt_one
      consecutive)
    (RFAP.DirichletWindow.AreConsecutiveBest.denominatorRatio_normSq_lt_one
      consecutive)
    (RFAP.DirichletWindow.AreConsecutiveBest.normalizedLinearCombinationExterior
      consecutive)

/-- Every consecutive normalized pair satisfies the strengthened displayed
gap `205/256`.  The proof uses five coefficient obstructions in one rational
octant and the shared finite eight-symmetry dispatcher. -/
theorem AreConsecutiveBest.sharpIndexOneGapBound_le_normalizedDeterminantGap
    {source : RFAP.HurwitzRational.Fraction}
    {lower upper : RFAP.HurwitzRational.ConvergentPair}
    (consecutive : RFAP.BestApproximation.AreConsecutiveBest
      source.value lower upper) :
    sharpIndexOneGapBound ≤
      normSq
        (1 - RFAP.DirichletWindow.denominatorRatio lower upper *
          RFAP.DirichletWindow.errorRatio source.value lower upper) := by
  exact sharpIndexOneGapBound_le_of_linearCombinationObstructions
    (RFAP.DirichletWindow.errorRatio source.value lower upper)
    (RFAP.DirichletWindow.denominatorRatio lower upper)
    (RFAP.IndexTwoWindow.AreConsecutiveBest.errorRatio_normSq_lt_one
      consecutive)
    (RFAP.DirichletWindow.AreConsecutiveBest.denominatorRatio_normSq_lt_one
      consecutive)
    (RFAP.DirichletWindow.AreConsecutiveBest.normalizedLinearCombinationExterior
      consecutive)

/-- Every rational threshold on the exact quadratic cut bounds the normalized
determinant gap of consecutive best pairs.  This is the square-root-free
index-one form of Chevallier's optimal chamber constant. -/
theorem AreConsecutiveBest.gapThreshold_le_normalizedDeterminantGap
    {source : RFAP.HurwitzRational.Fraction}
    {lower upper : RFAP.HurwitzRational.ConvergentPair}
    (threshold : Coordinate)
    (thresholdCertificate :
      RFAP.OptimalIndexOneWindow.IsGapThreshold threshold)
    (consecutive : RFAP.BestApproximation.AreConsecutiveBest
      source.value lower upper) :
    threshold ≤
      normSq
        (1 - RFAP.DirichletWindow.denominatorRatio lower upper *
          RFAP.DirichletWindow.errorRatio source.value lower upper) := by
  exact gapThreshold_le_of_linearCombinationObstructions threshold
    thresholdCertificate
    (RFAP.DirichletWindow.errorRatio source.value lower upper)
    (RFAP.DirichletWindow.denominatorRatio lower upper)
    (RFAP.IndexTwoWindow.AreConsecutiveBest.errorRatio_normSq_lt_one
      consecutive)
    (RFAP.DirichletWindow.AreConsecutiveBest.denominatorRatio_normSq_lt_one
      consecutive)
    (RFAP.DirichletWindow.AreConsecutiveBest.normalizedLinearCombinationExterior
      consecutive)

/-- At determinant index two, the centered obstruction chamber has normalized
gap at least `205/128`. -/
theorem AreConsecutiveBest.dyadicCenteredGapThreshold_le_normalizedDeterminantGap_of_indexTwo
    {source : RFAP.HurwitzRational.Fraction}
    {lower upper : RFAP.HurwitzRational.ConvergentPair}
    (consecutive : RFAP.BestApproximation.AreConsecutiveBest
      source.value lower upper)
    (indexTwo :
      RFAP.BestApproximation.coefficientIndexQuadrance lower upper = 2) :
    RFAP.IndexTwoWindow.dyadicCenteredGapThreshold ≤
      normSq
        (1 - RFAP.DirichletWindow.denominatorRatio lower upper *
          RFAP.DirichletWindow.errorRatio source.value lower upper) := by
  exact dyadicCenteredGapThreshold_le_of_centeredUnitObstructions
    (RFAP.DirichletWindow.errorRatio source.value lower upper)
    (RFAP.DirichletWindow.denominatorRatio lower upper)
    (RFAP.IndexTwoWindow.AreConsecutiveBest.errorRatio_normSq_lt_one
      consecutive)
    (RFAP.DirichletWindow.AreConsecutiveBest.denominatorRatio_normSq_lt_one
      consecutive)
    (RFAP.IndexTwoWindow.AreConsecutiveBest.normalizedCenteredUnitObstruction
      consecutive indexTwo)

/-- At determinant index two, every rational point of the exact centered cut
gives twice the corresponding index-one normalized gap. -/
theorem AreConsecutiveBest.twice_gapThreshold_le_normalizedDeterminantGap_of_indexTwo
    {source : RFAP.HurwitzRational.Fraction}
    {lower upper : RFAP.HurwitzRational.ConvergentPair}
    (gap : Coordinate)
    (certificate : RFAP.OptimalIndexTwoWindow.IsCenteredGapThreshold gap)
    (consecutive : RFAP.BestApproximation.AreConsecutiveBest
      source.value lower upper)
    (indexTwo :
      RFAP.BestApproximation.coefficientIndexQuadrance lower upper = 2) :
    2 * gap ≤
      normSq
        (1 - RFAP.DirichletWindow.denominatorRatio lower upper *
          RFAP.DirichletWindow.errorRatio source.value lower upper) := by
  exact twice_gapThreshold_le_of_centeredUnitObstructions gap certificate
    (RFAP.DirichletWindow.errorRatio source.value lower upper)
    (RFAP.DirichletWindow.denominatorRatio lower upper)
    (RFAP.IndexTwoWindow.AreConsecutiveBest.errorRatio_normSq_lt_one
      consecutive)
    (RFAP.DirichletWindow.AreConsecutiveBest.denominatorRatio_normSq_lt_one
      consecutive)
    (RFAP.IndexTwoWindow.AreConsecutiveBest.normalizedCenteredUnitObstruction
      consecutive indexTwo)

/-- Compatibility form of the finite octant theorem with the earlier
half-gap constant. -/
theorem AreConsecutiveBest.half_le_normalizedDeterminantGap
    {source : RFAP.HurwitzRational.Fraction}
    {lower upper : RFAP.HurwitzRational.ConvergentPair}
    (consecutive : RFAP.BestApproximation.AreConsecutiveBest
      source.value lower upper) :
    (1 / 2 : Coordinate) ≤
      normSq
        (1 - RFAP.DirichletWindow.denominatorRatio lower upper *
          RFAP.DirichletWindow.errorRatio source.value lower upper) := by
  exact (show (1 / 2 : Coordinate) ≤ 15 / 28 by decide).trans
    (RFAP.IndexOneWindow.AreConsecutiveBest.fifteen_twenty_eighths_le_normalizedDeterminantGap
      consecutive)

/-- At determinant index one, the `15/28` gap certificate and the exact
window-times-gap identity give the rational window bound `28/15`. -/
theorem AreConsecutiveBest.dirichletWindowQuadrance_le_twentyEight_fifteenths_of_indexOne
    {source : RFAP.HurwitzRational.Fraction}
    {lower upper : RFAP.HurwitzRational.ConvergentPair}
    (consecutive : RFAP.BestApproximation.AreConsecutiveBest
      source.value lower upper)
    (indexOne :
      RFAP.BestApproximation.coefficientIndexQuadrance lower upper = 1) :
    RFAP.BestApproximation.dirichletWindowQuadrance
      source.value lower upper ≤ 28 / 15 := by
  have scaledWindow :=
    RFAP.DirichletWindow.AreConsecutiveBest.threshold_mul_dirichletWindow_le_index
      consecutive (15 / 28 : Coordinate)
        (RFAP.IndexOneWindow.AreConsecutiveBest.fifteen_twenty_eighths_le_normalizedDeterminantGap
          consecutive)
  rw [indexOne, Nat.cast_one] at scaledWindow
  have scaled :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct scaledWindow
      (RFAP.ConstructiveFraction.div_nonneg_direct
        (numerator := (28 : Coordinate)) (denominator := (15 : Coordinate))
        (RFAP.ConstructiveFraction.natCast_pos_direct (by decide)).le
        (RFAP.ConstructiveFraction.natCast_pos_direct (by decide)).le)
  calc
    RFAP.BestApproximation.dirichletWindowQuadrance
          source.value lower upper =
        ((15 / 28 : Coordinate) *
          RFAP.BestApproximation.dirichletWindowQuadrance
            source.value lower upper) * (28 / 15) := by
      have factorsCancel : (15 / 28 : Coordinate) * (28 / 15) = 1 := by
        rw [RFAP.ConstructiveFraction.div_eq_mul_inv_direct,
          RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
        calc
          ((15 : Coordinate) * (28 : Coordinate)⁻¹) *
                ((28 : Coordinate) * (15 : Coordinate)⁻¹) =
              ((15 : Coordinate) * (15 : Coordinate)⁻¹) *
                ((28 : Coordinate)⁻¹ * (28 : Coordinate)) := by ring1
          _ = 1 * 1 := by
            rw [RFAP.ConstructiveFraction.mul_inv_cancel (15 : Coordinate)
                (RFAP.ConstructiveFraction.natCast_pos_direct
                  (show 0 < 15 by decide)).ne',
              RFAP.ConstructiveFraction.inv_mul_cancel (28 : Coordinate)
                (RFAP.ConstructiveFraction.natCast_pos_direct
                  (show 0 < 28 by decide)).ne']
          _ = 1 := by ring1
      calc
        RFAP.BestApproximation.dirichletWindowQuadrance
              source.value lower upper =
            1 * RFAP.BestApproximation.dirichletWindowQuadrance
              source.value lower upper := by ring1
        _ = ((15 / 28 : Coordinate) * (28 / 15)) *
            RFAP.BestApproximation.dirichletWindowQuadrance
              source.value lower upper := by rw [factorsCancel]
        _ = ((15 / 28 : Coordinate) *
            RFAP.BestApproximation.dirichletWindowQuadrance
              source.value lower upper) * (28 / 15) := by ring1
    _ ≤ (1 : Coordinate) * (28 / 15) := scaled
    _ = 28 / 15 := by ring1

/-- At determinant index one, the norm-two leading coefficient certificate
and the exact window-times-gap identity give the displayed rational bound
`112/71`.  The proof only multiplies by the positive gap threshold. -/
theorem AreConsecutiveBest.dirichletWindowQuadrance_le_normTwoIndexOneWindowBound_of_indexOne
    {source : RFAP.HurwitzRational.Fraction}
    {lower upper : RFAP.HurwitzRational.ConvergentPair}
    (consecutive : RFAP.BestApproximation.AreConsecutiveBest
      source.value lower upper)
    (indexOne :
      RFAP.BestApproximation.coefficientIndexQuadrance lower upper = 1) :
    RFAP.BestApproximation.dirichletWindowQuadrance
      source.value lower upper ≤ normTwoIndexOneWindowBound := by
  have scaledWindow :=
    RFAP.DirichletWindow.AreConsecutiveBest.threshold_mul_dirichletWindow_le_index
      consecutive normTwoIndexOneGapThreshold
        (RFAP.IndexOneWindow.AreConsecutiveBest.normTwoIndexOneGapThreshold_le_normalizedDeterminantGap
          consecutive)
  rw [indexOne, Nat.cast_one] at scaledWindow
  apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct
    (c := normTwoIndexOneGapThreshold)
  · calc
      RFAP.BestApproximation.dirichletWindowQuadrance
            source.value lower upper * normTwoIndexOneGapThreshold =
          normTwoIndexOneGapThreshold *
            RFAP.BestApproximation.dirichletWindowQuadrance
              source.value lower upper := by ring1
      _ ≤ 1 := scaledWindow
      _ = normTwoIndexOneWindowBound *
          normTwoIndexOneGapThreshold :=
        normTwoIndexOneWindowBound_mul_gapThreshold.symm
  · exact normTwoIndexOneGapThreshold_pos

/-- At determinant index one, every rational point of the exact gap cut gives
the division-free optimal-window family `threshold * window ≤ 1`.  Choosing
rational thresholds arbitrarily close to the cut recovers the optimal upper
constant without constructing its algebraic endpoint. -/
theorem AreConsecutiveBest.gapThreshold_mul_dirichletWindow_le_one_of_indexOne
    {source : RFAP.HurwitzRational.Fraction}
    {lower upper : RFAP.HurwitzRational.ConvergentPair}
    (threshold : Coordinate)
    (thresholdCertificate :
      RFAP.OptimalIndexOneWindow.IsGapThreshold threshold)
    (consecutive : RFAP.BestApproximation.AreConsecutiveBest
      source.value lower upper)
    (indexOne :
      RFAP.BestApproximation.coefficientIndexQuadrance lower upper = 1) :
    threshold * RFAP.BestApproximation.dirichletWindowQuadrance
      source.value lower upper ≤ 1 := by
  have scaledWindow :=
    RFAP.DirichletWindow.AreConsecutiveBest.threshold_mul_dirichletWindow_le_index
      consecutive threshold
        (RFAP.IndexOneWindow.AreConsecutiveBest.gapThreshold_le_normalizedDeterminantGap
          threshold thresholdCertificate consecutive)
  rw [indexOne, Nat.cast_one] at scaledWindow
  exact scaledWindow

/-- At determinant index two, every rational point of the exact centered cut
gives the same division-free window family as at index one. -/
theorem AreConsecutiveBest.gapThreshold_mul_dirichletWindow_le_one_of_indexTwo
    {source : RFAP.HurwitzRational.Fraction}
    {lower upper : RFAP.HurwitzRational.ConvergentPair}
    (gap : Coordinate)
    (certificate : RFAP.OptimalIndexTwoWindow.IsCenteredGapThreshold gap)
    (consecutive : RFAP.BestApproximation.AreConsecutiveBest
      source.value lower upper)
    (indexTwo :
      RFAP.BestApproximation.coefficientIndexQuadrance lower upper = 2) :
    gap * RFAP.BestApproximation.dirichletWindowQuadrance
      source.value lower upper ≤ 1 := by
  have scaledWindow :=
    RFAP.DirichletWindow.AreConsecutiveBest.threshold_mul_dirichletWindow_le_index
      consecutive (2 * gap)
        (RFAP.IndexOneWindow.AreConsecutiveBest.twice_gapThreshold_le_normalizedDeterminantGap_of_indexTwo
          gap certificate consecutive indexTwo)
  rw [indexTwo, Nat.cast_ofNat] at scaledWindow
  apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct (c := 2)
  · calc
      (gap * RFAP.BestApproximation.dirichletWindowQuadrance
          source.value lower upper) * 2 =
          (2 * gap) * RFAP.BestApproximation.dirichletWindowQuadrance
            source.value lower upper := by ring1
      _ ≤ 2 := scaledWindow
      _ = 1 * 2 := by ring1
  · decide

/-- Every consecutive displayed window satisfies the exact root-free
quadratic family `gap * window ≤ 1`.  Rational cuts in this family approach
Chevallier's optimal squared constant without naming its algebraic endpoint. -/
theorem AreConsecutiveBest.gapThreshold_mul_dirichletWindow_le_one
    {source : RFAP.HurwitzRational.Fraction}
    {lower upper : RFAP.HurwitzRational.ConvergentPair}
    (gap : Coordinate)
    (certificate : RFAP.OptimalIndexTwoWindow.IsCenteredGapThreshold gap)
    (consecutive : RFAP.BestApproximation.AreConsecutiveBest
      source.value lower upper) :
    gap * RFAP.BestApproximation.dirichletWindowQuadrance
      source.value lower upper ≤ 1 := by
  rcases consecutive.coefficientIndexQuadrance_eq_one_or_two with
      indexOne | indexTwo
  · exact gapThreshold_mul_dirichletWindow_le_one_of_indexOne gap
      certificate.2 consecutive indexOne
  · exact gapThreshold_mul_dirichletWindow_le_one_of_indexTwo gap certificate
      consecutive indexTwo

/-- At determinant index one, the dyadic five-obstruction chamber and the
exact window-times-gap identity give the stronger rational bound `256/205`.
This approaches the optimal algebraic constant without naming its square
root. -/
theorem AreConsecutiveBest.dirichletWindowQuadrance_le_sharpIndexOneWindowBound_of_indexOne
    {source : RFAP.HurwitzRational.Fraction}
    {lower upper : RFAP.HurwitzRational.ConvergentPair}
    (consecutive : RFAP.BestApproximation.AreConsecutiveBest
      source.value lower upper)
    (indexOne :
      RFAP.BestApproximation.coefficientIndexQuadrance lower upper = 1) :
    RFAP.BestApproximation.dirichletWindowQuadrance
      source.value lower upper ≤ sharpIndexOneWindowBound := by
  have scaledWindow :=
    RFAP.DirichletWindow.AreConsecutiveBest.threshold_mul_dirichletWindow_le_index
      consecutive sharpIndexOneGapBound
        (RFAP.IndexOneWindow.AreConsecutiveBest.sharpIndexOneGapBound_le_normalizedDeterminantGap
          consecutive)
  rw [indexOne, Nat.cast_one] at scaledWindow
  apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct
    (c := sharpIndexOneGapBound)
  · calc
      RFAP.BestApproximation.dirichletWindowQuadrance
            source.value lower upper * sharpIndexOneGapBound =
          sharpIndexOneGapBound *
            RFAP.BestApproximation.dirichletWindowQuadrance
              source.value lower upper := by ring1
      _ ≤ 1 := scaledWindow
      _ = sharpIndexOneWindowBound * sharpIndexOneGapBound :=
        sharpIndexOneWindowBound_mul_gapBound.symm
  · exact sharpIndexOneGapBound_pos

/-- At determinant index two, the strengthened centered gap and the exact
index-two factor give the matching squared-window bound `256/205`. -/
theorem AreConsecutiveBest.dirichletWindowQuadrance_le_dyadicCenteredWindowBound_of_indexTwo
    {source : RFAP.HurwitzRational.Fraction}
    {lower upper : RFAP.HurwitzRational.ConvergentPair}
    (consecutive : RFAP.BestApproximation.AreConsecutiveBest
      source.value lower upper)
    (indexTwo :
      RFAP.BestApproximation.coefficientIndexQuadrance lower upper = 2) :
    RFAP.BestApproximation.dirichletWindowQuadrance source.value lower upper ≤
      RFAP.IndexTwoWindow.dyadicCenteredWindowBound := by
  have scaledWindow :=
    RFAP.DirichletWindow.AreConsecutiveBest.threshold_mul_dirichletWindow_le_index
      consecutive RFAP.IndexTwoWindow.dyadicCenteredGapThreshold
        (RFAP.IndexOneWindow.AreConsecutiveBest.dyadicCenteredGapThreshold_le_normalizedDeterminantGap_of_indexTwo
          consecutive indexTwo)
  rw [indexTwo, Nat.cast_ofNat] at scaledWindow
  apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct
    (c := RFAP.IndexTwoWindow.dyadicCenteredGapThreshold)
  · calc
      RFAP.BestApproximation.dirichletWindowQuadrance source.value lower upper *
            RFAP.IndexTwoWindow.dyadicCenteredGapThreshold =
          RFAP.IndexTwoWindow.dyadicCenteredGapThreshold *
            RFAP.BestApproximation.dirichletWindowQuadrance
              source.value lower upper := by ring1
      _ ≤ 2 := scaledWindow
      _ = RFAP.IndexTwoWindow.dyadicCenteredWindowBound *
          RFAP.IndexTwoWindow.dyadicCenteredGapThreshold :=
        RFAP.IndexTwoWindow.dyadicCenteredWindowBound_mul_gapThreshold.symm
  · exact RFAP.IndexTwoWindow.dyadicCenteredGapThreshold_pos

/-- At determinant index one, the rational `28/15` bound in particular
recovers the earlier integer bound two. -/
theorem AreConsecutiveBest.dirichletWindowQuadrance_le_two_of_indexOne
    {source : RFAP.HurwitzRational.Fraction}
    {lower upper : RFAP.HurwitzRational.ConvergentPair}
    (consecutive : RFAP.BestApproximation.AreConsecutiveBest
      source.value lower upper)
    (indexOne :
      RFAP.BestApproximation.coefficientIndexQuadrance lower upper = 1) :
    RFAP.BestApproximation.dirichletWindowQuadrance
      source.value lower upper ≤ 2 :=
  (RFAP.IndexOneWindow.AreConsecutiveBest.dirichletWindowQuadrance_le_normTwoIndexOneWindowBound_of_indexOne
      consecutive indexOne).trans normTwoIndexOneWindowBound_le_two

/-- Every consecutive squared Dirichlet window is at most `256/205`.  The
five-obstruction octant chamber supplies this value at index one, and the
oriented centered chamber supplies the same value at index two. -/
theorem AreConsecutiveBest.dirichletWindowQuadrance_le_sharpDyadicUniversalWindowBound
    {source : RFAP.HurwitzRational.Fraction}
    {lower upper : RFAP.HurwitzRational.ConvergentPair}
    (consecutive : RFAP.BestApproximation.AreConsecutiveBest
      source.value lower upper) :
    RFAP.BestApproximation.dirichletWindowQuadrance source.value lower upper ≤
      sharpIndexOneWindowBound := by
  rcases consecutive.coefficientIndexQuadrance_eq_one_or_two with
      indexOne | indexTwo
  · exact
      RFAP.IndexOneWindow.AreConsecutiveBest.dirichletWindowQuadrance_le_sharpIndexOneWindowBound_of_indexOne
        consecutive indexOne
  · calc
      RFAP.BestApproximation.dirichletWindowQuadrance
            source.value lower upper ≤
          RFAP.IndexTwoWindow.dyadicCenteredWindowBound :=
        RFAP.IndexOneWindow.AreConsecutiveBest.dirichletWindowQuadrance_le_dyadicCenteredWindowBound_of_indexTwo
          consecutive indexTwo
      _ = sharpIndexOneWindowBound :=
        sharpIndexOneWindowBound_eq_dyadicCenteredWindowBound.symm

/-- Every consecutive squared Dirichlet window is at most the displayed
`112/71`.  The norm-two leading coefficient test gives this value at index
one, and the centered-coset certificates give the same value at index two. -/
theorem AreConsecutiveBest.dirichletWindowQuadrance_le_normTwoUniversalWindowBound
    {source : RFAP.HurwitzRational.Fraction}
    {lower upper : RFAP.HurwitzRational.ConvergentPair}
    (consecutive : RFAP.BestApproximation.AreConsecutiveBest
      source.value lower upper) :
    RFAP.BestApproximation.dirichletWindowQuadrance
      source.value lower upper ≤ normTwoIndexOneWindowBound := by
  rcases consecutive.coefficientIndexQuadrance_eq_one_or_two with
      indexOne | indexTwo
  · exact
      RFAP.IndexOneWindow.AreConsecutiveBest.dirichletWindowQuadrance_le_normTwoIndexOneWindowBound_of_indexOne
        consecutive indexOne
  · calc
      RFAP.BestApproximation.dirichletWindowQuadrance
            source.value lower upper ≤
          RFAP.IndexTwoWindow.centeredWindowBound :=
        RFAP.IndexTwoWindow.AreConsecutiveBest.dirichletWindowQuadrance_le_oneHundredTwelve_seventyFirsts_of_indexTwo
          consecutive indexTwo
      _ = normTwoIndexOneWindowBound :=
        normTwoIndexOneWindowBound_eq_centeredIndexTwoWindowBound.symm

/-- Every consecutive squared Dirichlet window is at most `28/15`: this is
the index-one finite-octant bound, while the centered index-two bound
`112/71` is strictly smaller. -/
theorem AreConsecutiveBest.dirichletWindowQuadrance_le_twentyEight_fifteenths
    {source : RFAP.HurwitzRational.Fraction}
    {lower upper : RFAP.HurwitzRational.ConvergentPair}
    (consecutive : RFAP.BestApproximation.AreConsecutiveBest
      source.value lower upper) :
    RFAP.BestApproximation.dirichletWindowQuadrance
      source.value lower upper ≤ 28 / 15 := by
  rcases consecutive.coefficientIndexQuadrance_eq_one_or_two with
      indexOne | indexTwo
  · exact
      RFAP.IndexOneWindow.AreConsecutiveBest.dirichletWindowQuadrance_le_twentyEight_fifteenths_of_indexOne
        consecutive indexOne
  · exact
      (RFAP.IndexTwoWindow.AreConsecutiveBest.dirichletWindowQuadrance_le_oneHundredTwelve_seventyFirsts_of_indexTwo
        consecutive indexTwo).trans (by
          rw [← normTwoIndexOneWindowBound_eq_centeredIndexTwoWindowBound]
          exact normTwoIndexOneWindowBound_le_twentyEight_fifteenths)

/-- Compatibility consequence of the sharper universal rational bound. -/
theorem AreConsecutiveBest.dirichletWindowQuadrance_le_two
    {source : RFAP.HurwitzRational.Fraction}
    {lower upper : RFAP.HurwitzRational.ConvergentPair}
    (consecutive : RFAP.BestApproximation.AreConsecutiveBest
      source.value lower upper) :
    RFAP.BestApproximation.dirichletWindowQuadrance
      source.value lower upper ≤ 2 :=
  (dirichletWindowQuadrance_le_normTwoUniversalWindowBound consecutive).trans
    normTwoIndexOneWindowBound_le_two

end RFAP.IndexOneWindow
