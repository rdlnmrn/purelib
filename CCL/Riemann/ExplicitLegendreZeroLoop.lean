import CCL.Riemann.ExplicitLegendreSegment

/-!
# Explicit lower crossing for a rational loop around zero

This module reflects the certified upper crossing from
`ExplicitLegendreSegment` into the lower half-plane.  The moving root travels
from `-1/4 - 2i` to `1/4 - 2i`; because it now starts below the fixed root at
zero, the extracted event is a second positive lower crossing.  The two
positive crossings are the geometric core of the standard zero braid.
-/

namespace CCL.Riemann.ExplicitLegendreZeroLoop

open CCL.Riemann.LegendrePaths
open CCL.Riemann.ExplicitLegendreSegment

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial :=
  RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Box := RFAP.Boxes.Box
abbrev LocalOwner := CCL.ProgressivePolynomialRoots.LocalOwner
abbrev BoundaryClearance := RFAP.BoxClearance.BoundaryClearance
abbrev CoefficientTable :=
  CCL.ProgressivePolynomialRoots.CoefficientTable

def lowerLeftParameter : Gaussian := gaussian (-(1 / 4)) (-2)
def lowerRightParameter : Gaussian := gaussian (1 / 4) (-2)

theorem lowerLeft_polynomial_eq_factors :
    polynomial lowerLeftParameter = factorsAt lowerLeftParameter := by
  decide

theorem lowerRight_polynomial_eq_factors :
    polynomial lowerRightParameter = factorsAt lowerRightParameter := by
  decide

def lowerMovingBox : Box where
  xLower := -1
  xUpper := 1
  yLower := -3
  yUpper := -1
  x_valid := by decide
  y_valid := by decide

theorem lowerMovingBox_proper : lowerMovingBox.Proper := by
  constructor <;> decide

/-! ## Six exact lower owners -/

def lowerLeftZeroClearance :
    BoundaryClearance (polynomial lowerLeftParameter) (fixedBox 0) := by
  rw [lowerLeft_polynomial_eq_factors]
  exact factorsClearance
    (centeredClearance 0 (by decide) (by decide) (by decide) (by decide))
    (belowClearance lowerLeftParameter (by decide))
    (rightClearance 1 (by decide))

def lowerLeftMovingClearance :
    BoundaryClearance (polynomial lowerLeftParameter) lowerMovingBox := by
  rw [lowerLeft_polynomial_eq_factors]
  exact factorsClearance
    (aboveClearance 0 (by decide))
    (centeredClearance lowerLeftParameter
      (by decide) (by decide) (by decide) (by decide))
    (aboveClearance 1 (by decide))

def lowerLeftOneClearance :
    BoundaryClearance (polynomial lowerLeftParameter) (fixedBox 1) := by
  rw [lowerLeft_polynomial_eq_factors]
  exact factorsClearance
    (leftClearance 0 (by decide))
    (belowClearance lowerLeftParameter (by decide))
    (centeredClearance 1 (by decide) (by decide) (by decide) (by decide))

def lowerRightZeroClearance :
    BoundaryClearance (polynomial lowerRightParameter) (fixedBox 0) := by
  rw [lowerRight_polynomial_eq_factors]
  exact factorsClearance
    (centeredClearance 0 (by decide) (by decide) (by decide) (by decide))
    (belowClearance lowerRightParameter (by decide))
    (rightClearance 1 (by decide))

def lowerRightMovingClearance :
    BoundaryClearance (polynomial lowerRightParameter) lowerMovingBox := by
  rw [lowerRight_polynomial_eq_factors]
  exact factorsClearance
    (aboveClearance 0 (by decide))
    (centeredClearance lowerRightParameter
      (by decide) (by decide) (by decide) (by decide))
    (aboveClearance 1 (by decide))

def lowerRightOneClearance :
    BoundaryClearance (polynomial lowerRightParameter) (fixedBox 1) := by
  rw [lowerRight_polynomial_eq_factors]
  exact factorsClearance
    (leftClearance 0 (by decide))
    (belowClearance lowerRightParameter (by decide))
    (centeredClearance 1 (by decide) (by decide) (by decide) (by decide))

def lowerSampleZeroClearance (lambda : Gaussian)
    (movingLeft : lambda.re < (sampleBox 0).xLower) :
    BoundaryClearance (factorsAt lambda) (sampleBox 0) :=
  factorsClearance
    (centeredClearance 0 (by decide) (by decide) (by decide) (by decide))
    (leftClearance lambda movingLeft)
    (rightClearance 1 (by decide))

def lowerSampleMovingClearance (lambda : Gaussian)
    (zeroRight : (sampleBox lambda).xUpper < (0 : Gaussian).re)
    (oneRight : (sampleBox lambda).xUpper < (1 : Gaussian).re) :
    BoundaryClearance (factorsAt lambda) (sampleBox lambda) :=
  factorsClearance
    (rightClearance 0 zeroRight)
    (centeredClearance lambda
      (by
        change lambda.re - 1 / 16 < lambda.re
        simpa using RFAP.ConstructiveFraction.sub_lt_sub_left_direct
          (by decide : (0 : Coordinate) < 1 / 16) lambda.re)
      (by
        change lambda.re < lambda.re + 1 / 16
        simpa using RFAP.ConstructiveFraction.add_lt_add_left_direct
          (by decide : (0 : Coordinate) < 1 / 16) lambda.re)
      (by
        change lambda.im - 1 / 16 < lambda.im
        simpa using RFAP.ConstructiveFraction.sub_lt_sub_left_direct
          (by decide : (0 : Coordinate) < 1 / 16) lambda.im)
      (by
        change lambda.im < lambda.im + 1 / 16
        simpa using RFAP.ConstructiveFraction.add_lt_add_left_direct
          (by decide : (0 : Coordinate) < 1 / 16) lambda.im))
    (rightClearance 1 oneRight)

def lowerSampleOneClearance (lambda : Gaussian)
    (movingLeft : lambda.re < (sampleBox 1).xLower) :
    BoundaryClearance (factorsAt lambda) (sampleBox 1) :=
  factorsClearance
    (leftClearance 0 (by decide))
    (leftClearance lambda movingLeft)
    (centeredClearance 1 (by decide) (by decide) (by decide) (by decide))

def lowerRightSampleZeroClearance (lambda : Gaussian)
    (movingRight : (sampleBox 0).xUpper < lambda.re) :
    BoundaryClearance (factorsAt lambda) (sampleBox 0) :=
  factorsClearance
    (centeredClearance 0 (by decide) (by decide) (by decide) (by decide))
    (rightClearance lambda movingRight)
    (rightClearance 1 (by decide))

def lowerRightSampleMovingClearance (lambda : Gaussian)
    (zeroLeft : (0 : Gaussian).re < (sampleBox lambda).xLower)
    (oneRight : (sampleBox lambda).xUpper < (1 : Gaussian).re) :
    BoundaryClearance (factorsAt lambda) (sampleBox lambda) :=
  factorsClearance
    (leftClearance 0 zeroLeft)
    (centeredClearance lambda
      (by
        change lambda.re - 1 / 16 < lambda.re
        simpa using RFAP.ConstructiveFraction.sub_lt_sub_left_direct
          (by decide : (0 : Coordinate) < 1 / 16) lambda.re)
      (by
        change lambda.re < lambda.re + 1 / 16
        simpa using RFAP.ConstructiveFraction.add_lt_add_left_direct
          (by decide : (0 : Coordinate) < 1 / 16) lambda.re)
      (by
        change lambda.im - 1 / 16 < lambda.im
        simpa using RFAP.ConstructiveFraction.sub_lt_sub_left_direct
          (by decide : (0 : Coordinate) < 1 / 16) lambda.im)
      (by
        change lambda.im < lambda.im + 1 / 16
        simpa using RFAP.ConstructiveFraction.add_lt_add_left_direct
          (by decide : (0 : Coordinate) < 1 / 16) lambda.im))
    (rightClearance 1 oneRight)

theorem lowerLeftZeroWinding :
    RFAP.Winding.quadrupledBoxWinding
      (polynomial lowerLeftParameter) (fixedBox 0) = 4 := by
  rw [lowerLeft_polynomial_eq_factors]
  apply factors_winding_of_sum (fixedBox_proper 0)
    (centeredClearance 0 (by decide) (by decide) (by decide) (by decide))
    (belowClearance lowerLeftParameter (by decide))
    (rightClearance 1 (by decide))
  have zeroWinding : RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor 0) (fixedBox 0) = 4 :=
    RFAP.AffineWinding.quadrupledBoxWinding_translatedCoordinate 0
      (by decide) (by decide) (by decide) (by decide)
  have movingWinding : RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor lowerLeftParameter)
        (fixedBox 0) = 0 := by decide
  have oneWinding : RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor 1) (fixedBox 0) = 0 := by
    decide
  rw [zeroWinding, movingWinding, oneWinding]
  ring1

theorem lowerLeftMovingWinding :
    RFAP.Winding.quadrupledBoxWinding
      (polynomial lowerLeftParameter) lowerMovingBox = 4 := by
  rw [lowerLeft_polynomial_eq_factors]
  apply factors_winding_of_sum lowerMovingBox_proper
    (aboveClearance 0 (by decide))
    (centeredClearance lowerLeftParameter
      (by decide) (by decide) (by decide) (by decide))
    (aboveClearance 1 (by decide))
  have zeroWinding : RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor 0) lowerMovingBox = 0 := by
    decide
  have movingWinding : RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor lowerLeftParameter)
        lowerMovingBox = 4 :=
    RFAP.AffineWinding.quadrupledBoxWinding_translatedCoordinate
      lowerLeftParameter (by decide) (by decide) (by decide) (by decide)
  have oneWinding : RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor 1) lowerMovingBox = 0 := by
    decide
  rw [zeroWinding, movingWinding, oneWinding]
  ring1

theorem lowerLeftOneWinding :
    RFAP.Winding.quadrupledBoxWinding
      (polynomial lowerLeftParameter) (fixedBox 1) = 4 := by
  rw [lowerLeft_polynomial_eq_factors]
  apply factors_winding_of_sum (fixedBox_proper 1)
    (leftClearance 0 (by decide))
    (belowClearance lowerLeftParameter (by decide))
    (centeredClearance 1 (by decide) (by decide) (by decide) (by decide))
  have zeroWinding : RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor 0) (fixedBox 1) = 0 := by
    decide
  have movingWinding : RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor lowerLeftParameter)
        (fixedBox 1) = 0 := by decide
  have oneWinding : RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor 1) (fixedBox 1) = 4 :=
    RFAP.AffineWinding.quadrupledBoxWinding_translatedCoordinate 1
      (by decide) (by decide) (by decide) (by decide)
  rw [zeroWinding, movingWinding, oneWinding]
  ring1

theorem lowerRightZeroWinding :
    RFAP.Winding.quadrupledBoxWinding
      (polynomial lowerRightParameter) (fixedBox 0) = 4 := by
  rw [lowerRight_polynomial_eq_factors]
  apply factors_winding_of_sum (fixedBox_proper 0)
    (centeredClearance 0 (by decide) (by decide) (by decide) (by decide))
    (belowClearance lowerRightParameter (by decide))
    (rightClearance 1 (by decide))
  have zeroWinding : RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor 0) (fixedBox 0) = 4 :=
    RFAP.AffineWinding.quadrupledBoxWinding_translatedCoordinate 0
      (by decide) (by decide) (by decide) (by decide)
  have movingWinding : RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor lowerRightParameter)
        (fixedBox 0) = 0 := by decide
  have oneWinding : RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor 1) (fixedBox 0) = 0 := by
    decide
  rw [zeroWinding, movingWinding, oneWinding]
  ring1

theorem lowerRightMovingWinding :
    RFAP.Winding.quadrupledBoxWinding
      (polynomial lowerRightParameter) lowerMovingBox = 4 := by
  rw [lowerRight_polynomial_eq_factors]
  apply factors_winding_of_sum lowerMovingBox_proper
    (aboveClearance 0 (by decide))
    (centeredClearance lowerRightParameter
      (by decide) (by decide) (by decide) (by decide))
    (aboveClearance 1 (by decide))
  have zeroWinding : RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor 0) lowerMovingBox = 0 := by
    decide
  have movingWinding : RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor lowerRightParameter)
        lowerMovingBox = 4 :=
    RFAP.AffineWinding.quadrupledBoxWinding_translatedCoordinate
      lowerRightParameter (by decide) (by decide) (by decide) (by decide)
  have oneWinding : RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor 1) lowerMovingBox = 0 := by
    decide
  rw [zeroWinding, movingWinding, oneWinding]
  ring1

theorem lowerRightOneWinding :
    RFAP.Winding.quadrupledBoxWinding
      (polynomial lowerRightParameter) (fixedBox 1) = 4 := by
  rw [lowerRight_polynomial_eq_factors]
  apply factors_winding_of_sum (fixedBox_proper 1)
    (leftClearance 0 (by decide))
    (belowClearance lowerRightParameter (by decide))
    (centeredClearance 1 (by decide) (by decide) (by decide) (by decide))
  have zeroWinding : RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor 0) (fixedBox 1) = 0 := by
    decide
  have movingWinding : RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor lowerRightParameter)
        (fixedBox 1) = 0 := by decide
  have oneWinding : RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor 1) (fixedBox 1) = 4 :=
    RFAP.AffineWinding.quadrupledBoxWinding_translatedCoordinate 1
      (by decide) (by decide) (by decide) (by decide)
  rw [zeroWinding, movingWinding, oneWinding]
  ring1

theorem lowerLeftSampleZeroWinding :
    RFAP.Winding.quadrupledBoxWinding
      (polynomial lowerLeftParameter) (sampleBox 0) = 4 := by
  rw [lowerLeft_polynomial_eq_factors]
  apply factors_winding_of_sum (sampleBox_proper 0)
    (centeredClearance 0 (by decide) (by decide) (by decide) (by decide))
    (leftClearance lowerLeftParameter (by decide))
    (rightClearance 1 (by decide))
  unfold CCL.Riemann.ExplicitLegendreFrame.factor
  have zeroWinding : RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor 0) (sampleBox 0) = 4 :=
    RFAP.AffineWinding.quadrupledBoxWinding_translatedCoordinate 0
      (by decide) (by decide) (by decide) (by decide)
  have movingWinding : RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor lowerLeftParameter)
        (sampleBox 0) = 0 := by decide
  have oneWinding : RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor 1) (sampleBox 0) = 0 := by
    decide
  simp only [CCL.Riemann.ExplicitLegendreFrame.factor] at zeroWinding movingWinding oneWinding
  rw [zeroWinding, movingWinding, oneWinding]
  ring1

theorem lowerLeftSampleMovingWinding :
    RFAP.Winding.quadrupledBoxWinding
      (polynomial lowerLeftParameter) (sampleBox lowerLeftParameter) = 4 := by
  rw [lowerLeft_polynomial_eq_factors]
  apply factors_winding_of_sum (sampleBox_proper lowerLeftParameter)
    (rightClearance 0 (by decide))
    (centeredClearance lowerLeftParameter
      (by decide) (by decide) (by decide) (by decide))
    (rightClearance 1 (by decide))
  unfold CCL.Riemann.ExplicitLegendreFrame.factor
  have zeroWinding : RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor 0)
        (sampleBox lowerLeftParameter) = 0 := by decide
  have movingWinding : RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor lowerLeftParameter)
        (sampleBox lowerLeftParameter) = 4 :=
    RFAP.AffineWinding.quadrupledBoxWinding_translatedCoordinate
      lowerLeftParameter (by decide) (by decide) (by decide) (by decide)
  have oneWinding : RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor 1)
        (sampleBox lowerLeftParameter) = 0 := by decide
  simp only [CCL.Riemann.ExplicitLegendreFrame.factor] at zeroWinding movingWinding oneWinding
  rw [zeroWinding, movingWinding, oneWinding]
  ring1

theorem lowerLeftSampleOneWinding :
    RFAP.Winding.quadrupledBoxWinding
      (polynomial lowerLeftParameter) (sampleBox 1) = 4 := by
  rw [lowerLeft_polynomial_eq_factors]
  apply factors_winding_of_sum (sampleBox_proper 1)
    (leftClearance 0 (by decide))
    (leftClearance lowerLeftParameter (by decide))
    (centeredClearance 1 (by decide) (by decide) (by decide) (by decide))
  unfold CCL.Riemann.ExplicitLegendreFrame.factor
  have zeroWinding : RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor 0) (sampleBox 1) = 0 := by
    decide
  have movingWinding : RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor lowerLeftParameter)
        (sampleBox 1) = 0 := by decide
  have oneWinding : RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor 1) (sampleBox 1) = 4 :=
    RFAP.AffineWinding.quadrupledBoxWinding_translatedCoordinate 1
      (by decide) (by decide) (by decide) (by decide)
  simp only [CCL.Riemann.ExplicitLegendreFrame.factor] at zeroWinding movingWinding oneWinding
  rw [zeroWinding, movingWinding, oneWinding]
  ring1

theorem lowerRightSampleZeroWinding :
    RFAP.Winding.quadrupledBoxWinding
      (polynomial lowerRightParameter) (sampleBox 0) = 4 := by
  rw [lowerRight_polynomial_eq_factors]
  apply factors_winding_of_sum (sampleBox_proper 0)
    (centeredClearance 0 (by decide) (by decide) (by decide) (by decide))
    (rightClearance lowerRightParameter (by decide))
    (rightClearance 1 (by decide))
  unfold CCL.Riemann.ExplicitLegendreFrame.factor
  have zeroWinding : RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor 0) (sampleBox 0) = 4 :=
    RFAP.AffineWinding.quadrupledBoxWinding_translatedCoordinate 0
      (by decide) (by decide) (by decide) (by decide)
  have movingWinding : RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor lowerRightParameter)
        (sampleBox 0) = 0 := by decide
  have oneWinding : RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor 1) (sampleBox 0) = 0 := by
    decide
  simp only [CCL.Riemann.ExplicitLegendreFrame.factor] at zeroWinding movingWinding oneWinding
  rw [zeroWinding, movingWinding, oneWinding]
  ring1

theorem lowerRightSampleMovingWinding :
    RFAP.Winding.quadrupledBoxWinding
      (polynomial lowerRightParameter) (sampleBox lowerRightParameter) = 4 := by
  rw [lowerRight_polynomial_eq_factors]
  apply factors_winding_of_sum (sampleBox_proper lowerRightParameter)
    (leftClearance 0 (by decide))
    (centeredClearance lowerRightParameter
      (by decide) (by decide) (by decide) (by decide))
    (rightClearance 1 (by decide))
  unfold CCL.Riemann.ExplicitLegendreFrame.factor
  have zeroWinding : RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor 0)
        (sampleBox lowerRightParameter) = 0 := by decide
  have movingWinding : RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor lowerRightParameter)
        (sampleBox lowerRightParameter) = 4 :=
    RFAP.AffineWinding.quadrupledBoxWinding_translatedCoordinate
      lowerRightParameter (by decide) (by decide) (by decide) (by decide)
  have oneWinding : RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor 1)
        (sampleBox lowerRightParameter) = 0 := by decide
  simp only [CCL.Riemann.ExplicitLegendreFrame.factor] at zeroWinding movingWinding oneWinding
  rw [zeroWinding, movingWinding, oneWinding]
  ring1

theorem lowerRightSampleOneWinding :
    RFAP.Winding.quadrupledBoxWinding
      (polynomial lowerRightParameter) (sampleBox 1) = 4 := by
  rw [lowerRight_polynomial_eq_factors]
  apply factors_winding_of_sum (sampleBox_proper 1)
    (leftClearance 0 (by decide))
    (leftClearance lowerRightParameter (by decide))
    (centeredClearance 1 (by decide) (by decide) (by decide) (by decide))
  unfold CCL.Riemann.ExplicitLegendreFrame.factor
  have zeroWinding : RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor 0) (sampleBox 1) = 0 := by
    decide
  have movingWinding : RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor lowerRightParameter)
        (sampleBox 1) = 0 := by decide
  have oneWinding : RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor 1) (sampleBox 1) = 4 :=
    RFAP.AffineWinding.quadrupledBoxWinding_translatedCoordinate 1
      (by decide) (by decide) (by decide) (by decide)
  simp only [CCL.Riemann.ExplicitLegendreFrame.factor] at zeroWinding movingWinding oneWinding
  rw [zeroWinding, movingWinding, oneWinding]
  ring1

def lowerLeftZeroOwner : LocalOwner (polynomial lowerLeftParameter) :=
  ownerOf (fixedBox 0) (fixedBox_proper 0) lowerLeftZeroClearance
    lowerLeftZeroWinding

def lowerLeftMovingOwner : LocalOwner (polynomial lowerLeftParameter) :=
  ownerOf lowerMovingBox lowerMovingBox_proper lowerLeftMovingClearance
    lowerLeftMovingWinding

def lowerLeftOneOwner : LocalOwner (polynomial lowerLeftParameter) :=
  ownerOf (fixedBox 1) (fixedBox_proper 1) lowerLeftOneClearance
    lowerLeftOneWinding

def lowerRightZeroOwner : LocalOwner (polynomial lowerRightParameter) :=
  ownerOf (fixedBox 0) (fixedBox_proper 0) lowerRightZeroClearance
    lowerRightZeroWinding

def lowerRightMovingOwner : LocalOwner (polynomial lowerRightParameter) :=
  ownerOf lowerMovingBox lowerMovingBox_proper lowerRightMovingClearance
    lowerRightMovingWinding

def lowerRightOneOwner : LocalOwner (polynomial lowerRightParameter) :=
  ownerOf (fixedBox 1) (fixedBox_proper 1) lowerRightOneClearance
    lowerRightOneWinding

def lowerLeftSampleZero : LocalOwner (polynomial lowerLeftParameter) := by
  apply ownerOf (sampleBox 0) (sampleBox_proper 0)
  · rw [lowerLeft_polynomial_eq_factors]
    exact lowerSampleZeroClearance lowerLeftParameter (by decide)
  · exact lowerLeftSampleZeroWinding

def lowerLeftSampleMoving : LocalOwner (polynomial lowerLeftParameter) := by
  apply ownerOf (sampleBox lowerLeftParameter)
    (sampleBox_proper lowerLeftParameter)
  · rw [lowerLeft_polynomial_eq_factors]
    exact lowerSampleMovingClearance lowerLeftParameter (by decide) (by decide)
  · exact lowerLeftSampleMovingWinding

def lowerLeftSampleOne : LocalOwner (polynomial lowerLeftParameter) := by
  apply ownerOf (sampleBox 1) (sampleBox_proper 1)
  · rw [lowerLeft_polynomial_eq_factors]
    exact lowerSampleOneClearance lowerLeftParameter (by decide)
  · exact lowerLeftSampleOneWinding

def lowerRightSampleZero : LocalOwner (polynomial lowerRightParameter) := by
  apply ownerOf (sampleBox 0) (sampleBox_proper 0)
  · rw [lowerRight_polynomial_eq_factors]
    exact lowerRightSampleZeroClearance lowerRightParameter (by decide)
  · exact lowerRightSampleZeroWinding

def lowerRightSampleMoving : LocalOwner (polynomial lowerRightParameter) := by
  apply ownerOf (sampleBox lowerRightParameter)
    (sampleBox_proper lowerRightParameter)
  · rw [lowerRight_polynomial_eq_factors]
    exact lowerRightSampleMovingClearance lowerRightParameter
      (by decide) (by decide)
  · exact lowerRightSampleMovingWinding

def lowerRightSampleOne : LocalOwner (polynomial lowerRightParameter) := by
  apply ownerOf (sampleBox 1) (sampleBox_proper 1)
  · rw [lowerRight_polynomial_eq_factors]
    exact lowerSampleOneClearance lowerRightParameter (by decide)
  · exact lowerRightSampleOneWinding

private theorem finThree_cases (index : Fin 3) :
    index = 0 ∨ index = 1 ∨ index = 2 := by
  rcases index with ⟨value, bound⟩
  omega0

def lowerLeftOwner : Fin 3 -> LocalOwner (polynomial lowerLeftParameter)
  | 0 => lowerLeftZeroOwner
  | 1 => lowerLeftMovingOwner
  | 2 => lowerLeftOneOwner

def lowerRightOwner : Fin 3 -> LocalOwner (polynomial lowerRightParameter)
  | 0 => lowerRightZeroOwner
  | 1 => lowerRightMovingOwner
  | 2 => lowerRightOneOwner

theorem lowerLeftOwner_pairwise : forall left right : Fin 3, left ≠ right ->
    (lowerLeftOwner left).box.Separated (lowerLeftOwner right).box := by
  intro left right different
  rcases finThree_cases left with leftZero | leftOne | leftTwo <;>
    subst left <;>
    rcases finThree_cases right with rightZero | rightOne | rightTwo <;>
    subst right <;>
    first | exact (different rfl).elim | decide

theorem lowerRightOwner_pairwise : forall left right : Fin 3, left ≠ right ->
    (lowerRightOwner left).box.Separated (lowerRightOwner right).box := by
  intro left right different
  rcases finThree_cases left with leftZero | leftOne | leftTwo <;>
    subst left <;>
    rcases finThree_cases right with rightZero | rightOne | rightTwo <;>
    subst right <;>
    first | exact (different rfl).elim | decide

def lowerLeftOwnerFamily :
    CCL.ProgressivePolynomialRoots.OwnerFamily
      (polynomial lowerLeftParameter) 3 where
  owner := lowerLeftOwner
  pairwiseSeparated := lowerLeftOwner_pairwise

def lowerRightOwnerFamily :
    CCL.ProgressivePolynomialRoots.OwnerFamily
      (polynomial lowerRightParameter) 3 where
  owner := lowerRightOwner
  pairwiseSeparated := lowerRightOwner_pairwise

/-! ## Exact lower chambers and projected frames -/

def lowerLeftSquarefree : RFAP.Squarefree.SquarefreeCertificate
    (coefficientTable lowerLeftParameter).polynomial := by
  rw [coefficientTable_polynomial]
  exact CCL.Riemann.ExplicitLegendreFrame.squarefreeAt lowerLeftParameter
    (by decide)

def lowerRightSquarefree : RFAP.Squarefree.SquarefreeCertificate
    (coefficientTable lowerRightParameter).polynomial := by
  rw [coefficientTable_polynomial]
  exact CCL.Riemann.ExplicitLegendreFrame.squarefreeAt lowerRightParameter
    (by decide)

def lowerLeftIsolationInput :
    RFAP.BoxFTA.Input (coefficientTable lowerLeftParameter).polynomial where
  squarefree := lowerLeftSquarefree
  degreeAtLeastTwo := by decide

def lowerRightIsolationInput :
    RFAP.BoxFTA.Input (coefficientTable lowerRightParameter).polynomial where
  squarefree := lowerRightSquarefree
  degreeAtLeastTwo := by decide

def lowerLeftChamber : CCL.FiniteMonodromy.ChamberFrame where
  reference := coefficientTable lowerLeftParameter
  chamber :=
    { degreeAtLeastTwo := by decide
      squarefree := lowerLeftSquarefree
      owners := lowerLeftOwnerFamily
      referenceSmall := coefficientTable_allowances_lt _
        (CCL.ProgressivePolynomialRoots.simpleRootChamberTarget_pos
          (coefficientTable lowerLeftParameter) lowerLeftSquarefree
          lowerLeftOwnerFamily)
      referenceMaximality :=
        (CCL.BoxRFAPBridge.prove lowerLeftIsolationInput).boxes.maximality }

def lowerRightChamber : CCL.FiniteMonodromy.ChamberFrame where
  reference := coefficientTable lowerRightParameter
  chamber :=
    { degreeAtLeastTwo := by decide
      squarefree := lowerRightSquarefree
      owners := lowerRightOwnerFamily
      referenceSmall := coefficientTable_allowances_lt _
        (CCL.ProgressivePolynomialRoots.simpleRootChamberTarget_pos
          (coefficientTable lowerRightParameter) lowerRightSquarefree
          lowerRightOwnerFamily)
      referenceMaximality :=
        (CCL.BoxRFAPBridge.prove lowerRightIsolationInput).boxes.maximality }

@[simp] theorem lowerLeftChamber_polynomial :
    lowerLeftChamber.polynomial = polynomial lowerLeftParameter := rfl

@[simp] theorem lowerRightChamber_polynomial :
    lowerRightChamber.polynomial = polynomial lowerRightParameter := rfl

def lowerLeftProjectionOwner :
    Fin 3 -> LocalOwner (polynomial lowerLeftParameter)
  | 0 => lowerLeftSampleMoving
  | 1 => lowerLeftSampleZero
  | 2 => lowerLeftSampleOne

def lowerRightProjectionOwner :
    Fin 3 -> LocalOwner (polynomial lowerRightParameter)
  | 0 => lowerRightSampleZero
  | 1 => lowerRightSampleMoving
  | 2 => lowerRightSampleOne

def lowerLeftFrame : Frame lowerLeftParameter where
  chamber := lowerLeftChamber
  polynomial_eq := rfl
  labels := CCL.FiniteMonodromy.FiniteBijection.identity 3
  owner_contains := by
    intro label
    rcases finThree_cases label with labelZero | labelOne | labelTwo <;>
      subst label <;> decide
  projectionOrder := targetProjectionOrder
  projectionOwner := fun position =>
    CCL.FiniteMonodromy.castOwner lowerLeftChamber_polynomial.symm
      (lowerLeftProjectionOwner position)
  projection_refines := by
    intro position
    rcases finThree_cases position with positionZero | positionOne |
      positionTwo <;> subst position <;>
      simp only [lowerLeftProjectionOwner, targetProjectionOrder,
        lowerLeftChamber, lowerLeftOwnerFamily, lowerLeftOwner,
        lowerLeftSampleMoving, lowerLeftSampleZero, lowerLeftSampleOne,
        lowerLeftMovingOwner, lowerLeftZeroOwner, lowerLeftOneOwner, ownerOf,
        CCL.FiniteMonodromy.castOwner_box,
        CCL.FiniteMonodromy.ChamberFrame.owner] <;>
      exact ⟨by decide, by decide, by decide, by decide⟩
  projection_xOrdered := by
    intro left right order
    rcases finThree_cases left with leftZero | leftOne | leftTwo <;>
      subst left <;>
      rcases finThree_cases right with rightZero | rightOne | rightTwo <;>
      subst right <;>
      simp only [Fin.isValue, CCL.FiniteMonodromy.castOwner_box] at order ⊢ <;>
      first | omega0 | decide

def lowerRightFrame : Frame lowerRightParameter where
  chamber := lowerRightChamber
  polynomial_eq := rfl
  labels := CCL.FiniteMonodromy.FiniteBijection.identity 3
  owner_contains := by
    intro label
    rcases finThree_cases label with labelZero | labelOne | labelTwo <;>
      subst label <;> decide
  projectionOrder := CCL.FiniteMonodromy.FiniteBijection.identity 3
  projectionOwner := fun position =>
    CCL.FiniteMonodromy.castOwner lowerRightChamber_polynomial.symm
      (lowerRightProjectionOwner position)
  projection_refines := by
    intro position
    rcases finThree_cases position with positionZero | positionOne |
      positionTwo <;> subst position <;>
      simp only [lowerRightProjectionOwner,
        CCL.FiniteMonodromy.FiniteBijection.identity,
        lowerRightChamber, lowerRightOwnerFamily, lowerRightOwner,
        lowerRightSampleMoving, lowerRightSampleZero, lowerRightSampleOne,
        lowerRightMovingOwner, lowerRightZeroOwner, lowerRightOneOwner, ownerOf,
        CCL.FiniteMonodromy.castOwner_box,
        CCL.FiniteMonodromy.ChamberFrame.owner] <;>
      exact ⟨by decide, by decide, by decide, by decide⟩
  projection_xOrdered := by
    intro left right order
    rcases finThree_cases left with leftZero | leftOne | leftTwo <;>
      subst left <;>
      rcases finThree_cases right with rightZero | rightOne | rightTwo <;>
      subst right <;>
      simp only [Fin.isValue, CCL.FiniteMonodromy.castOwner_box] at order ⊢ <;>
      first | omega0 | decide

/-! ## The lower positive crossing -/

def lowerPerturbation : GaussianPolynomial :=
  perturbationAt lowerLeftParameter lowerRightParameter

theorem lower_target_eq_add : polynomial lowerRightParameter =
    polynomial lowerLeftParameter + lowerPerturbation := by
  decide

def lowerOrientedRouche
    (owner : LocalOwner (polynomial lowerLeftParameter))
    (dominance : RFAP.WindingHomotopy.BoundaryNormDominance
      (polynomial lowerLeftParameter) lowerPerturbation owner.box) :
    CCL.FiniteMonodromy.OrientedRouche
      (polynomial lowerLeftParameter) (polynomial lowerRightParameter)
      owner.box where
  perturbation := lowerPerturbation
  target_eq_add := lower_target_eq_add
  dominance := dominance

def lowerZeroDominance : RFAP.WindingHomotopy.BoundaryNormDominance
    (polynomial lowerLeftParameter) lowerPerturbation
      lowerLeftZeroOwner.box :=
  factorMoveDominanceAt lowerLeftParameter lowerRightParameter
    (centeredClearance 0 (by decide) (by decide) (by decide) (by decide))
    (belowClearance lowerLeftParameter (by decide))
    (rightClearance 1 (by decide)) (by decide)

def lowerMovingDominance : RFAP.WindingHomotopy.BoundaryNormDominance
    (polynomial lowerLeftParameter) lowerPerturbation
      lowerLeftMovingOwner.box :=
  factorMoveDominanceAt lowerLeftParameter lowerRightParameter
    (aboveClearance 0 (by decide))
    (centeredClearance lowerLeftParameter
      (by decide) (by decide) (by decide) (by decide))
    (aboveClearance 1 (by decide)) (by decide)

def lowerOneDominance : RFAP.WindingHomotopy.BoundaryNormDominance
    (polynomial lowerLeftParameter) lowerPerturbation
      lowerLeftOneOwner.box :=
  factorMoveDominanceAt lowerLeftParameter lowerRightParameter
    (leftClearance 0 (by decide))
    (belowClearance lowerLeftParameter (by decide))
    (centeredClearance 1 (by decide) (by decide) (by decide) (by decide))
    (by decide)

def lowerZeroBridge : CCL.FiniteMonodromy.OwnerBridge
    (polynomial lowerLeftParameter) (polynomial lowerRightParameter) :=
  CCL.FiniteMonodromy.OwnerBridge.ofForward lowerLeftZeroOwner
    (lowerOrientedRouche lowerLeftZeroOwner lowerZeroDominance)

def lowerMovingBridge : CCL.FiniteMonodromy.OwnerBridge
    (polynomial lowerLeftParameter) (polynomial lowerRightParameter) :=
  CCL.FiniteMonodromy.OwnerBridge.ofForward lowerLeftMovingOwner
    (lowerOrientedRouche lowerLeftMovingOwner lowerMovingDominance)

def lowerOneBridge : CCL.FiniteMonodromy.OwnerBridge
    (polynomial lowerLeftParameter) (polynomial lowerRightParameter) :=
  CCL.FiniteMonodromy.OwnerBridge.ofForward lowerLeftOneOwner
    (lowerOrientedRouche lowerLeftOneOwner lowerOneDominance)

def lowerBridgeAt : Fin 3 -> CCL.FiniteMonodromy.OwnerBridge
    (polynomial lowerLeftParameter) (polynomial lowerRightParameter)
  | 0 => lowerZeroBridge
  | 1 => lowerMovingBridge
  | 2 => lowerOneBridge

def lowerChamberOverlap : CCL.FiniteMonodromy.ChamberOverlap
    lowerLeftChamber lowerRightChamber where
  matching := CCL.FiniteMonodromy.FiniteBijection.identity 3
  bridge := lowerBridgeAt
  bridge_refines_left := by
    intro index
    rcases finThree_cases index with indexZero | indexOne | indexTwo <;>
      subst index <;> exact RFAP.Boxes.Box.refines_refl _
  bridge_refines_right := by
    intro index
    rcases finThree_cases index with indexZero | indexOne | indexTwo <;>
      subst index <;> exact RFAP.Boxes.Box.refines_refl _

theorem lowerCrossingGeometry :
    CCL.Knot.ProjectedCrossings.CrossingGeometry
      lowerLeftFrame.projected lowerRightFrame.projected lowerChamberOverlap
      CCL.Riemann.LegendreConventions.lowerPositive where
  heightSeparated := by
    change lowerMovingBox.yUpper < (fixedBox 0).yLower
    decide

def lowerProjectedOverlap : CCL.Knot.ProjectedCrossings.ProjectedOverlap
    lowerLeftFrame.projected lowerRightFrame.projected :=
  .crossing lowerChamberOverlap
    CCL.Riemann.LegendreConventions.lowerPositive lowerCrossingGeometry (by
      intro position
      rcases finThree_cases position with positionZero | positionOne |
        positionTwo <;> subst position <;> rfl)

def lowerSheetBound : Coordinate :=
  min lowerZeroBridge.leftClearance.bound
    (min lowerZeroBridge.rightClearance.bound
      (min lowerMovingBridge.leftClearance.bound
        (min lowerMovingBridge.rightClearance.bound
          (min lowerOneBridge.leftClearance.bound
            lowerOneBridge.rightClearance.bound))))

theorem lowerSheetBound_positive : 0 < lowerSheetBound := by
  unfold lowerSheetBound
  exact lt_min lowerZeroBridge.leftClearance.positive
    (lt_min lowerZeroBridge.rightClearance.positive
      (lt_min lowerMovingBridge.leftClearance.positive
        (lt_min lowerMovingBridge.rightClearance.positive
          (lt_min lowerOneBridge.leftClearance.positive
            lowerOneBridge.rightClearance.positive))))

def lowerSheetClearance : BridgeClearance lowerLeftFrame lowerRightFrame
    lowerChamberOverlap where
  bound := lowerSheetBound
  positive := lowerSheetBound_positive
  leftLower := by
    intro index
    rcases finThree_cases index with indexZero | indexOne | indexTwo
    · subst index
      exact min_le_left _ _
    · subst index
      exact (min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _))
    · subst index
      exact (min_le_right _ _).trans
        ((min_le_right _ _).trans
          ((min_le_right _ _).trans
            ((min_le_right _ _).trans (min_le_left _ _))))
  rightLower := by
    intro index
    rcases finThree_cases index with indexZero | indexOne | indexTwo
    · subst index
      exact (min_le_right _ _).trans (min_le_left _ _)
    · subst index
      exact (min_le_right _ _).trans
        ((min_le_right _ _).trans
          ((min_le_right _ _).trans (min_le_left _ _)))
    · subst index
      exact (min_le_right _ _).trans
        ((min_le_right _ _).trans
          ((min_le_right _ _).trans
            ((min_le_right _ _).trans (min_le_right _ _))))

def lowerGeometry : AxisSegment lowerLeftParameter lowerRightParameter :=
  .horizontal (-(1 / 4)) (1 / 4) (-2)

def lowerGeometrySafe : AxisSegment.Safe lowerGeometry where
  avoidsZero := { bound := 1, positive := by decide, lower := by decide }
  avoidsOne := { bound := 1, positive := by decide, lower := by decide }

/-- The second positive lower half-twist needed by the zero loop. -/
def lowerSegment : Segment lowerLeftFrame lowerRightFrame :=
  Segment.ofProjectedOverlap lowerGeometry lowerGeometrySafe
    lowerProjectedOverlap lowerSheetClearance

@[simp] theorem lowerSegment_crossings : lowerSegment.crossings =
    [CCL.Riemann.LegendreConventions.lowerPositive] := rfl

def lowerPath : Path lowerLeftFrame lowerRightFrame :=
  .cons lowerSegment (.nil lowerRightFrame)

@[simp] theorem lowerPath_word : lowerPath.word =
    [CCL.Riemann.LegendreConventions.lowerPositive] := rfl

end CCL.Riemann.ExplicitLegendreZeroLoop
