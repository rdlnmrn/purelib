import CCL.Riemann.ExplicitLegendreZeroLoop

/-!
# Stationary rational connectors for the explicit Legendre zero loop

The two certified horizontal crossings live at imaginary heights `2` and
`-2`.  This module supplies a uniform family of exact root frames on the
vertical lines `re lambda = ±1/4`.  Narrow fixed-root boxes and a wider
moving-root box make a displacement of `1/5` Rouché-safe, so twenty finite
stationary cells join the two crossings on each side.
-/

namespace CCL.Riemann.ExplicitLegendreConnectors

open CCL.Riemann.LegendrePaths
open CCL.Riemann.ExplicitLegendreSegment
open CCL.Riemann.ExplicitLegendreZeroLoop

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial :=
  RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Box := RFAP.Boxes.Box
abbrev LocalOwner := CCL.ProgressivePolynomialRoots.LocalOwner
abbrev BoundaryClearance := RFAP.BoxClearance.BoundaryClearance
abbrev CoefficientTable :=
  CCL.ProgressivePolynomialRoots.CoefficientTable

/-- The four vertical sides of the rational rectangles around the two finite
Legendre branch parameters.  The legacy names `left` and `right` are the
sides around zero; `oneLeft` and `oneRight` are the sides around one. -/
inductive Side
  | left
  | right
  | oneLeft
  | oneRight
deriving DecidableEq, Repr

def sideReal : Side -> Coordinate
  | .left => -(1 / 4)
  | .right => 1 / 4
  | .oneLeft => 3 / 4
  | .oneRight => 5 / 4

def connectorParameter (side : Side) (height : Coordinate) : Gaussian :=
  gaussian (sideReal side) height

@[simp] theorem connectorParameter_re (side : Side) (height : Coordinate) :
    (connectorParameter side height).re = sideReal side := rfl

@[simp] theorem connectorParameter_im (side : Side) (height : Coordinate) :
    (connectorParameter side height).im = height := rfl

/-- Fixed roots use especially narrow boxes, leaving a large horizontal
Rouché margin even when the moving root passes at distance `1/4`. -/
def connectorFixedBox (root : Gaussian) : Box where
  xLower := root.re - 1 / 16
  xUpper := root.re + 1 / 16
  yLower := root.im - 1 / 16
  yUpper := root.im + 1 / 16
  x_valid := by
    apply le_of_lt
    calc
      root.re - 1 / 16 < root.re := by
        simpa using RFAP.ConstructiveFraction.sub_lt_sub_left_direct
          (by decide : (0 : Coordinate) < 1 / 16) root.re
      _ < root.re + 1 / 16 := by
        simpa using RFAP.ConstructiveFraction.add_lt_add_left_direct
          (by decide : (0 : Coordinate) < 1 / 16) root.re
  y_valid := by
    apply le_of_lt
    calc
      root.im - 1 / 16 < root.im := by
        simpa using RFAP.ConstructiveFraction.sub_lt_sub_left_direct
          (by decide : (0 : Coordinate) < 1 / 16) root.im
      _ < root.im + 1 / 16 := by
        simpa using RFAP.ConstructiveFraction.add_lt_add_left_direct
          (by decide : (0 : Coordinate) < 1 / 16) root.im

def connectorMovingBox (side : Side) (height : Coordinate) : Box where
  xLower := sideReal side - 1 / 10
  xUpper := sideReal side + 1 / 10
  yLower := height - 1 / 2
  yUpper := height + 1 / 2
  x_valid := by
    apply le_of_lt
    calc
      sideReal side - 1 / 10 < sideReal side := by
        simpa using RFAP.ConstructiveFraction.sub_lt_sub_left_direct
          (by decide : (0 : Coordinate) < 1 / 10) (sideReal side)
      _ < sideReal side + 1 / 10 := by
        simpa using RFAP.ConstructiveFraction.add_lt_add_left_direct
          (by decide : (0 : Coordinate) < 1 / 10) (sideReal side)
  y_valid := by
    apply le_of_lt
    calc
      height - 1 / 2 < height := by
        simpa using RFAP.ConstructiveFraction.sub_lt_sub_left_direct
          (by decide : (0 : Coordinate) < 1 / 2) height
      _ < height + 1 / 2 := by
        simpa using RFAP.ConstructiveFraction.add_lt_add_left_direct
          (by decide : (0 : Coordinate) < 1 / 2) height

theorem connectorFixedBox_proper (root : Gaussian) :
    (connectorFixedBox root).Proper := by
  constructor
  · change root.re - 1 / 16 < root.re + 1 / 16
    calc
      root.re - 1 / 16 < root.re := by
        simpa using RFAP.ConstructiveFraction.sub_lt_sub_left_direct
          (by decide : (0 : Coordinate) < 1 / 16) root.re
      _ < root.re + 1 / 16 := by
        simpa using RFAP.ConstructiveFraction.add_lt_add_left_direct
          (by decide : (0 : Coordinate) < 1 / 16) root.re
  · change root.im - 1 / 16 < root.im + 1 / 16
    calc
      root.im - 1 / 16 < root.im := by
        simpa using RFAP.ConstructiveFraction.sub_lt_sub_left_direct
          (by decide : (0 : Coordinate) < 1 / 16) root.im
      _ < root.im + 1 / 16 := by
        simpa using RFAP.ConstructiveFraction.add_lt_add_left_direct
          (by decide : (0 : Coordinate) < 1 / 16) root.im

theorem connectorMovingBox_proper (side : Side) (height : Coordinate) :
    (connectorMovingBox side height).Proper := by
  constructor
  · change sideReal side - 1 / 10 < sideReal side + 1 / 10
    calc
      sideReal side - 1 / 10 < sideReal side := by
        simpa using RFAP.ConstructiveFraction.sub_lt_sub_left_direct
          (by decide : (0 : Coordinate) < 1 / 10) (sideReal side)
      _ < sideReal side + 1 / 10 := by
        simpa using RFAP.ConstructiveFraction.add_lt_add_left_direct
          (by decide : (0 : Coordinate) < 1 / 10) (sideReal side)
  · change height - 1 / 2 < height + 1 / 2
    calc
      height - 1 / 2 < height := by
        simpa using RFAP.ConstructiveFraction.sub_lt_sub_left_direct
          (by decide : (0 : Coordinate) < 1 / 2) height
      _ < height + 1 / 2 := by
        simpa using RFAP.ConstructiveFraction.add_lt_add_left_direct
          (by decide : (0 : Coordinate) < 1 / 2) height

theorem connectorMovingBox_contains (side : Side) (height : Coordinate) :
    (connectorMovingBox side height).Contains
      (connectorParameter side height) := by
  constructor
  · change sideReal side - 1 / 10 <= sideReal side
    exact (by
      simpa using RFAP.ConstructiveFraction.sub_lt_sub_left_direct
        (by decide : (0 : Coordinate) < 1 / 10) (sideReal side) :
      sideReal side - 1 / 10 < sideReal side).le
  constructor
  · change sideReal side <= sideReal side + 1 / 10
    exact (by
      simpa using RFAP.ConstructiveFraction.add_lt_add_left_direct
        (by decide : (0 : Coordinate) < 1 / 10) (sideReal side) :
      sideReal side < sideReal side + 1 / 10).le
  constructor
  · change height - 1 / 2 <= height
    exact (by
      simpa using RFAP.ConstructiveFraction.sub_lt_sub_left_direct
        (by decide : (0 : Coordinate) < 1 / 2) height :
      height - 1 / 2 < height).le
  · change height <= height + 1 / 2
    exact (by
      simpa using RFAP.ConstructiveFraction.add_lt_add_left_direct
        (by decide : (0 : Coordinate) < 1 / 2) height :
      height < height + 1 / 2).le

theorem connectorFixedBox_left (root : Gaussian) :
    (connectorFixedBox root).xLower < root.re := by
  change root.re - 1 / 16 < root.re
  simpa using RFAP.ConstructiveFraction.sub_lt_sub_left_direct
    (by decide : (0 : Coordinate) < 1 / 16) root.re

theorem connectorFixedBox_right (root : Gaussian) :
    root.re < (connectorFixedBox root).xUpper := by
  change root.re < root.re + 1 / 16
  simpa using RFAP.ConstructiveFraction.add_lt_add_left_direct
    (by decide : (0 : Coordinate) < 1 / 16) root.re

theorem connectorFixedBox_below (root : Gaussian) :
    (connectorFixedBox root).yLower < root.im := by
  change root.im - 1 / 16 < root.im
  simpa using RFAP.ConstructiveFraction.sub_lt_sub_left_direct
    (by decide : (0 : Coordinate) < 1 / 16) root.im

theorem connectorFixedBox_above (root : Gaussian) :
    root.im < (connectorFixedBox root).yUpper := by
  change root.im < root.im + 1 / 16
  simpa using RFAP.ConstructiveFraction.add_lt_add_left_direct
    (by decide : (0 : Coordinate) < 1 / 16) root.im

theorem connectorFixedBox_contains (root : Gaussian) :
    (connectorFixedBox root).Contains root :=
  ⟨(connectorFixedBox_left root).le,
    (connectorFixedBox_right root).le,
    (connectorFixedBox_below root).le,
    (connectorFixedBox_above root).le⟩

theorem connectorMovingBox_left (side : Side) (height : Coordinate) :
    (connectorMovingBox side height).xLower < sideReal side := by
  change sideReal side - 1 / 10 < sideReal side
  simpa using RFAP.ConstructiveFraction.sub_lt_sub_left_direct
    (by decide : (0 : Coordinate) < 1 / 10) (sideReal side)

theorem connectorMovingBox_right (side : Side) (height : Coordinate) :
    sideReal side < (connectorMovingBox side height).xUpper := by
  change sideReal side < sideReal side + 1 / 10
  simpa using RFAP.ConstructiveFraction.add_lt_add_left_direct
    (by decide : (0 : Coordinate) < 1 / 10) (sideReal side)

theorem connectorMovingBox_below (side : Side) (height : Coordinate) :
    (connectorMovingBox side height).yLower < height := by
  change height - 1 / 2 < height
  simpa using RFAP.ConstructiveFraction.sub_lt_sub_left_direct
    (by decide : (0 : Coordinate) < 1 / 2) height

theorem connectorMovingBox_above (side : Side) (height : Coordinate) :
    height < (connectorMovingBox side height).yUpper := by
  change height < height + 1 / 2
  simpa using RFAP.ConstructiveFraction.add_lt_add_left_direct
    (by decide : (0 : Coordinate) < 1 / 2) height

theorem leftParameter_left_zero (height : Coordinate) :
    (connectorParameter .left height).re < (connectorFixedBox 0).xLower := by
  change (-(1 / 4 : Coordinate)) < -(1 / 16)
  decide

theorem zero_left_rightParameter (height : Coordinate) :
    (connectorFixedBox 0).xUpper <
      (connectorParameter .right height).re := by
  change (1 / 16 : Coordinate) < 1 / 4
  decide

theorem leftMoving_before_zero (height : Coordinate) :
    (connectorMovingBox .left height).xUpper < (0 : Gaussian).re := by
  change (-(1 / 4 : Coordinate)) + 1 / 10 < 0
  decide

theorem zero_before_rightMoving (height : Coordinate) :
    (0 : Gaussian).re < (connectorMovingBox .right height).xLower := by
  change (0 : Coordinate) < 1 / 4 - 1 / 10
  decide

theorem leftMoving_before_one (height : Coordinate) :
    (connectorMovingBox .left height).xUpper < (1 : Gaussian).re := by
  change (-(1 / 4 : Coordinate)) + 1 / 10 < 1
  decide

theorem rightMoving_before_one (height : Coordinate) :
    (connectorMovingBox .right height).xUpper < (1 : Gaussian).re := by
  change (1 / 4 : Coordinate) + 1 / 10 < 1
  decide

theorem oneLeftMoving_before_one (height : Coordinate) :
    (connectorMovingBox .oneLeft height).xUpper < (1 : Gaussian).re := by
  change (3 / 4 : Coordinate) + 1 / 10 < 1
  decide

theorem leftParameter_before_one (height : Coordinate) :
    (connectorParameter .left height).re < (connectorFixedBox 1).xLower := by
  change (-(1 / 4 : Coordinate)) < 1 - 1 / 16
  decide

theorem rightParameter_before_one (height : Coordinate) :
    (connectorParameter .right height).re < (connectorFixedBox 1).xLower := by
  change (1 / 4 : Coordinate) < 1 - 1 / 16
  decide

theorem zeroFixed_before_oneFixed :
    (connectorFixedBox 0).xUpper < (connectorFixedBox 1).xLower := by
  change (1 / 16 : Coordinate) < 1 - 1 / 16
  decide

theorem zeroFixed_before_oneRoot :
    (connectorFixedBox 0).xUpper < (1 : Gaussian).re := by
  change (1 / 16 : Coordinate) < 1
  decide

theorem zeroRoot_before_oneFixed :
    (0 : Gaussian).re < (connectorFixedBox 1).xLower := by
  change (0 : Coordinate) < 1 - 1 / 16
  decide

theorem leftMoving_before_zeroFixed (height : Coordinate) :
    (connectorMovingBox .left height).xUpper <
      (connectorFixedBox 0).xLower := by
  change (-(1 / 4 : Coordinate)) + 1 / 10 < -(1 / 16)
  decide

theorem zeroFixed_before_rightMoving (height : Coordinate) :
    (connectorFixedBox 0).xUpper <
      (connectorMovingBox .right height).xLower := by
  change (1 / 16 : Coordinate) < 1 / 4 - 1 / 10
  decide

theorem zeroFixed_before_oneLeftMoving (height : Coordinate) :
    (connectorFixedBox 0).xUpper <
      (connectorMovingBox .oneLeft height).xLower := by
  change (1 / 16 : Coordinate) < 3 / 4 - 1 / 10
  decide

theorem zeroFixed_before_oneRightMoving (height : Coordinate) :
    (connectorFixedBox 0).xUpper <
      (connectorMovingBox .oneRight height).xLower := by
  change (1 / 16 : Coordinate) < 5 / 4 - 1 / 10
  decide

theorem oneLeftMoving_before_oneFixed (height : Coordinate) :
    (connectorMovingBox .oneLeft height).xUpper <
      (connectorFixedBox 1).xLower := by
  change (3 / 4 : Coordinate) + 1 / 10 < 1 - 1 / 16
  decide

theorem oneFixed_before_oneRightMoving (height : Coordinate) :
    (connectorFixedBox 1).xUpper <
      (connectorMovingBox .oneRight height).xLower := by
  change (1 + 1 / 16 : Coordinate) < 5 / 4 - 1 / 10
  decide

theorem oneLeftParameter_before_one (height : Coordinate) :
    (connectorParameter .oneLeft height).re <
      (connectorFixedBox 1).xLower := by
  change (3 / 4 : Coordinate) < 1 - 1 / 16
  decide

theorem one_before_oneRightParameter (height : Coordinate) :
    (connectorFixedBox 1).xUpper <
      (connectorParameter .oneRight height).re := by
  change (1 + 1 / 16 : Coordinate) < 5 / 4
  decide

theorem leftMovingBox_before_oneFixed (height : Coordinate) :
    (connectorMovingBox .left height).xUpper <
      (connectorFixedBox 1).xLower := by
  change (-(1 / 4 : Coordinate)) + 1 / 10 < 1 - 1 / 16
  decide

theorem rightMovingBox_before_oneFixed (height : Coordinate) :
    (connectorMovingBox .right height).xUpper <
      (connectorFixedBox 1).xLower := by
  change (1 / 4 : Coordinate) + 1 / 10 < 1 - 1 / 16
  decide

theorem zero_moving_separated (side : Side) (height : Coordinate) :
    (connectorFixedBox 0).Separated (connectorMovingBox side height) := by
  cases side
  · exact Or.inr (Or.inl (leftMoving_before_zeroFixed height))
  · exact Or.inl (zeroFixed_before_rightMoving height)
  · exact Or.inl (zeroFixed_before_oneLeftMoving height)
  · exact Or.inl (zeroFixed_before_oneRightMoving height)

theorem zero_one_separated :
    (connectorFixedBox 0).Separated (connectorFixedBox 1) :=
  Or.inl zeroFixed_before_oneFixed

theorem moving_one_separated (side : Side) (height : Coordinate) :
    (connectorMovingBox side height).Separated (connectorFixedBox 1) := by
  cases side
  · exact Or.inl (leftMovingBox_before_oneFixed height)
  · exact Or.inl (rightMovingBox_before_oneFixed height)
  · exact Or.inl (oneLeftMoving_before_oneFixed height)
  · exact Or.inr (Or.inl (oneFixed_before_oneRightMoving height))

def fixedCenteredClearance (root : Gaussian) :
    BoundaryClearance
      (CCL.Riemann.ExplicitLegendreFrame.factor root)
      (connectorFixedBox root) :=
  centeredClearance root (connectorFixedBox_left root)
    (connectorFixedBox_right root) (connectorFixedBox_below root)
    (connectorFixedBox_above root)

def movingCenteredClearance (side : Side) (height : Coordinate) :
    BoundaryClearance
      (CCL.Riemann.ExplicitLegendreFrame.factor
        (connectorParameter side height))
      (connectorMovingBox side height) :=
  centeredClearance (connectorParameter side height)
    (connectorMovingBox_left side height)
    (connectorMovingBox_right side height)
    (connectorMovingBox_below side height)
    (connectorMovingBox_above side height)

def fixedZeroMovingClearance (side : Side) (height : Coordinate) :
    BoundaryClearance
      (CCL.Riemann.ExplicitLegendreFrame.factor
        (connectorParameter side height)) (connectorFixedBox 0) := by
  cases side with
  | left => exact leftClearance _ (leftParameter_left_zero height)
  | right => exact rightClearance _ (zero_left_rightParameter height)
  | oneLeft =>
      exact rightClearance _
        ((zeroFixed_before_oneLeftMoving height).trans
          (connectorMovingBox_left .oneLeft height))
  | oneRight =>
      exact rightClearance _
        ((zeroFixed_before_oneRightMoving height).trans
          (connectorMovingBox_left .oneRight height))

def movingZeroClearance (side : Side) (height : Coordinate) :
    BoundaryClearance (CCL.Riemann.ExplicitLegendreFrame.factor 0)
      (connectorMovingBox side height) := by
  cases side with
  | left => exact rightClearance 0 (leftMoving_before_zero height)
  | right => exact leftClearance 0 (zero_before_rightMoving height)
  | oneLeft =>
      exact leftClearance 0
        ((connectorFixedBox_right 0).trans
          (zeroFixed_before_oneLeftMoving height))
  | oneRight =>
      exact leftClearance 0
        ((connectorFixedBox_right 0).trans
          (zeroFixed_before_oneRightMoving height))

def movingOneClearance (side : Side) (height : Coordinate) :
    BoundaryClearance (CCL.Riemann.ExplicitLegendreFrame.factor 1)
      (connectorMovingBox side height) := by
  cases side with
  | left => exact rightClearance 1 (leftMoving_before_one height)
  | right => exact rightClearance 1 (rightMoving_before_one height)
  | oneLeft => exact rightClearance 1 (oneLeftMoving_before_one height)
  | oneRight =>
      exact leftClearance 1
        ((connectorFixedBox_right 1).trans
          (oneFixed_before_oneRightMoving height))

def fixedOneMovingClearance (side : Side) (height : Coordinate) :
    BoundaryClearance
      (CCL.Riemann.ExplicitLegendreFrame.factor
        (connectorParameter side height)) (connectorFixedBox 1) := by
  cases side with
  | left => exact leftClearance _ (leftParameter_before_one height)
  | right => exact leftClearance _ (rightParameter_before_one height)
  | oneLeft => exact leftClearance _ (oneLeftParameter_before_one height)
  | oneRight => exact rightClearance _ (one_before_oneRightParameter height)

def zeroClearance (side : Side) (height : Coordinate) :
    BoundaryClearance (factorsAt (connectorParameter side height))
      (connectorFixedBox 0) := by
  exact factorsClearance (fixedCenteredClearance 0)
    (fixedZeroMovingClearance side height)
    (rightClearance 1 zeroFixed_before_oneRoot)

def movingClearance (side : Side) (height : Coordinate) :
    BoundaryClearance (factorsAt (connectorParameter side height))
      (connectorMovingBox side height) := by
  exact factorsClearance (movingZeroClearance side height)
    (movingCenteredClearance side height) (movingOneClearance side height)

def oneClearance (side : Side) (height : Coordinate) :
    BoundaryClearance (factorsAt (connectorParameter side height))
      (connectorFixedBox 1) := by
  exact factorsClearance (leftClearance 0 zeroRoot_before_oneFixed)
    (fixedOneMovingClearance side height) (fixedCenteredClearance 1)

theorem zeroWinding (side : Side) (height : Coordinate) :
    RFAP.Winding.quadrupledBoxWinding
      (polynomial (connectorParameter side height))
      (connectorFixedBox 0) = 4 := by
  rw [polynomial_eq_factorsAt]
  apply factors_winding_of_sum (connectorFixedBox_proper 0)
    (fixedCenteredClearance 0)
    (fixedZeroMovingClearance side height)
    (rightClearance 1 zeroFixed_before_oneRoot)
  have fixed : RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor 0)
      (connectorFixedBox 0) = 4 :=
    RFAP.AffineWinding.quadrupledBoxWinding_translatedCoordinate 0
      (connectorFixedBox_left 0) (connectorFixedBox_right 0)
      (connectorFixedBox_below 0) (connectorFixedBox_above 0)
  have moving : RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor
        (connectorParameter side height)) (connectorFixedBox 0) = 0 := by
    cases side with
    | left =>
        exact factor_winding_zero_of_left _
          (connectorFixedBox_proper 0)
          (leftClearance _ (leftParameter_left_zero height))
          (leftParameter_left_zero height)
    | right =>
        exact factor_winding_zero_of_right _
          (connectorFixedBox_proper 0)
          (rightClearance _ (zero_left_rightParameter height))
          (zero_left_rightParameter height)
    | oneLeft =>
        exact factor_winding_zero_of_right _
          (connectorFixedBox_proper 0)
          (fixedZeroMovingClearance .oneLeft height)
          ((zeroFixed_before_oneLeftMoving height).trans
            (connectorMovingBox_left .oneLeft height))
    | oneRight =>
        exact factor_winding_zero_of_right _
          (connectorFixedBox_proper 0)
          (fixedZeroMovingClearance .oneRight height)
          ((zeroFixed_before_oneRightMoving height).trans
            (connectorMovingBox_left .oneRight height))
  have one : RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor 1)
      (connectorFixedBox 0) = 0 :=
    factor_winding_zero_of_right 1 (connectorFixedBox_proper 0)
      (rightClearance 1 zeroFixed_before_oneRoot)
      zeroFixed_before_oneRoot
  rw [fixed, moving, one]
  ring1

theorem movingWinding (side : Side) (height : Coordinate) :
    RFAP.Winding.quadrupledBoxWinding
      (polynomial (connectorParameter side height))
      (connectorMovingBox side height) = 4 := by
  rw [polynomial_eq_factorsAt]
  apply factors_winding_of_sum (connectorMovingBox_proper side height)
    (movingZeroClearance side height)
    (movingCenteredClearance side height)
    (movingOneClearance side height)
  have zero : RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor 0)
      (connectorMovingBox side height) = 0 := by
    cases side with
    | left =>
        exact factor_winding_zero_of_right 0
          (connectorMovingBox_proper .left height)
          (rightClearance 0 (leftMoving_before_zero height))
          (leftMoving_before_zero height)
    | right =>
        exact factor_winding_zero_of_left 0
          (connectorMovingBox_proper .right height)
          (leftClearance 0 (zero_before_rightMoving height))
          (zero_before_rightMoving height)
    | oneLeft =>
        exact factor_winding_zero_of_left 0
          (connectorMovingBox_proper .oneLeft height)
          (movingZeroClearance .oneLeft height)
          ((connectorFixedBox_right 0).trans
            (zeroFixed_before_oneLeftMoving height))
    | oneRight =>
        exact factor_winding_zero_of_left 0
          (connectorMovingBox_proper .oneRight height)
          (movingZeroClearance .oneRight height)
          ((connectorFixedBox_right 0).trans
            (zeroFixed_before_oneRightMoving height))
  have moving : RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor
        (connectorParameter side height))
      (connectorMovingBox side height) = 4 :=
    RFAP.AffineWinding.quadrupledBoxWinding_translatedCoordinate
      (connectorParameter side height)
      (connectorMovingBox_left side height)
      (connectorMovingBox_right side height)
      (connectorMovingBox_below side height)
      (connectorMovingBox_above side height)
  have one : RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor 1)
      (connectorMovingBox side height) = 0 := by
    cases side with
    | left =>
        exact factor_winding_zero_of_right 1
          (connectorMovingBox_proper .left height)
          (movingOneClearance .left height) (leftMoving_before_one height)
    | right =>
        exact factor_winding_zero_of_right 1
          (connectorMovingBox_proper .right height)
          (movingOneClearance .right height) (rightMoving_before_one height)
    | oneLeft =>
        exact factor_winding_zero_of_right 1
          (connectorMovingBox_proper .oneLeft height)
          (movingOneClearance .oneLeft height)
          (oneLeftMoving_before_one height)
    | oneRight =>
        exact factor_winding_zero_of_left 1
          (connectorMovingBox_proper .oneRight height)
          (movingOneClearance .oneRight height)
          ((connectorFixedBox_right 1).trans
            (oneFixed_before_oneRightMoving height))
  rw [zero, moving, one]
  ring1

theorem oneWinding (side : Side) (height : Coordinate) :
    RFAP.Winding.quadrupledBoxWinding
      (polynomial (connectorParameter side height))
      (connectorFixedBox 1) = 4 := by
  rw [polynomial_eq_factorsAt]
  apply factors_winding_of_sum (connectorFixedBox_proper 1)
    (leftClearance 0 zeroRoot_before_oneFixed)
    (fixedOneMovingClearance side height)
    (fixedCenteredClearance 1)
  have zero : RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor 0)
      (connectorFixedBox 1) = 0 :=
    factor_winding_zero_of_left 0 (connectorFixedBox_proper 1)
      (leftClearance 0 zeroRoot_before_oneFixed)
      zeroRoot_before_oneFixed
  have moving : RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor
        (connectorParameter side height)) (connectorFixedBox 1) = 0 := by
    cases side with
    | left =>
        exact factor_winding_zero_of_left _ (connectorFixedBox_proper 1)
          (fixedOneMovingClearance .left height)
          (leftParameter_before_one height)
    | right =>
        exact factor_winding_zero_of_left _ (connectorFixedBox_proper 1)
          (fixedOneMovingClearance .right height)
          (rightParameter_before_one height)
    | oneLeft =>
        exact factor_winding_zero_of_left _ (connectorFixedBox_proper 1)
          (fixedOneMovingClearance .oneLeft height)
          (oneLeftParameter_before_one height)
    | oneRight =>
        exact factor_winding_zero_of_right _ (connectorFixedBox_proper 1)
          (fixedOneMovingClearance .oneRight height)
          (one_before_oneRightParameter height)
  have fixed : RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor 1)
      (connectorFixedBox 1) = 4 :=
    RFAP.AffineWinding.quadrupledBoxWinding_translatedCoordinate 1
      (connectorFixedBox_left 1) (connectorFixedBox_right 1)
      (connectorFixedBox_below 1) (connectorFixedBox_above 1)
  rw [zero, moving, fixed]
  ring1

def connectorZeroOwner (side : Side) (height : Coordinate) :
    LocalOwner (polynomial (connectorParameter side height)) :=
  ownerOf (connectorFixedBox 0) (connectorFixedBox_proper 0)
    (by rw [polynomial_eq_factorsAt]; exact zeroClearance side height)
    (zeroWinding side height)

def connectorMovingOwner (side : Side) (height : Coordinate) :
    LocalOwner (polynomial (connectorParameter side height)) :=
  ownerOf (connectorMovingBox side height)
    (connectorMovingBox_proper side height)
    (by rw [polynomial_eq_factorsAt]; exact movingClearance side height)
    (movingWinding side height)

def connectorOneOwner (side : Side) (height : Coordinate) :
    LocalOwner (polynomial (connectorParameter side height)) :=
  ownerOf (connectorFixedBox 1) (connectorFixedBox_proper 1)
    (by rw [polynomial_eq_factorsAt]; exact oneClearance side height)
    (oneWinding side height)

private theorem finThree_cases (index : Fin 3) :
    index = 0 ∨ index = 1 ∨ index = 2 := by
  rcases index with ⟨value, bound⟩
  omega0

def connectorOwner (side : Side) (height : Coordinate) :
    Fin 3 -> LocalOwner (polynomial (connectorParameter side height))
  | 0 => connectorZeroOwner side height
  | 1 => connectorMovingOwner side height
  | 2 => connectorOneOwner side height

theorem connectorOwner_pairwise (side : Side) (height : Coordinate) :
    forall left right : Fin 3, left ≠ right ->
      (connectorOwner side height left).box.Separated
        (connectorOwner side height right).box := by
  intro left right different
  rcases finThree_cases left with leftZero | leftOne | leftTwo <;>
    subst left <;>
    rcases finThree_cases right with rightZero | rightOne | rightTwo <;>
    subst right
  · exact (different rfl).elim
  · exact zero_moving_separated side height
  · exact zero_one_separated
  · exact RFAP.Boxes.Box.separated_symm
      (zero_moving_separated side height)
  · exact (different rfl).elim
  · exact moving_one_separated side height
  · exact RFAP.Boxes.Box.separated_symm zero_one_separated
  · exact RFAP.Boxes.Box.separated_symm
      (moving_one_separated side height)
  · exact (different rfl).elim

def connectorOwnerFamily (side : Side) (height : Coordinate) :
    CCL.ProgressivePolynomialRoots.OwnerFamily
      (polynomial (connectorParameter side height)) 3 where
  owner := connectorOwner side height
  pairwiseSeparated := connectorOwner_pairwise side height

theorem connectorParameter_ne_zero (side : Side) (height : Coordinate) :
    connectorParameter side height ≠ 0 := by
  intro equal
  have real := congrArg (fun value : Gaussian => value.re) equal
  cases side
  · change (-(1 / 4 : Coordinate)) = 0 at real
    exact (show (-(1 / 4 : Coordinate)) ≠ 0 by decide) real
  · change (1 / 4 : Coordinate) = 0 at real
    exact (show (1 / 4 : Coordinate) ≠ 0 by decide) real
  · change (3 / 4 : Coordinate) = 0 at real
    exact (show (3 / 4 : Coordinate) ≠ 0 by decide) real
  · change (5 / 4 : Coordinate) = 0 at real
    exact (show (5 / 4 : Coordinate) ≠ 0 by decide) real

theorem connectorParameter_sub_one_ne_zero
    (side : Side) (height : Coordinate) :
    connectorParameter side height - 1 ≠ 0 := by
  intro equal
  have real := congrArg (fun value : Gaussian => value.re) equal
  cases side
  · change (-(1 / 4 : Coordinate)) - 1 = 0 at real
    exact (show (-(1 / 4 : Coordinate)) - 1 ≠ 0 by decide) real
  · change (1 / 4 : Coordinate) - 1 = 0 at real
    exact (show (1 / 4 : Coordinate) - 1 ≠ 0 by decide) real
  · change (3 / 4 : Coordinate) - 1 = 0 at real
    exact (show (3 / 4 : Coordinate) - 1 ≠ 0 by decide) real
  · change (5 / 4 : Coordinate) - 1 = 0 at real
    exact (show (5 / 4 : Coordinate) - 1 ≠ 0 by decide) real

def connectorSquarefree (side : Side) (height : Coordinate) :
    RFAP.Squarefree.SquarefreeCertificate
      (coefficientTable (connectorParameter side height)).polynomial := by
  rw [coefficientTable_polynomial]
  apply CCL.Riemann.ExplicitLegendreFrame.squarefreeAt
  exact RFAP.ConstructiveGaussian.Gaussian.mul_ne_zero_direct
    (RFAP.ConstructiveGaussian.Gaussian.pow_ne_zero_direct
      (connectorParameter side height)
      (connectorParameter_ne_zero side height) 2)
    (RFAP.ConstructiveGaussian.Gaussian.pow_ne_zero_direct
      (connectorParameter side height - 1)
      (connectorParameter_sub_one_ne_zero side height) 2)

def connectorIsolationInput (side : Side) (height : Coordinate) :
    RFAP.BoxFTA.Input
      (coefficientTable (connectorParameter side height)).polynomial where
  squarefree := connectorSquarefree side height
  degreeAtLeastTwo := by
    change 2 <= 3
    decide

def connectorChamber (side : Side) (height : Coordinate) :
    CCL.FiniteMonodromy.ChamberFrame where
  reference := coefficientTable (connectorParameter side height)
  chamber :=
    { degreeAtLeastTwo := by
        change 2 <= 3
        decide
      squarefree := connectorSquarefree side height
      owners := connectorOwnerFamily side height
      referenceSmall := coefficientTable_allowances_lt _
        (CCL.ProgressivePolynomialRoots.simpleRootChamberTarget_pos
          (coefficientTable (connectorParameter side height))
          (connectorSquarefree side height)
          (connectorOwnerFamily side height))
      referenceMaximality :=
        (CCL.BoxRFAPBridge.prove
          (connectorIsolationInput side height)).boxes.maximality }

@[simp] theorem connectorChamber_polynomial
    (side : Side) (height : Coordinate) :
    (connectorChamber side height).polynomial =
      polynomial (connectorParameter side height) := rfl

def oneRightProjectionOrder : CCL.FiniteMonodromy.FiniteBijection 3 3 where
  forward
    | 0 => 0
    | 1 => 2
    | 2 => 1
  backward
    | 0 => 0
    | 1 => 2
    | 2 => 1
  backward_forward := by
    intro position
    rcases finThree_cases position with positionZero | positionOne |
      positionTwo <;> subst position <;> rfl
  forward_backward := by
    intro position
    rcases finThree_cases position with positionZero | positionOne |
      positionTwo <;> subst position <;> rfl

def connectorProjectionOrder : Side ->
    CCL.FiniteMonodromy.FiniteBijection 3 3
  | .left => targetProjectionOrder
  | .right => CCL.FiniteMonodromy.FiniteBijection.identity 3
  | .oneLeft => CCL.FiniteMonodromy.FiniteBijection.identity 3
  | .oneRight => oneRightProjectionOrder

def connectorProjectionOwner (side : Side) (height : Coordinate)
    (position : Fin 3) :
    LocalOwner (polynomial (connectorParameter side height)) :=
  connectorOwner side height
    ((connectorProjectionOrder side).forward position)

theorem connectorProjection_xOrdered (side : Side) (height : Coordinate) :
    forall left right : Fin 3, left.val < right.val ->
      (connectorProjectionOwner side height left).box.xUpper <
        (connectorProjectionOwner side height right).box.xLower := by
  intro left right order
  cases side with
  | left =>
      rcases finThree_cases left with leftZero | leftOne | leftTwo <;>
        subst left <;>
        rcases finThree_cases right with rightZero | rightOne | rightTwo <;>
        subst right
      · omega0
      · exact leftMoving_before_zeroFixed height
      · exact leftMovingBox_before_oneFixed height
      · omega0
      · omega0
      · exact zeroFixed_before_oneFixed
      · omega0
      · omega0
      · omega0
  | right =>
      rcases finThree_cases left with leftZero | leftOne | leftTwo <;>
        subst left <;>
        rcases finThree_cases right with rightZero | rightOne | rightTwo <;>
        subst right
      · omega0
      · exact zeroFixed_before_rightMoving height
      · exact zeroFixed_before_oneFixed
      · omega0
      · omega0
      · exact rightMovingBox_before_oneFixed height
      · omega0
      · omega0
      · omega0
  | oneLeft =>
      rcases finThree_cases left with leftZero | leftOne | leftTwo <;>
        subst left <;>
        rcases finThree_cases right with rightZero | rightOne | rightTwo <;>
        subst right
      · omega0
      · exact zeroFixed_before_oneLeftMoving height
      · exact zeroFixed_before_oneFixed
      · omega0
      · omega0
      · exact oneLeftMoving_before_oneFixed height
      · omega0
      · omega0
      · omega0
  | oneRight =>
      rcases finThree_cases left with leftZero | leftOne | leftTwo <;>
        subst left <;>
        rcases finThree_cases right with rightZero | rightOne | rightTwo <;>
        subst right
      · omega0
      · exact zeroFixed_before_oneFixed
      · exact zeroFixed_before_oneRightMoving height
      · omega0
      · omega0
      · exact oneFixed_before_oneRightMoving height
      · omega0
      · omega0
      · omega0

def connectorFrame (side : Side) (height : Coordinate) :
    Frame (connectorParameter side height) where
  chamber := connectorChamber side height
  polynomial_eq := rfl
  labels := CCL.FiniteMonodromy.FiniteBijection.identity 3
  owner_contains := by
    intro label
    rcases finThree_cases label with labelZero | labelOne | labelTwo
    · subst label
      change (connectorFixedBox 0).Contains 0
      exact connectorFixedBox_contains 0
    · subst label
      exact connectorMovingBox_contains side height
    · subst label
      change (connectorFixedBox 1).Contains 1
      exact connectorFixedBox_contains 1
  projectionOrder := connectorProjectionOrder side
  projectionOwner := fun position =>
    CCL.FiniteMonodromy.castOwner
      (connectorChamber_polynomial side height).symm
      (connectorProjectionOwner side height position)
  projection_refines := by
    intro position
    change (connectorProjectionOwner side height position).box.Refines
      (connectorOwner side height
        ((connectorProjectionOrder side).forward position)).box
    exact RFAP.Boxes.Box.refines_refl _
  projection_xOrdered := connectorProjection_xOrdered side height

/-! ## One uniform descending stationary cell -/

def stepSize : Coordinate := 1 / 12

def nextHeight (height : Coordinate) : Coordinate := height - stepSize

theorem nextHeight_lt (height : Coordinate) : nextHeight height < height := by
  unfold nextHeight stepSize
  simpa using RFAP.ConstructiveFraction.sub_lt_sub_left_direct
    (by decide : (0 : Coordinate) < 1 / 12) height

def connectorMovingBridgeBox (side : Side) (height : Coordinate) : Box where
  xLower := sideReal side - 1 / 10
  xUpper := sideReal side + 1 / 10
  yLower := height - 1 / 2
  yUpper := nextHeight height + 1 / 2
  x_valid := by
    exact (connectorMovingBox_proper side height).1.le
  y_valid := by
    apply le_of_lt
    apply RFAP.ConstructiveFraction.lt_of_sub_pos_direct
    rw [show nextHeight height + 1 / 2 - (height - 1 / 2) =
        1 / 2 + 1 / 2 - stepSize by
      unfold nextHeight
      ring1]
    unfold stepSize
    decide

theorem connectorMovingBridgeBox_proper
    (side : Side) (height : Coordinate) :
    (connectorMovingBridgeBox side height).Proper := by
  constructor
  · exact (connectorMovingBox_proper side height).1
  · apply RFAP.ConstructiveFraction.lt_of_sub_pos_direct
    change 0 < nextHeight height + 1 / 2 - (height - 1 / 2)
    rw [show nextHeight height + 1 / 2 - (height - 1 / 2) =
        1 / 2 + 1 / 2 - stepSize by
      unfold nextHeight
      ring1]
    unfold stepSize
    decide

theorem connectorMovingBridgeBox_left
    (side : Side) (height : Coordinate) :
    (connectorMovingBridgeBox side height).xLower < sideReal side :=
  connectorMovingBox_left side height

theorem connectorMovingBridgeBox_right
    (side : Side) (height : Coordinate) :
    sideReal side < (connectorMovingBridgeBox side height).xUpper :=
  connectorMovingBox_right side height

theorem connectorMovingBridgeBox_below
    (side : Side) (height : Coordinate) :
    (connectorMovingBridgeBox side height).yLower < height :=
  connectorMovingBox_below side height

theorem connectorMovingBridgeBox_above
    (side : Side) (height : Coordinate) :
    height < (connectorMovingBridgeBox side height).yUpper := by
  apply RFAP.ConstructiveFraction.lt_of_sub_pos_direct
  change 0 < nextHeight height + 1 / 2 - height
  rw [show nextHeight height + 1 / 2 - height =
      1 / 2 - stepSize by
    unfold nextHeight
    ring1]
  unfold stepSize
  decide

theorem connectorMovingBridgeBox_refines_source
    (side : Side) (height : Coordinate) :
    (connectorMovingBridgeBox side height).Refines
      (connectorMovingBox side height) := by
  constructor
  · exact le_rfl
  constructor
  · exact le_rfl
  constructor
  · exact le_rfl
  · exact RFAP.ConstructiveFraction.add_le_add_right_direct
      (nextHeight_lt height).le (1 / 2)

theorem connectorMovingBridgeBox_refines_target
    (side : Side) (height : Coordinate) :
    (connectorMovingBridgeBox side height).Refines
      (connectorMovingBox side (nextHeight height)) := by
  constructor
  · exact le_rfl
  constructor
  · exact le_rfl
  constructor
  · exact RFAP.ConstructiveFraction.sub_le_sub_right_direct
      (nextHeight_lt height).le (1 / 2)
  · exact le_rfl

def bridgeMovingCenteredClearance (side : Side) (height : Coordinate) :
    BoundaryClearance
      (CCL.Riemann.ExplicitLegendreFrame.factor
        (connectorParameter side height))
      (connectorMovingBridgeBox side height) :=
  centeredClearance (connectorParameter side height)
    (connectorMovingBridgeBox_left side height)
    (connectorMovingBridgeBox_right side height)
    (connectorMovingBridgeBox_below side height)
    (connectorMovingBridgeBox_above side height)

def bridgeMovingZeroClearance (side : Side) (height : Coordinate) :
    BoundaryClearance (CCL.Riemann.ExplicitLegendreFrame.factor 0)
      (connectorMovingBridgeBox side height) := by
  cases side with
  | left => exact rightClearance 0 (by
      change (-(1 / 4 : Coordinate)) + 1 / 10 < 0
      decide)
  | right => exact leftClearance 0 (by
      change (0 : Coordinate) < 1 / 4 - 1 / 10
      decide)
  | oneLeft => exact leftClearance 0 (by
      change (0 : Coordinate) < 3 / 4 - 1 / 10
      decide)
  | oneRight => exact leftClearance 0 (by
      change (0 : Coordinate) < 5 / 4 - 1 / 10
      decide)

def bridgeMovingOneClearance (side : Side) (height : Coordinate) :
    BoundaryClearance (CCL.Riemann.ExplicitLegendreFrame.factor 1)
      (connectorMovingBridgeBox side height) := by
  cases side with
  | left => exact rightClearance 1 (by
      change (-(1 / 4 : Coordinate)) + 1 / 10 < 1
      decide)
  | right => exact rightClearance 1 (by
      change (1 / 4 : Coordinate) + 1 / 10 < 1
      decide)
  | oneLeft => exact rightClearance 1 (by
      change (3 / 4 : Coordinate) + 1 / 10 < 1
      decide)
  | oneRight => exact leftClearance 1 (by
      change (1 : Coordinate) < 5 / 4 - 1 / 10
      decide)

def bridgeMovingFactorsClearance (side : Side) (height : Coordinate) :
    BoundaryClearance (factorsAt (connectorParameter side height))
      (connectorMovingBridgeBox side height) := by
  exact factorsClearance (bridgeMovingZeroClearance side height)
    (bridgeMovingCenteredClearance side height)
    (bridgeMovingOneClearance side height)

theorem bridgeMovingWinding (side : Side) (height : Coordinate) :
    RFAP.Winding.quadrupledBoxWinding
      (polynomial (connectorParameter side height))
      (connectorMovingBridgeBox side height) = 4 := by
  rw [polynomial_eq_factorsAt]
  apply factors_winding_of_sum
    (connectorMovingBridgeBox_proper side height)
    (bridgeMovingZeroClearance side height)
    (bridgeMovingCenteredClearance side height)
    (bridgeMovingOneClearance side height)
  have zero : RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor 0)
      (connectorMovingBridgeBox side height) = 0 := by
    cases side with
    | left =>
        exact factor_winding_zero_of_right 0
          (connectorMovingBridgeBox_proper .left height)
          (rightClearance 0 (by
            change (-(1 / 4 : Coordinate)) + 1 / 10 < 0
            decide))
          (by
            change (-(1 / 4 : Coordinate)) + 1 / 10 < 0
            decide)
    | right =>
        exact factor_winding_zero_of_left 0
          (connectorMovingBridgeBox_proper .right height)
          (leftClearance 0 (by
            change (0 : Coordinate) < 1 / 4 - 1 / 10
            decide))
          (by
            change (0 : Coordinate) < 1 / 4 - 1 / 10
            decide)
    | oneLeft =>
        exact factor_winding_zero_of_left 0
          (connectorMovingBridgeBox_proper .oneLeft height)
          (bridgeMovingZeroClearance .oneLeft height)
          (by
            change (0 : Coordinate) < 3 / 4 - 1 / 10
            decide)
    | oneRight =>
        exact factor_winding_zero_of_left 0
          (connectorMovingBridgeBox_proper .oneRight height)
          (bridgeMovingZeroClearance .oneRight height)
          (by
            change (0 : Coordinate) < 5 / 4 - 1 / 10
            decide)
  have moving : RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor
        (connectorParameter side height))
      (connectorMovingBridgeBox side height) = 4 :=
    RFAP.AffineWinding.quadrupledBoxWinding_translatedCoordinate
      (connectorParameter side height)
      (connectorMovingBridgeBox_left side height)
      (connectorMovingBridgeBox_right side height)
      (connectorMovingBridgeBox_below side height)
      (connectorMovingBridgeBox_above side height)
  have one : RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor 1)
      (connectorMovingBridgeBox side height) = 0 := by
    cases side with
    | left =>
        exact factor_winding_zero_of_right 1
          (connectorMovingBridgeBox_proper .left height)
          (bridgeMovingOneClearance .left height) (by
            change (-(1 / 4 : Coordinate)) + 1 / 10 < 1
            decide)
    | right =>
        exact factor_winding_zero_of_right 1
          (connectorMovingBridgeBox_proper .right height)
          (bridgeMovingOneClearance .right height) (by
            change (1 / 4 : Coordinate) + 1 / 10 < 1
            decide)
    | oneLeft =>
        exact factor_winding_zero_of_right 1
          (connectorMovingBridgeBox_proper .oneLeft height)
          (bridgeMovingOneClearance .oneLeft height) (by
            change (3 / 4 : Coordinate) + 1 / 10 < 1
            decide)
    | oneRight =>
        exact factor_winding_zero_of_left 1
          (connectorMovingBridgeBox_proper .oneRight height)
          (bridgeMovingOneClearance .oneRight height) (by
            change (1 : Coordinate) < 5 / 4 - 1 / 10
            decide)
  rw [zero, moving, one]
  ring1

def bridgeMovingOwner (side : Side) (height : Coordinate) :
    LocalOwner (polynomial (connectorParameter side height)) :=
  ownerOf (connectorMovingBridgeBox side height)
    (connectorMovingBridgeBox_proper side height)
    (by
      rw [polynomial_eq_factorsAt]
      exact bridgeMovingFactorsClearance side height)
    (bridgeMovingWinding side height)

theorem connectorStep_displacement (side : Side) (height : Coordinate) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
      (connectorParameter side height -
        connectorParameter side (nextHeight height)) = stepSize ^ 2 := by
  cases side <;>
    simp only [connectorParameter, sideReal, gaussian, nextHeight, stepSize,
      RFAP.ConstructiveGaussian.Gaussian.normSq,
      RFAP.ConstructiveGaussian.Gaussian.sub_re,
      RFAP.ConstructiveGaussian.Gaussian.sub_im] <;>
    ring1

def zeroMovingFactorClearance (side : Side) (height : Coordinate) :
    BoundaryClearance
      (CCL.Riemann.ExplicitLegendreFrame.factor
      (connectorParameter side height)) (connectorFixedBox 0) :=
  fixedZeroMovingClearance side height

def oneMovingFactorClearance (side : Side) (height : Coordinate) :
    BoundaryClearance
      (CCL.Riemann.ExplicitLegendreFrame.factor
      (connectorParameter side height)) (connectorFixedBox 1) :=
  fixedOneMovingClearance side height

theorem zero_displacementSmall (side : Side) (height : Coordinate) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (connectorParameter side height -
          connectorParameter side (nextHeight height)) <
      (zeroMovingFactorClearance side height).bound := by
  rw [connectorStep_displacement]
  cases side
  · change stepSize ^ 2 <
      ((-(1 / 16 : Coordinate)) - (-(1 / 4 : Coordinate))) ^ 2
    unfold stepSize
    decide
  · change stepSize ^ 2 <
      ((1 / 4 : Coordinate) - 1 / 16) ^ 2
    unfold stepSize
    decide
  · change stepSize ^ 2 <
      ((3 / 4 : Coordinate) - 1 / 16) ^ 2
    unfold stepSize
    decide
  · change stepSize ^ 2 <
      ((5 / 4 : Coordinate) - 1 / 16) ^ 2
    unfold stepSize
    decide

theorem moving_displacementSmall (side : Side) (height : Coordinate) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (connectorParameter side height -
          connectorParameter side (nextHeight height)) <
      (bridgeMovingCenteredClearance side height).bound := by
  rw [connectorStep_displacement]
  change stepSize ^ 2 <
    min ((sideReal side - (sideReal side - 1 / 10)) ^ 2)
      (min ((sideReal side + 1 / 10 - sideReal side) ^ 2)
        (min ((height - (height - 1 / 2)) ^ 2)
          ((nextHeight height + 1 / 2 - height) ^ 2)))
  rw [show sideReal side - (sideReal side - 1 / 10) =
      (1 / 10 : Coordinate) by ring1,
    show sideReal side + 1 / 10 - sideReal side =
      (1 / 10 : Coordinate) by ring1,
    show height - (height - 1 / 2) = (1 / 2 : Coordinate) by ring1,
    show nextHeight height + 1 / 2 - height = 1 / 2 - stepSize by
      unfold nextHeight
      ring1]
  unfold stepSize
  decide

theorem one_displacementSmall (side : Side) (height : Coordinate) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (connectorParameter side height -
          connectorParameter side (nextHeight height)) <
      (oneMovingFactorClearance side height).bound := by
  rw [connectorStep_displacement]
  cases side
  · change stepSize ^ 2 <
      ((1 - 1 / 16 : Coordinate) - (-(1 / 4 : Coordinate))) ^ 2
    unfold stepSize
    decide
  · change stepSize ^ 2 <
      ((1 - 1 / 16 : Coordinate) - 1 / 4) ^ 2
    unfold stepSize
    decide
  · change stepSize ^ 2 <
      ((1 - 1 / 16 : Coordinate) - 3 / 4) ^ 2
    unfold stepSize
    decide
  · change stepSize ^ 2 <
      ((5 / 4 : Coordinate) - (1 + 1 / 16)) ^ 2
    unfold stepSize
    decide

def connectorPerturbation (side : Side) (height : Coordinate) :
    GaussianPolynomial :=
  perturbationAt (connectorParameter side height)
    (connectorParameter side (nextHeight height))

def connectorOrientedRouche (side : Side) (height : Coordinate)
    (owner : LocalOwner (polynomial (connectorParameter side height)))
    (dominance : RFAP.WindingHomotopy.BoundaryNormDominance
      (polynomial (connectorParameter side height))
      (connectorPerturbation side height) owner.box) :
    CCL.FiniteMonodromy.OrientedRouche
      (polynomial (connectorParameter side height))
      (polynomial (connectorParameter side (nextHeight height)))
      owner.box where
  perturbation := connectorPerturbation side height
  target_eq_add := target_eq_source_add_perturbationAt _ _
  dominance := dominance

def connectorZeroDominance (side : Side) (height : Coordinate) :
    RFAP.WindingHomotopy.BoundaryNormDominance
      (polynomial (connectorParameter side height))
      (connectorPerturbation side height)
      (connectorZeroOwner side height).box :=
  factorMoveDominanceAt _ _
    (fixedCenteredClearance 0)
    (zeroMovingFactorClearance side height)
    (rightClearance 1 zeroFixed_before_oneRoot)
    (zero_displacementSmall side height)

def connectorMovingDominance (side : Side) (height : Coordinate) :
    RFAP.WindingHomotopy.BoundaryNormDominance
      (polynomial (connectorParameter side height))
      (connectorPerturbation side height)
      (bridgeMovingOwner side height).box := by
  apply factorMoveDominanceAt _ _
    (bridgeMovingZeroClearance side height)
    (bridgeMovingCenteredClearance side height)
    (bridgeMovingOneClearance side height)
  exact moving_displacementSmall side height

def connectorOneDominance (side : Side) (height : Coordinate) :
    RFAP.WindingHomotopy.BoundaryNormDominance
      (polynomial (connectorParameter side height))
      (connectorPerturbation side height)
      (connectorOneOwner side height).box :=
  factorMoveDominanceAt _ _
    (leftClearance 0 zeroRoot_before_oneFixed)
    (oneMovingFactorClearance side height)
    (fixedCenteredClearance 1)
    (one_displacementSmall side height)

def connectorZeroBridge (side : Side) (height : Coordinate) :
    CCL.FiniteMonodromy.OwnerBridge
      (polynomial (connectorParameter side height))
      (polynomial (connectorParameter side (nextHeight height))) :=
  CCL.FiniteMonodromy.OwnerBridge.ofForward
    (connectorZeroOwner side height)
    (connectorOrientedRouche side height (connectorZeroOwner side height)
      (connectorZeroDominance side height))

def connectorMovingBridge (side : Side) (height : Coordinate) :
    CCL.FiniteMonodromy.OwnerBridge
      (polynomial (connectorParameter side height))
      (polynomial (connectorParameter side (nextHeight height))) :=
  CCL.FiniteMonodromy.OwnerBridge.ofForward
    (bridgeMovingOwner side height)
    (connectorOrientedRouche side height (bridgeMovingOwner side height)
      (connectorMovingDominance side height))

def connectorOneBridge (side : Side) (height : Coordinate) :
    CCL.FiniteMonodromy.OwnerBridge
      (polynomial (connectorParameter side height))
      (polynomial (connectorParameter side (nextHeight height))) :=
  CCL.FiniteMonodromy.OwnerBridge.ofForward
    (connectorOneOwner side height)
    (connectorOrientedRouche side height (connectorOneOwner side height)
      (connectorOneDominance side height))

def connectorBridgeAt (side : Side) (height : Coordinate) :
    Fin 3 -> CCL.FiniteMonodromy.OwnerBridge
      (polynomial (connectorParameter side height))
      (polynomial (connectorParameter side (nextHeight height)))
  | 0 => connectorZeroBridge side height
  | 1 => connectorMovingBridge side height
  | 2 => connectorOneBridge side height

def connectorChamberOverlap (side : Side) (height : Coordinate) :
    CCL.FiniteMonodromy.ChamberOverlap
      (connectorChamber side height)
      (connectorChamber side (nextHeight height)) where
  matching := CCL.FiniteMonodromy.FiniteBijection.identity 3
  bridge := connectorBridgeAt side height
  bridge_refines_left := by
    intro index
    rcases finThree_cases index with indexZero | indexOne | indexTwo
    · subst index
      exact RFAP.Boxes.Box.refines_refl _
    · subst index
      exact connectorMovingBridgeBox_refines_source side height
    · subst index
      exact RFAP.Boxes.Box.refines_refl _
  bridge_refines_right := by
    intro index
    rcases finThree_cases index with indexZero | indexOne | indexTwo
    · subst index
      exact RFAP.Boxes.Box.refines_refl _
    · subst index
      exact connectorMovingBridgeBox_refines_target side height
    · subst index
      exact RFAP.Boxes.Box.refines_refl _

def connectorProjectedOverlap (side : Side) (height : Coordinate) :
    CCL.Knot.ProjectedCrossings.ProjectedOverlap
      (connectorFrame side height).projected
      (connectorFrame side (nextHeight height)).projected :=
  .stationary (connectorChamberOverlap side height) (by
    intro position
    rfl)

@[simp] theorem connectorProjectedOverlap_word
    (side : Side) (height : Coordinate) :
    (connectorProjectedOverlap side height).word = [] := rfl

def connectorSheetBound (side : Side) (height : Coordinate) : Coordinate :=
  min (connectorZeroBridge side height).leftClearance.bound
    (min (connectorZeroBridge side height).rightClearance.bound
      (min (connectorMovingBridge side height).leftClearance.bound
        (min (connectorMovingBridge side height).rightClearance.bound
          (min (connectorOneBridge side height).leftClearance.bound
            (connectorOneBridge side height).rightClearance.bound))))

theorem connectorSheetBound_positive (side : Side) (height : Coordinate) :
    0 < connectorSheetBound side height := by
  unfold connectorSheetBound
  exact lt_min (connectorZeroBridge side height).leftClearance.positive
    (lt_min (connectorZeroBridge side height).rightClearance.positive
      (lt_min (connectorMovingBridge side height).leftClearance.positive
        (lt_min (connectorMovingBridge side height).rightClearance.positive
          (lt_min (connectorOneBridge side height).leftClearance.positive
            (connectorOneBridge side height).rightClearance.positive))))

def connectorSheetClearance (side : Side) (height : Coordinate) :
    BridgeClearance (connectorFrame side height)
      (connectorFrame side (nextHeight height))
      (connectorChamberOverlap side height) where
  bound := connectorSheetBound side height
  positive := connectorSheetBound_positive side height
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

def connectorGeometry (side : Side) (height : Coordinate) :
    AxisSegment (connectorParameter side height)
      (connectorParameter side (nextHeight height)) :=
  .vertical (sideReal side) height (nextHeight height)

def connectorGeometrySafe (side : Side) (height : Coordinate) :
    AxisSegment.Safe (connectorGeometry side height) where
  avoidsZero :=
    { bound := 1 / 16
      positive := by decide
      lower := by
        cases side
        · change (1 / 16 : Coordinate) <= (-(1 / 4) - 0) ^ 2
          decide
        · change (1 / 16 : Coordinate) <= (1 / 4 - 0) ^ 2
          decide
        · change (1 / 16 : Coordinate) <= (3 / 4 - 0) ^ 2
          decide
        · change (1 / 16 : Coordinate) <= (5 / 4 - 0) ^ 2
          decide }
  avoidsOne :=
    { bound := 1 / 16
      positive := by decide
      lower := by
        cases side
        · change (1 / 16 : Coordinate) <= (-(1 / 4) - 1) ^ 2
          decide
        · change (1 / 16 : Coordinate) <= (1 / 4 - 1) ^ 2
          decide
        · change (1 / 16 : Coordinate) <= (3 / 4 - 1) ^ 2
          decide
        · change (1 / 16 : Coordinate) <= (5 / 4 - 1) ^ 2
          decide }

/-- One Rouché-safe stationary descent by the exact rational height `1/12`. -/
def connectorSegment (side : Side) (height : Coordinate) :
    Segment (connectorFrame side height)
      (connectorFrame side (nextHeight height)) :=
  Segment.ofProjectedOverlap (connectorGeometry side height)
    (connectorGeometrySafe side height)
    (connectorProjectedOverlap side height)
    (connectorSheetClearance side height)

@[simp] theorem connectorSegment_crossings
    (side : Side) (height : Coordinate) :
    (connectorSegment side height).crossings = [] := rfl

/-! ## Stationary changes from the crossing frames -/

theorem topLeftPolynomial_eq :
    targetChamber.polynomial = (connectorChamber .left 2).polynomial := by
  rw [targetChamber_polynomial, connectorChamber_polynomial]
  rfl

theorem bottomLeftPolynomial_eq :
    (connectorChamber .left (-2)).polynomial =
      lowerLeftChamber.polynomial := by
  rw [connectorChamber_polynomial, lowerLeftChamber_polynomial]
  rfl

theorem bottomRightPolynomial_eq :
    lowerRightChamber.polynomial =
      (connectorChamber .right (-2)).polynomial := by
  rw [lowerRightChamber_polynomial, connectorChamber_polynomial]
  rfl

theorem topRightPolynomial_eq :
    (connectorChamber .right 2).polynomial = sourceChamber.polynomial := by
  rw [connectorChamber_polynomial, sourceChamber_polynomial]
  rfl

def topLeftBridge (index : Fin 3) : CCL.FiniteMonodromy.OwnerBridge
    targetChamber.polynomial (connectorChamber .left 2).polynomial :=
  @CCL.FiniteMonodromy.OwnerBridge.cast
    (connectorChamber .left 2).polynomial targetChamber.polynomial
    (connectorChamber .left 2).polynomial
    (connectorChamber .left 2).polynomial
    topLeftPolynomial_eq.symm rfl
    (CCL.FiniteMonodromy.OwnerBridge.reflexive
      (connectorOwner .left 2 index))

def bottomLeftBridge (index : Fin 3) : CCL.FiniteMonodromy.OwnerBridge
    (connectorChamber .left (-2)).polynomial
      lowerLeftChamber.polynomial :=
  @CCL.FiniteMonodromy.OwnerBridge.cast
    (connectorChamber .left (-2)).polynomial
    (connectorChamber .left (-2)).polynomial
    (connectorChamber .left (-2)).polynomial lowerLeftChamber.polynomial
    rfl bottomLeftPolynomial_eq
    (CCL.FiniteMonodromy.OwnerBridge.reflexive
      (connectorOwner .left (-2) index))

def bottomRightBridge (index : Fin 3) : CCL.FiniteMonodromy.OwnerBridge
    lowerRightChamber.polynomial
      (connectorChamber .right (-2)).polynomial :=
  @CCL.FiniteMonodromy.OwnerBridge.cast
    (connectorChamber .right (-2)).polynomial lowerRightChamber.polynomial
    (connectorChamber .right (-2)).polynomial
    (connectorChamber .right (-2)).polynomial
    bottomRightPolynomial_eq.symm rfl
    (CCL.FiniteMonodromy.OwnerBridge.reflexive
      (connectorOwner .right (-2) index))

def topRightBridge (index : Fin 3) : CCL.FiniteMonodromy.OwnerBridge
    (connectorChamber .right 2).polynomial sourceChamber.polynomial :=
  @CCL.FiniteMonodromy.OwnerBridge.cast
    (connectorChamber .right 2).polynomial
    (connectorChamber .right 2).polynomial
    (connectorChamber .right 2).polynomial sourceChamber.polynomial
    rfl topRightPolynomial_eq
    (CCL.FiniteMonodromy.OwnerBridge.reflexive
      (connectorOwner .right 2 index))

@[simp] theorem topLeftBridge_box (index : Fin 3) :
    (topLeftBridge index).box = (connectorOwner .left 2 index).box := by
  unfold topLeftBridge
  exact CCL.FiniteMonodromy.OwnerBridge.cast_box _ _ _

@[simp] theorem bottomLeftBridge_box (index : Fin 3) :
    (bottomLeftBridge index).box =
      (connectorOwner .left (-2) index).box := by
  unfold bottomLeftBridge
  exact CCL.FiniteMonodromy.OwnerBridge.cast_box _ _ _

@[simp] theorem bottomRightBridge_box (index : Fin 3) :
    (bottomRightBridge index).box =
      (connectorOwner .right (-2) index).box := by
  unfold bottomRightBridge
  exact CCL.FiniteMonodromy.OwnerBridge.cast_box _ _ _

@[simp] theorem topRightBridge_box (index : Fin 3) :
    (topRightBridge index).box = (connectorOwner .right 2 index).box := by
  unfold topRightBridge
  exact CCL.FiniteMonodromy.OwnerBridge.cast_box _ _ _

def topLeftOverlap : CCL.FiniteMonodromy.ChamberOverlap
    targetChamber (connectorChamber .left 2) where
  matching := CCL.FiniteMonodromy.FiniteBijection.identity 3
  bridge := topLeftBridge
  bridge_refines_left := by
    intro index
    rcases finThree_cases index with indexZero | indexOne | indexTwo
    · subst index
      rw [topLeftBridge_box]
      exact RFAP.Boxes.Box.refines_refl _
    · subst index
      rw [topLeftBridge_box]
      exact ⟨by decide, by decide, by decide, by decide⟩
    · subst index
      rw [topLeftBridge_box]
      exact RFAP.Boxes.Box.refines_refl _
  bridge_refines_right := by
    intro index
    rw [topLeftBridge_box]
    exact RFAP.Boxes.Box.refines_refl _

def bottomLeftOverlap : CCL.FiniteMonodromy.ChamberOverlap
    (connectorChamber .left (-2)) lowerLeftChamber where
  matching := CCL.FiniteMonodromy.FiniteBijection.identity 3
  bridge := bottomLeftBridge
  bridge_refines_left := by
    intro index
    rw [bottomLeftBridge_box]
    exact RFAP.Boxes.Box.refines_refl _
  bridge_refines_right := by
    intro index
    rcases finThree_cases index with indexZero | indexOne | indexTwo
    · subst index
      rw [bottomLeftBridge_box]
      exact RFAP.Boxes.Box.refines_refl _
    · subst index
      rw [bottomLeftBridge_box]
      exact ⟨by decide, by decide, by decide, by decide⟩
    · subst index
      rw [bottomLeftBridge_box]
      exact RFAP.Boxes.Box.refines_refl _

def bottomRightOverlap : CCL.FiniteMonodromy.ChamberOverlap
    lowerRightChamber (connectorChamber .right (-2)) where
  matching := CCL.FiniteMonodromy.FiniteBijection.identity 3
  bridge := bottomRightBridge
  bridge_refines_left := by
    intro index
    rcases finThree_cases index with indexZero | indexOne | indexTwo
    · subst index
      rw [bottomRightBridge_box]
      exact RFAP.Boxes.Box.refines_refl _
    · subst index
      rw [bottomRightBridge_box]
      exact ⟨by decide, by decide, by decide, by decide⟩
    · subst index
      rw [bottomRightBridge_box]
      exact RFAP.Boxes.Box.refines_refl _
  bridge_refines_right := by
    intro index
    rw [bottomRightBridge_box]
    exact RFAP.Boxes.Box.refines_refl _

def topRightOverlap : CCL.FiniteMonodromy.ChamberOverlap
    (connectorChamber .right 2) sourceChamber where
  matching := CCL.FiniteMonodromy.FiniteBijection.identity 3
  bridge := topRightBridge
  bridge_refines_left := by
    intro index
    rw [topRightBridge_box]
    exact RFAP.Boxes.Box.refines_refl _
  bridge_refines_right := by
    intro index
    rcases finThree_cases index with indexZero | indexOne | indexTwo
    · subst index
      rw [topRightBridge_box]
      exact RFAP.Boxes.Box.refines_refl _
    · subst index
      rw [topRightBridge_box]
      exact ⟨by decide, by decide, by decide, by decide⟩
    · subst index
      rw [topRightBridge_box]
      exact RFAP.Boxes.Box.refines_refl _

@[simp] theorem topLeftOverlap_bridge (index : Fin 3) :
    topLeftOverlap.bridge index = topLeftBridge index := rfl

@[simp] theorem bottomLeftOverlap_bridge (index : Fin 3) :
    bottomLeftOverlap.bridge index = bottomLeftBridge index := rfl

@[simp] theorem bottomRightOverlap_bridge (index : Fin 3) :
    bottomRightOverlap.bridge index = bottomRightBridge index := rfl

@[simp] theorem topRightOverlap_bridge (index : Fin 3) :
    topRightOverlap.bridge index = topRightBridge index := rfl

@[simp] theorem topLeftBridge_leftClearance_bound (index : Fin 3) :
    (topLeftBridge index).leftClearance.bound =
      (connectorOwner .left 2 index).clearance.bound := by
  unfold topLeftBridge
  rw [CCL.FiniteMonodromy.OwnerBridge.cast_leftClearance_bound]
  rfl

@[simp] theorem topLeftBridge_rightClearance_bound (index : Fin 3) :
    (topLeftBridge index).rightClearance.bound =
      (connectorOwner .left 2 index).clearance.bound := by
  unfold topLeftBridge
  rw [CCL.FiniteMonodromy.OwnerBridge.cast_rightClearance_bound]
  rfl

@[simp] theorem topRightBridge_leftClearance_bound (index : Fin 3) :
    (topRightBridge index).leftClearance.bound =
      (connectorOwner .right 2 index).clearance.bound := by
  unfold topRightBridge
  rw [CCL.FiniteMonodromy.OwnerBridge.cast_leftClearance_bound]
  rfl

@[simp] theorem topRightBridge_rightClearance_bound (index : Fin 3) :
    (topRightBridge index).rightClearance.bound =
      (connectorOwner .right 2 index).clearance.bound := by
  unfold topRightBridge
  rw [CCL.FiniteMonodromy.OwnerBridge.cast_rightClearance_bound]
  rfl

@[simp] theorem topLeftOverlap_leftClearance_bound (index : Fin 3) :
    (topLeftOverlap.bridge index).leftClearance.bound =
      (connectorOwner .left 2 index).clearance.bound := by
  rw [topLeftOverlap_bridge, topLeftBridge_leftClearance_bound]

@[simp] theorem topLeftOverlap_rightClearance_bound (index : Fin 3) :
    (topLeftOverlap.bridge index).rightClearance.bound =
      (connectorOwner .left 2 index).clearance.bound := by
  rw [topLeftOverlap_bridge, topLeftBridge_rightClearance_bound]

@[simp] theorem bottomLeftOverlap_leftClearance_bound (index : Fin 3) :
    (bottomLeftOverlap.bridge index).leftClearance.bound =
      (connectorOwner .left (-2) index).clearance.bound := by
  change (bottomLeftBridge index).leftClearance.bound = _
  unfold bottomLeftBridge
  rw [CCL.FiniteMonodromy.OwnerBridge.cast_leftClearance_bound]
  rfl

@[simp] theorem bottomLeftOverlap_rightClearance_bound (index : Fin 3) :
    (bottomLeftOverlap.bridge index).rightClearance.bound =
      (connectorOwner .left (-2) index).clearance.bound := by
  change (bottomLeftBridge index).rightClearance.bound = _
  unfold bottomLeftBridge
  rw [CCL.FiniteMonodromy.OwnerBridge.cast_rightClearance_bound]
  rfl

@[simp] theorem bottomRightOverlap_leftClearance_bound (index : Fin 3) :
    (bottomRightOverlap.bridge index).leftClearance.bound =
      (connectorOwner .right (-2) index).clearance.bound := by
  change (bottomRightBridge index).leftClearance.bound = _
  unfold bottomRightBridge
  rw [CCL.FiniteMonodromy.OwnerBridge.cast_leftClearance_bound]
  rfl

@[simp] theorem bottomRightOverlap_rightClearance_bound (index : Fin 3) :
    (bottomRightOverlap.bridge index).rightClearance.bound =
      (connectorOwner .right (-2) index).clearance.bound := by
  change (bottomRightBridge index).rightClearance.bound = _
  unfold bottomRightBridge
  rw [CCL.FiniteMonodromy.OwnerBridge.cast_rightClearance_bound]
  rfl

@[simp] theorem topRightOverlap_leftClearance_bound (index : Fin 3) :
    (topRightOverlap.bridge index).leftClearance.bound =
      (connectorOwner .right 2 index).clearance.bound := by
  rw [topRightOverlap_bridge, topRightBridge_leftClearance_bound]

@[simp] theorem topRightOverlap_rightClearance_bound (index : Fin 3) :
    (topRightOverlap.bridge index).rightClearance.bound =
      (connectorOwner .right 2 index).clearance.bound := by
  rw [topRightOverlap_bridge, topRightBridge_rightClearance_bound]

def topLeftProjectedOverlap : CCL.Knot.ProjectedCrossings.ProjectedOverlap
    targetFrame.projected (connectorFrame .left 2).projected :=
  .stationary topLeftOverlap (by intro position; rfl)

def bottomLeftProjectedOverlap :
    CCL.Knot.ProjectedCrossings.ProjectedOverlap
      (connectorFrame .left (-2)).projected lowerLeftFrame.projected :=
  .stationary bottomLeftOverlap (by intro position; rfl)

def bottomRightProjectedOverlap :
    CCL.Knot.ProjectedCrossings.ProjectedOverlap
      lowerRightFrame.projected (connectorFrame .right (-2)).projected :=
  .stationary bottomRightOverlap (by intro position; rfl)

def topRightProjectedOverlap : CCL.Knot.ProjectedCrossings.ProjectedOverlap
    (connectorFrame .right 2).projected sourceFrame.projected :=
  .stationary topRightOverlap (by intro position; rfl)

def transitionSheetBound (side : Side) (height : Coordinate) : Coordinate :=
  min (connectorZeroOwner side height).clearance.bound
    (min (connectorMovingOwner side height).clearance.bound
      (connectorOneOwner side height).clearance.bound)

theorem transitionSheetBound_positive (side : Side) (height : Coordinate) :
    0 < transitionSheetBound side height := by
  unfold transitionSheetBound
  exact lt_min (connectorZeroOwner side height).clearance.positive
    (lt_min (connectorMovingOwner side height).clearance.positive
      (connectorOneOwner side height).clearance.positive)

theorem transitionSheetBound_le (side : Side) (height : Coordinate)
    (index : Fin 3) :
    transitionSheetBound side height <=
      (connectorOwner side height index).clearance.bound := by
  rcases finThree_cases index with indexZero | indexOne | indexTwo
  · subst index
    exact min_le_left _ _
  · subst index
    exact (min_le_right _ _).trans (min_le_left _ _)
  · subst index
    exact (min_le_right _ _).trans (min_le_right _ _)

def topLeftSheetClearance :
    BridgeClearance targetFrame (connectorFrame .left 2)
      topLeftOverlap where
  bound := transitionSheetBound .left 2
  positive := transitionSheetBound_positive .left 2
  leftLower := by
    intro index
    rw [topLeftOverlap_leftClearance_bound]
    exact transitionSheetBound_le .left 2 index
  rightLower := by
    intro index
    rw [topLeftOverlap_rightClearance_bound]
    exact transitionSheetBound_le .left 2 index

def bottomLeftSheetClearance :
    BridgeClearance (connectorFrame .left (-2)) lowerLeftFrame
      bottomLeftOverlap where
  bound := transitionSheetBound .left (-2)
  positive := transitionSheetBound_positive .left (-2)
  leftLower := by
    intro index
    rw [bottomLeftOverlap_leftClearance_bound]
    exact transitionSheetBound_le .left (-2) index
  rightLower := by
    intro index
    rw [bottomLeftOverlap_rightClearance_bound]
    exact transitionSheetBound_le .left (-2) index

def bottomRightSheetClearance :
    BridgeClearance lowerRightFrame (connectorFrame .right (-2))
      bottomRightOverlap where
  bound := transitionSheetBound .right (-2)
  positive := transitionSheetBound_positive .right (-2)
  leftLower := by
    intro index
    rw [bottomRightOverlap_leftClearance_bound]
    exact transitionSheetBound_le .right (-2) index
  rightLower := by
    intro index
    rw [bottomRightOverlap_rightClearance_bound]
    exact transitionSheetBound_le .right (-2) index

def topRightSheetClearance :
    BridgeClearance (connectorFrame .right 2) sourceFrame
      topRightOverlap where
  bound := transitionSheetBound .right 2
  positive := transitionSheetBound_positive .right 2
  leftLower := by
    intro index
    rw [topRightOverlap_leftClearance_bound]
    exact transitionSheetBound_le .right 2 index
  rightLower := by
    intro index
    rw [topRightOverlap_rightClearance_bound]
    exact transitionSheetBound_le .right 2 index

def stationaryGeometry (side : Side) (height : Coordinate) :
    AxisSegment (connectorParameter side height)
      (connectorParameter side height) :=
  .vertical (sideReal side) height height

def stationaryGeometrySafe (side : Side) (height : Coordinate) :
    AxisSegment.Safe (stationaryGeometry side height) where
  avoidsZero :=
    { bound := 1 / 16
      positive := by decide
      lower := by
        cases side
        · change (1 / 16 : Coordinate) <= (-(1 / 4) - 0) ^ 2
          decide
        · change (1 / 16 : Coordinate) <= (1 / 4 - 0) ^ 2
          decide
        · change (1 / 16 : Coordinate) <= (3 / 4 - 0) ^ 2
          decide
        · change (1 / 16 : Coordinate) <= (5 / 4 - 0) ^ 2
          decide }
  avoidsOne :=
    { bound := 1 / 16
      positive := by decide
      lower := by
        cases side
        · change (1 / 16 : Coordinate) <= (-(1 / 4) - 1) ^ 2
          decide
        · change (1 / 16 : Coordinate) <= (1 / 4 - 1) ^ 2
          decide
        · change (1 / 16 : Coordinate) <= (3 / 4 - 1) ^ 2
          decide
        · change (1 / 16 : Coordinate) <= (5 / 4 - 1) ^ 2
          decide }

def topLeftTransition : Segment targetFrame (connectorFrame .left 2) :=
  Segment.ofProjectedOverlap (stationaryGeometry .left 2)
    (stationaryGeometrySafe .left 2) topLeftProjectedOverlap
    topLeftSheetClearance

def bottomLeftTransition :
    Segment (connectorFrame .left (-2)) lowerLeftFrame :=
  Segment.ofProjectedOverlap (stationaryGeometry .left (-2))
    (stationaryGeometrySafe .left (-2)) bottomLeftProjectedOverlap
    bottomLeftSheetClearance

def bottomRightTransition :
    Segment lowerRightFrame (connectorFrame .right (-2)) :=
  Segment.ofProjectedOverlap (stationaryGeometry .right (-2))
    (stationaryGeometrySafe .right (-2)) bottomRightProjectedOverlap
    bottomRightSheetClearance

def topRightTransition : Segment (connectorFrame .right 2) sourceFrame :=
  Segment.ofProjectedOverlap (stationaryGeometry .right 2)
    (stationaryGeometrySafe .right 2) topRightProjectedOverlap
    topRightSheetClearance

@[simp] theorem topLeftTransition_crossings :
    topLeftTransition.crossings = [] := rfl

@[simp] theorem bottomLeftTransition_crossings :
    bottomLeftTransition.crossings = [] := rfl

@[simp] theorem bottomRightTransition_crossings :
    bottomRightTransition.crossings = [] := rfl

@[simp] theorem topRightTransition_crossings :
    topRightTransition.crossings = [] := rfl

/-! ## Forty-eight-cell side paths -/

def descendHeight : Nat -> Coordinate -> Coordinate
  | 0, height => height
  | count + 1, height => descendHeight count (nextHeight height)

def descendingPath (side : Side) :
    (count : Nat) -> (height : Coordinate) ->
      Path (connectorFrame side height)
        (connectorFrame side (descendHeight count height))
  | 0, height => .nil (connectorFrame side height)
  | count + 1, height =>
      .cons (connectorSegment side height)
        (descendingPath side count (nextHeight height))

@[simp] theorem descendingPath_stepCount
    (side : Side) (count : Nat) (height : Coordinate) :
    (descendingPath side count height).stepCount = count := by
  induction count generalizing height with
  | zero => rfl
  | succ count inductionHypothesis =>
      simp only [descendingPath, Path.stepCount]
      exact congrArg (fun value : Nat => value + 1)
        (inductionHypothesis (nextHeight height))

@[simp] theorem descendingPath_word
    (side : Side) (count : Nat) (height : Coordinate) :
    (descendingPath side count height).word = [] := by
  induction count generalizing height with
  | zero => rfl
  | succ count inductionHypothesis =>
      change (descendingPath side count (nextHeight height)).word = []
      exact inductionHypothesis (nextHeight height)

theorem descendHeight_eq (count : Nat) (height : Coordinate) :
    descendHeight count height =
      height - (count : Coordinate) * stepSize := by
  induction count generalizing height with
  | zero =>
      simp only [descendHeight, Nat.cast_zero, zero_mul, sub_zero]
  | succ count inductionHypothesis =>
      rw [descendHeight, inductionHypothesis]
      unfold nextHeight
      rw [Nat.cast_succ]
      ring1

theorem descendHeight_fortyEight : descendHeight 48 2 = -2 := by
  rw [descendHeight_eq]
  unfold stepSize
  have castFortyEight : ((48 : Nat) : Coordinate) =
      (4 : Coordinate) * (12 : Coordinate) := by
    rw [show (48 : Nat) = 4 * 12 by decide, Nat.cast_mul]
    decide
  rw [castFortyEight]
  calc
    (2 : Coordinate) - (4 * 12) * (1 / 12) =
        (2 : Coordinate) - 4 * (12 * (1 / 12)) := by ring1
    _ = (2 : Coordinate) - 4 * 1 := by
      rw [show (12 : Coordinate) * (1 / 12) = 1 by decide]
    _ = (-(2 : Coordinate)) := by ring1

def castConnectorPathFinish {start : Gaussian} {left : Frame start}
    {side : Side} {source target : Coordinate}
    (same : source = target)
    (path : Path left (connectorFrame side source)) :
    Path left (connectorFrame side target) := by
  subst target
  exact path

@[simp] theorem castConnectorPathFinish_stepCount
    {start : Gaussian} {left : Frame start}
    {side : Side} {source target : Coordinate}
    (same : source = target)
    (path : Path left (connectorFrame side source)) :
    (castConnectorPathFinish same path).stepCount = path.stepCount := by
  subst target
  rfl

@[simp] theorem castConnectorPathFinish_word
    {start : Gaussian} {left : Frame start}
    {side : Side} {source target : Coordinate}
    (same : source = target)
    (path : Path left (connectorFrame side source)) :
    (castConnectorPathFinish same path).word = path.word := by
  subst target
  rfl

/-- The complete stationary descent on either side of the zero rectangle. -/
def sideDescent (side : Side) :
    Path (connectorFrame side 2) (connectorFrame side (-2)) :=
  castConnectorPathFinish descendHeight_fortyEight
    (descendingPath side 48 2)

@[simp] theorem sideDescent_stepCount (side : Side) :
    (sideDescent side).stepCount = 48 := by
  rw [sideDescent, castConnectorPathFinish_stepCount,
    descendingPath_stepCount]

@[simp] theorem sideDescent_word (side : Side) :
    (sideDescent side).word = [] := by
  rw [sideDescent, castConnectorPathFinish_word,
    descendingPath_word]

/-- The right side is traversed upward by reversing the certified descent. -/
def sideAscent (side : Side) :
    Path (connectorFrame side (-2)) (connectorFrame side 2) :=
  (sideDescent side).reverse

@[simp] theorem sideAscent_word (side : Side) :
    (sideAscent side).word = [] := by
  rw [sideAscent, Path.word_reverse, sideDescent_word]
  rfl

/-! ## The closed standard loop around zero -/

def leftConnector : Path targetFrame lowerLeftFrame :=
  .cons topLeftTransition
    ((sideDescent .left).append
      (.cons bottomLeftTransition (.nil lowerLeftFrame)))

@[simp] theorem leftConnector_word : leftConnector.word = [] := by
  rw [leftConnector]
  simp only [Path.word, topLeftTransition_crossings,
    Path.word_append, sideDescent_word, bottomLeftTransition_crossings,
    List.append_nil]

def rightConnector : Path lowerRightFrame sourceFrame :=
  .cons bottomRightTransition
    ((sideAscent .right).append
      (.cons topRightTransition (.nil sourceFrame)))

@[simp] theorem rightConnector_word : rightConnector.word = [] := by
  rw [rightConnector]
  simp only [Path.word, bottomRightTransition_crossings,
    Path.word_append, sideAscent_word, topRightTransition_crossings,
    List.append_nil]

/-- A concrete closed rational Legendre path based at `1/4 + 2i`.  Its only
nonstationary cells are the two certified positive crossings. -/
def zeroLoopPath : Path sourceFrame sourceFrame :=
  path.append
    (leftConnector.append (lowerPath.append rightConnector))

@[simp] theorem zeroLoopPath_word : zeroLoopPath.word =
    CCL.Riemann.LegendreMonodromy.zeroBraid := by
  rw [zeroLoopPath, Path.word_append, Path.word_append, Path.word_append,
    path_word, leftConnector_word, lowerPath_word, rightConnector_word]
  rfl

theorem zeroLoopWord : CCL.Knot.ArtinRelations.Equivalent zeroLoopPath.word
    CCL.Riemann.LegendreMonodromy.zeroBraid := by
  rw [zeroLoopPath_word]
  exact .refl _

end CCL.Riemann.ExplicitLegendreConnectors
