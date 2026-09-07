import CCL.Riemann.ExplicitLegendreConnectors
import CCL.Riemann.LegendreMonodromy

/-!
# One explicit rational Legendre loop around one

This module constructs the second standard Legendre loop at the same rational
base frame as the explicit loop around zero.  Its two horizontal crossings
move the Legendre root past the fixed root at one; the vertical pieces reuse
the uniform finite connector subdivision.
-/

namespace CCL.Riemann.ExplicitLegendreOneLoop

open CCL.Riemann.LegendrePaths
open CCL.Riemann.ExplicitLegendreSegment
open CCL.Riemann.ExplicitLegendreConnectors

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial :=
  RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Box := RFAP.Boxes.Box
abbrev LocalOwner := CCL.ProgressivePolynomialRoots.LocalOwner
abbrev BoundaryClearance := RFAP.BoxClearance.BoundaryClearance

inductive Level
  | upper
  | lower
deriving DecidableEq, Repr

inductive Position
  | left
  | right
deriving DecidableEq, Repr

def levelHeight : Level -> Coordinate
  | .upper => 2
  | .lower => -2

def connectorSide : Position -> Side
  | .left => .oneLeft
  | .right => .oneRight

def crossingParameter (level : Level) (position : Position) : Gaussian :=
  connectorParameter (connectorSide position) (levelHeight level)

@[simp] theorem crossingParameter_re (level : Level) (position : Position) :
    (crossingParameter level position).re = sideReal (connectorSide position) :=
  rfl

@[simp] theorem crossingParameter_im (level : Level) (position : Position) :
    (crossingParameter level position).im = levelHeight level := rfl

/-! ## Broad crossing owners -/

/-- A single rational box contains both moving-root endpoints of either
horizontal crossing.  Its asymmetric width also contains the bridge used by
the common-base approach from `1/4 + 2i`. -/
def crossingMovingBox (level : Level) : Box where
  xLower := -1
  xUpper := 2
  yLower := levelHeight level - 1
  yUpper := levelHeight level + 1
  x_valid := by decide
  y_valid := by cases level <;> decide

theorem crossingMovingBox_proper (level : Level) :
    (crossingMovingBox level).Proper := by
  constructor
  · change (-1 : Coordinate) < 2
    decide
  · cases level <;> decide

theorem crossingMovingBox_contains (level : Level) (position : Position) :
    (crossingMovingBox level).Contains
      (crossingParameter level position) := by
  cases level <;> cases position <;> decide

def crossingMovingCenteredClearance (level : Level) (position : Position) :
    BoundaryClearance
      (CCL.Riemann.ExplicitLegendreFrame.factor
        (crossingParameter level position)) (crossingMovingBox level) :=
  centeredClearance (crossingParameter level position)
    (by cases level <;> cases position <;> decide)
    (by cases level <;> cases position <;> decide)
    (by cases level <;> cases position <;> decide)
    (by cases level <;> cases position <;> decide)

def movingOnZeroBoxClearance (level : Level) (position : Position) :
    BoundaryClearance
      (CCL.Riemann.ExplicitLegendreFrame.factor
        (crossingParameter level position)) (connectorFixedBox 0) := by
  cases level with
  | upper => exact aboveClearance _ (by cases position <;> decide)
  | lower => exact belowClearance _ (by cases position <;> decide)

def movingOnOneBoxClearance (level : Level) (position : Position) :
    BoundaryClearance
      (CCL.Riemann.ExplicitLegendreFrame.factor
        (crossingParameter level position)) (connectorFixedBox 1) := by
  cases level with
  | upper => exact aboveClearance _ (by cases position <;> decide)
  | lower => exact belowClearance _ (by cases position <;> decide)

def zeroOnMovingBoxClearance (level : Level) :
    BoundaryClearance (CCL.Riemann.ExplicitLegendreFrame.factor 0)
      (crossingMovingBox level) := by
  cases level with
  | upper => exact belowClearance 0 (by decide)
  | lower => exact aboveClearance 0 (by decide)

def oneOnMovingBoxClearance (level : Level) :
    BoundaryClearance (CCL.Riemann.ExplicitLegendreFrame.factor 1)
      (crossingMovingBox level) := by
  cases level with
  | upper => exact belowClearance 1 (by decide)
  | lower => exact aboveClearance 1 (by decide)

/-- The vertical versions of the finite half-plane winding calculation used
by the crossing frames. -/
theorem factor_winding_zero_of_below (root : Gaussian) {box : Box}
    (proper : box.Proper)
    (clearance : BoundaryClearance
      (CCL.Riemann.ExplicitLegendreFrame.factor root) box)
    (below : root.im < box.yLower) :
    RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor root) box = 0 := by
  let minusI : Gaussian := gaussian 0 (-1)
  let constant := RFAP.GlobalWinding.gaussianConstant minusI
  have minusINonzero : minusI ≠ 0 := by decide
  let constantClearance :=
    RFAP.GlobalWinding.gaussianConstant_boundaryClearance minusINonzero box
  have productZero : RFAP.Winding.quadrupledBoxWinding
      (constant * CCL.Riemann.ExplicitLegendreFrame.factor root) box = 0 := by
    apply RFAP.HalfPlane.quadrupledBoxWinding_eq_zero_of_positive_real
      (constant * CCL.Riemann.ExplicitLegendreFrame.factor root) box proper
      (RFAP.BoxClearance.BoundaryClearance.mul constantClearance clearance)
    intro point boundary
    rw [RFAP.ComputablePolynomial.DensePolynomial.eval_mul,
      RFAP.GlobalWinding.gaussianConstant_eval,
      CCL.Riemann.ExplicitLegendreFrame.factor,
      RFAP.AffineWinding.translatedCoordinate_eval]
    change 0 < (minusI * (point - root)).re
    dsimp only [minusI, gaussian,
      RFAP.ConstructiveGaussian.Gaussian.mul_re,
      RFAP.ConstructiveGaussian.Gaussian.sub_re,
      RFAP.ConstructiveGaussian.Gaussian.sub_im]
    rw [show (0 : Coordinate) * (point.re - root.re) -
        (-1) * (point.im - root.im) = point.im - root.im by ring1]
    exact RFAP.ConstructiveFraction.sub_pos_direct
      (below.trans_le boundary.1.2.2.1)
  have productFormula :=
    RFAP.WindingProduct.quadrupledBoxWinding_mul_of_boundaryClearances
      constant (CCL.Riemann.ExplicitLegendreFrame.factor root) box proper
      constantClearance clearance
  have constantZero : RFAP.Winding.quadrupledBoxWinding constant box = 0 :=
    RFAP.GlobalWinding.quadrupledBoxWinding_gaussianConstant minusINonzero box
  rw [productZero, constantZero] at productFormula
  simpa only [Int.zero_add] using productFormula.symm

theorem factor_winding_zero_of_above (root : Gaussian) {box : Box}
    (proper : box.Proper)
    (clearance : BoundaryClearance
      (CCL.Riemann.ExplicitLegendreFrame.factor root) box)
    (above : box.yUpper < root.im) :
    RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor root) box = 0 := by
  let i : Gaussian := gaussian 0 1
  let constant := RFAP.GlobalWinding.gaussianConstant i
  have iNonzero : i ≠ 0 := by decide
  let constantClearance :=
    RFAP.GlobalWinding.gaussianConstant_boundaryClearance iNonzero box
  have productZero : RFAP.Winding.quadrupledBoxWinding
      (constant * CCL.Riemann.ExplicitLegendreFrame.factor root) box = 0 := by
    apply RFAP.HalfPlane.quadrupledBoxWinding_eq_zero_of_positive_real
      (constant * CCL.Riemann.ExplicitLegendreFrame.factor root) box proper
      (RFAP.BoxClearance.BoundaryClearance.mul constantClearance clearance)
    intro point boundary
    rw [RFAP.ComputablePolynomial.DensePolynomial.eval_mul,
      RFAP.GlobalWinding.gaussianConstant_eval,
      CCL.Riemann.ExplicitLegendreFrame.factor,
      RFAP.AffineWinding.translatedCoordinate_eval]
    change 0 < (i * (point - root)).re
    dsimp only [i, gaussian,
      RFAP.ConstructiveGaussian.Gaussian.mul_re,
      RFAP.ConstructiveGaussian.Gaussian.sub_re,
      RFAP.ConstructiveGaussian.Gaussian.sub_im]
    rw [show (0 : Coordinate) * (point.re - root.re) -
        1 * (point.im - root.im) = root.im - point.im by ring1]
    exact RFAP.ConstructiveFraction.sub_pos_direct
      (boundary.1.2.2.2.trans_lt above)
  have productFormula :=
    RFAP.WindingProduct.quadrupledBoxWinding_mul_of_boundaryClearances
      constant (CCL.Riemann.ExplicitLegendreFrame.factor root) box proper
      constantClearance clearance
  have constantZero : RFAP.Winding.quadrupledBoxWinding constant box = 0 :=
    RFAP.GlobalWinding.quadrupledBoxWinding_gaussianConstant iNonzero box
  rw [productZero, constantZero] at productFormula
  simpa only [Int.zero_add] using productFormula.symm

def crossingZeroFactorsClearance (level : Level) (position : Position) :
    BoundaryClearance (factorsAt (crossingParameter level position))
      (connectorFixedBox 0) :=
  factorsClearance (fixedCenteredClearance 0)
    (movingOnZeroBoxClearance level position)
    (rightClearance 1 zeroFixed_before_oneRoot)

def crossingMovingFactorsClearance (level : Level) (position : Position) :
    BoundaryClearance (factorsAt (crossingParameter level position))
      (crossingMovingBox level) :=
  factorsClearance (zeroOnMovingBoxClearance level)
    (crossingMovingCenteredClearance level position)
    (oneOnMovingBoxClearance level)

def crossingOneFactorsClearance (level : Level) (position : Position) :
    BoundaryClearance (factorsAt (crossingParameter level position))
      (connectorFixedBox 1) :=
  factorsClearance (leftClearance 0 zeroRoot_before_oneFixed)
    (movingOnOneBoxClearance level position) (fixedCenteredClearance 1)

theorem crossingZeroWinding (level : Level) (position : Position) :
    RFAP.Winding.quadrupledBoxWinding
      (polynomial (crossingParameter level position))
      (connectorFixedBox 0) = 4 := by
  rw [polynomial_eq_factorsAt]
  apply factors_winding_of_sum (connectorFixedBox_proper 0)
    (fixedCenteredClearance 0) (movingOnZeroBoxClearance level position)
    (rightClearance 1 zeroFixed_before_oneRoot)
  have zero : RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor 0)
      (connectorFixedBox 0) = 4 :=
    RFAP.AffineWinding.quadrupledBoxWinding_translatedCoordinate 0
      (connectorFixedBox_left 0) (connectorFixedBox_right 0)
      (connectorFixedBox_below 0) (connectorFixedBox_above 0)
  have moving : RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor
        (crossingParameter level position)) (connectorFixedBox 0) = 0 := by
    cases level with
    | upper =>
        exact factor_winding_zero_of_above _ (connectorFixedBox_proper 0)
          (movingOnZeroBoxClearance .upper position)
          (by cases position <;> decide)
    | lower =>
        exact factor_winding_zero_of_below _ (connectorFixedBox_proper 0)
          (movingOnZeroBoxClearance .lower position)
          (by cases position <;> decide)
  have one : RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor 1)
      (connectorFixedBox 0) = 0 :=
    factor_winding_zero_of_right 1 (connectorFixedBox_proper 0)
      (rightClearance 1 zeroFixed_before_oneRoot) zeroFixed_before_oneRoot
  rw [zero, moving, one]
  ring1

theorem crossingMovingWinding (level : Level) (position : Position) :
    RFAP.Winding.quadrupledBoxWinding
      (polynomial (crossingParameter level position))
      (crossingMovingBox level) = 4 := by
  rw [polynomial_eq_factorsAt]
  apply factors_winding_of_sum (crossingMovingBox_proper level)
    (zeroOnMovingBoxClearance level)
    (crossingMovingCenteredClearance level position)
    (oneOnMovingBoxClearance level)
  have zero : RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor 0)
      (crossingMovingBox level) = 0 := by
    cases level with
    | upper =>
        exact factor_winding_zero_of_below 0
          (crossingMovingBox_proper .upper) (zeroOnMovingBoxClearance .upper)
          (by decide)
    | lower =>
        exact factor_winding_zero_of_above 0
          (crossingMovingBox_proper .lower) (zeroOnMovingBoxClearance .lower)
          (by decide)
  have moving : RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor
        (crossingParameter level position)) (crossingMovingBox level) = 4 :=
    RFAP.AffineWinding.quadrupledBoxWinding_translatedCoordinate _
      (by cases level <;> cases position <;> decide)
      (by cases level <;> cases position <;> decide)
      (by cases level <;> cases position <;> decide)
      (by cases level <;> cases position <;> decide)
  have one : RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor 1)
      (crossingMovingBox level) = 0 := by
    cases level with
    | upper =>
        exact factor_winding_zero_of_below 1
          (crossingMovingBox_proper .upper) (oneOnMovingBoxClearance .upper)
          (by decide)
    | lower =>
        exact factor_winding_zero_of_above 1
          (crossingMovingBox_proper .lower) (oneOnMovingBoxClearance .lower)
          (by decide)
  rw [zero, moving, one]
  ring1

theorem crossingOneWinding (level : Level) (position : Position) :
    RFAP.Winding.quadrupledBoxWinding
      (polynomial (crossingParameter level position))
      (connectorFixedBox 1) = 4 := by
  rw [polynomial_eq_factorsAt]
  apply factors_winding_of_sum (connectorFixedBox_proper 1)
    (leftClearance 0 zeroRoot_before_oneFixed)
    (movingOnOneBoxClearance level position) (fixedCenteredClearance 1)
  have zero : RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor 0)
      (connectorFixedBox 1) = 0 :=
    factor_winding_zero_of_left 0 (connectorFixedBox_proper 1)
      (leftClearance 0 zeroRoot_before_oneFixed) zeroRoot_before_oneFixed
  have moving : RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor
        (crossingParameter level position)) (connectorFixedBox 1) = 0 := by
    cases level with
    | upper =>
        exact factor_winding_zero_of_above _ (connectorFixedBox_proper 1)
          (movingOnOneBoxClearance .upper position)
          (by cases position <;> decide)
    | lower =>
        exact factor_winding_zero_of_below _ (connectorFixedBox_proper 1)
          (movingOnOneBoxClearance .lower position)
          (by cases position <;> decide)
  have one : RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor 1)
      (connectorFixedBox 1) = 4 :=
    RFAP.AffineWinding.quadrupledBoxWinding_translatedCoordinate 1
      (connectorFixedBox_left 1) (connectorFixedBox_right 1)
      (connectorFixedBox_below 1) (connectorFixedBox_above 1)
  rw [zero, moving, one]
  ring1

def crossingZeroOwner (level : Level) (position : Position) :
    LocalOwner (polynomial (crossingParameter level position)) :=
  ownerOf (connectorFixedBox 0) (connectorFixedBox_proper 0)
    (by rw [polynomial_eq_factorsAt];
        exact crossingZeroFactorsClearance level position)
    (crossingZeroWinding level position)

def crossingMovingOwner (level : Level) (position : Position) :
    LocalOwner (polynomial (crossingParameter level position)) :=
  ownerOf (crossingMovingBox level) (crossingMovingBox_proper level)
    (by rw [polynomial_eq_factorsAt];
        exact crossingMovingFactorsClearance level position)
    (crossingMovingWinding level position)

def crossingOneOwner (level : Level) (position : Position) :
    LocalOwner (polynomial (crossingParameter level position)) :=
  ownerOf (connectorFixedBox 1) (connectorFixedBox_proper 1)
    (by rw [polynomial_eq_factorsAt];
        exact crossingOneFactorsClearance level position)
    (crossingOneWinding level position)

def sampleMovingCenteredClearance (level : Level) (position : Position) :
    BoundaryClearance
      (CCL.Riemann.ExplicitLegendreFrame.factor
        (crossingParameter level position))
      (sampleBox (crossingParameter level position)) :=
  centeredClearance _
    (by cases level <;> cases position <;> decide)
    (by cases level <;> cases position <;> decide)
    (by cases level <;> cases position <;> decide)
    (by cases level <;> cases position <;> decide)

def zeroOnSampleMovingClearance (level : Level) (position : Position) :
    BoundaryClearance (CCL.Riemann.ExplicitLegendreFrame.factor 0)
      (sampleBox (crossingParameter level position)) := by
  cases level with
  | upper => exact belowClearance 0 (by cases position <;> decide)
  | lower => exact aboveClearance 0 (by cases position <;> decide)

def oneOnSampleMovingClearance (level : Level) (position : Position) :
    BoundaryClearance (CCL.Riemann.ExplicitLegendreFrame.factor 1)
      (sampleBox (crossingParameter level position)) := by
  cases level with
  | upper => exact belowClearance 1 (by cases position <;> decide)
  | lower => exact aboveClearance 1 (by cases position <;> decide)

theorem crossingSampleMovingWinding (level : Level) (position : Position) :
    RFAP.Winding.quadrupledBoxWinding
      (polynomial (crossingParameter level position))
      (sampleBox (crossingParameter level position)) = 4 := by
  rw [polynomial_eq_factorsAt]
  apply factors_winding_of_sum (sampleBox_proper _)
    (zeroOnSampleMovingClearance level position)
    (sampleMovingCenteredClearance level position)
    (oneOnSampleMovingClearance level position)
  have zero : RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor 0)
      (sampleBox (crossingParameter level position)) = 0 := by
    cases level with
    | upper =>
        exact factor_winding_zero_of_below 0 (sampleBox_proper _)
          (zeroOnSampleMovingClearance .upper position)
          (by cases position <;> decide)
    | lower =>
        exact factor_winding_zero_of_above 0 (sampleBox_proper _)
          (zeroOnSampleMovingClearance .lower position)
          (by cases position <;> decide)
  have moving : RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor
        (crossingParameter level position))
      (sampleBox (crossingParameter level position)) = 4 :=
    RFAP.AffineWinding.quadrupledBoxWinding_translatedCoordinate _
      (by cases level <;> cases position <;> decide)
      (by cases level <;> cases position <;> decide)
      (by cases level <;> cases position <;> decide)
      (by cases level <;> cases position <;> decide)
  have one : RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor 1)
      (sampleBox (crossingParameter level position)) = 0 := by
    cases level with
    | upper =>
        exact factor_winding_zero_of_below 1 (sampleBox_proper _)
          (oneOnSampleMovingClearance .upper position)
          (by cases position <;> decide)
    | lower =>
        exact factor_winding_zero_of_above 1 (sampleBox_proper _)
          (oneOnSampleMovingClearance .lower position)
          (by cases position <;> decide)
  rw [zero, moving, one]
  ring1

def crossingSampleMovingOwner (level : Level) (position : Position) :
    LocalOwner (polynomial (crossingParameter level position)) :=
  ownerOf (sampleBox (crossingParameter level position)) (sampleBox_proper _)
    (by
      rw [polynomial_eq_factorsAt]
      exact factorsClearance (zeroOnSampleMovingClearance level position)
        (sampleMovingCenteredClearance level position)
        (oneOnSampleMovingClearance level position))
    (crossingSampleMovingWinding level position)

def crossingSampleOwner (level : Level) (position : Position) :
    Fin 3 -> LocalOwner (polynomial (crossingParameter level position))
  | 0 => crossingZeroOwner level position
  | 1 => crossingSampleMovingOwner level position
  | 2 => crossingOneOwner level position

private theorem finThree_cases (index : Fin 3) :
    index = 0 ∨ index = 1 ∨ index = 2 := by
  rcases index with ⟨value, bound⟩
  omega0

def crossingOwner (level : Level) (position : Position) :
    Fin 3 -> LocalOwner (polynomial (crossingParameter level position))
  | 0 => crossingZeroOwner level position
  | 1 => crossingMovingOwner level position
  | 2 => crossingOneOwner level position

theorem crossingOwner_pairwise (level : Level) (position : Position) :
    forall left right : Fin 3, left ≠ right ->
      (crossingOwner level position left).box.Separated
        (crossingOwner level position right).box := by
  intro left right different
  rcases finThree_cases left with leftZero | leftOne | leftTwo <;>
    subst left <;>
    rcases finThree_cases right with rightZero | rightOne | rightTwo <;>
    subst right <;>
    first | exact (different rfl).elim |
      cases level <;> cases position <;> decide

def crossingOwnerFamily (level : Level) (position : Position) :
    CCL.ProgressivePolynomialRoots.OwnerFamily
      (polynomial (crossingParameter level position)) 3 where
  owner := crossingOwner level position
  pairwiseSeparated := crossingOwner_pairwise level position

def crossingChamber (level : Level) (position : Position) :
    CCL.FiniteMonodromy.ChamberFrame where
  reference := coefficientTable (crossingParameter level position)
  chamber :=
    { degreeAtLeastTwo := by
        change 2 <= 3
        decide
      squarefree := connectorSquarefree (connectorSide position)
        (levelHeight level)
      owners := crossingOwnerFamily level position
      referenceSmall := coefficientTable_allowances_lt _
        (CCL.ProgressivePolynomialRoots.simpleRootChamberTarget_pos
          (coefficientTable (crossingParameter level position))
          (connectorSquarefree (connectorSide position) (levelHeight level))
          (crossingOwnerFamily level position))
      referenceMaximality :=
        (CCL.BoxRFAPBridge.prove
          (connectorIsolationInput (connectorSide position)
            (levelHeight level))).boxes.maximality }

@[simp] theorem crossingChamber_polynomial (level : Level)
    (position : Position) :
    (crossingChamber level position).polynomial =
      polynomial (crossingParameter level position) := rfl

def crossingProjectionOwner (level : Level) (position : Position)
    (order : Fin 3) :
    LocalOwner (polynomial (crossingParameter level position)) :=
  crossingSampleOwner level position
    ((connectorProjectionOrder (connectorSide position)).forward order)

def crossingFrame (level : Level) (position : Position) :
    Frame (crossingParameter level position) where
  chamber := crossingChamber level position
  polynomial_eq := rfl
  labels := CCL.FiniteMonodromy.FiniteBijection.identity 3
  owner_contains := by
    intro label
    rcases finThree_cases label with labelZero | labelOne | labelTwo <;>
      subst label
    · exact connectorFixedBox_contains 0
    · exact crossingMovingBox_contains level position
    · exact connectorFixedBox_contains 1
  projectionOrder := connectorProjectionOrder (connectorSide position)
  projectionOwner := fun order =>
    CCL.FiniteMonodromy.castOwner
      (crossingChamber_polynomial level position).symm
      (crossingProjectionOwner level position order)
  projection_refines := by
    intro order
    rcases finThree_cases order with orderZero | orderOne | orderTwo <;>
      subst order <;> cases level <;> cases position <;>
      exact ⟨by decide, by decide, by decide, by decide⟩
  projection_xOrdered := by
    intro left right ordered
    rcases finThree_cases left with leftZero | leftOne | leftTwo <;>
      subst left <;>
      rcases finThree_cases right with rightZero | rightOne | rightTwo <;>
      subst right <;> cases level <;> cases position <;>
      simp only [Fin.isValue, CCL.FiniteMonodromy.castOwner_box] at ordered ⊢ <;>
      first | omega0 | decide

/-! ## The two positive upper half-twists -/

def crossingSourcePosition : Level -> Position
  | .upper => .right
  | .lower => .left

def crossingTargetPosition : Level -> Position
  | .upper => .left
  | .lower => .right

def crossingSourceParameter (level : Level) : Gaussian :=
  crossingParameter level (crossingSourcePosition level)

def crossingTargetParameter (level : Level) : Gaussian :=
  crossingParameter level (crossingTargetPosition level)

def oneCrossingSourceFrame (level : Level) :
    Frame (crossingSourceParameter level) :=
  crossingFrame level (crossingSourcePosition level)

def oneCrossingTargetFrame (level : Level) :
    Frame (crossingTargetParameter level) :=
  crossingFrame level (crossingTargetPosition level)

def crossingPerturbation (level : Level) : GaussianPolynomial :=
  perturbationAt (crossingSourceParameter level)
    (crossingTargetParameter level)

theorem crossingTarget_eq_add (level : Level) :
    polynomial (crossingTargetParameter level) =
      polynomial (crossingSourceParameter level) +
        crossingPerturbation level :=
  target_eq_source_add_perturbationAt _ _

def crossingOrientedRouche (level : Level)
    (owner : LocalOwner (polynomial (crossingSourceParameter level)))
    (dominance : RFAP.WindingHomotopy.BoundaryNormDominance
      (polynomial (crossingSourceParameter level))
      (crossingPerturbation level) owner.box) :
    CCL.FiniteMonodromy.OrientedRouche
      (polynomial (crossingSourceParameter level))
      (polynomial (crossingTargetParameter level)) owner.box where
  perturbation := crossingPerturbation level
  target_eq_add := crossingTarget_eq_add level
  dominance := dominance

theorem crossingZeroDisplacementSmall (level : Level) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (crossingSourceParameter level - crossingTargetParameter level) <
      (movingOnZeroBoxClearance level
        (crossingSourcePosition level)).bound := by
  cases level <;> decide

theorem crossingMovingDisplacementSmall (level : Level) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (crossingSourceParameter level - crossingTargetParameter level) <
      (crossingMovingCenteredClearance level
        (crossingSourcePosition level)).bound := by
  cases level <;> decide

theorem crossingOneDisplacementSmall (level : Level) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (crossingSourceParameter level - crossingTargetParameter level) <
      (movingOnOneBoxClearance level
        (crossingSourcePosition level)).bound := by
  cases level <;> decide

def crossingZeroDominance (level : Level) :
    RFAP.WindingHomotopy.BoundaryNormDominance
      (polynomial (crossingSourceParameter level))
      (crossingPerturbation level)
      (crossingZeroOwner level (crossingSourcePosition level)).box :=
  factorMoveDominanceAt _ _ (fixedCenteredClearance 0)
    (movingOnZeroBoxClearance level (crossingSourcePosition level))
    (rightClearance 1 zeroFixed_before_oneRoot)
    (crossingZeroDisplacementSmall level)

def crossingMovingDominance (level : Level) :
    RFAP.WindingHomotopy.BoundaryNormDominance
      (polynomial (crossingSourceParameter level))
      (crossingPerturbation level)
      (crossingMovingOwner level (crossingSourcePosition level)).box :=
  factorMoveDominanceAt _ _ (zeroOnMovingBoxClearance level)
    (crossingMovingCenteredClearance level (crossingSourcePosition level))
    (oneOnMovingBoxClearance level)
    (crossingMovingDisplacementSmall level)

def crossingOneDominance (level : Level) :
    RFAP.WindingHomotopy.BoundaryNormDominance
      (polynomial (crossingSourceParameter level))
      (crossingPerturbation level)
      (crossingOneOwner level (crossingSourcePosition level)).box :=
  factorMoveDominanceAt _ _ (leftClearance 0 zeroRoot_before_oneFixed)
    (movingOnOneBoxClearance level (crossingSourcePosition level))
    (fixedCenteredClearance 1) (crossingOneDisplacementSmall level)

def crossingZeroBridge (level : Level) : CCL.FiniteMonodromy.OwnerBridge
    (polynomial (crossingSourceParameter level))
    (polynomial (crossingTargetParameter level)) :=
  CCL.FiniteMonodromy.OwnerBridge.ofForward
    (crossingZeroOwner level (crossingSourcePosition level))
    (crossingOrientedRouche level _ (crossingZeroDominance level))

def crossingMovingBridge (level : Level) : CCL.FiniteMonodromy.OwnerBridge
    (polynomial (crossingSourceParameter level))
    (polynomial (crossingTargetParameter level)) :=
  CCL.FiniteMonodromy.OwnerBridge.ofForward
    (crossingMovingOwner level (crossingSourcePosition level))
    (crossingOrientedRouche level _ (crossingMovingDominance level))

def crossingOneBridge (level : Level) : CCL.FiniteMonodromy.OwnerBridge
    (polynomial (crossingSourceParameter level))
    (polynomial (crossingTargetParameter level)) :=
  CCL.FiniteMonodromy.OwnerBridge.ofForward
    (crossingOneOwner level (crossingSourcePosition level))
    (crossingOrientedRouche level _ (crossingOneDominance level))

def crossingBridgeAt (level : Level) :
    Fin 3 -> CCL.FiniteMonodromy.OwnerBridge
      (polynomial (crossingSourceParameter level))
      (polynomial (crossingTargetParameter level))
  | 0 => crossingZeroBridge level
  | 1 => crossingMovingBridge level
  | 2 => crossingOneBridge level

def crossingChamberOverlap (level : Level) :
    CCL.FiniteMonodromy.ChamberOverlap
      (oneCrossingSourceFrame level).chamber
      (oneCrossingTargetFrame level).chamber where
  matching := CCL.FiniteMonodromy.FiniteBijection.identity 3
  bridge := crossingBridgeAt level
  bridge_refines_left := by
    intro index
    rcases finThree_cases index with indexZero | indexOne | indexTwo <;>
      subst index <;> exact RFAP.Boxes.Box.refines_refl _
  bridge_refines_right := by
    intro index
    rcases finThree_cases index with indexZero | indexOne | indexTwo <;>
      subst index <;> exact RFAP.Boxes.Box.refines_refl _

theorem crossingGeometry (level : Level) :
    CCL.Knot.ProjectedCrossings.CrossingGeometry
      (oneCrossingSourceFrame level).projected
      (oneCrossingTargetFrame level).projected
      (crossingChamberOverlap level)
      CCL.Riemann.LegendreConventions.upperPositive where
  heightSeparated := by
    cases level
    · change (1 / 16 : Coordinate) < 1
      decide
    · change (-1 : Coordinate) < -(1 / 16)
      decide

def crossingProjectedOverlap (level : Level) :
    CCL.Knot.ProjectedCrossings.ProjectedOverlap
      (oneCrossingSourceFrame level).projected
      (oneCrossingTargetFrame level).projected :=
  .crossing (crossingChamberOverlap level)
    CCL.Riemann.LegendreConventions.upperPositive (crossingGeometry level) (by
      intro order
      rcases finThree_cases order with orderZero | orderOne | orderTwo <;>
        subst order <;> cases level <;> rfl)

@[simp] theorem crossingProjectedOverlap_word (level : Level) :
    (crossingProjectedOverlap level).word =
      [CCL.Riemann.LegendreConventions.upperPositive] := rfl

def crossingSheetBound (level : Level) : Coordinate :=
  min (crossingZeroBridge level).leftClearance.bound
    (min (crossingZeroBridge level).rightClearance.bound
      (min (crossingMovingBridge level).leftClearance.bound
        (min (crossingMovingBridge level).rightClearance.bound
          (min (crossingOneBridge level).leftClearance.bound
            (crossingOneBridge level).rightClearance.bound))))

theorem crossingSheetBound_positive (level : Level) :
    0 < crossingSheetBound level := by
  unfold crossingSheetBound
  exact lt_min (crossingZeroBridge level).leftClearance.positive
    (lt_min (crossingZeroBridge level).rightClearance.positive
      (lt_min (crossingMovingBridge level).leftClearance.positive
        (lt_min (crossingMovingBridge level).rightClearance.positive
          (lt_min (crossingOneBridge level).leftClearance.positive
            (crossingOneBridge level).rightClearance.positive))))

def crossingSheetClearance (level : Level) :
    BridgeClearance (oneCrossingSourceFrame level)
      (oneCrossingTargetFrame level) (crossingChamberOverlap level) where
  bound := crossingSheetBound level
  positive := crossingSheetBound_positive level
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

def crossingAxis : (level : Level) ->
    AxisSegment (crossingSourceParameter level)
      (crossingTargetParameter level)
  | .upper => .horizontal (5 / 4) (3 / 4) 2
  | .lower => .horizontal (3 / 4) (5 / 4) (-2)

def crossingAxisSafe (level : Level) : AxisSegment.Safe (crossingAxis level) := by
  cases level
  · exact
      { avoidsZero := { bound := 1, positive := by decide, lower := by decide }
        avoidsOne := { bound := 1, positive := by decide, lower := by decide } }
  · exact
      { avoidsZero := { bound := 1, positive := by decide, lower := by decide }
        avoidsOne := { bound := 1, positive := by decide, lower := by decide } }

def crossingSegment (level : Level) :
    Segment (oneCrossingSourceFrame level) (oneCrossingTargetFrame level) :=
  Segment.ofProjectedOverlap (crossingAxis level) (crossingAxisSafe level)
    (crossingProjectedOverlap level) (crossingSheetClearance level)

@[simp] theorem crossingSegment_crossings (level : Level) :
    (crossingSegment level).crossings =
      [CCL.Riemann.LegendreConventions.upperPositive] := rfl

def crossingPath (level : Level) :
    Path (oneCrossingSourceFrame level) (oneCrossingTargetFrame level) :=
  .cons (crossingSegment level) (.nil _)

@[simp] theorem crossingPath_word (level : Level) :
    (crossingPath level).word =
      [CCL.Riemann.LegendreConventions.upperPositive] := rfl

/-! ## Stationary transitions to the uniform connector frames -/

theorem narrowBroadPolynomial_eq (level : Level) (position : Position) :
    (connectorChamber (connectorSide position)
      (levelHeight level)).polynomial =
      (crossingChamber level position).polynomial := by
  rw [connectorChamber_polynomial, crossingChamber_polynomial]
  rfl

def narrowBroadBridge (level : Level) (position : Position)
    (index : Fin 3) : CCL.FiniteMonodromy.OwnerBridge
      (connectorChamber (connectorSide position)
        (levelHeight level)).polynomial
      (crossingChamber level position).polynomial :=
  @CCL.FiniteMonodromy.OwnerBridge.cast
    (connectorChamber (connectorSide position)
      (levelHeight level)).polynomial
    (connectorChamber (connectorSide position)
      (levelHeight level)).polynomial
    (connectorChamber (connectorSide position)
      (levelHeight level)).polynomial
    (crossingChamber level position).polynomial rfl
    (narrowBroadPolynomial_eq level position)
    (CCL.FiniteMonodromy.OwnerBridge.reflexive
      (connectorOwner (connectorSide position) (levelHeight level) index))

@[simp] theorem narrowBroadBridge_box (level : Level) (position : Position)
    (index : Fin 3) :
    (narrowBroadBridge level position index).box =
      (connectorOwner (connectorSide position) (levelHeight level) index).box :=
  CCL.FiniteMonodromy.OwnerBridge.cast_box _ _ _

@[simp] theorem narrowBroadBridge_leftClearance_bound
    (level : Level) (position : Position) (index : Fin 3) :
    (narrowBroadBridge level position index).leftClearance.bound =
      (connectorOwner (connectorSide position)
        (levelHeight level) index).clearance.bound := by
  unfold narrowBroadBridge
  rw [CCL.FiniteMonodromy.OwnerBridge.cast_leftClearance_bound]
  rfl

@[simp] theorem narrowBroadBridge_rightClearance_bound
    (level : Level) (position : Position) (index : Fin 3) :
    (narrowBroadBridge level position index).rightClearance.bound =
      (connectorOwner (connectorSide position)
        (levelHeight level) index).clearance.bound := by
  unfold narrowBroadBridge
  rw [CCL.FiniteMonodromy.OwnerBridge.cast_rightClearance_bound]
  rfl

def narrowBroadOverlap (level : Level) (position : Position) :
    CCL.FiniteMonodromy.ChamberOverlap
      (connectorChamber (connectorSide position) (levelHeight level))
      (crossingChamber level position) where
  matching := CCL.FiniteMonodromy.FiniteBijection.identity 3
  bridge := narrowBroadBridge level position
  bridge_refines_left := by
    intro index
    rw [narrowBroadBridge_box]
    exact RFAP.Boxes.Box.refines_refl _
  bridge_refines_right := by
    intro index
    rw [narrowBroadBridge_box]
    rcases finThree_cases index with indexZero | indexOne | indexTwo <;>
      subst index
    · exact RFAP.Boxes.Box.refines_refl _
    · cases level <;> cases position <;>
        exact ⟨by decide, by decide, by decide, by decide⟩
    · exact RFAP.Boxes.Box.refines_refl _

@[simp] theorem narrowBroadOverlap_bridge (level : Level)
    (position : Position) (index : Fin 3) :
    (narrowBroadOverlap level position).bridge index =
      narrowBroadBridge level position index := rfl

@[simp] theorem narrowBroadOverlap_leftClearance_bound
    (level : Level) (position : Position) (index : Fin 3) :
    ((narrowBroadOverlap level position).bridge index).leftClearance.bound =
      (connectorOwner (connectorSide position)
        (levelHeight level) index).clearance.bound := by
  rw [narrowBroadOverlap_bridge, narrowBroadBridge_leftClearance_bound]

@[simp] theorem narrowBroadOverlap_rightClearance_bound
    (level : Level) (position : Position) (index : Fin 3) :
    ((narrowBroadOverlap level position).bridge index).rightClearance.bound =
      (connectorOwner (connectorSide position)
        (levelHeight level) index).clearance.bound := by
  rw [narrowBroadOverlap_bridge, narrowBroadBridge_rightClearance_bound]

def narrowBroadProjectedOverlap (level : Level) (position : Position) :
    CCL.Knot.ProjectedCrossings.ProjectedOverlap
      (connectorFrame (connectorSide position) (levelHeight level)).projected
      (crossingFrame level position).projected :=
  .stationary (narrowBroadOverlap level position) (by
    intro order
    rcases finThree_cases order with orderZero | orderOne | orderTwo <;>
      subst order <;> cases position <;> rfl)

@[simp] theorem narrowBroadProjectedOverlap_word
    (level : Level) (position : Position) :
    (narrowBroadProjectedOverlap level position).word = [] := rfl

def narrowBroadSheetClearance : (level : Level) -> (position : Position) ->
    BridgeClearance
      (connectorFrame (connectorSide position) (levelHeight level))
      (crossingFrame level position) (narrowBroadOverlap level position)
  | .upper, .left =>
      { bound := transitionSheetBound .oneLeft 2
        positive := transitionSheetBound_positive .oneLeft 2
        leftLower := by
          intro index
          rw [narrowBroadOverlap_leftClearance_bound]
          exact transitionSheetBound_le .oneLeft 2 index
        rightLower := by
          intro index
          rw [narrowBroadOverlap_rightClearance_bound]
          exact transitionSheetBound_le .oneLeft 2 index }
  | .upper, .right =>
      { bound := transitionSheetBound .oneRight 2
        positive := transitionSheetBound_positive .oneRight 2
        leftLower := by
          intro index
          rw [narrowBroadOverlap_leftClearance_bound]
          exact transitionSheetBound_le .oneRight 2 index
        rightLower := by
          intro index
          rw [narrowBroadOverlap_rightClearance_bound]
          exact transitionSheetBound_le .oneRight 2 index }
  | .lower, .left =>
      { bound := transitionSheetBound .oneLeft (-2)
        positive := transitionSheetBound_positive .oneLeft (-2)
        leftLower := by
          intro index
          rw [narrowBroadOverlap_leftClearance_bound]
          exact transitionSheetBound_le .oneLeft (-2) index
        rightLower := by
          intro index
          rw [narrowBroadOverlap_rightClearance_bound]
          exact transitionSheetBound_le .oneLeft (-2) index }
  | .lower, .right =>
      { bound := transitionSheetBound .oneRight (-2)
        positive := transitionSheetBound_positive .oneRight (-2)
        leftLower := by
          intro index
          rw [narrowBroadOverlap_leftClearance_bound]
          exact transitionSheetBound_le .oneRight (-2) index
        rightLower := by
          intro index
          rw [narrowBroadOverlap_rightClearance_bound]
          exact transitionSheetBound_le .oneRight (-2) index }

def narrowToBroadTransition (level : Level) (position : Position) :
    Segment
      (connectorFrame (connectorSide position) (levelHeight level))
      (crossingFrame level position) :=
  Segment.ofProjectedOverlap
    (stationaryGeometry (connectorSide position) (levelHeight level))
    (stationaryGeometrySafe (connectorSide position) (levelHeight level))
    (narrowBroadProjectedOverlap level position)
    (narrowBroadSheetClearance level position)

@[simp] theorem narrowToBroadTransition_crossings
    (level : Level) (position : Position) :
    (narrowToBroadTransition level position).crossings = [] := rfl

def broadToNarrowTransition (level : Level) (position : Position) :
    Segment (crossingFrame level position)
      (connectorFrame (connectorSide position) (levelHeight level)) :=
  (narrowToBroadTransition level position).reverse

@[simp] theorem broadToNarrowTransition_crossings
    (level : Level) (position : Position) :
    (broadToNarrowTransition level position).crossings = [] := by
  rw [broadToNarrowTransition, Segment.reverse_crossings,
    narrowToBroadTransition_crossings]
  rfl

def narrowToBroadPath (level : Level) (position : Position) :
    Path (connectorFrame (connectorSide position) (levelHeight level))
      (crossingFrame level position) :=
  .cons (narrowToBroadTransition level position) (.nil _)

@[simp] theorem narrowToBroadPath_word (level : Level) (position : Position) :
    (narrowToBroadPath level position).word = [] := rfl

def broadToNarrowPath (level : Level) (position : Position) :
    Path (crossingFrame level position)
      (connectorFrame (connectorSide position) (levelHeight level)) :=
  .cons (broadToNarrowTransition level position) (.nil _)

@[simp] theorem broadToNarrowPath_word (level : Level) (position : Position) :
    (broadToNarrowPath level position).word = [] := by
  rw [broadToNarrowPath]
  simp only [Path.word, broadToNarrowTransition_crossings, List.append_nil]

/-! ## The closed local rectangle around one -/

def topLeftBroadToNarrowPath :
    Path (crossingFrame .upper .left) (connectorFrame .oneLeft 2) := by
  exact broadToNarrowPath .upper .left

@[simp] theorem topLeftBroadToNarrowPath_word :
    topLeftBroadToNarrowPath.word = [] := by
  exact broadToNarrowPath_word .upper .left

def bottomLeftNarrowToBroadPath :
    Path (connectorFrame .oneLeft (-2)) (crossingFrame .lower .left) := by
  exact narrowToBroadPath .lower .left

@[simp] theorem bottomLeftNarrowToBroadPath_word :
    bottomLeftNarrowToBroadPath.word = [] := by
  exact narrowToBroadPath_word .lower .left

def bottomRightBroadToNarrowPath :
    Path (crossingFrame .lower .right) (connectorFrame .oneRight (-2)) := by
  exact broadToNarrowPath .lower .right

@[simp] theorem bottomRightBroadToNarrowPath_word :
    bottomRightBroadToNarrowPath.word = [] := by
  exact broadToNarrowPath_word .lower .right

def topRightNarrowToBroadPath :
    Path (connectorFrame .oneRight 2) (crossingFrame .upper .right) := by
  exact narrowToBroadPath .upper .right

@[simp] theorem topRightNarrowToBroadPath_word :
    topRightNarrowToBroadPath.word = [] := by
  exact narrowToBroadPath_word .upper .right

def lowerCrossingPath :
    Path (crossingFrame .lower .left) (crossingFrame .lower .right) := by
  exact crossingPath .lower

@[simp] theorem lowerCrossingPath_word : lowerCrossingPath.word =
    [CCL.Riemann.LegendreConventions.upperPositive] := by
  exact crossingPath_word .lower

def upperCrossingPath :
    Path (crossingFrame .upper .right) (crossingFrame .upper .left) := by
  exact crossingPath .upper

@[simp] theorem upperCrossingPath_word : upperCrossingPath.word =
    [CCL.Riemann.LegendreConventions.upperPositive] := by
  exact crossingPath_word .upper

def localOneLoop : Path (crossingFrame .upper .left)
    (crossingFrame .upper .left) :=
  topLeftBroadToNarrowPath.append
    ((sideDescent .oneLeft).append
      (bottomLeftNarrowToBroadPath.append
        (lowerCrossingPath.append
          (bottomRightBroadToNarrowPath.append
            ((sideAscent .oneRight).append
              (topRightNarrowToBroadPath.append upperCrossingPath))))))

@[simp] theorem localOneLoop_word : localOneLoop.word =
    [CCL.Riemann.LegendreConventions.upperPositive,
      CCL.Riemann.LegendreConventions.upperPositive] := by
  rw [localOneLoop, Path.word_append, Path.word_append, Path.word_append,
    Path.word_append, Path.word_append, Path.word_append, Path.word_append,
    topLeftBroadToNarrowPath_word, sideDescent_word,
    bottomLeftNarrowToBroadPath_word, lowerCrossingPath_word,
    bottomRightBroadToNarrowPath_word, sideAscent_word,
    topRightNarrowToBroadPath_word, upperCrossingPath_word]
  rfl

/-! ## No-crossing approach from the common base -/

def approachPerturbation : GaussianPolynomial :=
  perturbationAt sourceParameter (crossingParameter .upper .left)

theorem approachTarget_eq_add :
    polynomial (crossingParameter .upper .left) =
      polynomial sourceParameter + approachPerturbation :=
  target_eq_source_add_perturbationAt _ _

def approachOrientedRouche
    (owner : LocalOwner (polynomial sourceParameter))
    (dominance : RFAP.WindingHomotopy.BoundaryNormDominance
      (polynomial sourceParameter) approachPerturbation owner.box) :
    CCL.FiniteMonodromy.OrientedRouche
      (polynomial sourceParameter)
      (polynomial (crossingParameter .upper .left)) owner.box where
  perturbation := approachPerturbation
  target_eq_add := approachTarget_eq_add
  dominance := dominance

def approachZeroDominance : RFAP.WindingHomotopy.BoundaryNormDominance
    (polynomial sourceParameter) approachPerturbation sourceZeroOwner.box :=
  factorMoveDominanceAt sourceParameter (crossingParameter .upper .left)
    (centeredClearance 0 (by decide) (by decide) (by decide) (by decide))
    (aboveClearance sourceParameter source_above_fixedZero)
    (rightClearance 1 (by decide)) (by decide)

def approachMovingDominance : RFAP.WindingHomotopy.BoundaryNormDominance
    (polynomial sourceParameter) approachPerturbation sourceMovingOwner.box :=
  factorMoveDominanceAt sourceParameter (crossingParameter .upper .left)
    (belowClearance 0 (by decide))
    (centeredClearance sourceParameter source_in_movingBox.1
      source_in_movingBox.2.1 source_in_movingBox.2.2.1
      source_in_movingBox.2.2.2)
    (belowClearance 1 (by decide)) (by decide)

def approachOneDominance : RFAP.WindingHomotopy.BoundaryNormDominance
    (polynomial sourceParameter) approachPerturbation sourceOneOwner.box :=
  factorMoveDominanceAt sourceParameter (crossingParameter .upper .left)
    (leftClearance 0 (by decide))
    (aboveClearance sourceParameter source_above_fixedOne)
    (centeredClearance 1 (by decide) (by decide) (by decide) (by decide))
    (by decide)

def approachZeroBridge : CCL.FiniteMonodromy.OwnerBridge
    (polynomial sourceParameter)
    (polynomial (crossingParameter .upper .left)) :=
  CCL.FiniteMonodromy.OwnerBridge.ofForward sourceZeroOwner
    (approachOrientedRouche sourceZeroOwner approachZeroDominance)

def approachMovingBridge : CCL.FiniteMonodromy.OwnerBridge
    (polynomial sourceParameter)
    (polynomial (crossingParameter .upper .left)) :=
  CCL.FiniteMonodromy.OwnerBridge.ofForward sourceMovingOwner
    (approachOrientedRouche sourceMovingOwner approachMovingDominance)

def approachOneBridge : CCL.FiniteMonodromy.OwnerBridge
    (polynomial sourceParameter)
    (polynomial (crossingParameter .upper .left)) :=
  CCL.FiniteMonodromy.OwnerBridge.ofForward sourceOneOwner
    (approachOrientedRouche sourceOneOwner approachOneDominance)

def approachBridgeAt : Fin 3 -> CCL.FiniteMonodromy.OwnerBridge
    (polynomial sourceParameter)
    (polynomial (crossingParameter .upper .left))
  | 0 => approachZeroBridge
  | 1 => approachMovingBridge
  | 2 => approachOneBridge

def approachChamberOverlap : CCL.FiniteMonodromy.ChamberOverlap
    sourceChamber (crossingChamber .upper .left) where
  matching := CCL.FiniteMonodromy.FiniteBijection.identity 3
  bridge := approachBridgeAt
  bridge_refines_left := by
    intro index
    rcases finThree_cases index with indexZero | indexOne | indexTwo <;>
      subst index <;> exact RFAP.Boxes.Box.refines_refl _
  bridge_refines_right := by
    intro index
    rcases finThree_cases index with indexZero | indexOne | indexTwo <;>
      subst index <;>
      exact ⟨by decide, by decide, by decide, by decide⟩

def approachProjectedOverlap : CCL.Knot.ProjectedCrossings.ProjectedOverlap
    sourceFrame.projected (crossingFrame .upper .left).projected :=
  .stationary approachChamberOverlap (by
    intro order
    rcases finThree_cases order with orderZero | orderOne | orderTwo <;>
      subst order <;> rfl)

@[simp] theorem approachProjectedOverlap_word :
    approachProjectedOverlap.word = [] := rfl

def approachSheetBound : Coordinate :=
  min approachZeroBridge.leftClearance.bound
    (min approachZeroBridge.rightClearance.bound
      (min approachMovingBridge.leftClearance.bound
        (min approachMovingBridge.rightClearance.bound
          (min approachOneBridge.leftClearance.bound
            approachOneBridge.rightClearance.bound))))

theorem approachSheetBound_positive : 0 < approachSheetBound := by
  unfold approachSheetBound
  exact lt_min approachZeroBridge.leftClearance.positive
    (lt_min approachZeroBridge.rightClearance.positive
      (lt_min approachMovingBridge.leftClearance.positive
        (lt_min approachMovingBridge.rightClearance.positive
          (lt_min approachOneBridge.leftClearance.positive
            approachOneBridge.rightClearance.positive))))

def approachSheetClearance :
    BridgeClearance sourceFrame (crossingFrame .upper .left)
      approachChamberOverlap where
  bound := approachSheetBound
  positive := approachSheetBound_positive
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

def approachAxis : AxisSegment sourceParameter
    (crossingParameter .upper .left) :=
  .horizontal (1 / 4) (3 / 4) 2

def approachAxisSafe : AxisSegment.Safe approachAxis where
  avoidsZero := { bound := 1, positive := by decide, lower := by decide }
  avoidsOne := { bound := 1, positive := by decide, lower := by decide }

def approachSegment : Segment sourceFrame (crossingFrame .upper .left) :=
  Segment.ofProjectedOverlap approachAxis approachAxisSafe
    approachProjectedOverlap approachSheetClearance

@[simp] theorem approachSegment_crossings : approachSegment.crossings = [] :=
  rfl

def approachPath : Path sourceFrame (crossingFrame .upper .left) :=
  .cons approachSegment (.nil _)

@[simp] theorem approachPath_word : approachPath.word = [] := rfl

/-! ## The common-base standard one loop -/

def oneLoopPath : Path sourceFrame sourceFrame :=
  approachPath.append (localOneLoop.append approachPath.reverse)

@[simp] theorem oneLoopPath_word : oneLoopPath.word =
    [CCL.Riemann.LegendreConventions.upperPositive,
      CCL.Riemann.LegendreConventions.upperPositive] := by
  rw [oneLoopPath, Path.word_append, Path.word_append, approachPath_word,
    localOneLoop_word, Path.word_reverse, approachPath_word]
  rfl

theorem oneLoopWord : CCL.Knot.ArtinRelations.Equivalent oneLoopPath.word
    CCL.Riemann.LegendreMonodromy.oneBraid := by
  rw [oneLoopPath_word]
  exact .refl _

def standardLoops : CCL.Riemann.LegendreMonodromy.StandardLoops sourceFrame where
  zeroPath := zeroLoopPath
  onePath := oneLoopPath
  zeroWord := zeroLoopWord
  oneWord := oneLoopWord

end CCL.Riemann.ExplicitLegendreOneLoop
