import CCL.Riemann.ExplicitLegendreFrame
import CCL.Riemann.LegendreConventions
import CCL.Riemann.LegendreGaussManin
import CCL.Riemann.PreparedRefinementPrograms
import RFAP.Geometry.HalfPlane

/-!
# One explicit rational Legendre crossing segment

This module certifies a single positive projected crossing of the moving
Legendre root over the fixed root at zero.  The parameter moves horizontally
from `1/4 + 2i` to `-1/4 + 2i`.  Broad chamber-owner boxes retain the
same three roots across the coefficient overlap, while much smaller sample
owners certify the change in left-to-right projection order.
-/

namespace CCL.Riemann.ExplicitLegendreSegment

open CCL.Riemann.LegendrePaths

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial :=
  RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Box := RFAP.Boxes.Box
abbrev LocalOwner := CCL.ProgressivePolynomialRoots.LocalOwner
abbrev BoundaryClearance := RFAP.BoxClearance.BoundaryClearance

def sourceParameter : Gaussian := gaussian (1 / 4) 2
def targetParameter : Gaussian := gaussian (-(1 / 4)) 2

def factorsAt (lambda : Gaussian) : GaussianPolynomial :=
  (CCL.Riemann.ExplicitLegendreFrame.factor 0 *
    CCL.Riemann.ExplicitLegendreFrame.factor lambda) *
      CCL.Riemann.ExplicitLegendreFrame.factor 1

/-- The displayed three affine factors are coefficientwise the Legendre
cubic, uniformly in the rational parameter. -/
theorem polynomial_eq_factorsAt (lambda : Gaussian) :
    polynomial lambda = factorsAt lambda := by
  apply RFAP.FinitePolynomialExtensionality.normalized_eq_of_sub_isZero
  · apply RFAP.ComputablePolynomial.DensePolynomial.ext
    rfl
  · exact RFAP.ComputablePolynomial.DensePolynomial.normalize_mul _ _
  · apply RFAP.ConstructiveFiniteRoots.difference_isZero_of_candidate_evals
    intro point _member
    rw [polynomial_eval, factorsAt,
      RFAP.ComputablePolynomial.DensePolynomial.eval_mul,
      RFAP.ComputablePolynomial.DensePolynomial.eval_mul]
    unfold CCL.Riemann.ExplicitLegendreFrame.factor
    simp only [RFAP.AffineWinding.translatedCoordinate_eval]
    ring1

theorem source_polynomial_eq_factors :
    polynomial sourceParameter = factorsAt sourceParameter := by
  exact polynomial_eq_factorsAt sourceParameter

theorem target_polynomial_eq_factors :
    polynomial targetParameter = factorsAt targetParameter := by
  exact polynomial_eq_factorsAt targetParameter

/-! ## Rational owner and projection boxes -/

def fixedBox (x : Coordinate) : Box where
  xLower := x - 1 / 16
  xUpper := x + 1 / 16
  yLower := -(1 / 16)
  yUpper := 1 / 16
  x_valid := by
    apply le_of_lt
    calc
      x - 1 / 16 < x := by
        simpa using RFAP.ConstructiveFraction.sub_lt_sub_left_direct
          (by decide : (0 : Coordinate) < 1 / 16) x
      _ < x + 1 / 16 := by
        simpa using RFAP.ConstructiveFraction.add_lt_add_left_direct
          (by decide : (0 : Coordinate) < 1 / 16) x
  y_valid := by decide

def movingBox : Box where
  xLower := -1
  xUpper := 1
  yLower := 1
  yUpper := 3
  x_valid := by decide
  y_valid := by decide

def sampleBox (root : Gaussian) : Box where
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

theorem fixedBox_proper (x : Coordinate) : (fixedBox x).Proper := by
  constructor
  · change x - 1 / 16 < x + 1 / 16
    calc
      x - 1 / 16 < x := by
        simpa using RFAP.ConstructiveFraction.sub_lt_sub_left_direct
          (by decide : (0 : Coordinate) < 1 / 16) x
      _ < x + 1 / 16 := by
        simpa using RFAP.ConstructiveFraction.add_lt_add_left_direct
          (by decide : (0 : Coordinate) < 1 / 16) x
  · change (-(1 / 16 : Coordinate)) < 1 / 16
    decide

theorem movingBox_proper : movingBox.Proper := by
  constructor <;> decide

theorem sampleBox_proper (root : Gaussian) : (sampleBox root).Proper := by
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

/-! ## Factorwise boundary clearance -/

def centeredClearance (root : Gaussian) {box : Box}
    (left : box.xLower < root.re) (right : root.re < box.xUpper)
    (below : box.yLower < root.im) (above : root.im < box.yUpper) :
    BoundaryClearance
      (CCL.Riemann.ExplicitLegendreFrame.factor root) box :=
  RFAP.AffineWinding.translatedCoordinate_boundaryClearanceBox root
    left right below above

def belowClearance (root : Gaussian) {box : Box}
    (below : root.im < box.yLower) :
    BoundaryClearance
      (CCL.Riemann.ExplicitLegendreFrame.factor root) box :=
  RFAP.AffineWinding.translatedCoordinate_boundaryClearance_of_below
    root below

def aboveClearance (root : Gaussian) {box : Box}
    (above : box.yUpper < root.im) :
    BoundaryClearance
      (CCL.Riemann.ExplicitLegendreFrame.factor root) box :=
  RFAP.AffineWinding.translatedCoordinate_boundaryClearance_of_above
    root above

def leftClearance (root : Gaussian) {box : Box}
    (left : root.re < box.xLower) :
    BoundaryClearance
      (CCL.Riemann.ExplicitLegendreFrame.factor root) box :=
  RFAP.AffineWinding.translatedCoordinate_boundaryClearance_of_left root left

def rightClearance (root : Gaussian) {box : Box}
    (right : box.xUpper < root.re) :
    BoundaryClearance
      (CCL.Riemann.ExplicitLegendreFrame.factor root) box :=
  RFAP.AffineWinding.translatedCoordinate_boundaryClearance_of_right root right

/-- An affine factor whose root lies strictly left of a proper rational box
has zero winding there.  The proof uses the finite half-plane Cauchy scanner,
not an ambient argument principle. -/
theorem factor_winding_zero_of_left (root : Gaussian) {box : Box}
    (proper : box.Proper)
    (clearance : BoundaryClearance
      (CCL.Riemann.ExplicitLegendreFrame.factor root) box)
    (left : root.re < box.xLower) :
    RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor root) box = 0 := by
  apply RFAP.HalfPlane.quadrupledBoxWinding_eq_zero_of_positive_real
    (CCL.Riemann.ExplicitLegendreFrame.factor root) box proper clearance
  intro point boundary
  rw [CCL.Riemann.ExplicitLegendreFrame.factor,
    RFAP.AffineWinding.translatedCoordinate_eval]
  change 0 < point.re - root.re
  exact RFAP.ConstructiveFraction.sub_pos_direct
    (left.trans_le boundary.1.1)

/-- The reflected half-plane calculation for an affine root strictly right
of the box.  Multiplication by the exact constant `-1` makes the real part
positive; finite winding multiplicativity then cancels the constant's zero
winding. -/
theorem factor_winding_zero_of_right (root : Gaussian) {box : Box}
    (proper : box.Proper)
    (clearance : BoundaryClearance
      (CCL.Riemann.ExplicitLegendreFrame.factor root) box)
    (right : box.xUpper < root.re) :
    RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor root) box = 0 := by
  let minusOne : Gaussian := -1
  let constant := RFAP.GlobalWinding.gaussianConstant minusOne
  have minusOneNonzero : minusOne ≠ 0 := by decide
  let constantClearance :=
    RFAP.GlobalWinding.gaussianConstant_boundaryClearance minusOneNonzero box
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
    rw [show minusOne * (point - root) = -(point - root) by
      exact neg_one_mul (point - root)]
    rw [RFAP.ConstructiveGaussian.Gaussian.neg_re,
      RFAP.ConstructiveGaussian.Gaussian.sub_re]
    simpa only [neg_sub] using RFAP.ConstructiveFraction.sub_pos_direct
      (boundary.1.2.1.trans_lt right)
  have productFormula :=
    RFAP.WindingProduct.quadrupledBoxWinding_mul_of_boundaryClearances
      constant (CCL.Riemann.ExplicitLegendreFrame.factor root) box proper
      constantClearance clearance
  have constantZero : RFAP.Winding.quadrupledBoxWinding constant box = 0 :=
    RFAP.GlobalWinding.quadrupledBoxWinding_gaussianConstant
      minusOneNonzero box
  rw [productZero, constantZero] at productFormula
  simpa only [Int.zero_add] using productFormula.symm

def factorsClearance {lambda : Gaussian} {box : Box}
    (zero : BoundaryClearance
      (CCL.Riemann.ExplicitLegendreFrame.factor 0) box)
    (moving : BoundaryClearance
      (CCL.Riemann.ExplicitLegendreFrame.factor lambda) box)
    (one : BoundaryClearance
      (CCL.Riemann.ExplicitLegendreFrame.factor 1) box) :
    BoundaryClearance (factorsAt lambda) box :=
  RFAP.BoxClearance.BoundaryClearance.mul
    (RFAP.BoxClearance.BoundaryClearance.mul zero moving) one

def broadZeroClearance (lambda : Gaussian)
    (movingAbove : (fixedBox 0).yUpper < lambda.im) :
    BoundaryClearance (factorsAt lambda) (fixedBox 0) :=
  factorsClearance
    (centeredClearance 0 (by decide) (by decide) (by decide) (by decide))
    (aboveClearance lambda movingAbove)
    (rightClearance 1 (by decide))

def broadMovingClearance (lambda : Gaussian)
    (insideLeft : movingBox.xLower < lambda.re)
    (insideRight : lambda.re < movingBox.xUpper)
    (insideBelow : movingBox.yLower < lambda.im)
    (insideAbove : lambda.im < movingBox.yUpper) :
    BoundaryClearance (factorsAt lambda) movingBox :=
  factorsClearance
    (belowClearance 0 (by decide))
    (centeredClearance lambda insideLeft insideRight insideBelow insideAbove)
    (belowClearance 1 (by decide))

def broadOneClearance (lambda : Gaussian)
    (movingAbove : (fixedBox 1).yUpper < lambda.im) :
    BoundaryClearance (factorsAt lambda) (fixedBox 1) :=
  factorsClearance
    (leftClearance 0 (by decide))
    (aboveClearance lambda movingAbove)
    (centeredClearance 1 (by decide) (by decide) (by decide) (by decide))

def sampleZeroClearance (lambda : Gaussian)
    (movingAbove : (sampleBox 0).yUpper < lambda.im) :
    BoundaryClearance (factorsAt lambda) (sampleBox 0) :=
  factorsClearance
    (centeredClearance 0 (by decide) (by decide) (by decide) (by decide))
    (aboveClearance lambda movingAbove)
    (rightClearance 1 (by decide))

def sampleMovingClearance (lambda : Gaussian)
    (imaginaryHigh : (1 / 16 : Coordinate) < lambda.im) :
    BoundaryClearance (factorsAt lambda) (sampleBox lambda) :=
  factorsClearance
    (belowClearance 0 (by
      change (0 : Coordinate) < lambda.im - 1 / 16
      exact RFAP.ConstructiveFraction.sub_pos_direct imaginaryHigh))
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
    (belowClearance 1 (by
      change (0 : Coordinate) < lambda.im - 1 / 16
      exact RFAP.ConstructiveFraction.sub_pos_direct imaginaryHigh))

def sampleOneClearance (lambda : Gaussian)
    (movingAbove : (sampleBox 1).yUpper < lambda.im) :
    BoundaryClearance (factorsAt lambda) (sampleBox 1) :=
  factorsClearance
    (leftClearance 0 (by decide))
    (aboveClearance lambda movingAbove)
    (centeredClearance 1 (by decide) (by decide) (by decide) (by decide))

/-! ## Exact endpoint chambers -/

def sourcePolynomialClearance {box : Box}
    (clearance : BoundaryClearance (factorsAt sourceParameter) box) :
    BoundaryClearance (polynomial sourceParameter) box := by
  rw [source_polynomial_eq_factors]
  exact clearance

def targetPolynomialClearance {box : Box}
    (clearance : BoundaryClearance (factorsAt targetParameter) box) :
    BoundaryClearance (polynomial targetParameter) box := by
  rw [target_polynomial_eq_factors]
  exact clearance

def ownerOf {lambda : Gaussian} (box : Box) (proper : box.Proper)
    (clearance : BoundaryClearance (polynomial lambda) box)
    (winding : RFAP.Winding.quadrupledBoxWinding
      (polynomial lambda) box = 4) :
    LocalOwner (polynomial lambda) where
  box := box
  proper := proper
  clearance := clearance
  rawWindingFour := winding

theorem source_above_fixedZero :
    (fixedBox 0).yUpper < sourceParameter.im := by
  change (1 / 16 : Coordinate) < 2
  decide

theorem source_above_fixedOne :
    (fixedBox 1).yUpper < sourceParameter.im := source_above_fixedZero

theorem target_above_fixedZero :
    (fixedBox 0).yUpper < targetParameter.im := by
  change (1 / 16 : Coordinate) < 2
  decide

theorem target_above_fixedOne :
    (fixedBox 1).yUpper < targetParameter.im := target_above_fixedZero

theorem source_in_movingBox :
    movingBox.xLower < sourceParameter.re ∧
      sourceParameter.re < movingBox.xUpper ∧
      movingBox.yLower < sourceParameter.im ∧
      sourceParameter.im < movingBox.yUpper := by
  constructor
  · change (-1 : Coordinate) < 1 / 4
    decide
  constructor
  · change (1 / 4 : Coordinate) < 1
    decide
  constructor
  · change (1 : Coordinate) < 2
    decide
  · change (2 : Coordinate) < 3
    decide

theorem target_in_movingBox :
    movingBox.xLower < targetParameter.re ∧
      targetParameter.re < movingBox.xUpper ∧
      movingBox.yLower < targetParameter.im ∧
      targetParameter.im < movingBox.yUpper := by
  constructor
  · change (-1 : Coordinate) < -(1 / 4)
    decide
  constructor
  · change (-(1 / 4) : Coordinate) < 1
    decide
  exact source_in_movingBox.2.2

theorem source_above_sampleZero :
    (sampleBox 0).yUpper < sourceParameter.im := by
  change (1 / 16 : Coordinate) < 2
  decide

theorem source_above_sampleOne :
    (sampleBox 1).yUpper < sourceParameter.im := source_above_sampleZero

theorem target_above_sampleZero :
    (sampleBox 0).yUpper < targetParameter.im := by
  change (1 / 16 : Coordinate) < 2
  decide

theorem target_above_sampleOne :
    (sampleBox 1).yUpper < targetParameter.im := target_above_sampleZero

theorem source_imaginary_high :
    (1 / 16 : Coordinate) < sourceParameter.im := by
  change (1 / 16 : Coordinate) < 2
  decide

theorem target_imaginary_high :
    (1 / 16 : Coordinate) < targetParameter.im := by
  change (1 / 16 : Coordinate) < 2
  decide

theorem factors_winding_of_sum {lambda : Gaussian} {box : Box}
    (proper : box.Proper)
    (zeroClearance : BoundaryClearance
      (CCL.Riemann.ExplicitLegendreFrame.factor 0) box)
    (movingClearance : BoundaryClearance
      (CCL.Riemann.ExplicitLegendreFrame.factor lambda) box)
    (oneClearance : BoundaryClearance
      (CCL.Riemann.ExplicitLegendreFrame.factor 1) box)
    (sum :
      RFAP.Winding.quadrupledBoxWinding
          (CCL.Riemann.ExplicitLegendreFrame.factor 0) box +
        RFAP.Winding.quadrupledBoxWinding
          (CCL.Riemann.ExplicitLegendreFrame.factor lambda) box +
        RFAP.Winding.quadrupledBoxWinding
          (CCL.Riemann.ExplicitLegendreFrame.factor 1) box = 4) :
    RFAP.Winding.quadrupledBoxWinding (factorsAt lambda) box = 4 := by
  rw [factorsAt,
    RFAP.WindingProduct.quadrupledBoxWinding_mul_of_boundaryClearances
      _ _ box proper
        (RFAP.BoxClearance.BoundaryClearance.mul
          zeroClearance movingClearance) oneClearance,
    RFAP.WindingProduct.quadrupledBoxWinding_mul_of_boundaryClearances
      _ _ box proper zeroClearance movingClearance]
  exact sum

theorem sourceZeroWinding :
    RFAP.Winding.quadrupledBoxWinding
      (polynomial sourceParameter) (fixedBox 0) = 4 := by
  rw [source_polynomial_eq_factors]
  apply factors_winding_of_sum (fixedBox_proper 0)
    (centeredClearance 0 (by decide) (by decide) (by decide) (by decide))
    (aboveClearance sourceParameter source_above_fixedZero)
    (rightClearance 1 (by decide))
  have zeroWinding : RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor 0) (fixedBox 0) = 4 :=
    RFAP.AffineWinding.quadrupledBoxWinding_translatedCoordinate 0
      (by decide) (by decide) (by decide) (by decide)
  have movingWinding : RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor sourceParameter)
        (fixedBox 0) = 0 := by decide
  have oneWinding : RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor 1) (fixedBox 0) = 0 := by
    decide
  rw [zeroWinding, movingWinding, oneWinding]
  ring1

theorem sourceMovingWinding :
    RFAP.Winding.quadrupledBoxWinding
      (polynomial sourceParameter) movingBox = 4 := by
  rw [source_polynomial_eq_factors]
  apply factors_winding_of_sum movingBox_proper
    (belowClearance 0 (by decide))
    (centeredClearance sourceParameter source_in_movingBox.1
      source_in_movingBox.2.1 source_in_movingBox.2.2.1
      source_in_movingBox.2.2.2)
    (belowClearance 1 (by decide))
  have zeroWinding : RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor 0) movingBox = 0 := by decide
  have movingWinding : RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor sourceParameter)
        movingBox = 4 :=
    RFAP.AffineWinding.quadrupledBoxWinding_translatedCoordinate
      sourceParameter source_in_movingBox.1 source_in_movingBox.2.1
      source_in_movingBox.2.2.1 source_in_movingBox.2.2.2
  have oneWinding : RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor 1) movingBox = 0 := by decide
  rw [zeroWinding, movingWinding, oneWinding]
  ring1

theorem sourceOneWinding :
    RFAP.Winding.quadrupledBoxWinding
      (polynomial sourceParameter) (fixedBox 1) = 4 := by
  rw [source_polynomial_eq_factors]
  apply factors_winding_of_sum (fixedBox_proper 1)
    (leftClearance 0 (by decide))
    (aboveClearance sourceParameter source_above_fixedOne)
    (centeredClearance 1 (by decide) (by decide) (by decide) (by decide))
  have zeroWinding : RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor 0) (fixedBox 1) = 0 := by decide
  have movingWinding : RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor sourceParameter)
        (fixedBox 1) = 0 := by decide
  have oneWinding : RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor 1) (fixedBox 1) = 4 :=
    RFAP.AffineWinding.quadrupledBoxWinding_translatedCoordinate 1
      (by decide) (by decide) (by decide) (by decide)
  rw [zeroWinding, movingWinding, oneWinding]
  ring1

theorem targetZeroWinding :
    RFAP.Winding.quadrupledBoxWinding
      (polynomial targetParameter) (fixedBox 0) = 4 := by
  rw [target_polynomial_eq_factors]
  apply factors_winding_of_sum (fixedBox_proper 0)
    (centeredClearance 0 (by decide) (by decide) (by decide) (by decide))
    (aboveClearance targetParameter target_above_fixedZero)
    (rightClearance 1 (by decide))
  have zeroWinding : RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor 0) (fixedBox 0) = 4 :=
    RFAP.AffineWinding.quadrupledBoxWinding_translatedCoordinate 0
      (by decide) (by decide) (by decide) (by decide)
  have movingWinding : RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor targetParameter)
        (fixedBox 0) = 0 := by decide
  have oneWinding : RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor 1) (fixedBox 0) = 0 := by
    decide
  rw [zeroWinding, movingWinding, oneWinding]
  ring1

theorem targetMovingWinding :
    RFAP.Winding.quadrupledBoxWinding
      (polynomial targetParameter) movingBox = 4 := by
  rw [target_polynomial_eq_factors]
  apply factors_winding_of_sum movingBox_proper
    (belowClearance 0 (by decide))
    (centeredClearance targetParameter target_in_movingBox.1
      target_in_movingBox.2.1 target_in_movingBox.2.2.1
      target_in_movingBox.2.2.2)
    (belowClearance 1 (by decide))
  have zeroWinding : RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor 0) movingBox = 0 := by decide
  have movingWinding : RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor targetParameter)
        movingBox = 4 :=
    RFAP.AffineWinding.quadrupledBoxWinding_translatedCoordinate
      targetParameter target_in_movingBox.1 target_in_movingBox.2.1
      target_in_movingBox.2.2.1 target_in_movingBox.2.2.2
  have oneWinding : RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor 1) movingBox = 0 := by decide
  rw [zeroWinding, movingWinding, oneWinding]
  ring1

theorem targetOneWinding :
    RFAP.Winding.quadrupledBoxWinding
      (polynomial targetParameter) (fixedBox 1) = 4 := by
  rw [target_polynomial_eq_factors]
  apply factors_winding_of_sum (fixedBox_proper 1)
    (leftClearance 0 (by decide))
    (aboveClearance targetParameter target_above_fixedOne)
    (centeredClearance 1 (by decide) (by decide) (by decide) (by decide))
  have zeroWinding : RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor 0) (fixedBox 1) = 0 := by decide
  have movingWinding : RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor targetParameter)
        (fixedBox 1) = 0 := by decide
  have oneWinding : RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor 1) (fixedBox 1) = 4 :=
    RFAP.AffineWinding.quadrupledBoxWinding_translatedCoordinate 1
      (by decide) (by decide) (by decide) (by decide)
  rw [zeroWinding, movingWinding, oneWinding]
  ring1

theorem sourceSampleZeroWinding :
    RFAP.Winding.quadrupledBoxWinding
      (polynomial sourceParameter) (sampleBox 0) = 4 := by
  rw [source_polynomial_eq_factors]
  apply factors_winding_of_sum (sampleBox_proper 0)
    (centeredClearance 0 (by decide) (by decide) (by decide) (by decide))
    (aboveClearance sourceParameter source_above_sampleZero)
    (rightClearance 1 (by decide))
  have zeroWinding : RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor 0) (sampleBox 0) = 4 :=
    RFAP.AffineWinding.quadrupledBoxWinding_translatedCoordinate 0
      (by decide) (by decide) (by decide) (by decide)
  have movingWinding : RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor sourceParameter)
        (sampleBox 0) = 0 := by decide
  have oneWinding : RFAP.Winding.quadrupledBoxWinding
      (CCL.Riemann.ExplicitLegendreFrame.factor 1) (sampleBox 0) = 0 := by decide
  rw [zeroWinding, movingWinding, oneWinding]
  ring1

theorem sourceSampleMovingWinding :
    RFAP.Winding.quadrupledBoxWinding
      (polynomial sourceParameter) (sampleBox sourceParameter) = 4 := by
  rw [source_polynomial_eq_factors]
  exact factors_winding_of_sum (sampleBox_proper sourceParameter)
    (belowClearance 0 (by decide))
    (centeredClearance sourceParameter (by decide) (by decide)
      (by decide) (by decide))
    (belowClearance 1 (by decide)) (by decide)

theorem sourceSampleOneWinding :
    RFAP.Winding.quadrupledBoxWinding
      (polynomial sourceParameter) (sampleBox 1) = 4 := by
  rw [source_polynomial_eq_factors]
  exact factors_winding_of_sum (sampleBox_proper 1)
    (leftClearance 0 (by decide))
    (aboveClearance sourceParameter source_above_sampleOne)
    (centeredClearance 1 (by decide) (by decide) (by decide) (by decide))
    (by decide)

theorem targetSampleZeroWinding :
    RFAP.Winding.quadrupledBoxWinding
      (polynomial targetParameter) (sampleBox 0) = 4 := by
  rw [target_polynomial_eq_factors]
  exact factors_winding_of_sum (sampleBox_proper 0)
    (centeredClearance 0 (by decide) (by decide) (by decide) (by decide))
    (aboveClearance targetParameter target_above_sampleZero)
    (rightClearance 1 (by decide)) (by decide)

theorem targetSampleMovingWinding :
    RFAP.Winding.quadrupledBoxWinding
      (polynomial targetParameter) (sampleBox targetParameter) = 4 := by
  rw [target_polynomial_eq_factors]
  exact factors_winding_of_sum (sampleBox_proper targetParameter)
    (belowClearance 0 (by decide))
    (centeredClearance targetParameter (by decide) (by decide)
      (by decide) (by decide))
    (belowClearance 1 (by decide)) (by decide)

theorem targetSampleOneWinding :
    RFAP.Winding.quadrupledBoxWinding
      (polynomial targetParameter) (sampleBox 1) = 4 := by
  rw [target_polynomial_eq_factors]
  exact factors_winding_of_sum (sampleBox_proper 1)
    (leftClearance 0 (by decide))
    (aboveClearance targetParameter target_above_sampleOne)
    (centeredClearance 1 (by decide) (by decide) (by decide) (by decide))
    (by decide)

def sourceZeroOwner : LocalOwner (polynomial sourceParameter) :=
  ownerOf (fixedBox 0) (fixedBox_proper 0)
    (sourcePolynomialClearance
      (broadZeroClearance sourceParameter source_above_fixedZero))
    sourceZeroWinding

def sourceMovingOwner : LocalOwner (polynomial sourceParameter) :=
  ownerOf movingBox movingBox_proper
    (sourcePolynomialClearance
      (broadMovingClearance sourceParameter source_in_movingBox.1
        source_in_movingBox.2.1 source_in_movingBox.2.2.1
        source_in_movingBox.2.2.2)) sourceMovingWinding

def sourceOneOwner : LocalOwner (polynomial sourceParameter) :=
  ownerOf (fixedBox 1) (fixedBox_proper 1)
    (sourcePolynomialClearance
      (broadOneClearance sourceParameter source_above_fixedOne)) sourceOneWinding

def targetZeroOwner : LocalOwner (polynomial targetParameter) :=
  ownerOf (fixedBox 0) (fixedBox_proper 0)
    (targetPolynomialClearance
      (broadZeroClearance targetParameter target_above_fixedZero))
    targetZeroWinding

def targetMovingOwner : LocalOwner (polynomial targetParameter) :=
  ownerOf movingBox movingBox_proper
    (targetPolynomialClearance
      (broadMovingClearance targetParameter target_in_movingBox.1
        target_in_movingBox.2.1 target_in_movingBox.2.2.1
        target_in_movingBox.2.2.2)) targetMovingWinding

def targetOneOwner : LocalOwner (polynomial targetParameter) :=
  ownerOf (fixedBox 1) (fixedBox_proper 1)
    (targetPolynomialClearance
      (broadOneClearance targetParameter target_above_fixedOne)) targetOneWinding

def sourceSampleZero : LocalOwner (polynomial sourceParameter) :=
  ownerOf (sampleBox 0) (sampleBox_proper 0)
    (sourcePolynomialClearance
      (sampleZeroClearance sourceParameter source_above_sampleZero))
    sourceSampleZeroWinding

def sourceSampleMoving : LocalOwner (polynomial sourceParameter) :=
  ownerOf (sampleBox sourceParameter) (sampleBox_proper sourceParameter)
    (sourcePolynomialClearance
      (sampleMovingClearance sourceParameter source_imaginary_high))
    sourceSampleMovingWinding

def sourceSampleOne : LocalOwner (polynomial sourceParameter) :=
  ownerOf (sampleBox 1) (sampleBox_proper 1)
    (sourcePolynomialClearance
      (sampleOneClearance sourceParameter source_above_sampleOne))
    sourceSampleOneWinding

def targetSampleZero : LocalOwner (polynomial targetParameter) :=
  ownerOf (sampleBox 0) (sampleBox_proper 0)
    (targetPolynomialClearance
      (sampleZeroClearance targetParameter target_above_sampleZero))
    targetSampleZeroWinding

def targetSampleMoving : LocalOwner (polynomial targetParameter) :=
  ownerOf (sampleBox targetParameter) (sampleBox_proper targetParameter)
    (targetPolynomialClearance
      (sampleMovingClearance targetParameter target_imaginary_high))
    targetSampleMovingWinding

def targetSampleOne : LocalOwner (polynomial targetParameter) :=
  ownerOf (sampleBox 1) (sampleBox_proper 1)
    (targetPolynomialClearance
      (sampleOneClearance targetParameter target_above_sampleOne))
    targetSampleOneWinding

private theorem finThree_cases (index : Fin 3) :
    index = 0 ∨ index = 1 ∨ index = 2 := by
  rcases index with ⟨value, bound⟩
  omega0

def sourceOwner : Fin 3 -> LocalOwner (polynomial sourceParameter)
  | 0 => sourceZeroOwner
  | 1 => sourceMovingOwner
  | 2 => sourceOneOwner

def targetOwner : Fin 3 -> LocalOwner (polynomial targetParameter)
  | 0 => targetZeroOwner
  | 1 => targetMovingOwner
  | 2 => targetOneOwner

theorem sourceOwner_pairwise : forall left right : Fin 3, left ≠ right ->
    (sourceOwner left).box.Separated (sourceOwner right).box := by
  intro left right different
  rcases finThree_cases left with leftZero | leftOne | leftTwo <;>
    subst left <;>
    rcases finThree_cases right with rightZero | rightOne | rightTwo <;>
    subst right <;>
    first | exact (different rfl).elim | decide

theorem targetOwner_pairwise : forall left right : Fin 3, left ≠ right ->
    (targetOwner left).box.Separated (targetOwner right).box := by
  intro left right different
  rcases finThree_cases left with leftZero | leftOne | leftTwo <;>
    subst left <;>
    rcases finThree_cases right with rightZero | rightOne | rightTwo <;>
    subst right <;>
    first | exact (different rfl).elim | decide

def sourceOwnerFamily :
    CCL.ProgressivePolynomialRoots.OwnerFamily
      (polynomial sourceParameter) 3 where
  owner := sourceOwner
  pairwiseSeparated := sourceOwner_pairwise

def targetOwnerFamily :
    CCL.ProgressivePolynomialRoots.OwnerFamily
      (polynomial targetParameter) 3 where
  owner := targetOwner
  pairwiseSeparated := targetOwner_pairwise

abbrev CoefficientState :=
  CCL.ProgressivePolynomialRoots.CoefficientState
abbrev CoefficientTable :=
  CCL.ProgressivePolynomialRoots.CoefficientTable

def coefficientValues (lambda : Gaussian) : List Gaussian :=
  [-(1 + lambda), lambda, 0]

def coefficientTable (lambda : Gaussian) : CoefficientTable where
  entries := coefficientValues lambda |>.map
    CCL.Riemann.ExplicitLegendreFrame.exactCoefficientState

@[simp] theorem coefficientTable_degree (lambda : Gaussian) :
    (coefficientTable lambda).degree = 3 := rfl

@[simp] theorem coefficientTable_polynomial (lambda : Gaussian) :
    (coefficientTable lambda).polynomial = polynomial lambda := rfl

theorem coefficientTable_allowances_lt (lambda : Gaussian)
    {target : Coordinate} (positive : 0 < target) :
    CCL.ProgressivePolynomialRoots.CoefficientTable.AllowancesLt
      (coefficientTable lambda).entries target := by
  simp only [coefficientTable, coefficientValues, List.map_cons, List.map_nil,
    CCL.ProgressivePolynomialRoots.CoefficientTable.AllowancesLt,
    CCL.Riemann.ExplicitLegendreFrame.exactCoefficientState_allowance]
  exact ⟨positive, positive, positive, trivial⟩

def sourceSquarefree : RFAP.Squarefree.SquarefreeCertificate
    (coefficientTable sourceParameter).polynomial := by
  rw [coefficientTable_polynomial]
  exact CCL.Riemann.ExplicitLegendreFrame.squarefreeAt sourceParameter
    (by decide)

def targetSquarefree : RFAP.Squarefree.SquarefreeCertificate
    (coefficientTable targetParameter).polynomial := by
  rw [coefficientTable_polynomial]
  exact CCL.Riemann.ExplicitLegendreFrame.squarefreeAt targetParameter
    (by decide)

def sourceIsolationInput :
    RFAP.BoxFTA.Input (coefficientTable sourceParameter).polynomial where
  squarefree := sourceSquarefree
  degreeAtLeastTwo := by decide

def targetIsolationInput :
    RFAP.BoxFTA.Input (coefficientTable targetParameter).polynomial where
  squarefree := targetSquarefree
  degreeAtLeastTwo := by decide

def sourceChamber : CCL.FiniteMonodromy.ChamberFrame where
  reference := coefficientTable sourceParameter
  chamber :=
    { degreeAtLeastTwo := by decide
      squarefree := sourceSquarefree
      owners := sourceOwnerFamily
      referenceSmall := coefficientTable_allowances_lt sourceParameter
        (CCL.ProgressivePolynomialRoots.simpleRootChamberTarget_pos
          (coefficientTable sourceParameter) sourceSquarefree sourceOwnerFamily)
      referenceMaximality :=
        (CCL.BoxRFAPBridge.prove sourceIsolationInput).boxes.maximality }

def targetChamber : CCL.FiniteMonodromy.ChamberFrame where
  reference := coefficientTable targetParameter
  chamber :=
    { degreeAtLeastTwo := by decide
      squarefree := targetSquarefree
      owners := targetOwnerFamily
      referenceSmall := coefficientTable_allowances_lt targetParameter
        (CCL.ProgressivePolynomialRoots.simpleRootChamberTarget_pos
          (coefficientTable targetParameter) targetSquarefree targetOwnerFamily)
      referenceMaximality :=
        (CCL.BoxRFAPBridge.prove targetIsolationInput).boxes.maximality }

@[simp] theorem sourceChamber_polynomial :
    sourceChamber.polynomial = polynomial sourceParameter := rfl

@[simp] theorem targetChamber_polynomial :
    targetChamber.polynomial = polynomial targetParameter := rfl

@[simp] theorem sourceChamber_owner_box (index : Fin 3) :
    (sourceChamber.owner index).box = (sourceOwner index).box := rfl

@[simp] theorem targetChamber_owner_box (index : Fin 3) :
    (targetChamber.owner index).box = (targetOwner index).box := rfl

/-! ## Endpoint projection orders -/

def sourceProjectionOwner : Fin 3 -> LocalOwner (polynomial sourceParameter)
  | 0 => sourceSampleZero
  | 1 => sourceSampleMoving
  | 2 => sourceSampleOne

def targetProjectionOwner : Fin 3 -> LocalOwner (polynomial targetParameter)
  | 0 => targetSampleMoving
  | 1 => targetSampleZero
  | 2 => targetSampleOne

def targetProjectionOrder : CCL.FiniteMonodromy.FiniteBijection 3 3 where
  forward
    | 0 => 1
    | 1 => 0
    | 2 => 2
  backward
    | 0 => 1
    | 1 => 0
    | 2 => 2
  backward_forward := by
    intro position
    rcases finThree_cases position with positionZero | positionOne |
      positionTwo <;> subst position <;> rfl
  forward_backward := by
    intro position
    rcases finThree_cases position with positionZero | positionOne |
      positionTwo <;> subst position <;> rfl

def sourceFrame : Frame sourceParameter where
  chamber := sourceChamber
  polynomial_eq := rfl
  labels := CCL.FiniteMonodromy.FiniteBijection.identity 3
  owner_contains := by
    intro label
    rcases finThree_cases label with labelZero | labelOne | labelTwo <;>
      subst label <;> decide
  projectionOrder := CCL.FiniteMonodromy.FiniteBijection.identity 3
  projectionOwner := fun position =>
    CCL.FiniteMonodromy.castOwner sourceChamber_polynomial.symm
      (sourceProjectionOwner position)
  projection_refines := by
    intro position
    change (sourceProjectionOwner position).box.Refines
      (sourceChamber.owner position).box
    rw [sourceChamber_owner_box]
    rcases finThree_cases position with positionZero | positionOne |
      positionTwo <;> subst position <;>
      simp only [sourceProjectionOwner, sourceOwner, sourceSampleZero,
        sourceSampleMoving, sourceSampleOne, sourceZeroOwner,
        sourceMovingOwner, sourceOneOwner, ownerOf,
        RFAP.Boxes.Box.Refines] <;>
      exact ⟨by decide, by decide, by decide, by decide⟩
  projection_xOrdered := by
    intro left right order
    rcases finThree_cases left with leftZero | leftOne | leftTwo <;>
      subst left <;>
      rcases finThree_cases right with rightZero | rightOne | rightTwo <;>
      subst right <;>
      simp only [Fin.isValue, CCL.FiniteMonodromy.castOwner_box] at order ⊢ <;>
      first | omega0 | decide

def targetFrame : Frame targetParameter where
  chamber := targetChamber
  polynomial_eq := rfl
  labels := CCL.FiniteMonodromy.FiniteBijection.identity 3
  owner_contains := by
    intro label
    rcases finThree_cases label with labelZero | labelOne | labelTwo <;>
      subst label <;> decide
  projectionOrder := targetProjectionOrder
  projectionOwner := fun position =>
    CCL.FiniteMonodromy.castOwner targetChamber_polynomial.symm
      (targetProjectionOwner position)
  projection_refines := by
    intro position
    change (targetProjectionOwner position).box.Refines
      (targetChamber.owner (targetProjectionOrder.forward position)).box
    rw [targetChamber_owner_box]
    rcases finThree_cases position with positionZero | positionOne |
      positionTwo <;> subst position <;>
      simp only [targetProjectionOwner, targetProjectionOrder, targetOwner,
        targetSampleZero, targetSampleMoving, targetSampleOne,
        targetZeroOwner, targetMovingOwner, targetOneOwner, ownerOf,
        RFAP.Boxes.Box.Refines] <;>
      exact ⟨by decide, by decide, by decide, by decide⟩
  projection_xOrdered := by
    intro left right order
    rcases finThree_cases left with leftZero | leftOne | leftTwo <;>
      subst left <;>
      rcases finThree_cases right with rightZero | rightOne | rightTwo <;>
      subst right <;>
      simp only [Fin.isValue, CCL.FiniteMonodromy.castOwner_box] at order ⊢ <;>
      first | omega0 | decide

@[simp] theorem sourceFrame_projection_order (position : Fin 3) :
    sourceFrame.projected.ownerIndex position = position := rfl

/-! ## One finite coefficient overlap -/

/-- Coefficient perturbation for moving the Legendre root between any two
displayed Gaussian-rational parameters. -/
def perturbationAt (source target : Gaussian) : GaussianPolynomial :=
  polynomial target - polynomial source

/-- Changing the displayed Legendre parameter is exactly addition of the
finite coefficient perturbation, uniformly in both rational endpoints. -/
theorem target_eq_source_add_perturbationAt (source target : Gaussian) :
    polynomial target = polynomial source + perturbationAt source target := by
  apply RFAP.FinitePolynomialExtensionality.normalized_eq_of_sub_isZero
  · apply RFAP.ComputablePolynomial.DensePolynomial.ext
    rfl
  · exact RFAP.ComputablePolynomial.DensePolynomial.normalize_add _ _
  · apply RFAP.ConstructiveFiniteRoots.difference_isZero_of_candidate_evals
    intro point _member
    rw [RFAP.ComputablePolynomial.DensePolynomial.eval_add,
      perturbationAt, RFAP.ComputablePolynomial.DensePolynomial.eval_sub]
    ring1

theorem polynomial_eval_factorsAt (lambda point : Gaussian) :
    (polynomial lambda).eval point =
      (CCL.Riemann.ExplicitLegendreFrame.factor 0).eval point *
        (CCL.Riemann.ExplicitLegendreFrame.factor lambda).eval point *
        (CCL.Riemann.ExplicitLegendreFrame.factor 1).eval point := by
  rw [polynomial_eval]
  unfold CCL.Riemann.ExplicitLegendreFrame.factor
  simp only [RFAP.AffineWinding.translatedCoordinate_eval]
  ring1

theorem perturbationAt_eval (source target point : Gaussian) :
    (perturbationAt source target).eval point =
      (CCL.Riemann.ExplicitLegendreFrame.factor 0).eval point *
        (CCL.Riemann.ExplicitLegendreFrame.factor 1).eval point *
        (source - target) := by
  rw [perturbationAt, RFAP.ComputablePolynomial.DensePolynomial.eval_sub,
    polynomial_eval, polynomial_eval]
  unfold CCL.Riemann.ExplicitLegendreFrame.factor
  simp only [RFAP.AffineWinding.translatedCoordinate_eval]
  ring1

def perturbation : GaussianPolynomial :=
  perturbationAt sourceParameter targetParameter

theorem target_eq_source_add_perturbation :
    polynomial targetParameter =
      polynomial sourceParameter + perturbation := by
  decide

theorem sourcePolynomial_eval_factors (point : Gaussian) :
    (polynomial sourceParameter).eval point =
      (CCL.Riemann.ExplicitLegendreFrame.factor 0).eval point *
        (CCL.Riemann.ExplicitLegendreFrame.factor sourceParameter).eval point *
        (CCL.Riemann.ExplicitLegendreFrame.factor 1).eval point := by
  exact polynomial_eval_factorsAt sourceParameter point

theorem perturbation_eval (point : Gaussian) :
    perturbation.eval point =
      (CCL.Riemann.ExplicitLegendreFrame.factor 0).eval point *
        (CCL.Riemann.ExplicitLegendreFrame.factor 1).eval point *
        (sourceParameter - targetParameter) := by
  exact perturbationAt_eval sourceParameter targetParameter point

/-- The sharp Rouché estimate for changing only the moving Legendre factor.
Unlike a generic dense coefficient majorant, it retains the two common fixed
factors and therefore sees the exact root-displacement condition. -/
def factorMoveDominanceAt (source target : Gaussian) {box : Box}
    (zeroClearance : BoundaryClearance
      (CCL.Riemann.ExplicitLegendreFrame.factor 0) box)
    (movingClearance : BoundaryClearance
      (CCL.Riemann.ExplicitLegendreFrame.factor source) box)
    (oneClearance : BoundaryClearance
      (CCL.Riemann.ExplicitLegendreFrame.factor 1) box)
    (displacementSmall :
      RFAP.ConstructiveGaussian.Gaussian.normSq
          (source - target) < movingClearance.bound) :
    RFAP.WindingHomotopy.BoundaryNormDominance
      (polynomial source) (perturbationAt source target) box where
  margin := zeroClearance.bound * oneClearance.bound *
    (movingClearance.bound -
      RFAP.ConstructiveGaussian.Gaussian.normSq
        (source - target))
  positive := by
    apply RFAP.ConstructiveFraction.mul_pos_direct
    · exact RFAP.ConstructiveFraction.mul_pos_direct
        zeroClearance.positive oneClearance.positive
    · exact RFAP.ConstructiveFraction.sub_pos_direct displacementSmall
  lower := by
    intro point boundary
    have zeroLower := zeroClearance.lower point boundary
    have movingLower := movingClearance.lower point boundary
    have oneLower := oneClearance.lower point boundary
    have commonLower : zeroClearance.bound * oneClearance.bound ≤
        RFAP.ConstructiveGaussian.Gaussian.normSq
            ((CCL.Riemann.ExplicitLegendreFrame.factor 0).eval point) *
          RFAP.ConstructiveGaussian.Gaussian.normSq
            ((CCL.Riemann.ExplicitLegendreFrame.factor 1).eval point) := by
      exact (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        zeroLower oneClearance.positive.le).trans
          (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            oneLower
            (RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg
              ((CCL.Riemann.ExplicitLegendreFrame.factor 0).eval point)))
    have gapLower : movingClearance.bound -
          RFAP.ConstructiveGaussian.Gaussian.normSq
            (source - target) ≤
        RFAP.ConstructiveGaussian.Gaussian.normSq
            ((CCL.Riemann.ExplicitLegendreFrame.factor source).eval
              point) -
          RFAP.ConstructiveGaussian.Gaussian.normSq
            (source - target) :=
      RFAP.ConstructiveFraction.sub_le_sub_right_direct movingLower _
    have gapNonnegative : 0 ≤ movingClearance.bound -
        RFAP.ConstructiveGaussian.Gaussian.normSq
          (source - target) :=
      (RFAP.ConstructiveFraction.sub_pos_direct displacementSmall).le
    have commonNonnegative : 0 ≤
        RFAP.ConstructiveGaussian.Gaussian.normSq
            ((CCL.Riemann.ExplicitLegendreFrame.factor 0).eval point) *
          RFAP.ConstructiveGaussian.Gaussian.normSq
            ((CCL.Riemann.ExplicitLegendreFrame.factor 1).eval point) :=
      RFAP.ConstructiveFraction.mul_nonneg_direct
        (RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg _)
        (RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg _)
    have scaled :=
      (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        commonLower gapNonnegative).trans
        (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          gapLower commonNonnegative)
    rw [polynomial_eval_factorsAt source,
      perturbationAt_eval source target,
      RFAP.ConstructiveGaussian.Gaussian.normSq_mul,
      RFAP.ConstructiveGaussian.Gaussian.normSq_mul,
      RFAP.ConstructiveGaussian.Gaussian.normSq_mul,
      RFAP.ConstructiveGaussian.Gaussian.normSq_mul]
    calc
      zeroClearance.bound * oneClearance.bound *
          (movingClearance.bound -
            RFAP.ConstructiveGaussian.Gaussian.normSq
              (source - target)) ≤
        (RFAP.ConstructiveGaussian.Gaussian.normSq
            ((CCL.Riemann.ExplicitLegendreFrame.factor 0).eval point) *
          RFAP.ConstructiveGaussian.Gaussian.normSq
            ((CCL.Riemann.ExplicitLegendreFrame.factor 1).eval point)) *
          (RFAP.ConstructiveGaussian.Gaussian.normSq
              ((CCL.Riemann.ExplicitLegendreFrame.factor
                source).eval point) -
            RFAP.ConstructiveGaussian.Gaussian.normSq
              (source - target)) := scaled
      _ =
          RFAP.ConstructiveGaussian.Gaussian.normSq
                ((CCL.Riemann.ExplicitLegendreFrame.factor 0).eval point) *
              RFAP.ConstructiveGaussian.Gaussian.normSq
                ((CCL.Riemann.ExplicitLegendreFrame.factor
                  source).eval point) *
              RFAP.ConstructiveGaussian.Gaussian.normSq
                ((CCL.Riemann.ExplicitLegendreFrame.factor 1).eval point) -
            RFAP.ConstructiveGaussian.Gaussian.normSq
                ((CCL.Riemann.ExplicitLegendreFrame.factor 0).eval point) *
              RFAP.ConstructiveGaussian.Gaussian.normSq
                ((CCL.Riemann.ExplicitLegendreFrame.factor 1).eval point) *
              RFAP.ConstructiveGaussian.Gaussian.normSq
                (source - target) := by ring1

/-- Specialization used by the original upper crossing. -/
def factorMoveDominance {box : Box}
    (zeroClearance : BoundaryClearance
      (CCL.Riemann.ExplicitLegendreFrame.factor 0) box)
    (movingClearance : BoundaryClearance
      (CCL.Riemann.ExplicitLegendreFrame.factor sourceParameter) box)
    (oneClearance : BoundaryClearance
      (CCL.Riemann.ExplicitLegendreFrame.factor 1) box)
    (displacementSmall :
      RFAP.ConstructiveGaussian.Gaussian.normSq
          (sourceParameter - targetParameter) < movingClearance.bound) :
    RFAP.WindingHomotopy.BoundaryNormDominance
      (polynomial sourceParameter) perturbation box :=
  factorMoveDominanceAt sourceParameter targetParameter zeroClearance
    movingClearance oneClearance displacementSmall

def orientedRouche
    (owner : LocalOwner (polynomial sourceParameter))
    (dominance : RFAP.WindingHomotopy.BoundaryNormDominance
      (polynomial sourceParameter) perturbation owner.box) :
    CCL.FiniteMonodromy.OrientedRouche
      (polynomial sourceParameter) (polynomial targetParameter) owner.box where
  perturbation := perturbation
  target_eq_add := target_eq_source_add_perturbation
  dominance := dominance

def zeroDominance : RFAP.WindingHomotopy.BoundaryNormDominance
    (polynomial sourceParameter) perturbation sourceZeroOwner.box :=
  factorMoveDominance
    (centeredClearance 0 (by decide) (by decide) (by decide) (by decide))
    (aboveClearance sourceParameter source_above_fixedZero)
    (rightClearance 1 (by decide)) (by decide)

def movingDominance : RFAP.WindingHomotopy.BoundaryNormDominance
    (polynomial sourceParameter) perturbation sourceMovingOwner.box :=
  factorMoveDominance
    (belowClearance 0 (by decide))
    (centeredClearance sourceParameter source_in_movingBox.1
      source_in_movingBox.2.1 source_in_movingBox.2.2.1
      source_in_movingBox.2.2.2)
    (belowClearance 1 (by decide)) (by decide)

def oneDominance : RFAP.WindingHomotopy.BoundaryNormDominance
    (polynomial sourceParameter) perturbation sourceOneOwner.box :=
  factorMoveDominance
    (leftClearance 0 (by decide))
    (aboveClearance sourceParameter source_above_fixedOne)
    (centeredClearance 1 (by decide) (by decide) (by decide) (by decide))
    (by decide)

def zeroBridge : CCL.FiniteMonodromy.OwnerBridge
    (polynomial sourceParameter) (polynomial targetParameter) :=
  CCL.FiniteMonodromy.OwnerBridge.ofForward sourceZeroOwner
    (orientedRouche sourceZeroOwner zeroDominance)

def movingBridge : CCL.FiniteMonodromy.OwnerBridge
    (polynomial sourceParameter) (polynomial targetParameter) :=
  CCL.FiniteMonodromy.OwnerBridge.ofForward sourceMovingOwner
    (orientedRouche sourceMovingOwner movingDominance)

def oneBridge : CCL.FiniteMonodromy.OwnerBridge
    (polynomial sourceParameter) (polynomial targetParameter) :=
  CCL.FiniteMonodromy.OwnerBridge.ofForward sourceOneOwner
    (orientedRouche sourceOneOwner oneDominance)

def bridgeAt : Fin 3 -> CCL.FiniteMonodromy.OwnerBridge
    (polynomial sourceParameter) (polynomial targetParameter)
  | 0 => zeroBridge
  | 1 => movingBridge
  | 2 => oneBridge

def chamberOverlap : CCL.FiniteMonodromy.ChamberOverlap
    sourceChamber targetChamber where
  matching := CCL.FiniteMonodromy.FiniteBijection.identity 3
  bridge := bridgeAt
  bridge_refines_left := by
    intro index
    rcases finThree_cases index with indexZero | indexOne | indexTwo <;>
      subst index <;>
      exact RFAP.Boxes.Box.refines_refl _
  bridge_refines_right := by
    intro index
    rcases finThree_cases index with indexZero | indexOne | indexTwo <;>
      subst index <;>
      exact RFAP.Boxes.Box.refines_refl _

theorem crossingGeometry : CCL.Knot.ProjectedCrossings.CrossingGeometry
    sourceFrame.projected targetFrame.projected chamberOverlap
      CCL.Riemann.LegendreConventions.lowerPositive where
  heightSeparated := by
    change (fixedBox 0).yUpper < movingBox.yLower
    change (1 / 16 : Coordinate) < 1
    decide

/-- The persistent moving root crosses the zero root positively: the zero
owner starts on the left and remains strictly below it in the common bridge
chart. -/
def projectedOverlap : CCL.Knot.ProjectedCrossings.ProjectedOverlap
    sourceFrame.projected targetFrame.projected :=
  .crossing chamberOverlap CCL.Riemann.LegendreConventions.lowerPositive
    crossingGeometry (by
      intro position
      rcases finThree_cases position with positionZero | positionOne |
        positionTwo <;> subst position <;> rfl)

@[simp] theorem projectedOverlap_word : projectedOverlap.word =
    [CCL.Riemann.LegendreConventions.lowerPositive] := rfl

def sheetBound : Coordinate :=
  min zeroBridge.leftClearance.bound
    (min zeroBridge.rightClearance.bound
      (min movingBridge.leftClearance.bound
        (min movingBridge.rightClearance.bound
          (min oneBridge.leftClearance.bound
            oneBridge.rightClearance.bound))))

theorem sheetBound_positive : 0 < sheetBound := by
  unfold sheetBound
  exact lt_min zeroBridge.leftClearance.positive
    (lt_min zeroBridge.rightClearance.positive
      (lt_min movingBridge.leftClearance.positive
        (lt_min movingBridge.rightClearance.positive
          (lt_min oneBridge.leftClearance.positive
            oneBridge.rightClearance.positive))))

def sheetClearance : BridgeClearance sourceFrame targetFrame chamberOverlap where
  bound := sheetBound
  positive := sheetBound_positive
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

def geometry : AxisSegment sourceParameter targetParameter :=
  .horizontal (1 / 4) (-(1 / 4)) 2

def geometrySafe : AxisSegment.Safe geometry where
  avoidsZero :=
    { bound := 1
      positive := by decide
      lower := by decide }
  avoidsOne :=
    { bound := 1
      positive := by decide
      lower := by decide }

/-- The complete concrete pilot segment, including singularity avoidance,
the Rouché owner overlap, square-root clearance, and extracted crossing. -/
def segment : Segment sourceFrame targetFrame :=
  Segment.ofProjectedOverlap geometry geometrySafe projectedOverlap
    sheetClearance

@[simp] theorem segment_crossings : segment.crossings =
    [CCL.Riemann.LegendreConventions.lowerPositive] := rfl

def path : Path sourceFrame targetFrame :=
  .cons segment (.nil targetFrame)

@[simp] theorem path_stepCount : path.stepCount = 1 := rfl

@[simp] theorem path_word : path.word =
    [CCL.Riemann.LegendreConventions.lowerPositive] := rfl

/-- The same certified event controls both the extracted braid permutation
and the persistent chamber-owner transport. -/
theorem owner_transport_agrees (position : Fin 3) :
    path.ownerTransport.forward (sourceFrame.projected.ownerIndex position) =
      targetFrame.projected.ownerIndex
        (path.word.permutation.forward position) :=
  path.ownerTransport_agrees position

/-! ## Actual endpoint period programs -/

/-- Unconditional prepared standard periods on the source fibre. -/
def sourceFibre : CCL.Riemann.LegendreGaussManin.FibreData sourceFrame where
  periods :=
    CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData
      (CCL.Riemann.LegendreGaussManin.frameCurve sourceFrame)

/-- Unconditional prepared standard periods on the target fibre. -/
def targetFibre : CCL.Riemann.LegendreGaussManin.FibreData targetFrame where
  periods :=
    CCL.Riemann.PreparedRefinementPrograms.automaticStandardPeriodData
      (CCL.Riemann.LegendreGaussManin.frameCurve targetFrame)

/-- The concrete source-labelled homology basis continued to the actual
target fibre.  Its endpoint periods are defined from the target's certified
period programs and the dual of the extracted braid action. -/
def endpointContinuation :
    CCL.Riemann.LegendreGaussManin.EndpointContinuation path where
  source := sourceFibre
  target := targetFibre

/-- The extracted positive lower half-twist acts on the endpoint period
column by the transpose matrix `[[1,0],[-1,1]]`. -/
theorem path_periodMatrix :
    CCL.Riemann.LegendrePicardLefschetz.periodMatrix path.word =
      CCL.Riemann.LegendrePicardLefschetz.matrix₂ 1 0 (-1) 1 := by
  rw [path_word]
  rfl

def endpoint_periods_explicit :
    CCL.Riemann.LegendreGaussManin.VectorEquivalent
      endpointContinuation.periods
      (CCL.Riemann.LegendreGaussManin.matrixAction
        (CCL.Riemann.LegendrePicardLefschetz.matrix₂ 1 0 (-1) 1)
        targetFibre.rawPeriods) := by
  rw [CCL.Riemann.LegendreGaussManin.EndpointContinuation.periods,
    path_periodMatrix]
  exact CCL.Riemann.LegendreGaussManin.VectorEquivalent.refl _

end CCL.Riemann.ExplicitLegendreSegment
