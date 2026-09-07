import CCL.Riemann.LegendreSquarefree
import RFAP.Geometry.HalfPlane

/-!
# Factorwise finite geometry for Legendre cubics

These reusable rational clearance and winding lemmas depend only on the
three displayed affine factors.  Concrete path examples and executable
period clients can therefore share them without importing one another.
-/

namespace CCL.Riemann.LegendreFactorGeometry

open CCL.Riemann.LegendrePaths

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial :=
  RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Box := RFAP.Boxes.Box
abbrev BoundaryClearance := RFAP.BoxClearance.BoundaryClearance

/-- One displayed affine factor `x - root`. -/
def factor (root : Gaussian) : GaussianPolynomial :=
  RFAP.AffineWinding.translatedCoordinate root

/-- The three Legendre factors in logical branch order. -/
def factors (lambda : Gaussian) : GaussianPolynomial :=
  (factor 0 * factor lambda) * factor 1

theorem polynomial_eq_factors (lambda : Gaussian) :
    polynomial lambda = factors lambda := by
  apply RFAP.FinitePolynomialExtensionality.normalized_eq_of_sub_isZero
  · apply RFAP.ComputablePolynomial.DensePolynomial.ext
    rfl
  · exact RFAP.ComputablePolynomial.DensePolynomial.normalize_mul _ _
  · apply RFAP.ConstructiveFiniteRoots.difference_isZero_of_candidate_evals
    intro point _member
    rw [polynomial_eval, factors,
      RFAP.ComputablePolynomial.DensePolynomial.eval_mul,
      RFAP.ComputablePolynomial.DensePolynomial.eval_mul]
    unfold factor
    simp only [RFAP.AffineWinding.translatedCoordinate_eval]
    ring1

def centeredClearance (root : Gaussian) {box : Box}
    (left : box.xLower < root.re) (right : root.re < box.xUpper)
    (below : box.yLower < root.im) (above : root.im < box.yUpper) :
    BoundaryClearance (factor root) box :=
  RFAP.AffineWinding.translatedCoordinate_boundaryClearanceBox root
    left right below above

def aboveClearance (root : Gaussian) {box : Box}
    (above : box.yUpper < root.im) :
    BoundaryClearance (factor root) box :=
  RFAP.AffineWinding.translatedCoordinate_boundaryClearance_of_above
    root above

def leftClearance (root : Gaussian) {box : Box}
    (left : root.re < box.xLower) :
    BoundaryClearance (factor root) box :=
  RFAP.AffineWinding.translatedCoordinate_boundaryClearance_of_left root left

def rightClearance (root : Gaussian) {box : Box}
    (right : box.xUpper < root.re) :
    BoundaryClearance (factor root) box :=
  RFAP.AffineWinding.translatedCoordinate_boundaryClearance_of_right root right

def factorsClearance {lambda : Gaussian} {box : Box}
    (zero : BoundaryClearance (factor 0) box)
    (moving : BoundaryClearance (factor lambda) box)
    (one : BoundaryClearance (factor 1) box) :
    BoundaryClearance (factors lambda) box :=
  RFAP.BoxClearance.BoundaryClearance.mul
    (RFAP.BoxClearance.BoundaryClearance.mul zero moving) one

theorem factor_winding_zero_of_left (root : Gaussian) {box : Box}
    (proper : box.Proper) (clearance : BoundaryClearance (factor root) box)
    (left : root.re < box.xLower) :
    RFAP.Winding.quadrupledBoxWinding (factor root) box = 0 := by
  apply RFAP.HalfPlane.quadrupledBoxWinding_eq_zero_of_positive_real
    (factor root) box proper clearance
  intro point boundary
  rw [factor, RFAP.AffineWinding.translatedCoordinate_eval]
  change 0 < point.re - root.re
  exact RFAP.ConstructiveFraction.sub_pos_direct
    (left.trans_le boundary.1.1)

theorem factor_winding_zero_of_right (root : Gaussian) {box : Box}
    (proper : box.Proper) (clearance : BoundaryClearance (factor root) box)
    (right : box.xUpper < root.re) :
    RFAP.Winding.quadrupledBoxWinding (factor root) box = 0 := by
  let minusOne : Gaussian := -1
  let constant := RFAP.GlobalWinding.gaussianConstant minusOne
  have minusOneNonzero : minusOne ≠ 0 := by decide
  let constantClearance :=
    RFAP.GlobalWinding.gaussianConstant_boundaryClearance minusOneNonzero box
  have productZero : RFAP.Winding.quadrupledBoxWinding
      (constant * factor root) box = 0 := by
    apply RFAP.HalfPlane.quadrupledBoxWinding_eq_zero_of_positive_real
      (constant * factor root) box proper
      (RFAP.BoxClearance.BoundaryClearance.mul constantClearance clearance)
    intro point boundary
    rw [RFAP.ComputablePolynomial.DensePolynomial.eval_mul,
      RFAP.GlobalWinding.gaussianConstant_eval, factor,
      RFAP.AffineWinding.translatedCoordinate_eval]
    rw [show minusOne * (point - root) = -(point - root) by
      exact neg_one_mul (point - root)]
    rw [RFAP.ConstructiveGaussian.Gaussian.neg_re,
      RFAP.ConstructiveGaussian.Gaussian.sub_re]
    simpa only [neg_sub] using RFAP.ConstructiveFraction.sub_pos_direct
      (boundary.1.2.1.trans_lt right)
  have productFormula :=
    RFAP.WindingProduct.quadrupledBoxWinding_mul_of_boundaryClearances
      constant (factor root) box proper constantClearance clearance
  have constantZero : RFAP.Winding.quadrupledBoxWinding constant box = 0 :=
    RFAP.GlobalWinding.quadrupledBoxWinding_gaussianConstant
      minusOneNonzero box
  rw [productZero, constantZero] at productFormula
  simpa only [Int.zero_add] using productFormula.symm

theorem factors_winding_of_sum {lambda : Gaussian} {box : Box}
    (proper : box.Proper)
    (zeroClearance : BoundaryClearance (factor 0) box)
    (movingClearance : BoundaryClearance (factor lambda) box)
    (oneClearance : BoundaryClearance (factor 1) box)
    (sum :
      RFAP.Winding.quadrupledBoxWinding (factor 0) box +
        RFAP.Winding.quadrupledBoxWinding (factor lambda) box +
        RFAP.Winding.quadrupledBoxWinding (factor 1) box = 4) :
    RFAP.Winding.quadrupledBoxWinding (factors lambda) box = 4 := by
  rw [factors,
    RFAP.WindingProduct.quadrupledBoxWinding_mul_of_boundaryClearances
      _ _ box proper
        (RFAP.BoxClearance.BoundaryClearance.mul
          zeroClearance movingClearance) oneClearance,
    RFAP.WindingProduct.quadrupledBoxWinding_mul_of_boundaryClearances
      _ _ box proper zeroClearance movingClearance]
  exact sum

end CCL.Riemann.LegendreFactorGeometry
