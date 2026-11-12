module
import Purelib.Data.Int.Arithmetic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Outside
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Constant
public import Purelib.Polynomial.Clearance.Box.Boundary.Operations
public import Purelib.Polynomial.Clearance.Box.Boundary.Translated
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Extensionality
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Constants
import Purelib.Polynomial.Dense.Gaussian.Linear.Translated
import Purelib.Polynomial.Dense.Gaussian.NonzeroEvaluation
import Purelib.Polynomial.Dense.Multiplication
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.Polynomial.Winding.Box.Constant
import Purelib.Polynomial.Winding.Box.HalfPlane
import Purelib.Polynomial.Winding.Box.Product
import Purelib.Polynomial.Winding.Box.Affine.Outside
import Purelib.Polynomial.Clearance.Box.Interior

public import Purelib.Curves.Legendre.Paths
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Curves.Legendre.Squarefree
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

/-!
# Factorwise finite geometry for Legendre cubics

These reusable rational clearance and winding lemmas depend only on the
three displayed affine factors.  Concrete path examples and executable
period clients can therefore share them without importing one another.
-/

namespace Purelib.Curves.Legendre.FactorGeometry
public section
open Purelib
open Purelib.Curves.Legendre
open Purelib.Data.Rat
open Purelib.Geometry
open Purelib.Polynomial
open Purelib.Polynomial.Clearance.Box
open Purelib.Polynomial.Clearance.Box.Boundary
open Purelib.Polynomial.Clearance.Box.Boundary.Basic
open Purelib.Polynomial.Clearance.Box.Boundary.Translated
open Purelib.Polynomial.Dense
open Purelib.Polynomial.Dense.Basic
open _root_.Purelib.Polynomial.Dense.Basic renaming CoefficientPolynomial -> Dense
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Polynomial.Dense.Gaussian.Linear
open Purelib.Polynomial.Dense.Gaussian.Linear.Translated
open Purelib.Polynomial.Winding.Box

open Purelib.Curves.Legendre.Paths

/-- Exact rational box coordinates and clearance bounds. -/
abbrev Coordinate := Fraction.Rational
/-- Exact Gaussian rational roots and parameters. -/
abbrev Gaussian := Data.Gaussian.Basic.Canonical
/-- Executable dense Gaussian polynomials for the displayed affine factors. -/
abbrev GaussianPolynomial :=
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial
/-- An exact rational axis-aligned box. -/
abbrev Box := Rational.Box
/-- A retained positive polynomial clearance on the original box boundary. -/
abbrev BoundaryClearance := Boundary.Basic.BoundaryClearance

/-- One displayed affine factor `x - root`. -/
@[expose]
def factor (root : Gaussian) : GaussianPolynomial :=
  Translated.translatedCoordinate root

/-- The three Legendre factors in logical branch order. -/
@[expose]
def factors (lambda : Gaussian) : GaussianPolynomial :=
  (factor 0 * factor lambda) *
    factor 1

/-- The displayed Legendre polynomial equals the product of its three exact affine factors. -/
theorem polynomial_eq_factors (lambda : Gaussian) :
    Paths.polynomial lambda = factors lambda := by
  apply Extensionality.normalized_eq_of_sub_isZero
  · apply DensePolynomial.ext
    rfl
  · exact DensePolynomial.normalize_mul _ _
  · apply NonzeroEvaluation.difference_isZero_of_candidate_evals
    intro point _member
    rw [Paths.polynomial_eval, factors,
      DensePolynomial.eval_mul,
      DensePolynomial.eval_mul]
    unfold factor
    simp only [Translated.translatedCoordinate_eval]
    ring1

/-- Construct affine-factor boundary clearance when its root is strictly inside the original box. -/
@[expose]
def centeredClearance (root : Gaussian) {box : Box}
    (left : box.xLower < root.re) (right : root.re < box.xUpper)
    (below : box.yLower < root.im) (above : root.im < box.yUpper) :
    BoundaryClearance (factor root) box :=
  Affine.translatedCoordinate_boundaryClearanceBox root
    left right below above

/-- Construct affine-factor boundary clearance when its root is strictly above the original box. -/
@[expose]
def aboveClearance (root : Gaussian) {box : Box}
    (above : box.yUpper < root.im) :
    BoundaryClearance (factor root) box :=
  Affine.translatedCoordinate_boundaryClearance_of_above
    root above

/-- Construct affine-factor boundary clearance when its root is strictly left of the original box. -/
@[expose]
def leftClearance (root : Gaussian) {box : Box}
    (left : root.re < box.xLower) :
    BoundaryClearance (factor root) box :=
  Affine.translatedCoordinate_boundaryClearance_of_left root left

/-- Construct affine-factor boundary clearance when its root is strictly right of the original box. -/
@[expose]
def rightClearance (root : Gaussian) {box : Box}
    (right : box.xUpper < root.re) :
    BoundaryClearance (factor root) box :=
  Affine.translatedCoordinate_boundaryClearance_of_right root right

/-- Multiply the retained clearances of the zero, moving and one factors on the same original box. -/
@[expose]
def factorsClearance {lambda : Gaussian} {box : Box}
    (zero : BoundaryClearance (factor 0) box)
    (moving : BoundaryClearance (factor lambda) box)
    (one : BoundaryClearance (factor 1) box) :
    BoundaryClearance (factors lambda) box :=
  BoundaryClearance.mul
    (BoundaryClearance.mul zero moving) one

/-- An affine factor with root strictly left of the proper box has zero finite boundary winding. -/
theorem factor_winding_zero_of_left (root : Gaussian) {box :
  Box}
    (proper : box.Proper) (clearance : BoundaryClearance
      (factor root) box)
    (left : root.re < box.xLower) :
    Winding.Box.Basic.quadrupledBoxWinding (factor root) box = 0 := by
  apply HalfPlane.quadrupledBoxWinding_eq_zero_of_positive_real
    (factor root) box proper clearance
  intro point boundary
  rw [factor, Translated.translatedCoordinate_eval]
  change 0 < point.re - root.re
  exact Fraction.Order.Arithmetic.sub_pos_direct
    (left.trans_le boundary.1.1)

/-- An affine factor with root strictly right of the proper box has zero finite boundary winding.

The scalar transport retains the original factor, box and boundary witness. Its winding identity uses the same retained
nonzero constant and factor values. -/
theorem factor_winding_zero_of_right (root : Gaussian) {box :
  Box}
    (proper : box.Proper) (clearance : BoundaryClearance
      (factor root) box)
    (right : box.xUpper < root.re) :
    Winding.Box.Basic.quadrupledBoxWinding (factor root) box = 0 := by
  let minusOne : Gaussian := -1
  let constant := Constants.gaussianConstant minusOne
  have minusOneNonzero : minusOne ≠ 0 := by decide
  let constantClearance :=
    Constant.gaussianConstant_boundaryClearance minusOneNonzero box
  have productZero : Winding.Box.Basic.quadrupledBoxWinding
      (constant * factor root) box = 0 := by
    apply HalfPlane.quadrupledBoxWinding_eq_zero_of_positive_real
      (constant * factor root) box proper
      (BoundaryClearance.mul constantClearance clearance)
    intro point boundary
    rw [DensePolynomial.eval_mul,
      Constants.gaussianConstant_eval, factor,
      Translated.translatedCoordinate_eval]
    rw [show minusOne * (point - root) = -(point - root) by
      ring1]
    rw [Data.Gaussian.Basic.neg_re,
      Data.Gaussian.Basic.sub_re]
    have reflected : -(point.re - root.re) = root.re - point.re := by ring1
    rewrite [reflected]
    exact Fraction.Order.Arithmetic.sub_pos_direct (boundary.1.2.1.trans_lt right)
  have productFormula :=
    Winding.Box.Product.quadrupledBoxWinding_mul_of_boundaryClearances
      constant (factor root) box proper constantClearance clearance
  have constantZero : Winding.Box.Basic.quadrupledBoxWinding constant box = 0 :=
    Constant.quadrupledBoxWinding_gaussianConstant
      minusOneNonzero box
  rw [productZero, constantZero] at productFormula
  rewrite [Data.Int.Arithmetic.zero_add] at productFormula
  exact productFormula.symm

/-- The three actual affine-factor windings add to the original product winding.

Each factor retains its own quantitative clearance on the same proper
box. The original finite product formula is applied in the displayed
coefficient order, without a prescribed total winding.
-/
theorem factors_winding {lambda : Gaussian} {box : Box}
    (proper : box.Proper)
    (zeroClearance : BoundaryClearance (factor 0) box)
    (movingClearance : BoundaryClearance (factor lambda) box)
    (oneClearance : BoundaryClearance (factor 1) box) :
    Winding.Box.Basic.quadrupledBoxWinding (factors lambda) box =
      Winding.Box.Basic.quadrupledBoxWinding (factor 0) box +
      Winding.Box.Basic.quadrupledBoxWinding (factor lambda) box +
      Winding.Box.Basic.quadrupledBoxWinding (factor 1) box := by
  rw [factors,
    Winding.Box.Product.quadrupledBoxWinding_mul_of_boundaryClearances
      _ _ box proper (BoundaryClearance.mul zeroClearance movingClearance) oneClearance,
    Winding.Box.Product.quadrupledBoxWinding_mul_of_boundaryClearances
      _ _ box proper zeroClearance movingClearance]

/-- If the three retained factor windings sum to four, their product has quadrupled box winding four. -/
theorem factors_winding_of_sum {lambda : Gaussian} {box :
  Box}
    (proper : box.Proper)
    (zeroClearance : BoundaryClearance (factor 0) box)
    (movingClearance : BoundaryClearance (factor lambda)
      box)
    (oneClearance : BoundaryClearance (factor 1) box)
    (sum :
      Winding.Box.Basic.quadrupledBoxWinding (factor 0) box +
        Winding.Box.Basic.quadrupledBoxWinding (factor lambda) box +
        Winding.Box.Basic.quadrupledBoxWinding (factor 1) box = 4) :
    Winding.Box.Basic.quadrupledBoxWinding (factors lambda) box = 4 := by
  exact (factors_winding proper zeroClearance movingClearance oneClearance).trans sum

/-- Excluding all three exact branch points gives zero winding on the actual box.

Each failed membership has an explicit rational outside side. The same
side supplies the original affine clearance and zero-winding certificate;
finite multiplicativity retains the displayed Legendre polynomial.
-/
theorem winding_zero_of_outside {lambda : Gaussian} {box : Box}
    (proper : box.Proper) (zero : box.OutsideSide 0) (moving : box.OutsideSide lambda)
    (one : box.OutsideSide 1) :
    Winding.Box.Basic.quadrupledBoxWinding (Paths.polynomial lambda) box = 0 := by
  let zeroClearance := Affine.translatedCoordinate_boundaryClearance_of_outside 0 zero
  let movingClearance := Affine.translatedCoordinate_boundaryClearance_of_outside lambda moving
  let oneClearance := Affine.translatedCoordinate_boundaryClearance_of_outside 1 one
  have zeroWinding : Winding.Box.Basic.quadrupledBoxWinding (factor 0) box = 0 :=
    Winding.Box.Affine.Outside.quadrupledBoxWinding_translatedCoordinate_of_outside proper zero
  have movingWinding : Winding.Box.Basic.quadrupledBoxWinding (factor lambda) box = 0 :=
    Winding.Box.Affine.Outside.quadrupledBoxWinding_translatedCoordinate_of_outside proper moving
  have oneWinding : Winding.Box.Basic.quadrupledBoxWinding (factor 1) box = 0 :=
    Winding.Box.Affine.Outside.quadrupledBoxWinding_translatedCoordinate_of_outside proper one
  rw [polynomial_eq_factors lambda, factors_winding proper zeroClearance movingClearance oneClearance,
    zeroWinding, movingWinding, oneWinding]
  rfl

/-- A nonzero-winding box contains at least one of the three original exact branch points.

The finite rational membership decisions retain the actual box. If all
three are excluded, their explicit outside-side windings contradict the
supplied nonzero winding; no root selection or limit is used.
-/
theorem winding_contains_branch {lambda : Gaussian} {box : Box} (proper : box.Proper)
    (winding : Winding.Box.Basic.quadrupledBoxWinding (Paths.polynomial lambda) box ≠ 0) :
    box.Contains 0 ∨ box.Contains lambda ∨ box.Contains 1 := by
  by_cases zero : box.Contains 0
  · exact Or.inl zero
  by_cases moving : box.Contains lambda
  · exact Or.inr (Or.inl moving)
  by_cases one : box.Contains 1
  · exact Or.inr (Or.inr one)
  exact (winding (winding_zero_of_outside proper (Rational.Box.outsideSide zero)
    (Rational.Box.outsideSide moving) (Rational.Box.outsideSide one))).elim

/-- Every clear nonzero-winding Legendre box at a real parameter strictly crosses the real axis.

One of the original exact branch points belongs to this same box. The
original boundary-clearance law places that point strictly inside; all
three branch points have imaginary coordinate zero.
-/
theorem real_axis_of_winding {lambda : Gaussian} {box : Box} (real : lambda.im = 0)
    (proper : box.Proper) (clearance : BoundaryClearance (Paths.polynomial lambda) box)
    (winding : Winding.Box.Basic.quadrupledBoxWinding (Paths.polynomial lambda) box ≠ 0) :
    box.yLower < 0 ∧ 0 < box.yUpper := by
  rcases winding_contains_branch proper winding with zero | moving | one
  · have strict := clearance.root_strictContains zero (Paths.polynomial_zero lambda)
    exact ⟨strict.2.2.1, strict.2.2.2⟩
  · have strict := clearance.root_strictContains moving (Paths.polynomial_lambda lambda)
    have below := strict.2.2.1
    have above := strict.2.2.2
    rw [real] at below above
    exact ⟨below, above⟩
  · have strict := clearance.root_strictContains one (Paths.polynomial_one lambda)
    exact ⟨strict.2.2.1, strict.2.2.2⟩

/-- Read a logical branch label from the same nonzero-winding box.

The three displayed exact points are checked in their original logical
order. The nonzero-winding theorem discharges the impossible all-excluded
branch. The result retains exact membership in the supplied box, without
creating a new root or replacing its retained winding owner.
-/
def branchInBox {lambda : Gaussian} {box : Box} (proper : box.Proper)
    (winding : Winding.Box.Basic.quadrupledBoxWinding (Paths.polynomial lambda) box ≠ 0) :
    { label : Fin 3 // box.Contains (Paths.branchPoint lambda label) } :=
  if zero : box.Contains 0 then ⟨0, zero⟩
  else if moving : box.Contains lambda then ⟨1, moving⟩
  else if one : box.Contains 1 then ⟨2, one⟩
  else False.elim (winding (winding_zero_of_outside proper (Rational.Box.outsideSide zero)
    (Rational.Box.outsideSide moving) (Rational.Box.outsideSide one)))

end
end Purelib.Curves.Legendre.FactorGeometry
