module
import Purelib.Data.Int.Arithmetic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Legendre.Paths
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Constant
import Purelib.Polynomial.Clearance.Box.Boundary.Operations
import Purelib.Polynomial.Dense.Gaussian.Constants
public import Purelib.Polynomial.Dense.Gaussian.Linear.Translated
import Purelib.Polynomial.Dense.Multiplication
public import Purelib.Polynomial.Winding.Box.Basic
import Purelib.Polynomial.Winding.Box.Constant
import Purelib.Polynomial.Winding.Box.HalfPlane
import Purelib.Polynomial.Winding.Box.Product
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Tactic.Ring

/-!
# Boundary-clear affine factors in rational half-planes

Multiplication by a retained nonzero Gaussian constant carries the factor
values into the positive real half-plane. The product winding certificate
then gives the exact zero winding on the original proper box.
-/

namespace Purelib.Polynomial.Winding.Affine.HalfPlane
public section
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Polynomial

/-- The vertical versions of the finite half-plane winding calculation used
by the crossing frames.

The scalar transport retains the original factor, box and boundary witness. Its winding identity uses the same retained
nonzero constant and factor values. -/
theorem factor_winding_zero_of_below (root : Gaussian.Basic.Canonical) {box : Box}
    (proper : box.Proper)
    (clearance : Clearance.Box.Boundary.Basic.BoundaryClearance
      (Dense.Gaussian.Linear.Translated.translatedCoordinate root) box)
    (below : root.im < box.yLower) :
    Winding.Box.Basic.quadrupledBoxWinding
      (Dense.Gaussian.Linear.Translated.translatedCoordinate root) box = 0 := open Purelib in by
  let minusI : Gaussian.Basic.Canonical := Curves.Legendre.Paths.gaussian 0 (-1)
  let constant := Dense.Gaussian.Constants.gaussianConstant minusI
  have minusINonzero : minusI ≠ 0 := by decide
  let constantClearance :=
    Clearance.Box.Boundary.Constant.gaussianConstant_boundaryClearance minusINonzero box
  have productZero : Winding.Box.Basic.quadrupledBoxWinding
      (constant * Dense.Gaussian.Linear.Translated.translatedCoordinate root) box = 0 := by
    apply Winding.Box.HalfPlane.quadrupledBoxWinding_eq_zero_of_positive_real
      (constant * Dense.Gaussian.Linear.Translated.translatedCoordinate root) box proper
      (Clearance.Box.Boundary.Basic.BoundaryClearance.mul constantClearance clearance)
    intro point boundary
    rw [Dense.Basic.DensePolynomial.eval_mul,
      Dense.Gaussian.Constants.gaussianConstant_eval,
      Dense.Gaussian.Linear.Translated.translatedCoordinate_eval]
    change 0 < (minusI * (point - root)).re
    dsimp only [minusI, Curves.Legendre.Paths.gaussian,
      Gaussian.Basic.mul_re,
      Gaussian.Basic.sub_re,
      Gaussian.Basic.sub_im]
    rw [show (0 : Fraction.Rational) * (point.re - root.re) -
        (-1) * (point.im - root.im) = point.im - root.im by ring1]
    exact Fraction.Order.Arithmetic.sub_pos_direct
      (below.trans_le boundary.1.2.2.1)
  have productFormula :=
    Winding.Box.Product.quadrupledBoxWinding_mul_of_boundaryClearances
      constant (Dense.Gaussian.Linear.Translated.translatedCoordinate root) box proper
      constantClearance clearance
  have constantZero : Winding.Box.Basic.quadrupledBoxWinding constant box = 0 :=
    Winding.Box.Constant.quadrupledBoxWinding_gaussianConstant minusINonzero box
  rw [productZero, constantZero] at productFormula
  rewrite [Data.Int.Arithmetic.zero_add] at productFormula
  exact productFormula.symm

/-- An affine factor with root strictly above a proper, boundary-clear box has zero winding.

Multiplication by the constant imaginary unit places the boundary values in the positive real half-plane. -/
theorem factor_winding_zero_of_above (root : Gaussian.Basic.Canonical) {box : Box}
    (proper : box.Proper)
    (clearance : Clearance.Box.Boundary.Basic.BoundaryClearance
      (Dense.Gaussian.Linear.Translated.translatedCoordinate root) box)
    (above : box.yUpper < root.im) :
    Winding.Box.Basic.quadrupledBoxWinding
      (Dense.Gaussian.Linear.Translated.translatedCoordinate root) box = 0 := open Purelib in by
  let i : Gaussian.Basic.Canonical := Curves.Legendre.Paths.gaussian 0 1
  let constant := Dense.Gaussian.Constants.gaussianConstant i
  have iNonzero : i ≠ 0 := by decide
  let constantClearance :=
    Clearance.Box.Boundary.Constant.gaussianConstant_boundaryClearance iNonzero box
  have productZero : Winding.Box.Basic.quadrupledBoxWinding
      (constant * Dense.Gaussian.Linear.Translated.translatedCoordinate root) box = 0 := by
    apply Winding.Box.HalfPlane.quadrupledBoxWinding_eq_zero_of_positive_real
      (constant * Dense.Gaussian.Linear.Translated.translatedCoordinate root) box proper
      (Clearance.Box.Boundary.Basic.BoundaryClearance.mul constantClearance clearance)
    intro point boundary
    rw [Dense.Basic.DensePolynomial.eval_mul,
      Dense.Gaussian.Constants.gaussianConstant_eval,
      Dense.Gaussian.Linear.Translated.translatedCoordinate_eval]
    change 0 < (i * (point - root)).re
    dsimp only [i, Curves.Legendre.Paths.gaussian,
      Gaussian.Basic.mul_re,
      Gaussian.Basic.sub_re,
      Gaussian.Basic.sub_im]
    rw [show (0 : Fraction.Rational) * (point.re - root.re) -
        1 * (point.im - root.im) = root.im - point.im by ring1]
    exact Fraction.Order.Arithmetic.sub_pos_direct
      (boundary.1.2.2.2.trans_lt above)
  have productFormula :=
    Winding.Box.Product.quadrupledBoxWinding_mul_of_boundaryClearances
      constant (Dense.Gaussian.Linear.Translated.translatedCoordinate root) box proper
      constantClearance clearance
  have constantZero : Winding.Box.Basic.quadrupledBoxWinding constant box = 0 :=
    Winding.Box.Constant.quadrupledBoxWinding_gaussianConstant iNonzero box
  rw [productZero, constantZero] at productFormula
  rewrite [Data.Int.Arithmetic.zero_add] at productFormula
  exact productFormula.symm

/-- An affine factor whose root lies strictly left of a proper rational box
has zero winding there.  The proof uses the finite half-plane Cauchy scanner,
not an ambient argument principle. -/
theorem factor_winding_zero_of_left (root : Gaussian.Basic.Canonical) {box : Box}
    (proper : box.Proper)
    (clearance : Clearance.Box.Boundary.Basic.BoundaryClearance
      (Dense.Gaussian.Linear.Translated.translatedCoordinate root) box)
    (left : root.re < box.xLower) :
    Winding.Box.Basic.quadrupledBoxWinding
      (Dense.Gaussian.Linear.Translated.translatedCoordinate root) box = 0 := by
  apply Winding.Box.HalfPlane.quadrupledBoxWinding_eq_zero_of_positive_real
    (Dense.Gaussian.Linear.Translated.translatedCoordinate root) box proper clearance
  intro point boundary
  rw [Dense.Gaussian.Linear.Translated.translatedCoordinate_eval]
  change 0 < point.re - root.re
  exact Fraction.Order.Arithmetic.sub_pos_direct
    (left.trans_le boundary.1.1)

/-- The reflected half-plane calculation for an affine root strictly right
of the box.  Multiplication by the exact constant `-1` makes the real part
positive; finite winding multiplicativity then cancels the constant's zero
winding.

The scalar transport retains the original factor, box and boundary witness. Its winding identity uses the same retained
nonzero constant and factor values. -/
theorem factor_winding_zero_of_right (root : Gaussian.Basic.Canonical) {box : Box}
    (proper : box.Proper)
    (clearance : Clearance.Box.Boundary.Basic.BoundaryClearance
      (Dense.Gaussian.Linear.Translated.translatedCoordinate root) box)
    (right : box.xUpper < root.re) :
    Winding.Box.Basic.quadrupledBoxWinding
      (Dense.Gaussian.Linear.Translated.translatedCoordinate root) box = 0 := by
  let minusOne : Gaussian.Basic.Canonical := -1
  let constant := Dense.Gaussian.Constants.gaussianConstant minusOne
  have minusOneNonzero : minusOne ≠ 0 := by decide
  let constantClearance :=
    Clearance.Box.Boundary.Constant.gaussianConstant_boundaryClearance minusOneNonzero box
  have productZero : Winding.Box.Basic.quadrupledBoxWinding
      (constant * Dense.Gaussian.Linear.Translated.translatedCoordinate root) box = 0 := by
    apply Winding.Box.HalfPlane.quadrupledBoxWinding_eq_zero_of_positive_real
      (constant * Dense.Gaussian.Linear.Translated.translatedCoordinate root) box proper
      (Clearance.Box.Boundary.Basic.BoundaryClearance.mul constantClearance clearance)
    intro point boundary
    rw [Dense.Basic.DensePolynomial.eval_mul,
      Dense.Gaussian.Constants.gaussianConstant_eval,
      Dense.Gaussian.Linear.Translated.translatedCoordinate_eval]
    rw [show minusOne * (point - root) = -(point - root) by
      ring1]
    rw [Gaussian.Basic.neg_re,
      Gaussian.Basic.sub_re]
    have reflected : -(point.re - root.re) = root.re - point.re := by ring1
    rewrite [reflected]
    exact Fraction.Order.Arithmetic.sub_pos_direct (boundary.1.2.1.trans_lt right)
  have productFormula :=
    Winding.Box.Product.quadrupledBoxWinding_mul_of_boundaryClearances
      constant (Dense.Gaussian.Linear.Translated.translatedCoordinate root) box proper
      constantClearance clearance
  have constantZero : Winding.Box.Basic.quadrupledBoxWinding constant box = 0 :=
    Winding.Box.Constant.quadrupledBoxWinding_gaussianConstant
      minusOneNonzero box
  rw [productZero, constantZero] at productFormula
  rewrite [Data.Int.Arithmetic.zero_add] at productFormula
  exact productFormula.symm

end
end Purelib.Polynomial.Winding.Affine.HalfPlane
