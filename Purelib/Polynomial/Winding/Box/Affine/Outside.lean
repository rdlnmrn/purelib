module

public import Purelib.Polynomial.Winding.Box.Affine
public import Purelib.Geometry.Rational.Box.Outside
public import Purelib.Polynomial.Dense.Gaussian.Roots.Linear
import Purelib.Polynomial.Winding.Box.HalfPlane
import Purelib.Polynomial.Winding.Box.Product
import Purelib.Polynomial.Winding.Box.Constant
import Purelib.Polynomial.Clearance.Box.Boundary.Constant
import Purelib.Polynomial.Clearance.Box.Boundary.Operations
import Purelib.Polynomial.Clearance.Box.Boundary.Translated
import Purelib.Polynomial.Dense.Gaussian.Linear.Translated
import Purelib.Polynomial.Dense.Gaussian.Constants
import Purelib.Polynomial.Dense.Gaussian.Roots.Linear.Evaluation
import Purelib.Polynomial.Dense.Multiplication
import Purelib.Data.Gaussian.Constants
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-!
# Winding of a translated coordinate with an excluded zero

A retained outside side puts the translated coordinate in one open half-plane.
An explicit coordinate-axis rotation gives positive real part, and finite
product winding removes that same nonzero constant rotation.
-/

namespace Purelib.Polynomial.Winding.Box.Affine.Outside

open Purelib.Data
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Rational
open Purelib.Polynomial

/-- A nonzero constant rotation into the right half-plane certifies zero winding of the original polynomial. -/
private theorem winding_zero_of_rotation
    {polynomial : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {box : Box}
    (proper : box.Proper) (clearance : Clearance.Box.Boundary.Basic.BoundaryClearance polynomial box)
    (phase : Canonical) (nonzero : phase ≠ 0)
    (positive : ∀ point : Canonical, Box.Boundary.OnBoxBoundary box point →
      0 < (phase * polynomial.eval point).re) :
    Winding.Box.Basic.quadrupledBoxWinding polynomial box = 0 := by
  let constant := Dense.Gaussian.Constants.gaussianConstant phase
  let constantClearance := Clearance.Box.Boundary.Constant.gaussianConstant_boundaryClearance nonzero box
  have zero := Winding.Box.HalfPlane.quadrupledBoxWinding_eq_zero_of_positive_real
    (constant * polynomial) box proper (constantClearance.mul clearance) (by
      intro point boundary
      rewrite [Dense.Basic.DensePolynomial.eval_mul, Dense.Gaussian.Constants.gaussianConstant_eval]
      exact positive point boundary)
  rewrite [Winding.Box.Product.quadrupledBoxWinding_mul_of_boundaryClearances
    constant polynomial box proper constantClearance clearance,
    Winding.Box.Constant.quadrupledBoxWinding_gaussianConstant nonzero box] at zero
  exact (Int.zero_add _).symm.trans zero

/-- An original translated coordinate has zero winding when its zero has a certified strict outside side.

The same side supplies quantitative clearance on the original box. Four
explicit unit rotations cover the four coordinate sides without searching
for a root or changing the polynomial's zero.
-/
public theorem quadrupledBoxWinding_translatedCoordinate_of_outside
    {root : Canonical} {box : Box} (proper : box.Proper) (side : box.OutsideSide root) :
    Winding.Box.Basic.quadrupledBoxWinding
      (Dense.Gaussian.Linear.Translated.translatedCoordinate root) box = 0 := by
  let clearance := Clearance.Box.Boundary.Translated.Affine.translatedCoordinate_boundaryClearance_of_outside
    root side
  cases side with
  | left less =>
      apply winding_zero_of_rotation proper clearance 1 (by decide +kernel)
      intro point boundary
      rewrite [Dense.Gaussian.Linear.Translated.translatedCoordinate_eval, Gaussian.Basic.one_mul,
        Gaussian.Basic.sub_re]
      exact Rat.Fraction.Order.Arithmetic.sub_pos_direct (less.trans_le boundary.1.1)
  | right less =>
      apply winding_zero_of_rotation proper clearance (-1) (by decide +kernel)
      intro point boundary
      rewrite [Dense.Gaussian.Linear.Translated.translatedCoordinate_eval]
      have real : ((-1 : Canonical) * (point - root)).re = root.re - point.re := by
        change -1 * (point.re - root.re) - 0 * (point.im - root.im) = root.re - point.re
        ring1
      rewrite [real]
      exact Rat.Fraction.Order.Arithmetic.sub_pos_direct (boundary.1.2.1.trans_lt less)
  | bottom less =>
      apply winding_zero_of_rotation proper clearance Gaussian.Constants.negativeImaginaryUnit (by decide +kernel)
      intro point boundary
      rewrite [Dense.Gaussian.Linear.Translated.translatedCoordinate_eval,
        Gaussian.Constants.negativeImaginaryUnit_mul_re, Gaussian.Basic.sub_im]
      exact Rat.Fraction.Order.Arithmetic.sub_pos_direct (less.trans_le boundary.1.2.2.1)
  | top less =>
      apply winding_zero_of_rotation proper clearance Gaussian.Constants.imaginaryUnit (by decide +kernel)
      intro point boundary
      rewrite [Dense.Gaussian.Linear.Translated.translatedCoordinate_eval]
      have real : (Gaussian.Constants.imaginaryUnit * (point - root)).re = root.im - point.im := by
        change 0 * (point.re - root.re) - 1 * (point.im - root.im) = root.im - point.im
        ring1
      rewrite [real]
      exact Rat.Fraction.Order.Arithmetic.sub_pos_direct (boundary.1.2.2.2.trans_lt less)

/-- An original affine polynomial has zero winding on a proper box excluding its retained exact root.

Its original leading coefficient and cached point give the same ordered
constant/displacement factorization. Both actual factors have zero winding.
-/
public theorem quadrupledBoxWinding_linear_of_outside
    {polynomial : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (data : Dense.Gaussian.Roots.Linear.RootData polynomial) {box : Box}
    (proper : box.Proper) (side : Box.OutsideSide box data.point) :
    Winding.Box.Basic.quadrupledBoxWinding polynomial box = 0 := by
  let constantClearance := Clearance.Box.Boundary.Constant.gaussianConstant_boundaryClearance
    data.leadingNonzero box
  let translatedClearance :=
    Clearance.Box.Boundary.Translated.Affine.translatedCoordinate_boundaryClearance_of_outside data.point side
  have winding := Winding.Box.Product.quadrupledBoxWinding_of_productIdentity box proper
    data.factorization constantClearance translatedClearance
  rewrite [Winding.Box.Constant.quadrupledBoxWinding_gaussianConstant data.leadingNonzero box,
    quadrupledBoxWinding_translatedCoordinate_of_outside proper side, Int.zero_add] at winding
  exact winding

end Purelib.Polynomial.Winding.Box.Affine.Outside
