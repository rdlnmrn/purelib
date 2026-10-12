module
public import Purelib.Polynomial.Power.Gaussian
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Gaussian.Cast.Imaginary
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Gaussian.Constants
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Geometry.Rational.Affine.Axis
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Path.Components
import Purelib.Polynomial.Dense.Rational.Bezout.Basic
public import Purelib.Polynomial.Elimination.Axis.Certificate

import Purelib.Data.Rat.Fraction.Compatibility
public import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring

/-!
# Explicit quadratic axis elimination

The short quartic resultants and their finite Bézout certificates are shared
by raw Rouché transport, prepared owners and their later shrinking tracks.
This module deliberately precedes the continuation-chain implementation.
-/

namespace Purelib.RootIsolation.SquareRoot.Clearance.QuadraticAxisElimination

open Purelib.Geometry.Rational
open Purelib.Algebra.Field
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Polynomial
open Purelib.Riemann.RootContinuation

/-- The rational coordinate type for quadratic elimination. -/
public abbrev Coordinate := Fraction.Rational

/-- The canonical Gaussian rational parameter type. -/
public abbrev Gaussian := Gaussian.Basic.Canonical

/-- Dense polynomials over the retained rational coordinate type. -/
public abbrev Polynomial := Dense.Basic.DensePolynomial Coordinate

/-- The degree-two power polynomial with the supplied Gaussian parameter.

The retained positive degree selects the original three-term coefficient table
for the quadratic root equation. -/
public abbrev rootPolynomial (parameter : Gaussian) :=
  Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
    SquareRootDegree.degreeTwo

/-- Construct the two-coefficient polynomial with the displayed slope and intercept.

The descending coefficient list retains the supplied slope first and the
intercept second, with no normalization or coefficient selection. -/
@[expose] public def linearPolynomial (slope intercept : Coordinate) : Polynomial :=
  ⟨[slope, intercept]⟩

/-- The two-coefficient polynomial evaluates to slope times input plus intercept.

The original Horner fold starts from zero. Its two retained coefficients
reduce by scalar zero multiplication and addition. -/
@[simp] private theorem eval_linearPolynomial
    (slope intercept value : Coordinate) :
    (linearPolynomial slope intercept).eval value = slope * value + intercept := by
  change (0 * value + slope) * value + intercept = slope * value + intercept
  rewrite [Fraction.Field.zero_mul_direct, Fraction.zero_add]
  exact Eq.refl _

/-- The displayed point's real coordinate is its first argument. -/
@[simp] private theorem point_re (x y : Coordinate) :
    (Gaussian.Components.Basic.point x y).re = x := rfl

/-- The displayed point's imaginary coordinate is its second argument. -/
@[simp] private theorem point_im (x y : Coordinate) :
    (Gaussian.Components.Basic.point x y).im = y := rfl

/-- The exact vertical-line resultant of the quadratic root polynomial.

The value combines the fixed real coordinate and both parameter coordinates.
Its exact rational nonzeroness is the retained vertical-side condition. -/
@[expose] public def verticalDeterminant (parameter : Gaussian.Basic.Canonical) (x : Coordinate) : Coordinate :=
  4 * x ^ 2 * (x ^ 2 - parameter.re) - parameter.im ^ 2

/-- A displayed nonzero quadratic vertical resultant gives an explicit
Bézout certificate for the real and imaginary path polynomials.

The constant and linear polynomial coefficients retain the original vertical
determinant denominator. Their identity holds at each supplied line parameter. -/
@[expose] public def verticalCoprime (parameter : Gaussian.Basic.Canonical) (x : Coordinate)
    (determinantNonzero : verticalDeterminant parameter x ≠ 0) :
    Dense.Rational.Bezout.Basic.CoprimeCertificate
      (Dense.Gaussian.Path.Components.pathReal (rootPolynomial parameter) (Gaussian.Cast.Winding.verticalBase x)
        Gaussian.Constants.imaginaryUnit)
      (Dense.Gaussian.Path.Components.pathImag (rootPolynomial parameter) (Gaussian.Cast.Winding.verticalBase x)
        Gaussian.Constants.imaginaryUnit) where
  left := Dense.Basic.DensePolynomial.constant (4 * x ^ 2 / verticalDeterminant parameter x)
  right := linearPolynomial
    (2 * x / verticalDeterminant parameter x)
    (parameter.im / verticalDeterminant parameter x)
  identity := by
    intro y
    simp only [Dense.Basic.DensePolynomial.eval_constant, eval_linearPolynomial,
      Dense.Gaussian.Path.Components.eval_pathReal,
      Dense.Gaussian.Path.Components.eval_pathImag, rootPolynomial,
        Purelib.Polynomial.Power.Gaussian.rootPolynomial_eval,
      SquareRootDegree.degreeTwo_value, pow_two, Affine.Axis.line_vertical,
      Gaussian.Basic.sub_re, Gaussian.Basic.sub_im, Gaussian.Basic.mul_re, Gaussian.Basic.mul_im, point_re, point_im]
    rw [ExplicitField.div_eq_mul_inv,
      ExplicitField.div_eq_mul_inv,
      ExplicitField.div_eq_mul_inv]
    calc
      1 = (verticalDeterminant parameter x)⁻¹ *
          verticalDeterminant parameter x :=
        (Fraction.Field.inv_mul_cancel _ determinantNonzero).symm
      _ = _ := by
        dsimp only [verticalDeterminant]
        ring1

/-- The exact horizontal-line resultant of `Z² - parameter`.

The value combines the fixed imaginary coordinate and both parameter coordinates.
Its exact rational nonzeroness is the retained horizontal-side condition. -/
@[expose] public def horizontalDeterminant
    (parameter : Gaussian.Basic.Canonical) (y : Coordinate) : Coordinate :=
  parameter.im ^ 2 - 4 * y ^ 2 * (y ^ 2 + parameter.re)

/-- A displayed nonzero quadratic horizontal resultant gives an explicit
Bézout certificate for the real and imaginary path polynomials.

The constant and linear polynomial coefficients retain the original horizontal
determinant denominator, including both original coefficient signs. -/
@[expose] public def horizontalCoprime (parameter : Gaussian.Basic.Canonical) (y : Coordinate)
    (determinantNonzero : horizontalDeterminant parameter y ≠ 0) :
    Dense.Rational.Bezout.Basic.CoprimeCertificate
      (Dense.Gaussian.Path.Components.pathReal (rootPolynomial parameter) (Gaussian.Cast.Imaginary.horizontalBase y)
        Gaussian.Constants.horizontalDirection)
      (Dense.Gaussian.Path.Components.pathImag (rootPolynomial parameter) (Gaussian.Cast.Imaginary.horizontalBase y)
        Gaussian.Constants.horizontalDirection) where
  left := Dense.Basic.DensePolynomial.constant (4 * y ^ 2 / horizontalDeterminant parameter y)
  right := linearPolynomial
    (-(2 * y) / horizontalDeterminant parameter y)
    (-parameter.im / horizontalDeterminant parameter y)
  identity := by
    intro x
    simp only [Dense.Basic.DensePolynomial.eval_constant, eval_linearPolynomial,
      Dense.Gaussian.Path.Components.eval_pathReal,
      Dense.Gaussian.Path.Components.eval_pathImag, rootPolynomial,
        Purelib.Polynomial.Power.Gaussian.rootPolynomial_eval,
      SquareRootDegree.degreeTwo_value, pow_two, Affine.Axis.line_horizontal,
      Gaussian.Basic.sub_re, Gaussian.Basic.sub_im, Gaussian.Basic.mul_re, Gaussian.Basic.mul_im, point_re, point_im]
    rw [ExplicitField.div_eq_mul_inv,
      ExplicitField.div_eq_mul_inv,
      ExplicitField.div_eq_mul_inv]
    calc
      1 = (horizontalDeterminant parameter y)⁻¹ *
          horizontalDeterminant parameter y :=
        (Fraction.Field.inv_mul_cancel _ determinantNonzero).symm
      _ = _ := by
        dsimp only [horizontalDeterminant]
        ring1

/-- The exact vertical-axis resultant of `Z² - parameter`.

The descending five-entry coefficient list retains the original quartic,
including the two zero odd coefficients and the squared imaginary constant. -/
@[expose] public def quadraticVerticalEliminant (parameter : Gaussian.Basic.Canonical) : Polynomial :=
  ⟨[4, 0, -(4 * parameter.re), 0, -(parameter.im ^ 2)]⟩

/-- The exact horizontal-axis resultant of `Z² - parameter`.

The descending five-entry coefficient list retains the original quartic,
including its negative leading coefficient and positive imaginary constant. -/
@[expose] public def quadraticHorizontalEliminant (parameter : Gaussian.Basic.Canonical) : Polynomial :=
  ⟨[-4, 0, -(4 * parameter.re), 0, parameter.im ^ 2]⟩

/-- The vertical eliminant evaluates to the displayed vertical determinant.

Evaluating the retained quartic coefficient list gives the same rational
expression as the vertical resultant at the supplied real coordinate. -/
@[simp] public theorem quadraticVerticalEliminant_eval
    (parameter : Gaussian.Basic.Canonical) (x : Coordinate) :
    (quadraticVerticalEliminant parameter).eval x = verticalDeterminant parameter x := by
  simp only [quadraticVerticalEliminant, Dense.Basic.DensePolynomial.eval, Dense.Basic.DensePolynomial.evalCoeffs,
    List.foldl_cons, List.foldl_nil]
  unfold verticalDeterminant
  ring1

/-- The horizontal eliminant evaluates to the displayed horizontal determinant.

Evaluating the retained quartic coefficient list gives the same rational
expression as the horizontal resultant at the supplied imaginary coordinate. -/
@[simp] public theorem quadraticHorizontalEliminant_eval
    (parameter : Gaussian.Basic.Canonical) (y : Coordinate) :
    (quadraticHorizontalEliminant parameter).eval y = horizontalDeterminant parameter y := by
  simp only [quadraticHorizontalEliminant, Dense.Basic.DensePolynomial.eval, Dense.Basic.DensePolynomial.evalCoeffs,
    List.foldl_cons, List.foldl_nil]
  unfold horizontalDeterminant
  ring1

/-- A degree-four axis elimination certificate for the quadratic root polynomial.

Both retained quartics have degree at most four and are nonzero. A nonzero
evaluated resultant supplies the corresponding original finite Bézout certificate. -/
@[expose] public def quadraticAxisElimination (parameter : Gaussian.Basic.Canonical) :
    Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate (rootPolynomial parameter) 4 where
  vertical := quadraticVerticalEliminant parameter
  horizontal := quadraticHorizontalEliminant parameter
  vertical_nonzero := by change false = false; rfl
  horizontal_nonzero := by change false = false; rfl
  vertical_degree := by change 4 ≤ 4; decide
  horizontal_degree := by change 4 ≤ 4; decide
  vertical_coprime := by
    intro x nonzero
    apply verticalCoprime parameter x
    rw [← quadraticVerticalEliminant_eval]
    exact nonzero
  horizontal_coprime := by
    intro y nonzero
    apply horizontalCoprime parameter y
    rw [← quadraticHorizontalEliminant_eval]
    exact nonzero

end Purelib.RootIsolation.SquareRoot.Clearance.QuadraticAxisElimination
