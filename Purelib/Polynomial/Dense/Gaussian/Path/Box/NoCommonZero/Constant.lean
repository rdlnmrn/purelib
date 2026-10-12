module
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Cast.Imaginary
import Purelib.Data.Gaussian.Constants
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Polynomial.Dense.Gaussian.Constants
public import Purelib.Polynomial.Dense.Gaussian.Path.Box.NoCommonZero
import Purelib.Polynomial.Dense.Gaussian.Path.Pair
import Purelib.Polynomial.Dense.Gaussian.Path.Pair.NoCommonZero

import Purelib.Tactic.QuotientFreeOmega

open Purelib.Polynomial.Dense.Rational.Pair.Path.Basic (PolynomialEdge)

open Purelib.Data

open Purelib.Geometry.Rational

open Purelib.Polynomial

section
@[expose] public section

/-!
# Choice-free global winding on a finite constructive square

This module develops the coefficient-computed large-square theorem entirely
over the explicit constructive fraction and Gaussian representations.  Its
first layer computes the winding of the coordinate polynomial symbolically;
later layers transfer that value to a general positive-degree polynomial.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Path.Box.NoCommonZero.Constant

/-- A nonzero constant Gaussian polynomial has coprime coordinate paths on every box boundary.

Each of the four oriented edges retains the same nonzero constant evaluation, so the edge coordinate polynomials have no
common zero. -/
theorem gaussianConstant_boundaryCoprime {c :
  Gaussian.Basic.Canonical} (nonzero : c ≠ 0)
    (box : Box) : Dense.Gaussian.Path.Box.NoCommonZero.BoundaryCoprime
      (Dense.Gaussian.Constants.gaussianConstant c) box := by
  constructor
  · change (PolynomialEdge.ofLine (Dense.Gaussian.Constants.gaussianConstant c)
      (Gaussian.Cast.Imaginary.horizontalBase box.yLower) Gaussian.Constants.horizontalDirection
      box.xLower box.xUpper).Coprime
    apply PolynomialEdge.ofLine_coprime_of_eval_ne_zero
    intro t
    rw [Dense.Gaussian.Constants.gaussianConstant_eval]
    exact nonzero
  · change (PolynomialEdge.ofLine (Dense.Gaussian.Constants.gaussianConstant c)
      (Gaussian.Cast.Winding.verticalBase box.xUpper) Gaussian.Constants.imaginaryUnit
      box.yLower box.yUpper).Coprime
    apply PolynomialEdge.ofLine_coprime_of_eval_ne_zero
    intro t
    rw [Dense.Gaussian.Constants.gaussianConstant_eval]
    exact nonzero
  · change (PolynomialEdge.ofLine (Dense.Gaussian.Constants.gaussianConstant c)
      (Gaussian.Cast.Imaginary.horizontalBase box.yUpper) Gaussian.Constants.horizontalDirection
      box.xUpper box.xLower).Coprime
    apply PolynomialEdge.ofLine_coprime_of_eval_ne_zero
    intro t
    rw [Dense.Gaussian.Constants.gaussianConstant_eval]
    exact nonzero
  · change (PolynomialEdge.ofLine (Dense.Gaussian.Constants.gaussianConstant c)
      (Gaussian.Cast.Winding.verticalBase box.xLower) Gaussian.Constants.imaginaryUnit
      box.yUpper box.yLower).Coprime
    apply PolynomialEdge.ofLine_coprime_of_eval_ne_zero
    intro t
    rw [Dense.Gaussian.Constants.gaussianConstant_eval]
    exact nonzero
end Purelib.Polynomial.Dense.Gaussian.Path.Box.NoCommonZero.Constant

end
