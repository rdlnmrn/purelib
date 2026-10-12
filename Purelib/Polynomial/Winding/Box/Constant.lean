module
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Cast.Imaginary
import Purelib.Data.Gaussian.Constants
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Basic
public import Purelib.Polynomial.Dense.Gaussian.Constants
import Purelib.Polynomial.Dense.Gaussian.Path.Pair
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Basic
public import Purelib.Polynomial.Winding.Box.Basic
import Purelib.Polynomial.Winding.Edge.Constant

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring

open Purelib.Data

open Purelib.Geometry.Rational

open Purelib.Polynomial

section
public section

/-!
# Choice-free global winding on a finite constructive square

This module develops the coefficient-computed large-square theorem entirely
over the explicit constructive fraction and Gaussian representations.  Its
first layer computes the winding of the coordinate polynomial symbolically;
later layers transfer that value to a general positive-degree polynomial.
-/

namespace Purelib.Polynomial.Winding.Box.Constant

/-- A nonzero constant path has zero raw winding on every constructive box.
Oppositely oriented edges cancel exactly; no product formula is used. -/
theorem quadrupledBoxWinding_gaussianConstant
    {c : Gaussian.Basic.Canonical} (nonzero : c ≠ 0) (box : Box) :
    Winding.Box.Basic.quadrupledBoxWinding (Dense.Gaussian.Constants.gaussianConstant c) box = 0 := by
  rw [Winding.Box.Basic.quadrupledBoxWinding_eq]
  change
    (Dense.Rational.Pair.Path.Basic.PolynomialEdge.ofLine (Dense.Gaussian.Constants.gaussianConstant c)
        (Gaussian.Cast.Imaginary.horizontalBase box.yLower) Gaussian.Constants.horizontalDirection
        box.xLower box.xUpper).doubledWinding +
      (Dense.Rational.Pair.Path.Basic.PolynomialEdge.ofLine (Dense.Gaussian.Constants.gaussianConstant c)
        (Gaussian.Cast.Winding.verticalBase box.xUpper) Gaussian.Constants.imaginaryUnit
        box.yLower box.yUpper).doubledWinding +
      (Dense.Rational.Pair.Path.Basic.PolynomialEdge.ofLine (Dense.Gaussian.Constants.gaussianConstant c)
        (Gaussian.Cast.Imaginary.horizontalBase box.yUpper) Gaussian.Constants.horizontalDirection
        box.xUpper box.xLower).doubledWinding +
      (Dense.Rational.Pair.Path.Basic.PolynomialEdge.ofLine (Dense.Gaussian.Constants.gaussianConstant c)
        (Gaussian.Cast.Winding.verticalBase box.xLower) Gaussian.Constants.imaginaryUnit
        box.yUpper box.yLower).doubledWinding = 0
  rw [Purelib.Polynomial.Winding.Edge.Constant.gaussianConstant_edge_winding _ _ _ _ _ nonzero,
    Purelib.Polynomial.Winding.Edge.Constant.gaussianConstant_edge_winding _ _ _ _ _ nonzero,
    Purelib.Polynomial.Winding.Edge.Constant.gaussianConstant_edge_winding _ _ _ _ _ nonzero,
    Purelib.Polynomial.Winding.Edge.Constant.gaussianConstant_edge_winding _ _ _ _ _ nonzero,
    Dense.Rational.CauchyIndex.Basic.cauchyIndex2_reverse (Dense.Basic.DensePolynomial.constant c.re)
      (Dense.Basic.DensePolynomial.constant c.im)
      box.xLower box.xUpper,
    Dense.Rational.CauchyIndex.Basic.cauchyIndex2_reverse (Dense.Basic.DensePolynomial.constant c.re)
      (Dense.Basic.DensePolynomial.constant c.im)
      box.yLower box.yUpper]
  ring1
end Purelib.Polynomial.Winding.Box.Constant

end
