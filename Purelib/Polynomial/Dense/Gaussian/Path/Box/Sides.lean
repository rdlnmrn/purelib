module
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Gaussian.Cast.Imaginary
public import Purelib.Data.Gaussian.Components.Basic
public import Purelib.Data.Gaussian.Constants
import Purelib.Geometry.Rational.Affine.Axis
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Path.Pair

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Rational.Pair.Path.Basic

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Rational.Pair.Path.Basic (PolynomialEdge)

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Polynomial

section
@[expose] public section

/-!
# Constructive winding on finite polynomial edges

Each oriented box edge is converted directly to two dense coordinate
polynomials and evaluated by the finite signed-remainder-chain program.  Edge
reversal and rectangular subdivision are exact integer identities.  No
polynomial extensionality, root set, or infinite carrier is used.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Path.Box.Sides

/-- The oriented horizontal edge `t + iy`, for `a` to `b`. -/
def horizontalEdge (p :
  CoefficientPolynomial) (y
  a b : Fraction.Rational) :
    PolynomialEdge :=
  PolynomialEdge.ofLine p (Gaussian.Cast.Imaginary.horizontalBase y)
    Gaussian.Constants.horizontalDirection a b

/-- The oriented vertical edge `x + it`, for `a` to `b`. -/
def verticalEdge (p :
  CoefficientPolynomial) (x a
  b : Fraction.Rational) :
    PolynomialEdge :=
  PolynomialEdge.ofLine p (Gaussian.Cast.Winding.verticalBase x)
    Gaussian.Constants.imaginaryUnit a b

/-- Normalizing the polynomial preserves its displayed horizontal edge coefficient pair. -/
@[simp] theorem horizontalEdge_normalize (p :
  CoefficientPolynomial)
    (y a b : Fraction.Rational) :
    horizontalEdge p.normalize y a b = horizontalEdge p y a
      b := by
  unfold horizontalEdge
  exact PolynomialEdge.ofLine_normalize p _ _ _ _

/-- Normalizing the polynomial preserves its displayed vertical edge coefficient pair. -/
@[simp] theorem verticalEdge_normalize (p :
  CoefficientPolynomial)
    (x a b : Fraction.Rational) :
    verticalEdge p.normalize x a b = verticalEdge p x a b :=
      by
  unfold verticalEdge
  exact PolynomialEdge.ofLine_normalize p _ _ _ _

/-- The horizontal edge's real coordinate polynomial evaluates to the original Gaussian polynomial's real component. -/
@[simp] theorem horizontalEdge_real_eval (p :
  CoefficientPolynomial)
    (y a b t : Fraction.Rational) :
    (horizontalEdge p y a b).realPart.eval t = (p.eval (Gaussian.Components.Basic.point t
      y)).re := open Purelib.Geometry.Rational in by
  simpa only [horizontalEdge, Affine.Axis.line_horizontal] using
    PolynomialEdge.ofLine_real_eval p (Gaussian.Cast.Imaginary.horizontalBase y)
      Gaussian.Constants.horizontalDirection a b t

/-- The horizontal edge's imaginary coordinate polynomial evaluates to the original Gaussian polynomial's imaginary
component. -/
@[simp] theorem horizontalEdge_imag_eval (p :
  CoefficientPolynomial)
    (y a b t : Fraction.Rational) :
    (horizontalEdge p y a b).imagPart.eval t = (p.eval (Gaussian.Components.Basic.point t
      y)).im := open Purelib.Geometry.Rational in by
  simpa only [horizontalEdge, Affine.Axis.line_horizontal] using
    PolynomialEdge.ofLine_imag_eval p (Gaussian.Cast.Imaginary.horizontalBase y)
      Gaussian.Constants.horizontalDirection a b t

/-- The vertical edge's real coordinate polynomial evaluates to the original Gaussian polynomial's real component. -/
@[simp] theorem verticalEdge_real_eval (p :
  CoefficientPolynomial)
    (x a b t : Fraction.Rational) :
    (verticalEdge p x a b).realPart.eval t = (p.eval (Gaussian.Components.Basic.point x
      t)).re := open Purelib.Geometry.Rational in by
  simpa only [verticalEdge, Affine.Axis.line_vertical] using
    PolynomialEdge.ofLine_real_eval p (Gaussian.Cast.Winding.verticalBase x)
      Gaussian.Constants.imaginaryUnit a b t

/-- The vertical edge's imaginary coordinate polynomial evaluates to the original Gaussian polynomial's imaginary
component. -/
@[simp] theorem verticalEdge_imag_eval (p :
  CoefficientPolynomial)
    (x a b t : Fraction.Rational) :
    (verticalEdge p x a b).imagPart.eval t = (p.eval (Gaussian.Components.Basic.point x
      t)).im := open Purelib.Geometry.Rational in by
  simpa only [verticalEdge, Affine.Axis.line_vertical] using
    PolynomialEdge.ofLine_imag_eval p (Gaussian.Cast.Winding.verticalBase x)
      Gaussian.Constants.imaginaryUnit a b t
end Purelib.Polynomial.Dense.Gaussian.Path.Box.Sides

end
