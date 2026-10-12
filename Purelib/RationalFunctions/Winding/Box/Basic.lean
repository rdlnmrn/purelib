module
import Purelib.Data.Int.Division
public import Purelib.Data.Gaussian.Cast.Imaginary
public import Purelib.Data.Gaussian.Constants
public import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.Path
public import Purelib.RationalFunctions.Path.Polynomial
import Purelib.Data.Gaussian.Cast
import Purelib.Tactic.Ring

section
public section

/-!
# Constructive winding of a displayed rational function

The boundary value of `numerator / denominator` is represented by the
polynomial coordinate pair of

`numerator(z) * conj(denominator(z))`.

The omitted factor `normSq (denominator(z))` is positive wherever the
denominator boundary is clear, so this pair has exactly the direction of the
quotient.  Conjugation is performed only on the two coordinate polynomials of
one displayed affine edge; it is never promoted to a polynomial in `z`.
-/

namespace Purelib.RationalFunctions.Winding.Box.Basic

open Purelib.Data in
open Purelib.Polynomial in
open Purelib.Geometry in
open Purelib.RationalFunctions in
/-- Construct the four positively oriented denominator-cleared quotient edges of a rational box.

The list visits bottom, right, top and left edges with the corresponding parameter directions. Each edge retains the
numerator-times-conjugate-denominator coordinate polynomials. -/
@[expose] def quotientBoundary
    (numerator denominator : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (box :
      Rational.Box) :
    List Dense.Rational.Pair.Path.Basic.PolynomialEdge :=
  [Path.Polynomial.quotientEdge numerator denominator
      (Gaussian.Cast.Imaginary.horizontalBase box.yLower) Gaussian.Constants.horizontalDirection
      box.xLower box.xUpper,
    Path.Polynomial.quotientEdge numerator denominator
      (Gaussian.Cast.Winding.verticalBase box.xUpper) Gaussian.Constants.imaginaryUnit
      box.yLower box.yUpper,
    Path.Polynomial.quotientEdge numerator denominator
      (Gaussian.Cast.Imaginary.horizontalBase box.yUpper) Gaussian.Constants.horizontalDirection
      box.xUpper box.xLower,
    Path.Polynomial.quotientEdge numerator denominator
      (Gaussian.Cast.Winding.verticalBase box.xLower) Gaussian.Constants.imaginaryUnit
      box.yUpper box.yLower]

section
open Purelib.Polynomial
open Purelib.Geometry
open Purelib.RationalFunctions
/-- Sum the doubled edge winding values over the four quotient boundary edges.

This is the raw integer convention used for quadrupled rational-function box winding. It is computed from finite
polynomial edge data. -/
@[expose] def rationalQuadrupledWinding
    (numerator denominator : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (box :
      Rational.Box) : Int :=
  ((Winding.Box.Basic.quotientBoundary numerator denominator box).map
    Dense.Rational.Pair.Path.Basic.PolynomialEdge.doubledWinding).sum

/-- Divide the raw quadrupled rational-function box winding by four. -/
@[expose] def rationalBoxWinding
    (numerator denominator : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (box :
      Rational.Box) : Int :=
  Winding.Box.Basic.rationalQuadrupledWinding numerator denominator box / 4

/-- An exact raw winding value of four times an integer yields that integer after normalization. -/
theorem rationalBoxWinding_eq_of_quadrupled_eq_four_mul
    {numerator denominator : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {box :
      Rational.Box} {value : Int}
    (raw : Winding.Box.Basic.rationalQuadrupledWinding numerator denominator box = 4 * value) :
    Winding.Box.Basic.rationalBoxWinding numerator denominator box = value := by
  rw [Winding.Box.Basic.rationalBoxWinding, raw]
  exact Purelib.Data.Int.Division.mul_ediv_cancel_left value (by decide)

end

open Purelib.Data in
open Purelib.Polynomial in
open Purelib.Geometry in
open Purelib.RationalFunctions in
/-- The raw quotient box winding is the sum of the bottom, right, top and left edge contributions. -/
theorem rationalQuadrupledWinding_eq
    (numerator denominator : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (box :
      Rational.Box) :
    Winding.Box.Basic.rationalQuadrupledWinding numerator denominator box =
      (Path.Polynomial.quotientEdge numerator denominator
        (Gaussian.Cast.Imaginary.horizontalBase box.yLower) Gaussian.Constants.horizontalDirection
        box.xLower box.xUpper).doubledWinding +
      (Path.Polynomial.quotientEdge numerator denominator
        (Gaussian.Cast.Winding.verticalBase box.xUpper) Gaussian.Constants.imaginaryUnit
        box.yLower box.yUpper).doubledWinding +
      (Path.Polynomial.quotientEdge numerator denominator
        (Gaussian.Cast.Imaginary.horizontalBase box.yUpper) Gaussian.Constants.horizontalDirection
        box.xUpper box.xLower).doubledWinding +
      (Path.Polynomial.quotientEdge numerator denominator
        (Gaussian.Cast.Winding.verticalBase box.xLower) Gaussian.Constants.imaginaryUnit
        box.yUpper box.yLower).doubledWinding := by
  simp only [Winding.Box.Basic.rationalQuadrupledWinding, Winding.Box.Basic.quotientBoundary, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil]
  ring1
end Purelib.RationalFunctions.Winding.Box.Basic

end
