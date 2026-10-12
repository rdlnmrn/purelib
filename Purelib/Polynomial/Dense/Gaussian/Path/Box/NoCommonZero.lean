module
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Gaussian.Cast.Imaginary
import Purelib.Data.Gaussian.Constants
import Purelib.Data.Gaussian.Field
public import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Path.Box.Sides
import Purelib.Polynomial.Dense.Gaussian.Path.Pair.NoCommonZero
public import Purelib.Polynomial.Dense.Multiplication

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Basic
public import Purelib.Polynomial.Dense.Rational.Pair.Path.NoCommonZero

open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Rational.Pair.Path.Basic (PolynomialEdge)

open Purelib.Data

open Purelib.Geometry.Rational

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

namespace Purelib.Polynomial.Dense.Gaussian.Path.Box.NoCommonZero

/-- Proof-relevant coprimality of all four oriented boundary coordinate
pairs.  Constructive path-clearance certificates supply these fields. -/
structure BoundaryCoprime (p :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (box : Box) : Prop where
  /-- Coprimality of the coordinate pair on the bottom edge, oriented left to right. -/ bottom :
    (Dense.Gaussian.Path.Box.Sides.horizontalEdge p box.yLower box.xLower box.xUpper).Coprime
  /-- Coprimality of the coordinate pair on the right edge, oriented upward. -/ right :
    (Dense.Gaussian.Path.Box.Sides.verticalEdge p box.xUpper box.yLower box.yUpper).Coprime
  /-- Coprimality of the coordinate pair on the top edge, oriented right to left. -/ top :
    (Dense.Gaussian.Path.Box.Sides.horizontalEdge p box.yUpper box.xUpper box.xLower).Coprime
  /-- Coprimality of the coordinate pair on the left edge, oriented downward. -/ left :
    (Dense.Gaussian.Path.Box.Sides.verticalEdge p box.xLower box.yUpper box.yLower).Coprime

/-- Boundary coprimality is preserved by exact finite polynomial
multiplication. -/
theorem BoundaryCoprime.mul {p q :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {box : Box}
    (pCoprime : BoundaryCoprime p box)
    (qCoprime : BoundaryCoprime q box) :
    BoundaryCoprime (p * q) box := by
  constructor
  · apply PolynomialEdge.ofLine_coprime_of_eval_ne_zero
    intro t
    rw [DensePolynomial.eval_mul]
    exact Gaussian.Field.mul_ne_zero_direct
      (PolynomialEdge.eval_ne_zero_of_ofLine_coprime p
        (Gaussian.Cast.Imaginary.horizontalBase box.yLower) Gaussian.Constants.horizontalDirection
        box.xLower box.xUpper t pCoprime.bottom)
      (PolynomialEdge.eval_ne_zero_of_ofLine_coprime q
        (Gaussian.Cast.Imaginary.horizontalBase box.yLower) Gaussian.Constants.horizontalDirection
        box.xLower box.xUpper t qCoprime.bottom)
  · apply PolynomialEdge.ofLine_coprime_of_eval_ne_zero
    intro t
    rw [DensePolynomial.eval_mul]
    exact Gaussian.Field.mul_ne_zero_direct
      (PolynomialEdge.eval_ne_zero_of_ofLine_coprime p
        (Gaussian.Cast.Winding.verticalBase box.xUpper) Gaussian.Constants.imaginaryUnit
        box.yLower box.yUpper t pCoprime.right)
      (PolynomialEdge.eval_ne_zero_of_ofLine_coprime q
        (Gaussian.Cast.Winding.verticalBase box.xUpper) Gaussian.Constants.imaginaryUnit
        box.yLower box.yUpper t qCoprime.right)
  · apply PolynomialEdge.ofLine_coprime_of_eval_ne_zero
    intro t
    rw [DensePolynomial.eval_mul]
    exact Gaussian.Field.mul_ne_zero_direct
      (PolynomialEdge.eval_ne_zero_of_ofLine_coprime p
        (Gaussian.Cast.Imaginary.horizontalBase box.yUpper) Gaussian.Constants.horizontalDirection
        box.xUpper box.xLower t pCoprime.top)
      (PolynomialEdge.eval_ne_zero_of_ofLine_coprime q
        (Gaussian.Cast.Imaginary.horizontalBase box.yUpper) Gaussian.Constants.horizontalDirection
        box.xUpper box.xLower t qCoprime.top)
  · apply PolynomialEdge.ofLine_coprime_of_eval_ne_zero
    intro t
    rw [DensePolynomial.eval_mul]
    exact Gaussian.Field.mul_ne_zero_direct
      (PolynomialEdge.eval_ne_zero_of_ofLine_coprime p
        (Gaussian.Cast.Winding.verticalBase box.xLower) Gaussian.Constants.imaginaryUnit
        box.yUpper box.yLower t pCoprime.left)
      (PolynomialEdge.eval_ne_zero_of_ofLine_coprime q
        (Gaussian.Cast.Winding.verticalBase box.xLower) Gaussian.Constants.imaginaryUnit
        box.yUpper box.yLower t qCoprime.left)
end Purelib.Polynomial.Dense.Gaussian.Path.Box.NoCommonZero

end
