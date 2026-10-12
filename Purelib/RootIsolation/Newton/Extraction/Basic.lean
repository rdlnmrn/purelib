module

import Purelib.Data.Rat.Fraction
public import Purelib.Geometry.Rational.Box.Square.Centered
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Taylor
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
public import Purelib.Polynomial.Clearance.Box.ProtectedRadius
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Squarefree
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Anchor
public import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Band.Parameters
public import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Squarefree
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Winding.Box.Basic
public import Purelib.RootIsolation.State.Raw
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Bezout
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Certificate
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

/-!
# Certified local Newton extraction outputs

The original polynomial, squarefree witness, current state and positive accuracy request index the retained source,
radius, Newton center, strict output box and quantitative Taylor, clearance and winding certificates.
-/

public section

namespace Purelib.RootIsolation.Newton.Extraction.Basic

set_option genInjectivity false in
/-- Complete local output: a strictly nested clear box with raw winding four
and the requested squared-diagonal accuracy.

The original polynomial, squarefree witness, current state and positive accuracy request index the retained source,
radius, Newton center, strict output box and quantitative Taylor, clearance and winding certificates. -/
structure Output
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    (current : State.Raw.RawWindingState p ambient) (epsilon : Fraction.Rational) where
  /-- The retained nonzero-winding source box inside the original current box. -/ source : State.Raw.RawWindingState p
    current.box
  /-- The rational radius used by this Newton extraction. -/ radius : Fraction.Rational
  /-- The retained extraction radius is strictly positive. -/ radiusPositive : 0 < radius
  /-- The Newton-center certificate for the same polynomial, current box and retained source box. -/ newton :
    Dense.Gaussian.Newton.Box.Squarefree.NewtonCenterCertificate p current.box source.box squarefree
  /-- The squared Newton-center displacement from the source anchor is at most the squared radius. -/ displacementSmall
    : Data.Gaussian.Norm.Basic.normSq
    (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source.box - source.box.anchor) ≤ radius ^ 2
  /-- All four source sides remain more than four protected boundary radii inside the current box. -/ stripBounds :
    current.box.xLower + 4 *
        Clearance.Box.ProtectedRadius.protectedBoundaryRadius p current.box current.clearance <
          source.box.xLower ∧
      source.box.xUpper < current.box.xUpper - 4 *
        Clearance.Box.ProtectedRadius.protectedBoundaryRadius p current.box current.clearance ∧
      current.box.yLower + 4 *
        Clearance.Box.ProtectedRadius.protectedBoundaryRadius p current.box current.clearance <
          source.box.yLower ∧
      source.box.yUpper < current.box.yUpper - 4 *
        Clearance.Box.ProtectedRadius.protectedBoundaryRadius p current.box current.clearance
  /-- The radius-scaled band Taylor remainder fits within the squarefree derivative margin. -/ bandTaylorSmall :
    2 * (Dense.Gaussian.Newton.Box.Band.Parameters.extractionBandTaylorCoefficient *
      Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound p current.box * radius ^ 2) ≤
        Dense.Gaussian.Derivative.Separation.Squarefree.derivativeMargin squarefree current.box
  /-- The retained centered Newton square. -/ box : Box
  /-- The retained box is exactly the radius square centered at the original source's Newton point. -/ box_eq : box =
    Box.Square.Centered.Affine.centeredSquare
    (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source.box) radius radiusPositive.le
  /-- The extracted box lies strictly inside the original current box. -/ strictCurrent : box.StrictInterior current.box
  /-- The extracted box refines the original fixed ambient box. -/ refinesAmbient : box.Refines ambient
  /-- The extracted box has strictly positive width and height. -/ proper : box.Proper
  /-- A retained positive boundary-clearance certificate for the original polynomial on the extracted box. -/ clearance
    : Clearance.Box.Boundary.Basic.BoundaryClearance p box
  /-- The original polynomial has quadrupled winding four on the extracted box. -/ rawWindingFour :
    Winding.Box.Basic.quadrupledBoxWinding p box = 4
  /-- The extracted box's squared diagonal is at most the squared requested accuracy. -/ diagonalSq_le : box.diagonalSq
    ≤ epsilon ^ 2

constructive_injectivity Output

end Purelib.RootIsolation.Newton.Extraction.Basic

end
