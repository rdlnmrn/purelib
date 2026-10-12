module

import Purelib.Data.Rat.Fraction
public import Purelib.Geometry.Rational.Box.Band.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
public import Purelib.Polynomial.Clearance.Box.Line.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Anchor
public import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Squarefree
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Winding.Box.Basic
public import Purelib.RootIsolation.State.Raw
import Purelib.Geometry.Rational.Box.Bounds
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
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
# Certified local Newton band outputs

The original polynomial, squarefree witness, current raw state and accuracy request index the retained source, positive
radius and band, together with their displacement, nesting, winding and quantitative clearance certificates.
-/

public section

namespace Purelib.RootIsolation.Newton.Band.Basic

set_option genInjectivity false in
/-- A strictly nested winding-four band together with four full-line
clearances in both the current and fixed ambient boxes.

The original polynomial, squarefree witness, current raw state and accuracy request index the retained source, positive
radius and band, together with their displacement, nesting, winding and quantitative clearance certificates. -/
structure Output
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    (current : State.Raw.RawWindingState p ambient) (epsilon : Fraction.Rational) where
  /-- The retained nonzero-winding source box inside the original current box. -/ source : State.Raw.RawWindingState p
    current.box
  /-- The rational radius used by this Newton extraction. -/ radius : Fraction.Rational
  /-- The retained extraction radius is strictly positive. -/ radiusPositive : 0 < radius
  /-- The retained band around the actual source Newton center, with the original extraction radius. -/ band :
    Box.Band.Basic.BandBox (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source.box) radius
  /-- The Newton-center certificate for the same polynomial, current box and retained source box. -/ newton :
    Dense.Gaussian.Newton.Box.Squarefree.NewtonCenterCertificate
    p current.box source.box squarefree
  /-- The squared Newton-center displacement from the source anchor is at most the squared radius. -/ displacementSmall
    : Gaussian.Basic.Canonical.normSq
    (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source.box - source.box.anchor) ≤ radius ^ 2
  /-- The extracted box lies strictly inside the original current box. -/ strictCurrent : band.box.StrictInterior
    current.box
  /-- The extracted box refines the original fixed ambient box. -/ refinesAmbient : band.box.Refines ambient
  /-- The extracted box has strictly positive width and height. -/ proper : band.box.Proper
  /-- The polynomial is clear on the band's left vertical line throughout the current box. -/ leftLineClearance :
    Clearance.Box.Line.Basic.VerticalLineClearance p current.box band.box.xLower
  /-- The polynomial is clear on the band's right vertical line throughout the current box. -/ rightLineClearance :
    Clearance.Box.Line.Basic.VerticalLineClearance p current.box band.box.xUpper
  /-- The polynomial is clear on the band's bottom horizontal line throughout the current box. -/ bottomLineClearance :
    Clearance.Box.Line.Basic.HorizontalLineClearance p current.box band.box.yLower
  /-- The polynomial is clear on the band's top horizontal line throughout the current box. -/ topLineClearance :
    Clearance.Box.Line.Basic.HorizontalLineClearance p current.box band.box.yUpper
  /-- The polynomial is clear on the band's left vertical line throughout the original ambient box. -/
    ambientLeftClearance : Clearance.Box.Line.Basic.VerticalLineClearance p ambient band.box.xLower
  /-- The polynomial is clear on the band's right vertical line throughout the original ambient box. -/
    ambientRightClearance : Clearance.Box.Line.Basic.VerticalLineClearance p ambient band.box.xUpper
  /-- The polynomial is clear on the band's bottom horizontal line throughout the original ambient box. -/
    ambientBottomClearance : Clearance.Box.Line.Basic.HorizontalLineClearance p ambient band.box.yLower
  /-- The polynomial is clear on the band's top horizontal line throughout the original ambient box. -/
    ambientTopClearance : Clearance.Box.Line.Basic.HorizontalLineClearance p ambient band.box.yUpper
  /-- A retained positive boundary-clearance certificate for the original polynomial on the extracted box. -/ clearance
    : Clearance.Box.Boundary.Basic.BoundaryClearance p band.box
  /-- The original polynomial has quadrupled winding four on the extracted box. -/ rawWindingFour :
    Winding.Box.Basic.quadrupledBoxWinding p band.box = 4
  /-- The band's squared diagonal is at most half the squared requested accuracy. -/ diagonalSq_le_half :
    band.box.diagonalSq ≤ (1 / 2 : Fraction.Rational) * epsilon ^ 2
  /-- The extracted box's squared diagonal is at most the squared requested accuracy. -/ diagonalSq_le :
    band.box.diagonalSq ≤ epsilon ^ 2

constructive_injectivity Output

/-- Read the rational box of the retained eliminant-safe Newton band. -/
@[expose] def Output.box
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    {squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p}
    {current : State.Raw.RawWindingState p ambient} {epsilon : Fraction.Rational}
    (output : Newton.Band.Basic.Output squarefree current epsilon) : Box :=
  output.band.box

end Purelib.RootIsolation.Newton.Band.Basic

end
