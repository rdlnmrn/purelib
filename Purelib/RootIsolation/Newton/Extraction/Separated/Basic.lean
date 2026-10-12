module

import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Basic
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Anchor
public import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Budget.Separated
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Certificate
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Square.Bounds
public import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Square.Separated
import Purelib.Polynomial.Winding.Box.Basic
public import Purelib.RootIsolation.State.Raw
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rational.Box.Square.Centered
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Taylor
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

public section

/-!
# Choice-free local Newton-square extraction

A finite raw-winding subdivision first crosses explicit residual, protected
boundary, displacement, and Taylor thresholds.  The exact rational Newton
point then centers a strictly nested winding-one square.  No root is selected
and no completed or infinite carrier is used.
-/

namespace Purelib.RootIsolation.Newton.Extraction.Separated.Basic

set_option genInjectivity false in
/-- Strictly nested Newton-square output obtained without a global
squarefree certificate for the displayed polynomial.

The original raw source, separation and requested epsilon index the retained
Newton center, selected radius, centered box, strictness, winding and clearance
witnesses. Every readback identifies those exact cached fields. -/
structure SeparatedOutput
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (current : State.Raw.RawWindingState p ambient)
    (separation : Dense.Gaussian.Derivative.Separation.Basic.Certificate p current.box)
    (epsilon : Fraction.Rational) where
  /-- The retained nonzero-winding source box inside the original current box. -/ source : State.Raw.RawWindingState p
    current.box
  /-- The rational radius used by this Newton extraction. -/ radius : Fraction.Rational
  /-- The retained radius is the original separated-extraction budget for the current box, clearance and accuracy. -/
    radius_eq : radius = Dense.Gaussian.Newton.Box.Budget.Separated.separatedExtractionRadius separation current.box
    current.clearance epsilon
  /-- The retained extraction radius is strictly positive. -/ radiusPositive : 0 < radius
  /-- The Newton-center certificate for the same polynomial, current box and retained source box. -/ newton :
    Dense.Gaussian.Newton.Box.Certificate.SeparatedNewtonCenterCertificate
    p current.box source.box separation
  /-- The squared Newton-center displacement from the source anchor is at most the squared radius. -/ displacementSmall
    : Data.Gaussian.Norm.Basic.normSq
    (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source.box - source.box.anchor) ≤ radius ^ 2
  /-- The radius-scaled Taylor remainder fits within the supplied derivative-separation margin. -/ taylorSmall :
    2 * (36 * Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound p current.box * radius ^ 2) ≤
      separation.margin
  /-- The retained centered Newton square. -/ box : Box
  /-- The retained box is exactly the radius square centered at the original source's Newton point. -/ box_eq : box =
    Box.Square.Centered.Affine.centeredSquare
    (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source.box) radius radiusPositive.le
  /-- The extracted box lies strictly inside the original current box. -/ strictCurrent : box.StrictInterior current.box
  /-- The extracted box refines the original fixed ambient box. -/ refinesAmbient : box.Refines ambient
  /-- The extracted box has strictly positive width and height. -/ proper : box.Proper
  /-- A retained positive boundary-clearance certificate for the original polynomial on the extracted box. -/ clearance
    : Clearance.Box.Boundary.Basic.BoundaryClearance p box
  /-- The retained clearance has the exact squared dominance-margin quotient determined by the original linearization
    majorant. -/ clearance_bound : clearance.bound =
    Dense.Gaussian.Newton.Box.Square.Separated.separatedNewtonDominanceMargin separation radius ^ 2 /
      (4 * Dense.Gaussian.Newton.Box.Square.Bounds.separatedNewtonLinearizationMajorant
        p current.box radius)
  /-- The original polynomial has quadrupled winding four on the extracted box. -/ rawWindingFour :
    Winding.Box.Basic.quadrupledBoxWinding p box = 4
  /-- The extracted box's squared diagonal is at most the squared requested accuracy. -/ diagonalSq_le : box.diagonalSq
    ≤ epsilon ^ 2

constructive_injectivity SeparatedOutput

end Purelib.RootIsolation.Newton.Extraction.Separated.Basic

end
