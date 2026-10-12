module
public import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Path.Box.Sides

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Polynomial.Dense.Rational.Pair.Path.Basic

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

namespace Purelib.Polynomial.Dense.Gaussian.Path.Box.Boundary

/-- Positively oriented four-edge boundary of a constructive box. -/
def boxBoundary (p :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
  (box : Box) : List Dense.Rational.Pair.Path.Basic.PolynomialEdge :=
  [Dense.Gaussian.Path.Box.Sides.horizontalEdge p box.yLower box.xLower box.xUpper,
    Dense.Gaussian.Path.Box.Sides.verticalEdge p box.xUpper box.yLower box.yUpper,
    Dense.Gaussian.Path.Box.Sides.horizontalEdge p box.yUpper box.xUpper box.xLower,
    Dense.Gaussian.Path.Box.Sides.verticalEdge p box.xLower box.yUpper box.yLower]
end Purelib.Polynomial.Dense.Gaussian.Path.Box.Boundary

end
