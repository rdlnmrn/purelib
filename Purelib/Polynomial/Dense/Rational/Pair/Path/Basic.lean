module

import Purelib.Data.Rat.Fraction
public import Purelib.Polynomial.Dense.Rational.Basic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Constructive winding on finite polynomial edges

Each oriented box edge is converted directly to two dense coordinate
polynomials and evaluated by the finite signed-remainder-chain program.  Edge
reversal and rectangular subdivision are exact integer identities.  No
polynomial extensionality, root set, or infinite carrier is used.
-/

namespace Purelib.Polynomial.Dense.Rational.Pair.Path.Basic

open Purelib.Polynomial

set_option genInjectivity false in
/-- An oriented finite polynomial edge with rational coordinate polynomials and endpoints.

The record retains both coordinate polynomials and the start and stop parameters. Reversal and restriction reuse those
same polynomials. -/
structure PolynomialEdge where
  /-- The rational polynomial giving the real coordinate. -/ realPart :
    Dense.Rational.Basic.CoordinatePolynomial
  /-- The rational polynomial giving the imaginary coordinate. -/ imagPart :
    Dense.Rational.Basic.CoordinatePolynomial
  /-- The initial rational parameter of the oriented edge. -/ start : Fraction.Rational
  /-- The final rational parameter of the oriented edge. -/ stop : Fraction.Rational
deriving DecidableEq

constructive_injectivity PolynomialEdge

/-- Reverse an edge by exchanging its endpoint parameters.

Both coordinate polynomials are retained while the start and stop fields are exchanged. -/
def PolynomialEdge.reverse (edge : PolynomialEdge) : PolynomialEdge :=
  { edge with start := edge.stop, stop := edge.start }

/-- Restrict an edge to supplied start and stop parameters.

The coordinate polynomials are retained exactly; the supplied parameters replace the original endpoints. -/
def PolynomialEdge.restrict (edge : PolynomialEdge)
    (start stop : Fraction.Rational) : PolynomialEdge :=
  { edge with start, stop }
end Purelib.Polynomial.Dense.Rational.Pair.Path.Basic

end
