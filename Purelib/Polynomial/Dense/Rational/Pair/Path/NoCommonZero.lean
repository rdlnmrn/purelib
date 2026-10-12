module
public import Purelib.Polynomial.Dense.Rational.Pair.NoCommonZero
public import Purelib.Polynomial.Dense.Rational.Pair.Path.Basic

import Purelib.Tactic.QuotientFreeOmega

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

namespace Purelib.Polynomial.Dense.Rational.Pair.Path.Basic.PolynomialEdge

/-- The two displayed coordinates of an edge have no common rational
parameter zero. -/
def Coprime (edge :
  Dense.Rational.Pair.Path.Basic.PolynomialEdge) : Prop :=
  Polynomial.Dense.Rational.Pair.NoCommonZero edge.realPart edge.imagPart
end Purelib.Polynomial.Dense.Rational.Pair.Path.Basic.PolynomialEdge

end
