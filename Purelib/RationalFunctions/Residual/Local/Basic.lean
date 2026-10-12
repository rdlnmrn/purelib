module

import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Coprime.Basic
import Purelib.RootIsolation.State.WindingOne.Basic
public import Purelib.RootIsolation.Track.Basic
meta import Purelib.Elab.ConstructiveInjectivity

section
@[expose] public section

/-!
# Two-way residual and chordal bounds for rational functions

For a reduced coprime pair, a protectedState source track has a uniform positive
margin for the opposite polynomial.  This converts the polynomial
box-to-residual and residual-to-box theorems into corresponding theorems for
the quotient.  Swapping source and opposite gives the pole statements.
-/

namespace Purelib.RationalFunctions.Residual.Local.Basic

open Purelib.Polynomial in
open Purelib.Geometry in
open Purelib.RootIsolation in
set_option genInjectivity false in
/-- Retained source-root data and coprimality evidence for a local quotient.

The source has positive degree. A winding-one track and a current winding-one state are both indexed by that source and
the same ambient box, while the Bézout certificate relates the source and opposite polynomials. -/
structure LocalQuotientContext
    (source opposite : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (ambient :
      Rational.Box) where
  /-- The source polynomial has positive natural degree. -/ sourceDegreePositive : 0 < source.natDegree
  /-- The retained executable coprimality certificate for the source and opposite polynomials. -/ coprime :
    Dense.Gaussian.Coprime.Basic.CoprimeCertificate source opposite
  /-- The retained winding-one source track in the indexed ambient box. -/ track : Track.Basic.WindingOneTrack source
    ambient
  /-- The retained current winding-one source state in the indexed ambient box. -/ current :
    State.WindingOne.Basic.WindingOneState source ambient

constructive_injectivity LocalQuotientContext

end Purelib.RationalFunctions.Residual.Local.Basic

end

section
@[expose] public section

/-!
# Denominator height for rational-function residuals

The same finite height bounds apply to a rational function once the
nonvanishing opposite polynomial is kept explicit.  A zero track uses the
numerator as source and the denominator as opposite; a pole track swaps them,
so its shrinking quantity is the reciprocal residual.
-/

namespace Purelib.RationalFunctions.DenominatorHeight
end Purelib.RationalFunctions.DenominatorHeight

end
