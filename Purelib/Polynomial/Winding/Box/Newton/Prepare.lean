module
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Residual
import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Basic
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Certificate
public import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Prepare
import Purelib.Polynomial.Winding.Box.Basic
public import Purelib.Polynomial.Winding.Box.Residual
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Basic

open Purelib.Geometry.Rational

open Purelib.Polynomial

section
@[expose] public section

/-!
# Choice-free local residual extraction

A fixed rational corner of a shrinking box supplies the local sample.  Finite
Horner bounds and the box diagonal bound its residual variation.  If that
sample value were larger than the variation, a finite Rouché contraction to
the nonzero constant path would force raw winding zero.  Thus every proper
nonzero-winding box has an explicitly small rational residual.
-/

namespace Purelib.Polynomial.Winding.Box.Newton.Prepare

/-- Raw-winding form using only explicit derivative separation. -/
def computeNewtonCenterOfRawWindingSeparated
    (p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) {ambient small : Box}
    (degreePositive : 0 < p.natDegree)
    (separation : Dense.Gaussian.Derivative.Separation.Basic.Certificate p ambient)
    (refines : small.Refines ambient) (proper : small.Proper)
    (windingNonzero : Winding.Box.Basic.quadrupledBoxWinding p small ≠ 0)
    (threshold : Dense.Gaussian.Bounds.Box.Residual.anchorResidualBound p ambient small ≤
      separation.threshold) :
    Dense.Gaussian.Newton.Box.Certificate.SeparatedNewtonCenterCertificate p ambient small separation :=
  Dense.Gaussian.Newton.Box.Prepare.computeNewtonCenterOfResidualSeparated p separation refines
    (Winding.Box.Residual.anchor_residual_le_of_quadrupledBoxWinding_ne_zero
      p degreePositive refines proper windingNonzero)
    threshold
end Purelib.Polynomial.Winding.Box.Newton.Prepare

end
