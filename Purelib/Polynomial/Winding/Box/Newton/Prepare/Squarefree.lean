module
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Residual
import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Bezout
public import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Squarefree
public import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Squarefree
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Winding.Box.Basic
public import Purelib.Polynomial.Winding.Box.Newton.Prepare
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

namespace Purelib.Polynomial.Winding.Box.Newton.Prepare.Squarefree

/-- Raw-winding form of the finite local Newton step. -/
def computeNewtonCenterOfRawWinding
    (p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) {ambient small : Box}
    (degreePositive : 0 < p.natDegree)
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    (refines : small.Refines ambient) (proper : small.Proper)
    (windingNonzero : Winding.Box.Basic.quadrupledBoxWinding p small ≠ 0)
    (threshold : Dense.Gaussian.Bounds.Box.Residual.anchorResidualBound p ambient small ≤
      Dense.Gaussian.Derivative.Separation.Squarefree.derivativeThreshold squarefree ambient) :
    Dense.Gaussian.Newton.Box.Squarefree.NewtonCenterCertificate p ambient small squarefree :=
  Winding.Box.Newton.Prepare.computeNewtonCenterOfRawWindingSeparated p degreePositive
    (Dense.Gaussian.Derivative.Separation.Bezout.ofSquarefree squarefree ambient)
    refines proper windingNonzero threshold

end Purelib.Polynomial.Winding.Box.Newton.Prepare.Squarefree

end
