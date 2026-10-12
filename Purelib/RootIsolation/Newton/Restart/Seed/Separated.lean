module
import Purelib.Polynomial.Clearance.Box.Region.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Residual
import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Basic
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Certificate
public import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Prepare
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
public import Purelib.RootIsolation.Newton.Restart.Seed.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Winding bands from displayed rational residuals

A sufficiently small value of a squarefree polynomial at a displayed
Gaussian-rational sample gives a finite Newton certificate.  When supplied
with explicit rational displacement, Taylor, and containment budgets, the
selected eliminant-safe band has winding four and therefore starts a normal
shrinking track.

Nothing in this module turns a small residual, a winding count, or a Sturm
count into a root.  The only distinguished point is the supplied rational
anchor of `source`.
-/

namespace Purelib.RootIsolation.Newton.Restart.Seed

section Seed

variable {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient :
  Purelib.Geometry.Rational.Box}
  {degreeBound : Nat}
variable {squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p}
variable {elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound}
variable {current : Clearance.Box.Region.ProtectedAmbient p ambient}

/-- Re-read the seed's displayed source through any derivative-separation
certificate whose residual threshold admits that source. -/
def separatedNewton
    (seed : Seed squarefree elimination current)
    (separation : Dense.Gaussian.Derivative.Separation.Basic.Certificate p current.box)
    (sourceThreshold :
      Dense.Gaussian.Bounds.Box.Residual.anchorResidualBound p current.box seed.source ≤
        separation.threshold) :
    Dense.Gaussian.Newton.Box.Certificate.SeparatedNewtonCenterCertificate
      p current.box seed.source separation :=
  Dense.Gaussian.Newton.Box.Prepare.computeNewtonCenterOfResidualSeparated p separation
    seed.sourceRefines seed.residual sourceThreshold
end Seed

end Purelib.RootIsolation.Newton.Restart.Seed

end
