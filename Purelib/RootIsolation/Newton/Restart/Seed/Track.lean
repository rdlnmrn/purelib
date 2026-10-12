module
import Purelib.Polynomial.Clearance.Box.Region.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.RootIsolation.Newton.Restart.Seed.Basic
import Purelib.RootIsolation.Track.Basic
public import Purelib.RootIsolation.Track.Newton.Build
public import Purelib.RootIsolation.Newton.Restart.Seed.State
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic

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

/-- The standard finite refiner turns the residual-built state into a total
shrinking track. -/
def track
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (seed : Seed squarefree elimination current) :
    Track.Basic.WindingOneTrack p ambient :=
  Track.Newton.Build.ofInitial degreeAtLeastTwo squarefree
    elimination (seed.state degreeAtLeastTwo)
end Seed

end Purelib.RootIsolation.Newton.Restart.Seed

end
