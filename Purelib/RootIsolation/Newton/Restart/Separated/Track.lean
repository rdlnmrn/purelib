module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Boundary
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Basic
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Linearization
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.RootIsolation.Newton.Restart.Separated.Basic
public import Purelib.RootIsolation.Newton.Restart.Separated.State
import Purelib.RootIsolation.Track.Basic
public import Purelib.RootIsolation.Track.Newton.Build
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation

open Purelib.Data

open Purelib.Data.Rat

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

namespace Purelib.RootIsolation.Newton.Restart.Separated.Basic

namespace SeparatedRestartInput

variable {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
variable {separation : Dense.Gaussian.Derivative.Separation.Basic.Certificate p ambient}

/-- The ordinary finite shrinking program beginning at a direct separated
restart.  Squarefreeness and elimination are used only by the subsequent
shrinker, not to choose the restart radius. -/
def centeredTrackWithMajorant
    {degreeBound : Nat}
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (degreeAtLeastTwo : 2 <= p.natDegree)
    (input : Newton.Restart.Separated.Basic.SeparatedRestartInput separation)
    (linearizationMajorant : Fraction.Rational)
    (linearizationMajorantPositive : 0 < linearizationMajorant)
    (linearizationUpper : forall z : Gaussian.Basic.Canonical,
      Box.Boundary.OnBoxBoundary input.centeredBox z ->
        Data.Gaussian.Norm.Basic.normSq
          ((Dense.Gaussian.Newton.Box.Linearization.newtonLinearization p input.source).eval z) <=
            linearizationMajorant) :
    Track.Basic.WindingOneTrack p input.centeredBox :=
  Track.Newton.Build.ofInitial degreeAtLeastTwo squarefree elimination
    (Newton.Restart.Separated.Basic.SeparatedRestartInput.centeredStateWithMajorant degreeAtLeastTwo input
      linearizationMajorant
      linearizationMajorantPositive linearizationUpper)

end SeparatedRestartInput

end Purelib.RootIsolation.Newton.Restart.Separated.Basic

end
