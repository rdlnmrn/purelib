module
import Purelib.Polynomial.Clearance.Box.Region.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Boundary
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Residual
import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Basic
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Anchor
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Linearization
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.RootIsolation.Newton.Restart.Seed.Basic
public import Purelib.RootIsolation.Newton.Restart.Seed.Separated.State
import Purelib.RootIsolation.Track.Basic
public import Purelib.RootIsolation.Track.Newton.Build
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Taylor
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.RootIsolation.Newton.Restart.Seed.Geometry

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

namespace Purelib.RootIsolation.Newton.Restart.Seed

section Seed

variable {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient :
  Purelib.Geometry.Rational.Box}
  {degreeBound : Nat}
variable {squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p}
variable {elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound}
variable {current : Clearance.Box.Region.ProtectedAmbient p ambient}

/-- The centered restart retains the ordinary total finite shrinking
refiner, now beginning with a predictable box and clearance formula. -/
def separatedCenteredTrackWithMajorant
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (seed : Seed squarefree elimination current)
    (separation : Dense.Gaussian.Derivative.Separation.Basic.Certificate p current.box)
    (sourceThreshold :
      Dense.Gaussian.Bounds.Box.Residual.anchorResidualBound p current.box seed.source ≤
        separation.threshold)
    (displacementSmall :
      Data.Gaussian.Norm.Basic.normSq (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p seed.source -
        seed.source.anchor) ≤
        seed.radius ^ 2)
    (taylorSmall :
      2 * (36 * Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound p current.box * seed.radius ^ 2) ≤
        separation.margin)
    (linearizationMajorant : Fraction.Rational)
    (linearizationMajorantPositive : 0 < linearizationMajorant)
    (linearizationUpper : ∀ z : Gaussian.Basic.Canonical,
      Box.Boundary.OnBoxBoundary seed.centeredBox z →
        Data.Gaussian.Norm.Basic.normSq ((Dense.Gaussian.Newton.Box.Linearization.newtonLinearization p
          seed.source).eval z) ≤
          linearizationMajorant) :
    Track.Basic.WindingOneTrack p seed.centeredBox :=
  Track.Newton.Build.ofInitial degreeAtLeastTwo squarefree elimination
    (separatedCenteredStateWithMajorant degreeAtLeastTwo seed separation
      sourceThreshold displacementSmall taylorSmall linearizationMajorant
      linearizationMajorantPositive linearizationUpper)
end Seed

end Purelib.RootIsolation.Newton.Restart.Seed

end
