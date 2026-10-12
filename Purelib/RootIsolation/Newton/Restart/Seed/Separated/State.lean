module
import Purelib.Polynomial.Clearance.Box.Region.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Boundary
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Square.Centered
public import Purelib.Polynomial.Clearance.Box.Boundary.Lines
public import Purelib.Polynomial.Clearance.Box.Boundary.Newton.Square.Separated
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Residual
import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Basic
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Anchor
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Linearization
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Square.Separated
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.Polynomial.Winding.Box.Basic
public import Purelib.Polynomial.Winding.Box.Newton.Square.Separated
import Purelib.RootIsolation.Newton.Restart.Seed.Basic
public import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Taylor
public import Purelib.RootIsolation.Newton.Restart.Seed.Geometry
public import Purelib.RootIsolation.Newton.Restart.Seed.Separated
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Certificate

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

/-- Restart a residual seed on its exact centered square, using an explicit
derivative separation and any displayed upper bound for the Newton
linearization.  The square is used as its own finite ambient, so its boundary
clearance supplies all four ambient-line certificates without a global-line
choice. -/
def separatedCenteredStateWithMajorant
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
    State.WindingOne.Basic.WindingOneState p seed.centeredBox := by
  let newton := seed.separatedNewton separation sourceThreshold
  let clearance :=
    Clearance.Box.Boundary.Newton.Square.Separated.separatedNewtonSquareBoundaryClearanceWithMajorant
      degreeAtLeastTwo newton seed.sourceRefines seed.radiusPositive
      seed.centeredBox_refines_current displacementSmall taylorSmall
      linearizationMajorant linearizationMajorantPositive linearizationUpper
  have windingFour :
      Winding.Box.Basic.quadrupledBoxWinding p seed.centeredBox = 4 :=
    Winding.Box.Newton.Square.Separated.quadrupledBoxWinding_eq_four_of_separatedNewtonSquare
      degreeAtLeastTwo newton seed.sourceRefines seed.radiusPositive
      seed.centeredBox_refines_current displacementSmall taylorSmall
  exact
    { box := seed.centeredBox
      refinesAmbient := Box.refines_refl seed.centeredBox
      proper := Box.Square.Centered.centeredSquare_proper _ seed.radiusPositive
      clearance := clearance
      rawWindingFour := windingFour
      ambientLeftClearance := Clearance.Box.Boundary.Lines.leftOfBoundary clearance
      ambientRightClearance := Clearance.Box.Boundary.Lines.rightOfBoundary clearance
      ambientBottomClearance := Clearance.Box.Boundary.Lines.bottomOfBoundary clearance
      ambientTopClearance := Clearance.Box.Boundary.Lines.topOfBoundary clearance }

/-- The centered restart retains the exact squared dominance-margin quotient determined by the supplied positive
linearization majorant. -/
theorem separatedCenteredStateWithMajorant_clearance_bound
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
    (separatedCenteredStateWithMajorant degreeAtLeastTwo seed separation
      sourceThreshold displacementSmall taylorSmall linearizationMajorant
      linearizationMajorantPositive linearizationUpper).clearance.bound =
        Dense.Gaussian.Newton.Box.Square.Separated.separatedNewtonDominanceMargin separation
            seed.radius ^ 2 /
          (4 * linearizationMajorant) := by
  unfold separatedCenteredStateWithMajorant
  exact
    Clearance.Box.Boundary.Newton.Square.Separated.separatedNewtonSquareBoundaryClearanceWithMajorant_bound
      degreeAtLeastTwo (seed.separatedNewton separation sourceThreshold)
      seed.sourceRefines seed.radiusPositive seed.centeredBox_refines_current
      displacementSmall taylorSmall linearizationMajorant
      linearizationMajorantPositive linearizationUpper
end Seed

end Purelib.RootIsolation.Newton.Restart.Seed

end
