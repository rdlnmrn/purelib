module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Boundary
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Square.Centered
public import Purelib.Polynomial.Clearance.Box.Boundary.Lines
public import Purelib.Polynomial.Clearance.Box.Boundary.Newton.Square.Separated
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Basic
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Linearization
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Square.Separated
import Purelib.Polynomial.Winding.Box.Basic
public import Purelib.Polynomial.Winding.Box.Newton.Square.Separated
public import Purelib.RootIsolation.Newton.Restart.Separated.Basic
public import Purelib.RootIsolation.State.WindingOne.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Anchor

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

namespace Purelib.RootIsolation.Newton.Restart.Separated.Basic.SeparatedRestartInput

section SeparatedRestartInput

variable {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
variable {separation : Dense.Gaussian.Derivative.Separation.Basic.Certificate p ambient}

/-- Restart directly on the predictable centered square, retaining an
explicit upper bound for the Newton linearization so that the resulting
boundary-clearance formula is known before any later owner is read. -/
def centeredStateWithMajorant
    (degreeAtLeastTwo : 2 <= p.natDegree)
    (input : Newton.Restart.Separated.Basic.SeparatedRestartInput separation)
    (linearizationMajorant : Fraction.Rational)
    (linearizationMajorantPositive : 0 < linearizationMajorant)
    (linearizationUpper : forall z : Gaussian.Basic.Canonical,
      Box.Boundary.OnBoxBoundary input.centeredBox z ->
        Data.Gaussian.Norm.Basic.normSq
          ((Dense.Gaussian.Newton.Box.Linearization.newtonLinearization p input.source).eval z) <=
            linearizationMajorant) :
    State.WindingOne.Basic.WindingOneState p input.centeredBox := by
  let clearance :=
    Clearance.Box.Boundary.Newton.Square.Separated.separatedNewtonSquareBoundaryClearanceWithMajorant
      degreeAtLeastTwo input.newton input.sourceRefines input.radiusPositive
      input.centeredBox_refines input.displacementSmall input.taylorSmall
      linearizationMajorant linearizationMajorantPositive linearizationUpper
  have windingFour :
      Winding.Box.Basic.quadrupledBoxWinding p input.centeredBox = 4 :=
    Winding.Box.Newton.Square.Separated.quadrupledBoxWinding_eq_four_of_separatedNewtonSquare
      degreeAtLeastTwo input.newton input.sourceRefines input.radiusPositive
      input.centeredBox_refines input.displacementSmall input.taylorSmall
  exact
    { box := input.centeredBox
      refinesAmbient := Box.refines_refl input.centeredBox
      proper := Box.Square.Centered.centeredSquare_proper _
        input.radiusPositive
      clearance := clearance
      rawWindingFour := windingFour
      ambientLeftClearance := Clearance.Box.Boundary.Lines.leftOfBoundary clearance
      ambientRightClearance := Clearance.Box.Boundary.Lines.rightOfBoundary clearance
      ambientBottomClearance := Clearance.Box.Boundary.Lines.bottomOfBoundary clearance
      ambientTopClearance := Clearance.Box.Boundary.Lines.topOfBoundary clearance }

/-- The restarted centered state retains the exact clearance quotient from the supplied linearization majorant.

Its numerator is the squared separated Newton dominance margin, and its denominator is four times the original positive
majorant. -/
theorem
  centeredStateWithMajorant_clearance_bound
    (degreeAtLeastTwo : 2 <= p.natDegree)
    (input : Newton.Restart.Separated.Basic.SeparatedRestartInput separation)
    (linearizationMajorant : Fraction.Rational)
    (linearizationMajorantPositive : 0 < linearizationMajorant)
    (linearizationUpper : forall z : Gaussian.Basic.Canonical,
      Box.Boundary.OnBoxBoundary input.centeredBox z ->
        Data.Gaussian.Norm.Basic.normSq
          ((Dense.Gaussian.Newton.Box.Linearization.newtonLinearization p input.source).eval z) <=
            linearizationMajorant) :
    (Newton.Restart.Separated.Basic.SeparatedRestartInput.centeredStateWithMajorant degreeAtLeastTwo input
      linearizationMajorant linearizationMajorantPositive
      linearizationUpper).clearance.bound =
        Dense.Gaussian.Newton.Box.Square.Separated.separatedNewtonDominanceMargin separation
            input.radius ^ 2 /
          (4 * linearizationMajorant) := by
  unfold Newton.Restart.Separated.Basic.SeparatedRestartInput.centeredStateWithMajorant
  exact
    Clearance.Box.Boundary.Newton.Square.Separated.separatedNewtonSquareBoundaryClearanceWithMajorant_bound
      degreeAtLeastTwo input.newton input.sourceRefines input.radiusPositive
      input.centeredBox_refines input.displacementSmall input.taylorSmall
      linearizationMajorant linearizationMajorantPositive linearizationUpper
end SeparatedRestartInput

end Purelib.RootIsolation.Newton.Restart.Separated.Basic.SeparatedRestartInput

end
