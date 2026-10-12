module
import Purelib.Polynomial.Clearance.Box.Region.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
public import Purelib.Polynomial.Clearance.Box.Boundary.Lines
public import Purelib.Polynomial.Clearance.Box.Line.Elimination.Band
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Anchor
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Elimination.Axis.Band
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.Polynomial.Winding.Box.Basic
public import Purelib.Polynomial.Winding.Box.Newton.Band
import Purelib.RootIsolation.Newton.Restart.Seed.Basic
public import Purelib.RootIsolation.State.WindingOne.Basic
public import Purelib.RootIsolation.Newton.Restart.Seed.Geometry
public import Purelib.Polynomial.Clearance.Box.Line.Restriction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Band.Basic
public import Purelib.Geometry.Rational.Box.Band.Bounds
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Clearance.Box.Line.Basic
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

/-- The rational residual seed produces an ordinary winding-one state, with
all boundary and ambient-line clearances needed by the standard refiner. -/
def state
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (seed : Seed squarefree elimination current) :
    State.WindingOne.Basic.WindingOneState p ambient := by
  let center := Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p seed.source
  let band := seed.band
  have bandRefinesCurrent : band.box.Refines current.box :=
    seed.band_refines_current
  let leftLine := Clearance.Box.Line.Elimination.Band.selectedBandLeftClearance elimination current.box center
    seed.radiusPositive
  let rightLine := Clearance.Box.Line.Elimination.Band.selectedBandRightClearance elimination current.box center
    seed.radiusPositive
  let bottomLine := Clearance.Box.Line.Elimination.Band.selectedBandBottomClearance elimination current.box center
    seed.radiusPositive
  let topLine := Clearance.Box.Line.Elimination.Band.selectedBandTopClearance elimination current.box center
    seed.radiusPositive
  let ambientLeftLine := Clearance.Box.Line.Elimination.Band.selectedBandLeftClearance elimination ambient center
    seed.radiusPositive
  let ambientRightLine := Clearance.Box.Line.Elimination.Band.selectedBandRightClearance elimination ambient center
    seed.radiusPositive
  let ambientBottomLine := Clearance.Box.Line.Elimination.Band.selectedBandBottomClearance elimination ambient
    center seed.radiusPositive
  let ambientTopLine := Clearance.Box.Line.Elimination.Band.selectedBandTopClearance elimination ambient center
    seed.radiusPositive
  let clearance : Clearance.Box.Boundary.Basic.BoundaryClearance p band.box :=
    Clearance.Box.Boundary.Lines.boundaryOfLines
    (Clearance.Box.Line.Basic.VerticalLineClearance.restrict leftLine bandRefinesCurrent)
    (Clearance.Box.Line.Basic.VerticalLineClearance.restrict rightLine bandRefinesCurrent)
    (Clearance.Box.Line.Basic.HorizontalLineClearance.restrict bottomLine bandRefinesCurrent)
    (Clearance.Box.Line.Basic.HorizontalLineClearance.restrict topLine bandRefinesCurrent)
  have windingFour :
      Winding.Box.Basic.quadrupledBoxWinding p band.box = 4 :=
    Winding.Box.Newton.Band.quadrupledBoxWinding_eq_four_of_newtonBand degreeAtLeastTwo seed.newton
      seed.sourceRefines seed.radiusPositive band bandRefinesCurrent
      seed.displacementSmall seed.taylorSmall
  exact
    { box := band.box
      refinesAmbient := bandRefinesCurrent.trans current.refinesAmbient
      proper := band.proper seed.radiusPositive
      clearance := clearance
      rawWindingFour := windingFour
      ambientLeftClearance := ambientLeftLine
      ambientRightClearance := ambientRightLine
      ambientBottomClearance := ambientBottomLine
      ambientTopClearance := ambientTopLine }

/-- The winding-one state built from a residual seed lies strictly inside its original current box. -/
theorem state_strict_current
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (seed : Seed squarefree elimination current) :
    (seed.state degreeAtLeastTwo).box.StrictInterior current.box := by
  change (Elimination.Axis.Band.selectedBand elimination (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p
    seed.source)
    seed.radius seed.radiusPositive).box.StrictInterior current.box
  exact seed.bandStrict
end Seed

end Purelib.RootIsolation.Newton.Restart.Seed

end
