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
public import Purelib.RootIsolation.Newton.Band.Prepare
public import Purelib.Polynomial.Clearance.Box.Line.Restriction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Band.Basic
public import Purelib.Geometry.Rational.Box.Band.Bounds
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Clearance.Box.Line.Basic
import Purelib.Polynomial.Dense.Basic

open Purelib.Polynomial.Clearance.Box.Line.Elimination

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

variable {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient :
  Box}
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
  let leftLine := Band.selectedBandLeftClearance elimination current.box center
    seed.radiusPositive
  let rightLine := Band.selectedBandRightClearance elimination current.box center
    seed.radiusPositive
  let bottomLine := Band.selectedBandBottomClearance elimination current.box center
    seed.radiusPositive
  let topLine := Band.selectedBandTopClearance elimination current.box center
    seed.radiusPositive
  let ambientLeftLine := Band.selectedBandLeftClearance elimination ambient center
    seed.radiusPositive
  let ambientRightLine := Band.selectedBandRightClearance elimination ambient center
    seed.radiusPositive
  let ambientBottomLine := Band.selectedBandBottomClearance elimination ambient
    center seed.radiusPositive
  let ambientTopLine := Band.selectedBandTopClearance elimination ambient center
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

public section

namespace Purelib.RootIsolation.Newton.Restart.Seed

open Dense.Gaussian.Newton.Box

variable {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
  {degreeBound : Nat}
  {squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p}
  {elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound}
  {current : Clearance.Box.Region.ProtectedAmbient p ambient}

/-- Restore the original residual state from its retained band and eight original line certificates.

The supplied band is used directly. Coordinate transports identify the cached
current-box and fixed-ambient clearances without running their producers. -/
def stateFromLines (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (seed : Seed squarefree elimination current)
    (band : Box.Band.Basic.BandBox (Anchor.anchorNewtonCenter p seed.source) seed.radius)
    (sameBand : band = seed.band)
    (lines : Newton.Band.Prepare.Lines elimination current.box ambient
      (Anchor.anchorNewtonCenter p seed.source) seed.radiusPositive) :
    State.WindingOne.Basic.WindingOneState p ambient := by
  have refinesCurrent : band.box.Refines current.box := by
    rewrite [sameBand]
    exact seed.band_refines_current
  have leftEq := congrArg (fun value => value.box.xLower) sameBand
  have rightEq := congrArg (fun value => value.box.xUpper) sameBand
  have bottomEq := congrArg (fun value => value.box.yLower) sameBand
  have topEq := congrArg (fun value => value.box.yUpper) sameBand
  let leftLine := leftEq.symm ▸ lines.left.1.val
  let rightLine := rightEq.symm ▸ lines.right.1.val
  let bottomLine := bottomEq.symm ▸ lines.bottom.1.val
  let topLine := topEq.symm ▸ lines.top.1.val
  exact
    { box := band.box
      refinesAmbient := refinesCurrent.trans current.refinesAmbient
      proper := band.proper seed.radiusPositive
      clearance := Clearance.Box.Boundary.Lines.boundaryOfLines
        (leftLine.restrict refinesCurrent) (rightLine.restrict refinesCurrent)
        (bottomLine.restrict refinesCurrent) (topLine.restrict refinesCurrent)
      rawWindingFour :=
        Winding.Box.Newton.Band.quadrupledBoxWinding_eq_four_of_newtonBand
          degreeAtLeastTwo seed.newton seed.sourceRefines seed.radiusPositive band
          refinesCurrent seed.displacementSmall seed.taylorSmall
      ambientLeftClearance := leftEq.symm ▸ lines.left.2.val
      ambientRightClearance := rightEq.symm ▸ lines.right.2.val
      ambientBottomClearance := bottomEq.symm ▸ lines.bottom.2.val
      ambientTopClearance := topEq.symm ▸ lines.top.2.val }

/-- Read back the supplied band and complete original state from the same retained line cache. -/
private theorem stateFromLines_readbacks (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (seed : Seed squarefree elimination current)
    (band : Box.Band.Basic.BandBox (Anchor.anchorNewtonCenter p seed.source) seed.radius)
    (sameBand : band = seed.band)
    (lines : Newton.Band.Prepare.Lines elimination current.box ambient
      (Anchor.anchorNewtonCenter p seed.source) seed.radiusPositive) :
    (stateFromLines degreeAtLeastTwo seed band sameBand lines).box = band.box ∧
      stateFromLines degreeAtLeastTwo seed band sameBand lines = seed.state degreeAtLeastTwo := by
  constructor
  · rfl
  · cases sameBand
    rcases lines with ⟨⟨⟨left, leftEq⟩, ⟨ambientLeft, ambientLeftEq⟩⟩,
      ⟨⟨right, rightEq⟩, ⟨ambientRight, ambientRightEq⟩⟩,
      ⟨⟨bottom, bottomEq⟩, ⟨ambientBottom, ambientBottomEq⟩⟩,
      ⟨⟨top, topEq⟩, ⟨ambientTop, ambientTopEq⟩⟩⟩
    cases leftEq
    cases ambientLeftEq
    cases rightEq
    cases ambientRightEq
    cases bottomEq
    cases ambientBottomEq
    cases topEq
    cases ambientTopEq
    rfl

/-- Restoring the original seed state keeps the actual supplied band box. -/
theorem stateFromLines_box (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (seed : Seed squarefree elimination current)
    (band : Box.Band.Basic.BandBox (Anchor.anchorNewtonCenter p seed.source) seed.radius)
    (sameBand : band = seed.band)
    (lines : Newton.Band.Prepare.Lines elimination current.box ambient
      (Anchor.anchorNewtonCenter p seed.source) seed.radiusPositive) :
    (stateFromLines degreeAtLeastTwo seed band sameBand lines).box = band.box :=
  (stateFromLines_readbacks degreeAtLeastTwo seed band sameBand lines).1

/-- Restoring all original band lines returns the complete original seed state. -/
theorem stateFromLines_eq (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (seed : Seed squarefree elimination current)
    (band : Box.Band.Basic.BandBox (Anchor.anchorNewtonCenter p seed.source) seed.radius)
    (sameBand : band = seed.band)
    (lines : Newton.Band.Prepare.Lines elimination current.box ambient
      (Anchor.anchorNewtonCenter p seed.source) seed.radiusPositive) :
    stateFromLines degreeAtLeastTwo seed band sameBand lines = seed.state degreeAtLeastTwo :=
  (stateFromLines_readbacks degreeAtLeastTwo seed band sameBand lines).2

end Purelib.RootIsolation.Newton.Restart.Seed

end
