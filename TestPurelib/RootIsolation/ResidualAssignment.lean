module

import Purelib.RootIsolation.Residual.Global.Assignment
import Purelib.RootIsolation.Exact.Ownership.Replay
import Purelib.RootIsolation.Newton.Band.Prepare
import Purelib.RootIsolation.Newton.Extraction.Geometry
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.RootIsolation.Newton.Restart.Seed.State
import Purelib.RootIsolation.Newton.Restart.Seed.Track
import Purelib.Geometry.Rational.Box.Band.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Anchor

/-!
# Original residual assignments from retained numerical work

The clients restore complete seed states and tracks, then attach the original
partition ownership from its authenticated assignment-radius state. Their
readbacks retain whole original objects, including arbitrary isolation tracks.
-/

namespace TestPurelib.RootIsolation.ResidualAssignment

open Purelib
open Purelib.Data
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.RootIsolation
open Purelib.RootIsolation.Newton.Restart
open Purelib.RootIsolation.Residual.Global

section Seed

variable {p : CoefficientPolynomial} {ambient : Box} {degreeBound : Nat}
  {squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p}
  {elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound}
  {current : Clearance.Box.Region.ProtectedAmbient p ambient}
  (degree : 2 ≤ p.natDegree) (seed : Seed squarefree elimination current)
  (band : Box.Band.Basic.BandBox (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p seed.source) seed.radius)
  (sameBand : band = seed.band)
  (lines : Newton.Band.Prepare.Lines elimination current.box ambient
    (Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p seed.source) seed.radiusPositive)

example : (seed.stateFromLines degree band sameBand lines).box = band.box :=
  seed.stateFromLines_box degree band sameBand lines

example : seed.stateFromLines degree band sameBand lines = seed.state degree :=
  seed.stateFromLines_eq degree band sameBand lines

example :
    seed.trackFromState degree (seed.stateFromLines degree band sameBand lines)
      (seed.stateFromLines_eq degree band sameBand lines) = seed.track degree :=
  seed.trackFromState_eq degree _ _

example :
    (seed.trackFromState degree (seed.stateFromLines degree band sameBand lines)
      (seed.stateFromLines_eq degree band sameBand lines)).initial.box = band.box :=
  (congrArg (fun state => state.box) (seed.trackFromState_initial degree _ _)).trans
    (seed.stateFromLines_box degree band sameBand lines)

end Seed

section Band

variable {p : CoefficientPolynomial} {ambient : Box} {degreeBound : Nat}
  (degree : 2 ≤ p.natDegree) (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
  (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
  (current : State.Raw.RawWindingState p ambient) {epsilon : Rational}
  (geometry : Newton.Extraction.Geometry squarefree current epsilon)
  (band : Box.Band.Basic.BandBox geometry.newton.point geometry.radius)
  (same : band = Elimination.Axis.Band.selectedBand elimination
    geometry.newton.point geometry.radius geometry.radiusPositive)
  (lines : Newton.Band.Prepare.Lines elimination current.box ambient
    geometry.newton.point geometry.radiusPositive)

example :
    Newton.Band.Prepare.fromGeometryWithBand degree squarefree elimination current geometry band same lines =
      Newton.Band.Prepare.fromGeometry degree squarefree elimination current geometry :=
  (Newton.Band.Prepare.fromGeometryWithBand_eq degree squarefree elimination current geometry band same lines).trans
    (Newton.Band.Prepare.fromGeometryWithLines_eq degree squarefree elimination current geometry lines)

example :
    (Newton.Band.Prepare.fromGeometryWithBand degree squarefree elimination current geometry band same lines).band =
      band.recenter geometry.newton.point_eq :=
  Newton.Band.Prepare.fromGeometryWithBand_band degree squarefree elimination current geometry band same lines

/-- Retain the actual constructed box with its original half-square accuracy bound. -/
def retainedBandBox : {box : Box // box = band.box ∧ box.diagonalSq ≤ (1 / 2 : Rational) * epsilon ^ 2} := by
  let result := Newton.Band.Prepare.fromGeometryWithBand degree squarefree elimination current geometry band same lines
  have boxSame : result.box = band.box :=
    Newton.Band.Prepare.fromGeometryWithBand_box degree squarefree elimination current geometry band same lines
  exact ⟨result.box, boxSame, result.diagonalSq_le_half⟩

example : band.box.diagonalSq ≤ (1 / 2 : Rational) * epsilon ^ 2 := by
  let retained := retainedBandBox degree squarefree elimination current geometry band same lines
  rewrite [← retained.property.1]
  exact retained.property.2

-- Existing clients can still reduce the original default's retained fields directly.
example :
    (Newton.Band.Prepare.fromGeometryWithLines degree squarefree elimination current geometry lines).source =
      geometry.source := rfl

example :
    (Newton.Band.Prepare.fromGeometryWithLines degree squarefree elimination current geometry lines).radius =
      geometry.radius := rfl

example :
    (Newton.Band.Prepare.fromGeometryWithLines degree squarefree elimination current geometry lines).newton =
      geometry.newton := rfl

example :
    (Newton.Band.Prepare.fromGeometryWithLines degree squarefree elimination current geometry lines).box =
      (Elimination.Axis.Band.selectedBand elimination geometry.newton.point geometry.radius
        geometry.radiusPositive).box := rfl

end Band

section Assignment

variable {p : CoefficientPolynomial} (input : FTA.Squarefree.Input p) {degreeBound : Nat}
  (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
  (output : Exact.Basic.Output p (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p) p.natDegree)
  (support : output.support = Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p)
  (sample : Gaussian.Basic.Canonical)
  (inside : (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p).Contains sample)
  {epsilon : Rational} (positive : 0 < epsilon)
  (small : Gaussian.Norm.Basic.normSq (p.eval sample) < Assignment.insideResidualTarget input epsilon)
  (seed : Seed input.squarefree elimination (Assignment.largeSquareProtectedAmbient input.degreePositive))
  (sameSeed : seed = Assignment.insideSeed input elimination sample inside positive small)
  (state : State.WindingOne.Basic.WindingOneState p (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p))
  (sameState : state = seed.state input.degreeAtLeastTwo)
  (track : Track.Basic.WindingOneTrack p (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p))
  (sameTrack : track = seed.track input.degreeAtLeastTwo)
  (saved : Exact.Ownership.Replay.Refined output track)

/-- Restore original partition ownership and assemble the assignment without another refinement. -/
def restoreAssigned : Assignment.AssignedResult input sample epsilon output := by
  let boxes := FTA.Squarefree.Build.BoxFTA.fromIsolation input output
  have supported : track.initial.box.Refines output.support := support.symm ▸ track.initial.refinesAmbient
  let owner := Exact.Ownership.Replay.restore input.degreeAtLeastTwo input.squarefree input.elimination
    output track supported saved
  have sameOwner : owner = boxes.ownership track supported :=
    Exact.Ownership.Replay.restore_eq input.degreeAtLeastTwo input.squarefree input.elimination
      output track supported saved
  exact Assignment.assignInsideFromCaches input elimination boxes support sample inside positive small
    seed sameSeed state sameState track sameTrack owner sameOwner

/-- The cache-only chain returns the complete original assignment on the same isolation. -/
theorem restoreAssigned_eq :
    restoreAssigned input elimination output support sample inside positive small seed sameSeed state sameState
      track sameTrack saved =
      Assignment.assignInsideWithElimination input elimination (FTA.Squarefree.Build.BoxFTA.fromIsolation input output)
        support sample inside positive small := by
  exact Assignment.assignInsideFromCaches_eq input elimination _ support sample inside positive small
    seed sameSeed state sameState track sameTrack _
    (Exact.Ownership.Replay.restore_eq input.degreeAtLeastTwo input.squarefree input.elimination
      output track (support.symm ▸ track.initial.refinesAmbient) saved)

end Assignment

end TestPurelib.RootIsolation.ResidualAssignment
