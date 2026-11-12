module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Clearance.Pair.Bezout
import Purelib.Polynomial.Clearance.Pair.Replay
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Path.Components
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.RootIsolation.State.WindingOne.Raw

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance
import Purelib.RootIsolation.SquareRoot.Clearance.QuadraticCoefficientClearance
import Purelib.RootIsolation.SquareRoot.Replay.PreparedBoundaryReplay
public import Purelib.RootIsolation.SquareRoot.Replay.PreparedRootStateReplay
public import Purelib.Riemann.RootContinuation.CheckedSquareRootPreparation
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Rational.Bezout.Basic
import Purelib.Polynomial.Power.Gaussian
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.Riemann.RootContinuation.UniformSquareRootPreparation
import Purelib.RootIsolation.Refinement.Basic
import Purelib.RootIsolation.SquareRoot.Clearance.QuadraticAxisElimination
import Purelib.RootIsolation.State.Raw
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib

open Purelib.RootIsolation

public section

/-!
# Reusing legacy root data at raw-state-dependent preparation boundaries

The old snapshot retains the box and boundary bound, but not the original
ambient-line bounds or refiner.  Checked cofactors supply *new* ambient-line
certificates, solely to construct a representative of the same raw state.
This is not restoration of the original complete owner.  The equalities
below identify only operations proved to ignore those missing fields.
-/

namespace Purelib.RootIsolation.SquareRoot.Replay.PreparedRawStateReplay

open Purelib.Riemann.Integration Purelib.Riemann.RootContinuation Purelib.Riemann.Topology

/-- The rational coordinate field of the retained replay measurements. -/
abbrev Coordinate := Fraction.Rational
/-- The exact Gaussian parameter type of the quadratic source. -/
abbrev Gaussian := Gaussian.Basic.Canonical
/-- The rational rectangular box used by the retained quadratic state. -/
abbrev Box := Geometry.Rational.Box
/-- The original winding-one state for the quadratic parameter and its retained ambient box. -/
abbrev State := PreparedRootStateReplay.State
/-- The original quadratic owner, including its actual track and refinement function. -/
abbrev Owner := SquareRootContinuationChain.Owner

set_option genInjectivity false in
/-- The original raw-state payload consisting of its exact box and boundary-clearance bound. -/
structure Data where
  /-- The exact original state box. -/ box : Box
  /-- The exact original boundary-clearance bound. -/ boundary : Coordinate

constructive_injectivity Data

/-- Read the original state's box and boundary bound without asserting equality of its ambient-line data. -/
@[expose] def capture {parameter : Gaussian} {ambient :
  Box} (state : State parameter
  ambient) : Data :=
  ⟨state.box, state.clearance.bound⟩

/-- The raw state has no executable fields beyond this finite legacy data.
Ambient containment, properness and winding nonzeroness are proofs. -/
theorem raw_eq_of_capture_eq {parameter : Gaussian} {ambient :
  Box}
    (first second : State parameter ambient) (same :
      capture first = capture second)
      :
    first.raw = second.raw := by
  cases first with
  | mk firstBox _ _ firstBoundary _ _ _ _ _ =>
    cases second with
    | mk secondBox _ _ secondBoundary _ _ _ _ _ =>
      cases firstBoundary
      cases secondBoundary
      cases same
      rfl

/-- Check a cofactor identity once, then derive a positive bound on the actual
ambient interval.  The number is new; it is never labelled an original bound. -/
@[expose] def auxiliaryLine (axis : PreparedRootStateReplay.Axis) (parameter :
  Gaussian) (ambient : Box)
    (coordinate : Coordinate) (witness :
      PreparedBoundaryReplay.Witness) :
    Except Clearance.Pair.Replay.Failure (axis.Clearance parameter ambient coordinate) := do
  let coprime ← Clearance.Pair.Replay.checkCoprime
    (Dense.Gaussian.Path.Components.pathReal (PreparedBoundaryReplay.rootPolynomial parameter)
      (axis.base coordinate) axis.direction)
    (Dense.Gaussian.Path.Components.pathImag (PreparedBoundaryReplay.rootPolynomial parameter)
      (axis.base coordinate) axis.direction)
    witness
  return axis.ofPath parameter ambient coordinate
    (Clearance.Pair.Bezout.certificateOfCoprime coprime (axis.interval ambient))

/-- Select the vertical or horizontal axis corresponding to the retained boundary side. -/
@[expose] def sideAxis : PreparedBoundaryReplay.Side → PreparedRootStateReplay.Axis
  | .left | .right => .vertical
  | .bottom | .top => .horizontal

/-- Read the original box coordinate of the selected boundary side. -/
@[expose] def sideCoordinate (box : Box) :
  PreparedBoundaryReplay.Side → Coordinate
  | .left => box.xLower
  | .right => box.xUpper
  | .bottom => box.yLower
  | .top => box.yUpper

/-- Read the retained finite polynomial-pair witness for the selected side. -/
@[expose] def sideWitness (witnesses : PreparedBoundaryReplay.Witnesses) :
  PreparedBoundaryReplay.Side → PreparedBoundaryReplay.Witness
  | .left => witnesses.left
  | .right => witnesses.right
  | .bottom => witnesses.bottom
  | .top => witnesses.top

/-- Check the selected original side witness and construct a certified auxiliary ambient-line bound. -/
@[expose] def attemptLine (side : PreparedBoundaryReplay.Side) (parameter :
  Gaussian) (ambient : Box)
    (box : Box) (witnesses :
      PreparedBoundaryReplay.Witnesses) :=
  auxiliaryLine (sideAxis side)
    parameter ambient (sideCoordinate box side)
    (sideWitness witnesses side)

set_option genInjectivity false in
/-- A retained failed raw-state reconstruction on the original checkpoint.

Preserve geometry, boundary, line-check procedure and exact winding failures while distinguishing newly computed ambient
bounds from original checkpoint data. -/
inductive Failure (parameter : Gaussian) (ambient :
  Box) (data : Data) (witnesses :
  PreparedBoundaryReplay.Witnesses) where
  /-- The supplied box fails properness. -/ | notProper (failed : ¬ data.box.Proper)
  /-- The supplied box fails refinement of the original ambient. -/ | outsideAmbient (failed : ¬ data.box.Refines
    ambient)
  /-- The requested original boundary bound fails its retained reconstruction check. -/ | boundary (failure :
    PreparedBoundaryReplay.QuadraticFailure parameter data.box data.boundary witnesses)
  /-- Retain the selected side, auxiliary line failure and exact failed procedure equation. -/ | line (side :
    PreparedBoundaryReplay.Side) (failure : Clearance.Pair.Replay.Failure)
      (procedure : attemptLine side parameter ambient data.box witnesses =
        .error failure)
  /-- Retain the actual computed winding and the proof that it differs from four. -/ | winding (actual : Int)
      (actual_eq : actual = Winding.Box.Basic.quadrupledBoxWinding
        (PreparedBoundaryReplay.rootPolynomial parameter) data.box)
      (failed : actual ≠ 4)

constructive_injectivity Failure

set_option genInjectivity false in
/-- A certified representative whose raw payload equals the supplied checkpoint.

Its auxiliary ambient-line bounds are newly constructed; the guarantee preserves the original raw state rather than an
unknown refinement history. -/
structure Checked (parameter : Gaussian) (ambient :
  Box) (data : Data) where
  /-- The certified state with restored raw data and newly computed auxiliary ambient-line bounds. -/ representative :
    State parameter ambient
  /-- The representative's box and boundary bound equal the original supplied checkpoint. -/ capture_eq :
    capture representative = data

constructive_injectivity Checked

/-- Check one original side and retain its actual failed procedure equation when reconstruction fails. -/
@[expose] def checkedLine (side : PreparedBoundaryReplay.Side) (parameter :
  Gaussian) (ambient : Box)
    (data : Data) (witnesses :
      PreparedBoundaryReplay.Witnesses) :
    Except (Failure parameter ambient data witnesses)
      ((sideAxis side).Clearance parameter ambient
        (sideCoordinate data.box side)) :=
  match procedure : attemptLine side parameter ambient data.box witnesses with
  | .ok clearance => .ok clearance
  | .error failure => .error (.line side failure procedure)

open Purelib.RootIsolation.SquareRoot.Replay.PreparedRawStateReplay in
/-- Restore the raw state and construct certified auxiliary ambient fields.
No original side numbers are inferred and no shrinking or isolation runs. -/
@[expose] def check (parameter : Gaussian) (ambient :
  Box) (data : Data) (witnesses :
  PreparedBoundaryReplay.Witnesses) :
    Except (Failure parameter ambient data witnesses)
      (Checked parameter ambient data) := by
  letI : Decidable data.box.Proper := by unfold Box.Proper; infer_instance
  letI : Decidable (data.box.Refines ambient) := by unfold Box.Refines; infer_instance
  if proper : data.box.Proper then
    if within : data.box.Refines ambient then
      exact do
        let boundary ← (PreparedBoundaryReplay.checkQuadratic parameter data.box data.boundary
          witnesses).mapError .boundary
        let actual := Winding.Box.Basic.quadrupledBoxWinding (PreparedBoundaryReplay.rootPolynomial
          parameter) data.box
        if winding : actual = 4 then
          let left ← checkedLine .left parameter ambient data witnesses
          let right ← checkedLine .right parameter ambient data witnesses
          let bottom ← checkedLine .bottom parameter ambient data witnesses
          let top ← checkedLine .top parameter ambient data witnesses
          let representative : State parameter ambient :=
            { box := data.box, refinesAmbient := within, proper := proper,
              clearance := boundary.result.clearance, rawWindingFour := winding,
              ambientLeftClearance := left, ambientRightClearance := right,
              ambientBottomClearance := bottom, ambientTopClearance := top }
          return ⟨representative, by
            change Data.mk data.box boundary.result.clearance.bound = data
            rw [boundary.result.bound_eq]⟩
        else .error (.winding actual rfl winding)
    else exact .error (.outsideAmbient within)
  else exact .error (.notProper proper)

/-- The reconstructed representative has exactly the original raw state. -/
theorem Checked.raw_eq_original {parameter : Gaussian} {ambient :
  Box}
    (original : State parameter ambient) (restored :
      Checked parameter ambient
      (capture original)) :
    restored.representative.raw = original.raw :=
  raw_eq_of_capture_eq restored.representative original restored.capture_eq

/-- Coefficient strengthening discards the incoming ambient-line bounds and
refiner.  It creates exactly the same whole owner from the same raw state. -/
theorem strengthen_eq_of_raw_eq {parameter : Gaussian}
    (first second : Owner parameter) (ambient : first.ambient = second.ambient)
    (same : ambient ▸ first.track.initial.raw = second.track.initial.raw) :
    Clearance.QuadraticCoefficientClearance.strengthen first =
      Clearance.QuadraticCoefficientClearance.strengthen second := by
  cases first with
  | mk firstNonzero firstAmbient firstTrack =>
    cases second with
    | mk secondNonzero secondAmbient secondTrack =>
      cases ambient
      cases firstTrack with
      | mk firstState _ _ _ _ =>
        cases secondTrack with
        | mk secondState _ _ _ _ =>
          cases firstState with
          | mk firstBox _ _ firstBoundary _ _ _ _ _ =>
            cases secondState with
            | mk secondBox _ _ secondBoundary _ _ _ _ _ =>
              cases firstBoundary
              cases secondBoundary
              cases same
              rfl

/-- The optional diameter search consumes only the raw state.  Comparison
projects away the result's source-indexed proof fields, not its target owner.
Thus neither success nor failure can depend on omitted ambient-line bounds
or on an unidentified incoming refiner. -/
theorem attempt_values_eq_of_raw_eq
    {polynomial : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {ambient : Box} {start finish :
      Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) (parameter :
      Coordinate)
    (first second : Owner (polynomial.eval (segment.pointAt parameter)))
    (sameAmbient : first.ambient = second.ambient)
    (same : sameAmbient ▸ first.track.initial.raw = second.track.initial.raw)
    (diameter : Coordinate) :
    ((CheckedSquareRootPreparation.attempt segment parameter first diameter).value).map
      (fun result => result.value) =
      ((CheckedSquareRootPreparation.attempt segment parameter second diameter).value).map
        (fun result => result.value) := by
  cases first with
  | mk firstNonzero firstAmbient firstTrack =>
    cases second with
    | mk secondNonzero secondAmbient secondTrack =>
      cases sameAmbient
      cases firstTrack with
      | mk firstState _ _ _ _ =>
        cases secondTrack with
        | mk secondState _ _ _ _ =>
          cases firstState with
          | mk firstBox _ _ firstBoundary _ _ _ _ _ =>
            cases secondState with
            | mk secondBox _ _ secondBoundary _ _ _ _ _ =>
              cases firstBoundary
              cases secondBoundary
              cases same
              letI (box ambient : Box) : Decidable (box.Refines ambient) := by
                unfold Box.Refines
                infer_instance
              rw [CheckedSquareRootPreparation.attempt_value_eq,
                CheckedSquareRootPreparation.attempt_value_eq]
              unfold CheckedSquareRootPreparation.searchValue
                CheckedSquareRootPreparation.initialProposal
                CheckedSquareRootPreparation.acceptedValue
                CheckedSquareRootPreparation.Candidate.check
                CheckedSquareRootPreparation.Candidate.capture
              dsimp only [State.WindingOne.Basic.WindingOneState.raw]
              split <;> simp_all only [Option.map, -eq_self, -iff_self]
              all_goals first | rfl | (split_ifs <;> rfl)

/-- Coefficient strengthening of the reconstructed representative recovers the original strengthened owner exactly. -/
theorem Checked.strengthen_eq_original {parameter : Gaussian} (original :
  Owner parameter)
    (restored : Checked parameter original.ambient
      (capture original.track.initial)) :
    Clearance.QuadraticCoefficientClearance.strengthen
        (Clearance.ExactQuadraticOwnerClearance.ownerOfState original.parameterNonzero
          restored.representative) =
      Clearance.QuadraticCoefficientClearance.strengthen original :=
  strengthen_eq_of_raw_eq _ original rfl (restored.raw_eq_original
    original.track.initial)

/-- The optional diameter search returns the same target-owner values from the reconstructed raw state as from the
original owner. -/
theorem Checked.attemptValues_eq_original
    {polynomial : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {ambient : Box} {start finish :
      Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) (parameter :
      Coordinate)
    (original : Owner (polynomial.eval (segment.pointAt parameter)))
    (restored : Checked _ original.ambient
      (capture original.track.initial)) (diameter :
      Coordinate) :
    ((CheckedSquareRootPreparation.attempt segment parameter
        (Clearance.ExactQuadraticOwnerClearance.ownerOfState original.parameterNonzero
          restored.representative)
        diameter).value).map (fun result => result.value) =
      ((CheckedSquareRootPreparation.attempt segment parameter original diameter).value).map
        (fun result => result.value) :=
  attempt_values_eq_of_raw_eq segment parameter
    (Clearance.ExactQuadraticOwnerClearance.ownerOfState original.parameterNonzero restored.representative)
      original rfl
    (restored.raw_eq_original original.track.initial) diameter

end Purelib.RootIsolation.SquareRoot.Replay.PreparedRawStateReplay

end
