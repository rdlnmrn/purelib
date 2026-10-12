module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Gaussian.Cast.Imaginary
import Purelib.Data.Gaussian.Constants
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Interval.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Intervals
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Clearance.Box.Line.Basic
import Purelib.Polynomial.Clearance.Box.Line.Path
import Purelib.Polynomial.Clearance.Pair.Basic
import Purelib.Polynomial.Clearance.Pair.Replay
import Purelib.Polynomial.Dense.Gaussian.Path.Components
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.RootIsolation.State.WindingOne.Basic

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance
import Purelib.RootIsolation.SquareRoot.Clearance.QuadraticCoefficientClearance
public import Purelib.RootIsolation.SquareRoot.Replay.PreparedBoundaryReplay

import Purelib.Elab.Deriving.Repr
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Multiplication
import Purelib.Polynomial.Dense.Rational.Basic
import Purelib.Polynomial.Dense.Rational.Bezout.Basic

public section

/-!
# Checked restoration of complete finite quadratic root states

The snapshot retains all five original clearance numbers.  Checking restores
their proofs and the finite winding equation, not merely another state on the
same box.  The four ambient-line bounds cannot be inferred from the boundary
minimum.  A restored state determines the existing accelerated/deferred owner
constructors, but not an arbitrary owner's missing refinement history.
-/

namespace Purelib.RootIsolation.SquareRoot.Replay.PreparedRootStateReplay

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

open Purelib.Riemann.Integration Purelib.Riemann.Topology Purelib.RootIsolation.SquareRoot.Replay
open Purelib.Polynomial.Geometry.BoxClearance Purelib.Polynomial.Path Purelib.RootIsolation.Winding

/-- The rational coordinate field of the retained replay measurements. -/
abbrev Coordinate := Fraction.Rational
/-- The exact Gaussian parameter type of the quadratic source. -/
abbrev Gaussian := Gaussian.Basic.Canonical
/-- The rational rectangular box used by the retained quadratic state. -/
abbrev Box := Purelib.Geometry.Rational.Box

set_option genInjectivity false in
/-- The complete finite executable payload of a quadratic winding-one state.

Retain its exact box, boundary bound and all four ambient-line bounds; the remaining state fields are proofs. -/
structure Data where
  /-- The exact state box retained by the checkpoint. -/ box : SquareRoot.Replay.PreparedRootStateReplay.Box
  /-- The original box-boundary clearance bound. -/ boundary : SquareRoot.Replay.PreparedRootStateReplay.Coordinate
  /-- The original left ambient-line clearance bound. -/ left : SquareRoot.Replay.PreparedRootStateReplay.Coordinate
  /-- The original right ambient-line clearance bound. -/ right : SquareRoot.Replay.PreparedRootStateReplay.Coordinate
  /-- The original bottom ambient-line clearance bound. -/ bottom : SquareRoot.Replay.PreparedRootStateReplay.Coordinate
  /-- The original top ambient-line clearance bound. -/ top : SquareRoot.Replay.PreparedRootStateReplay.Coordinate

constructive_injectivity Data

/-- The original winding-one state for the quadratic parameter and its retained ambient box. -/
abbrev State (parameter : SquareRoot.Replay.PreparedRootStateReplay.Gaussian) (ambient :
  SquareRoot.Replay.PreparedRootStateReplay.Box) :=
  State.WindingOne.Basic.WindingOneState (SquareRoot.Replay.PreparedBoundaryReplay.rootPolynomial parameter) ambient

/-- Read the exact box and five clearance bounds from the supplied winding-one state. -/
@[expose] def capture {parameter : SquareRoot.Replay.PreparedRootStateReplay.Gaussian} {ambient :
  SquareRoot.Replay.PreparedRootStateReplay.Box} (state : SquareRoot.Replay.PreparedRootStateReplay.State parameter
  ambient) : Data :=
  ⟨state.box, state.clearance.bound, state.ambientLeftClearance.bound,
    state.ambientRightClearance.bound, state.ambientBottomClearance.bound,
    state.ambientTopClearance.bound⟩

/-- Equality of these finite payloads identifies the whole state because the
remaining fields are proofs.  This says nothing about a track's functions. -/
theorem capture_injective {parameter : SquareRoot.Replay.PreparedRootStateReplay.Gaussian} {ambient :
  SquareRoot.Replay.PreparedRootStateReplay.Box}
    (first second : SquareRoot.Replay.PreparedRootStateReplay.State parameter ambient) (same :
      SquareRoot.Replay.PreparedRootStateReplay.capture first = SquareRoot.Replay.PreparedRootStateReplay.capture
      second) :
    first = second := by
  cases first with
  | mk firstBox _ _ firstBoundary _ firstLeft firstRight firstBottom firstTop =>
    cases second with
    | mk secondBox _ _ secondBoundary _ secondLeft secondRight secondBottom secondTop =>
      cases firstBoundary
      cases firstLeft
      cases firstRight
      cases firstBottom
      cases firstTop
      cases secondBoundary
      cases secondLeft
      cases secondRight
      cases secondBottom
      cases secondTop
      cases same
      rfl

/-- The orientation of a retained vertical or horizontal line-clearance request. -/
inductive Axis where
  /-- A vertical line at the supplied real coordinate. -/ | vertical /-- A horizontal line at the supplied imaginary
    coordinate. -/ | horizontal
deriving DecidableEq
derive_exposed_repr Purelib.RootIsolation.SquareRoot.Replay.PreparedRootStateReplay.Axis

/-- Read the Gaussian base point of the selected line at its supplied coordinate. -/
@[expose] def Axis.base : SquareRoot.Replay.PreparedRootStateReplay.Axis →
  SquareRoot.Replay.PreparedRootStateReplay.Coordinate → SquareRoot.Replay.PreparedRootStateReplay.Gaussian
  | .vertical => Gaussian.Cast.Winding.verticalBase
  | .horizontal => Gaussian.Cast.Imaginary.horizontalBase

/-- Read the canonical unit direction of the selected vertical or horizontal line. -/
@[expose] def Axis.direction : SquareRoot.Replay.PreparedRootStateReplay.Axis →
  SquareRoot.Replay.PreparedRootStateReplay.Gaussian
  | .vertical => Gaussian.Constants.imaginaryUnit
  | .horizontal => Gaussian.Constants.horizontalDirection

/-- Read the ambient box's interval along the selected line orientation. -/
@[expose] def Axis.interval : SquareRoot.Replay.PreparedRootStateReplay.Axis →
  SquareRoot.Replay.PreparedRootStateReplay.Box → Data.Rat.Interval.Bounds
  | .vertical => Box.Intervals.verticalInterval
  | .horizontal => Box.Intervals.horizontalInterval

/-- The original vertical or horizontal line-clearance certificate selected by the axis. -/
@[expose] def Axis.Clearance (axis : SquareRoot.Replay.PreparedRootStateReplay.Axis) (parameter :
  SquareRoot.Replay.PreparedRootStateReplay.Gaussian) (ambient : SquareRoot.Replay.PreparedRootStateReplay.Box)
    (coordinate : SquareRoot.Replay.PreparedRootStateReplay.Coordinate) : Type :=
  match axis with
  | .vertical => Clearance.Box.Line.Basic.VerticalLineClearance (SquareRoot.Replay.PreparedBoundaryReplay.rootPolynomial
    parameter) ambient coordinate
  | .horizontal => Clearance.Box.Line.Basic.HorizontalLineClearance
    (SquareRoot.Replay.PreparedBoundaryReplay.rootPolynomial parameter) ambient coordinate

/-- Read the exact rational bound retained by the selected line-clearance certificate. -/
@[expose] def Axis.bound {axis : SquareRoot.Replay.PreparedRootStateReplay.Axis} {parameter :
  SquareRoot.Replay.PreparedRootStateReplay.Gaussian} {ambient : SquareRoot.Replay.PreparedRootStateReplay.Box}
  {coordinate : SquareRoot.Replay.PreparedRootStateReplay.Coordinate}
    (clearance : axis.Clearance parameter ambient coordinate) : Fraction.Rational :=
  match axis with
  | .vertical => clearance.bound
  | .horizontal => clearance.bound

/-- Compute the quadratic coefficient and gap lower bound for the selected line. -/
@[expose] def Axis.ceiling : SquareRoot.Replay.PreparedRootStateReplay.Axis →
  SquareRoot.Replay.PreparedRootStateReplay.Gaussian → SquareRoot.Replay.PreparedRootStateReplay.Box →
  SquareRoot.Replay.PreparedRootStateReplay.Coordinate → SquareRoot.Replay.PreparedRootStateReplay.Coordinate
  | .vertical => SquareRoot.Clearance.QuadraticCoefficientClearance.verticalBound
  | .horizontal => SquareRoot.Clearance.QuadraticCoefficientClearance.horizontalBound

/-- Transport the checked polynomial-pair path certificate to the same vertical or horizontal line. -/
@[expose] def Axis.ofPath (axis : SquareRoot.Replay.PreparedRootStateReplay.Axis) (parameter :
  SquareRoot.Replay.PreparedRootStateReplay.Gaussian) (ambient : SquareRoot.Replay.PreparedRootStateReplay.Box)
  (coordinate : SquareRoot.Replay.PreparedRootStateReplay.Coordinate)
    (certificate : Clearance.Pair.Basic.Certificate
      (Dense.Gaussian.Path.Components.pathReal (SquareRoot.Replay.PreparedBoundaryReplay.rootPolynomial parameter)
        (axis.base coordinate) axis.direction)
      (Dense.Gaussian.Path.Components.pathImag (SquareRoot.Replay.PreparedBoundaryReplay.rootPolynomial parameter)
        (axis.base coordinate) axis.direction)
      (axis.interval ambient)) : axis.Clearance parameter ambient coordinate := by
  cases axis with
  | vertical =>
      exact Clearance.Box.Line.Path.verticalOfPathCertificate
        (SquareRoot.Replay.PreparedBoundaryReplay.rootPolynomial parameter) ambient coordinate certificate
  | horizontal =>
      exact Clearance.Box.Line.Path.horizontalOfPathCertificate
        (SquareRoot.Replay.PreparedBoundaryReplay.rootPolynomial parameter) ambient coordinate certificate

/-- Line-clearance transport preserves the original path certificate's bound exactly. -/
theorem Axis.ofPath_bound (axis : SquareRoot.Replay.PreparedRootStateReplay.Axis) (parameter :
  SquareRoot.Replay.PreparedRootStateReplay.Gaussian) (ambient : SquareRoot.Replay.PreparedRootStateReplay.Box)
  (coordinate : SquareRoot.Replay.PreparedRootStateReplay.Coordinate)
    (certificate : Clearance.Pair.Basic.Certificate
      (Dense.Gaussian.Path.Components.pathReal (SquareRoot.Replay.PreparedBoundaryReplay.rootPolynomial parameter)
        (axis.base coordinate) axis.direction)
      (Dense.Gaussian.Path.Components.pathImag (SquareRoot.Replay.PreparedBoundaryReplay.rootPolynomial parameter)
        (axis.base coordinate) axis.direction)
      (axis.interval ambient)) :
    SquareRoot.Replay.PreparedRootStateReplay.Axis.bound (axis.ofPath parameter ambient coordinate certificate) =
      certificate.bound := by
  cases axis <;> rfl

/-- Certify the requested positive line bound from the computed quadratic coefficient ceiling.

The original line, polynomial and ambient interval remain fixed, and the retained bound is the supplied request. -/
@[expose] def Axis.ofCeiling (axis : SquareRoot.Replay.PreparedRootStateReplay.Axis) (parameter :
  SquareRoot.Replay.PreparedRootStateReplay.Gaussian) (ambient : SquareRoot.Replay.PreparedRootStateReplay.Box)
    (coordinate bound : SquareRoot.Replay.PreparedRootStateReplay.Coordinate) (positive : 0 < bound)
    (carries : bound ≤ axis.ceiling parameter ambient coordinate) :
    axis.Clearance parameter ambient coordinate :=
  match axis with
  | .vertical =>
      { bound := bound, positive := positive,
        lower := fun value lower upper => carries.trans
          (by
            have scalar := SquareRoot.Clearance.QuadraticCoefficientClearance.vertical_lower parameter ambient
              coordinate value lower upper
            simpa only [Gaussian.Norm.Basic.normSq_eq_canonical, SquareRoot.Replay.PreparedRootStateReplay.Axis.ceiling,
              SquareRoot.Replay.PreparedBoundaryReplay.rootPolynomial,
              SquareRoot.Clearance.QuadraticCoefficientClearance.rootPolynomial] using scalar) }
  | .horizontal =>
      { bound := bound, positive := positive,
        lower := fun value lower upper => carries.trans
          (by
            have scalar := SquareRoot.Clearance.QuadraticCoefficientClearance.horizontal_lower parameter ambient value
              coordinate lower upper
            simpa only [Gaussian.Norm.Basic.normSq_eq_canonical, SquareRoot.Replay.PreparedRootStateReplay.Axis.ceiling,
              SquareRoot.Replay.PreparedBoundaryReplay.rootPolynomial,
              SquareRoot.Clearance.QuadraticCoefficientClearance.rootPolynomial] using scalar) }

/-- The coefficient-based line certificate retains the requested bound exactly. -/
theorem Axis.ofCeiling_bound (axis : SquareRoot.Replay.PreparedRootStateReplay.Axis) (parameter :
  SquareRoot.Replay.PreparedRootStateReplay.Gaussian) (ambient : SquareRoot.Replay.PreparedRootStateReplay.Box)
    (coordinate bound : SquareRoot.Replay.PreparedRootStateReplay.Coordinate) (positive : 0 < bound)
    (carries : bound ≤ axis.ceiling parameter ambient coordinate) :
    SquareRoot.Replay.PreparedRootStateReplay.Axis.bound (axis.ofCeiling parameter ambient coordinate bound positive
      carries) = bound := by
  cases axis <;> rfl

/-- Check the supplied finite witness on the original quadratic line and ambient interval. -/
@[expose] def attemptLine (axis : SquareRoot.Replay.PreparedRootStateReplay.Axis) (parameter :
  SquareRoot.Replay.PreparedRootStateReplay.Gaussian) (ambient : SquareRoot.Replay.PreparedRootStateReplay.Box)
    (coordinate bound : SquareRoot.Replay.PreparedRootStateReplay.Coordinate) (witness :
      SquareRoot.Replay.PreparedBoundaryReplay.Witness) :=
  Clearance.Pair.Replay.check
    (Dense.Gaussian.Path.Components.pathReal (SquareRoot.Replay.PreparedBoundaryReplay.rootPolynomial parameter)
      (axis.base coordinate) axis.direction)
    (Dense.Gaussian.Path.Components.pathImag (SquareRoot.Replay.PreparedBoundaryReplay.rootPolynomial parameter)
      (axis.base coordinate) axis.direction)
    (axis.interval ambient) bound witness

set_option genInjectivity false in
/-- A retained failure to restore the requested quadratic line bound.

Distinguish nonpositive requests, invalid witness data and an insufficient witness bound whose quadratic fallback also
fails. -/
inductive LineFailure (axis : SquareRoot.Replay.PreparedRootStateReplay.Axis) (parameter :
  SquareRoot.Replay.PreparedRootStateReplay.Gaussian) (ambient : SquareRoot.Replay.PreparedRootStateReplay.Box)
    (coordinate bound : SquareRoot.Replay.PreparedRootStateReplay.Coordinate) (witness :
      SquareRoot.Replay.PreparedBoundaryReplay.Witness) where
  /-- The requested line bound fails positivity. -/ | nonpositive (failed : ¬ 0 < bound)
  /-- The finite witness is invalid, retaining the exact failed checking equation. -/ | invalidWitness (failure :
    Clearance.Pair.Replay.Failure)
      (procedure : SquareRoot.Replay.PreparedRootStateReplay.attemptLine axis parameter ambient coordinate bound witness
        = .error failure)
  /-- Retain the failed witness check, exact quadratic ceiling and failed requested-bound comparison. -/ | insufficient
    (failure : Clearance.Pair.Replay.Failure)
      (procedure : SquareRoot.Replay.PreparedRootStateReplay.attemptLine axis parameter ambient coordinate bound witness
        = .error failure)
      (ceiling : SquareRoot.Replay.PreparedRootStateReplay.Coordinate) (ceiling_eq : ceiling = axis.ceiling parameter
        ambient coordinate)
      (failed : ¬ bound ≤ ceiling)

constructive_injectivity LineFailure

set_option genInjectivity false in
/-- The reconstructed original line-clearance certificate with exactly the requested bound.

The original axis, parameter, ambient box, line coordinate and requested bound index the retained line certificate and
its exact rational readback. -/
structure CheckedLine (axis : SquareRoot.Replay.PreparedRootStateReplay.Axis) (parameter :
  SquareRoot.Replay.PreparedRootStateReplay.Gaussian) (ambient : SquareRoot.Replay.PreparedRootStateReplay.Box)
    (coordinate bound : SquareRoot.Replay.PreparedRootStateReplay.Coordinate) where
  /-- The actual reconstructed line-clearance certificate on the original inputs. -/ clearance : axis.Clearance
    parameter ambient coordinate
  /-- The reconstructed line certificate retains the supplied bound exactly. -/ bound_eq :
    SquareRoot.Replay.PreparedRootStateReplay.Axis.bound clearance = bound

constructive_injectivity CheckedLine

set_option backward.match.sparseCases false in
/-- Reconstruct the requested line bound, not a new choice of bound.  A weak
valid cofactor can use the quadratic supplement; a malformed one cannot.

The retained original witness check is consumed before any coefficient
fallback. Its exact procedure equation, computed ceiling and typed failure
or certificate remain tied to the same original request. -/
@[expose] def checkLine (axis : SquareRoot.Replay.PreparedRootStateReplay.Axis) (parameter :
  SquareRoot.Replay.PreparedRootStateReplay.Gaussian) (ambient : SquareRoot.Replay.PreparedRootStateReplay.Box)
    (coordinate bound : SquareRoot.Replay.PreparedRootStateReplay.Coordinate) (witness :
      SquareRoot.Replay.PreparedBoundaryReplay.Witness) :
    Except (SquareRoot.Replay.PreparedRootStateReplay.LineFailure axis parameter ambient coordinate bound witness)
      (SquareRoot.Replay.PreparedRootStateReplay.CheckedLine axis parameter ambient coordinate bound) :=
  if positive : 0 < bound then
    match attempted : SquareRoot.Replay.PreparedRootStateReplay.attemptLine axis parameter ambient coordinate bound
      witness with
    | .ok verified => .ok
        ⟨axis.ofPath parameter ambient coordinate verified.certificate,
          (axis.ofPath_bound parameter ambient coordinate verified.certificate).trans verified.bound_eq⟩
    | .error failure =>
        match failure with
        | .insufficient .. =>
            let ceiling := axis.ceiling parameter ambient coordinate
            if carries : bound ≤ ceiling then
              .ok ⟨axis.ofCeiling parameter ambient coordinate bound positive carries,
                axis.ofCeiling_bound parameter ambient coordinate bound positive carries⟩
            else .error (.insufficient _ attempted ceiling rfl carries)
        | _ => .error (.invalidWitness _ attempted)
  else .error (.nonpositive positive)

set_option genInjectivity false in
/-- A failed finite state reconstruction with its actual offending input or check.

The alternatives retain improper geometry, failed ambient refinement, boundary or line failures, or the exact winding
value different from four. -/
inductive Failure (parameter : SquareRoot.Replay.PreparedRootStateReplay.Gaussian) (ambient :
  SquareRoot.Replay.PreparedRootStateReplay.Box) (data : SquareRoot.Replay.PreparedRootStateReplay.Data) (witnesses :
  SquareRoot.Replay.PreparedBoundaryReplay.Witnesses) where
  /-- The supplied state box fails properness. -/ | notProper (failed : ¬ data.box.Proper)
  /-- The supplied state box fails refinement of the original ambient box. -/ | outsideAmbient (failed : ¬
    data.box.Refines ambient)
  /-- The requested boundary clearance fails its retained quadratic reconstruction check. -/ | boundary (failure :
    SquareRoot.Replay.PreparedBoundaryReplay.QuadraticFailure parameter data.box data.boundary witnesses)
  /-- The original left ambient-line bound fails its retained finite reconstruction check. -/ | left (failure :
    SquareRoot.Replay.PreparedRootStateReplay.LineFailure .vertical parameter ambient data.box.xLower data.left
    witnesses.left)
  /-- The original right ambient-line bound fails its retained finite reconstruction check. -/ | right (failure :
    SquareRoot.Replay.PreparedRootStateReplay.LineFailure .vertical parameter ambient data.box.xUpper data.right
    witnesses.right)
  /-- The original bottom ambient-line bound fails its retained finite reconstruction check. -/ | bottom (failure :
    SquareRoot.Replay.PreparedRootStateReplay.LineFailure .horizontal parameter ambient data.box.yLower data.bottom
    witnesses.bottom)
  /-- The original top ambient-line bound fails its retained finite reconstruction check. -/ | top (failure :
    SquareRoot.Replay.PreparedRootStateReplay.LineFailure .horizontal parameter ambient data.box.yUpper data.top
    witnesses.top)
  /-- Retain the exact computed raw winding and the proof that it is not four. -/ | winding (actual : Int)
      (actual_eq : actual = Winding.Box.Basic.quadrupledBoxWinding
        (SquareRoot.Replay.PreparedBoundaryReplay.rootPolynomial parameter) data.box)
      (failed : actual ≠ 4)

constructive_injectivity Failure

set_option genInjectivity false in
/-- The reconstructed quadratic state whose entire finite payload equals the supplied data.

The retained state has the original parameter and ambient box; its exact capture equality identifies the saved box and
all five original clearance bounds. -/
structure Checked (parameter : SquareRoot.Replay.PreparedRootStateReplay.Gaussian) (ambient :
  SquareRoot.Replay.PreparedRootStateReplay.Box) (data : SquareRoot.Replay.PreparedRootStateReplay.Data) where
  /-- The actual reconstructed winding-one state on the original parameter and ambient. -/ state :
    SquareRoot.Replay.PreparedRootStateReplay.State parameter ambient
  /-- The reconstructed state's entire finite executable payload equals the supplied checkpoint. -/ data_eq :
    SquareRoot.Replay.PreparedRootStateReplay.capture state = data

constructive_injectivity Checked

open Purelib.RootIsolation.SquareRoot.Replay.PreparedRootStateReplay in
/-- Check all original finite state fields, including exact winding four.
No shrinking, preparation or owner generator is used. -/
@[expose] def check (parameter : SquareRoot.Replay.PreparedRootStateReplay.Gaussian) (ambient :
  SquareRoot.Replay.PreparedRootStateReplay.Box) (data : SquareRoot.Replay.PreparedRootStateReplay.Data) (witnesses :
  SquareRoot.Replay.PreparedBoundaryReplay.Witnesses) :
    Except (SquareRoot.Replay.PreparedRootStateReplay.Failure parameter ambient data witnesses)
      (SquareRoot.Replay.PreparedRootStateReplay.Checked parameter ambient data) := by
  letI : Decidable data.box.Proper := by unfold Box.Proper; infer_instance
  letI : Decidable (data.box.Refines ambient) := by unfold Box.Refines; infer_instance
  if proper : data.box.Proper then
    if within : data.box.Refines ambient then
      exact do
        let boundary ← (SquareRoot.Replay.PreparedBoundaryReplay.checkQuadratic parameter data.box data.boundary
          witnesses).mapError .boundary
        let left ← (checkLine .vertical parameter ambient data.box.xLower data.left witnesses.left).mapError .left
        let right ← (checkLine .vertical parameter ambient data.box.xUpper data.right witnesses.right).mapError .right
        let bottom ← (checkLine .horizontal parameter ambient data.box.yLower data.bottom witnesses.bottom).mapError
          .bottom
        let top ← (checkLine .horizontal parameter ambient data.box.yUpper data.top witnesses.top).mapError .top
        let actual := Winding.Box.Basic.quadrupledBoxWinding (SquareRoot.Replay.PreparedBoundaryReplay.rootPolynomial
          parameter) data.box
        if winding : actual = 4 then
          let state : SquareRoot.Replay.PreparedRootStateReplay.State parameter ambient :=
            { box := data.box, refinesAmbient := within, proper := proper,
              clearance := boundary.result.clearance, rawWindingFour := winding,
              ambientLeftClearance := left.clearance, ambientRightClearance := right.clearance,
              ambientBottomClearance := bottom.clearance, ambientTopClearance := top.clearance }
          return ⟨state, by
            change SquareRoot.Replay.PreparedRootStateReplay.Data.mk data.box boundary.result.clearance.bound
              (SquareRoot.Replay.PreparedRootStateReplay.Axis.bound left.clearance)
                (SquareRoot.Replay.PreparedRootStateReplay.Axis.bound right.clearance)
              (SquareRoot.Replay.PreparedRootStateReplay.Axis.bound bottom.clearance)
                (SquareRoot.Replay.PreparedRootStateReplay.Axis.bound top.clearance) = data
            rw [boundary.result.bound_eq, left.bound_eq, right.bound_eq, bottom.bound_eq, top.bound_eq]⟩
        else .error (.winding actual rfl winding)
    else exact .error (.outsideAmbient within)
  else exact .error (.notProper proper)

/-- Matching the complete finite payload restores the original winding-one state exactly. -/
theorem Checked.eq_original {parameter : SquareRoot.Replay.PreparedRootStateReplay.Gaussian} {ambient :
  SquareRoot.Replay.PreparedRootStateReplay.Box}
    (original : SquareRoot.Replay.PreparedRootStateReplay.State parameter ambient) (restored :
      SquareRoot.Replay.PreparedRootStateReplay.Checked parameter ambient
      (SquareRoot.Replay.PreparedRootStateReplay.capture original)) :
    restored.state = original :=
  SquareRoot.Replay.PreparedRootStateReplay.capture_injective restored.state original restored.data_eq

/-- Reconstituting the same *named* owner constructor is exact, including
its refinement function.  Do not apply this to an unidentified owner recipe. -/
theorem Checked.deferredOwner_eq_original {parameter : SquareRoot.Replay.PreparedRootStateReplay.Gaussian} {ambient :
  SquareRoot.Replay.PreparedRootStateReplay.Box}
    (nonzero : parameter ≠ 0) (original : SquareRoot.Replay.PreparedRootStateReplay.State parameter ambient)
    (restored : SquareRoot.Replay.PreparedRootStateReplay.Checked parameter ambient
      (SquareRoot.Replay.PreparedRootStateReplay.capture original)) :
    SquareRoot.Clearance.ExactQuadraticOwnerClearance.ownerOfState nonzero restored.state =
      SquareRoot.Clearance.ExactQuadraticOwnerClearance.ownerOfState nonzero original :=
  congrArg (SquareRoot.Clearance.ExactQuadraticOwnerClearance.ownerOfState nonzero) (restored.eq_original original)

/-- Applying the same accelerated owner constructor to the restored state recovers the original constructed owner
exactly. -/
theorem Checked.acceleratedOwner_eq_original {parameter : SquareRoot.Replay.PreparedRootStateReplay.Gaussian} {ambient :
  SquareRoot.Replay.PreparedRootStateReplay.Box}
    (nonzero : parameter ≠ 0) (original : SquareRoot.Replay.PreparedRootStateReplay.State parameter ambient)
    (restored : SquareRoot.Replay.PreparedRootStateReplay.Checked parameter ambient
      (SquareRoot.Replay.PreparedRootStateReplay.capture original)) :
    Riemann.Topology.SquareRootContinuationChain.Owner.ofState nonzero restored.state =
      Riemann.Topology.SquareRootContinuationChain.Owner.ofState nonzero original :=
  congrArg (Riemann.Topology.SquareRootContinuationChain.Owner.ofState nonzero) (restored.eq_original original)

end Purelib.RootIsolation.SquareRoot.Replay.PreparedRootStateReplay

end
