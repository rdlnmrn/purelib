module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Riemann.Readings.PreparedBoundaryGluing
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Winding.Polygon.Basic
import Purelib.Riemann.Paths.PreparedPathWinding
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.State.WindingOne.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
public import Purelib.Riemann.Paths.PreparedPathClosure
public import Purelib.Riemann.Paths.PreparedDyadicTrace
public import Purelib.Riemann.RootContinuation.RootReturnBox
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Topology.PreparedCycleModels
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Riemann.Paths.PreparedPathGluing
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Polynomial.Dense.Evaluation
import Mathlib.Order.Basic
import Purelib.Tactic.QuotientFreeOmega

public section

/-!
# Actual root closure of the prepared two-branch boundary tour

The four traces below are indexed by the existing integration banks.  Their
internal handoffs use the cached terminal owners, the connector and reversed
connector cancel in winding, and the two checked branch boundaries contribute
eight.  Even-winding closure then supplies the missing operational return.

The closed constructor first prepares ordinary banks and checks root return
by containment of the endpoint windows or one common winding-one box. Only
an inconclusive finite return check needs the finer winding trace. Both routes
use the supplied geometry and one initial root owner. They do not identify
a global cut-surface boundary with the standard A/B period programs.
-/

namespace Purelib.Riemann.Readings.PreparedBoundaryClosure

open Purelib.Curves.Hyperelliptic
open Purelib.Riemann.Paths
open Purelib.Approximation.Gaussian

open Purelib.Data.Rat

set_option backward.match.sparseCases false

open Purelib.Riemann.Curves.AlgebraicDifferentials
open Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts (ownerBoundaryPath ownerBoundaryPath_withinAmbient)
open Purelib.Riemann.Paths.PreparedClearPathModels
open Purelib.Riemann.Readings.PreparedBoundaryGluing (JoinedBoundaryDoublePath)
open Purelib.Riemann.Paths.PreparedDyadicTrace.PreparedClearPathModels.PreparedPath (Tracing)
open Purelib.Riemann.Paths.PreparedDyadicTrace.PreparedCycleModels (TracedFinishedDyadic)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.RootContinuation

set_option genInjectivity false in
/-- A joined boundary cycle with exact owner traces and unit boundary windings.

The four traces retain the original prepared banks; both owner-boundary paths carry quadrupled winding four, while the
connector and its reverse cancel. -/
structure TracedBoundaryDoublePath {genus : Nat} (curve : Basic.HyperellipticCurve genus) where
  /-- The original sequentially owner-linked four-bank boundary tour. -/ joined : JoinedBoundaryDoublePath curve
  /-- The owner trace of the exact forward connector bank. -/ forward : Tracing joined.data.forward
  /-- The owner trace of the exact right boundary bank. -/ right : Tracing joined.data.rightBoundary
  /-- The owner trace of the exact reverse connector bank. -/ backward : Tracing joined.data.backward
  /-- The owner trace of the exact left boundary bank. -/ left : Tracing joined.data.leftBoundary
  /-- The original right owner-boundary path has quadrupled winding four. -/ right_winding :
    PreparedPathWinding.ClearPath.rawWinding joined.data.rightBoundaryPath = 4
  /-- The original left owner-boundary path has quadrupled winding four. -/ left_winding :
    PreparedPathWinding.ClearPath.rawWinding joined.data.leftBoundaryPath = 4

constructive_injectivity TracedBoundaryDoublePath

namespace TracedBoundaryDoublePath

open Purelib.Polynomial
open Purelib.Riemann.Paths
open Purelib.Approximation.Gaussian
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.RootIsolation

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus}

/-- Append the four retained owner traces using the exact successive owner identities. -/
@[expose] def trace (tour : TracedBoundaryDoublePath curve) :
    OwnerPath curve.polynomial tour.joined.data.leftState.box.anchor tour.joined.data.forwardOwner
      tour.joined.data.leftState.box.anchor tour.joined.finishOwner :=
  tour.forward.trace.append
    ((tour.right.trace.reindexOwners tour.joined.rightOwner_eq rfl).append
      ((tour.backward.trace.reindexOwners tour.joined.backwardOwner_eq rfl).append
        (tour.left.trace.reindexOwners tour.joined.leftOwner_eq tour.joined.finishOwner_eq.symm)))

/-- The complete boundary tour has raw quadrupled winding eight. -/
theorem trace_winding (tour : TracedBoundaryDoublePath curve) :
    Winding.Polygon.Basic.chainRaw curve.polynomial tour.joined.data.leftState.box.anchor tour.trace.vertices = 8 := by
  simp only [trace, OwnerPath.append_vertices, OwnerPath.reindexOwners_vertices,
    Winding.Polygon.Basic.chainRaw_append, OwnerPath.vertices_terminal]
  rw [tour.forward.winding_eq, tour.right.winding_eq, tour.backward.winding_eq, tour.left.winding_eq,
    PreparedPathClosure.ClearPath.rawWinding_reverse, tour.right_winding, tour.left_winding]
  omega

/-- The retained final root name is equivalent to the original initial root name. -/
@[expose] def rootEquivalent (tour : TracedBoundaryDoublePath curve) :
    Equivalence.NamedEquivalent
      (ownerName tour.joined.finishOwner) (ownerName tour.joined.data.forwardOwner) :=
  PreparedPathClosure.SquareRootTrace.OwnerPath.rootEquivalent_of_even
    tour.joined.data.leftState tour.trace 1 tour.trace_winding

/-- Assemble a traced boundary tour from the four sequentially owner-linked banks.

All trace and winding certificates belong to those exact supplied banks and the original two owner-boundary paths. -/
@[expose] def ofFinished {leftAmbient rightAmbient connectorAmbient : Purelib.Geometry.Rational.Box}
    (leftState : State.WindingOne.Basic.WindingOneState curve.polynomial leftAmbient)
    (rightState : State.WindingOne.Basic.WindingOneState curve.polynomial rightAmbient)
    (connector : Polynomial.Geometry.ClearPath curve.polynomial connectorAmbient leftState.box.anchor
      rightState.box.anchor)
    (owner : Owner (curve.polynomial.eval leftState.box.anchor))
    (diameter : Fraction.Rational) (positive : 0 < diameter)
    (forward : TracedFinishedDyadic connector owner diameter positive)
    (right : TracedFinishedDyadic (BranchCutLifts.ownerBoundaryPath rightState) forward.bank.finishOwner diameter
      positive)
    (backward : TracedFinishedDyadic (BranchCutLifts.ClearPath.reverse connector)
      right.bank.finishOwner diameter positive)
    (left : TracedFinishedDyadic (BranchCutLifts.ownerBoundaryPath leftState) backward.bank.finishOwner diameter
      positive) :
    TracedBoundaryDoublePath curve :=
  { joined := JoinedBoundaryDoublePath.ofFinished leftState rightState connector owner diameter positive
      forward.bank right.bank backward.bank left.bank
    forward := forward.tracing
    right := right.tracing
    backward := backward.tracing
    left := left.tracing
    right_winding := PreparedPathWinding.BranchCutLifts.ownerBoundaryPath_rawWinding rightState
    left_winding := PreparedPathWinding.BranchCutLifts.ownerBoundaryPath_rawWinding leftState }

/-- Prepare the four sequential owner traces with one common positive diameter bound.

The minimum of their retained path budgets fixes the diameter, while each bank is selected beyond its own movement-depth
floor and starts at the preceding bank's exact terminal owner. -/
@[expose] def total {leftAmbient rightAmbient connectorAmbient : Purelib.Geometry.Rational.Box}
    (leftState : State.WindingOne.Basic.WindingOneState curve.polynomial leftAmbient)
    (rightState : State.WindingOne.Basic.WindingOneState curve.polynomial rightAmbient)
    (connector : Polynomial.Geometry.ClearPath curve.polynomial connectorAmbient leftState.box.anchor
      rightState.box.anchor)
    (within : connector.WithinAmbient) (owner : Owner (curve.polynomial.eval leftState.box.anchor)) :
    TracedBoundaryDoublePath curve := by
  let forwardBudget := PreparedDyadicTrace.PreparedClearPathModels.PathTraceBudgets.build connector
  let rightPath := BranchCutLifts.ownerBoundaryPath rightState
  let rightBudget := PreparedDyadicTrace.PreparedClearPathModels.PathTraceBudgets.build rightPath
  let backwardPath := BranchCutLifts.ClearPath.reverse connector
  let backwardBudget := PreparedDyadicTrace.PreparedClearPathModels.PathTraceBudgets.build backwardPath
  let leftPath := BranchCutLifts.ownerBoundaryPath leftState
  let leftBudget := PreparedDyadicTrace.PreparedClearPathModels.PathTraceBudgets.build leftPath
  let diameter := min (min forwardBudget.diameter rightBudget.diameter)
    (min backwardBudget.diameter leftBudget.diameter)
  have positive : 0 < diameter := Fraction.Order.Basic.lt_min
    (Fraction.Order.Basic.lt_min forwardBudget.diameter_positive rightBudget.diameter_positive)
    (Fraction.Order.Basic.lt_min backwardBudget.diameter_positive leftBudget.diameter_positive)
  let forward := TracedFinishedDyadic.total connector within owner forwardBudget diameter positive
    ((Fraction.Order.Basic.min_le_left _ _).trans (Fraction.Order.Basic.min_le_left _ _))
  let right := TracedFinishedDyadic.total rightPath (BranchCutLifts.ownerBoundaryPath_withinAmbient rightState)
    forward.bank.finishOwner rightBudget diameter positive ((Fraction.Order.Basic.min_le_left _ _).trans
      (Fraction.Order.Basic.min_le_right _ _))
  let backward := TracedFinishedDyadic.total backwardPath
    (BranchCutLifts.ClearPath.reverse_withinAmbient connector within)
    right.bank.finishOwner backwardBudget diameter positive ((Fraction.Order.Basic.min_le_right _ _).trans
      (Fraction.Order.Basic.min_le_left _ _))
  let left := TracedFinishedDyadic.total leftPath (BranchCutLifts.ownerBoundaryPath_withinAmbient leftState)
    backward.bank.finishOwner leftBudget diameter positive ((Fraction.Order.Basic.min_le_right _ _).trans
      (Fraction.Order.Basic.min_le_right _ _))
  exact ofFinished leftState rightState connector owner diameter positive forward right backward left

end TracedBoundaryDoublePath

set_option genInjectivity false in
/-- A joined boundary cycle with retained endpoint root names and their return equivalence.

Exact name identities link both stored names to the original initial and final owners; the comparison preserves their
final-to-initial direction. -/
structure ClosedBoundaryDoublePath {genus : Nat} (curve : Basic.HyperellipticCurve genus) where
  /-- The original sequentially owner-linked four-bank boundary tour. -/ joined : JoinedBoundaryDoublePath curve
  /-- The retained name of the original initial root owner. -/ firstRoot : Name.Basic.Named
  /-- The retained name of the original final root owner. -/ lastRoot : Name.Basic.Named
  /-- The retained initial name equals the name of the original forward owner. -/ firstRoot_eq : firstRoot = ownerName
    joined.data.forwardOwner
  /-- The retained final name equals the name of the original finishing owner. -/ lastRoot_eq : lastRoot = ownerName
    joined.finishOwner
  /-- The retained final root name is equivalent to the retained initial root name. -/ rootReturn :
    Equivalence.NamedEquivalent lastRoot firstRoot

constructive_injectivity ClosedBoundaryDoublePath

namespace ClosedBoundaryDoublePath

open Purelib.Approximation.Gaussian
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.RootIsolation
open Purelib.Data.Gaussian
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Riemann.Topology

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus}

/-- Read a closed boundary cycle from the supplied trace and its certified root return. -/
@[expose] def ofTraced (tour : TracedBoundaryDoublePath curve) : ClosedBoundaryDoublePath curve :=
  ⟨tour.joined, ownerName tour.joined.data.forwardOwner, ownerName tour.joined.finishOwner,
    rfl, rfl, tour.rootEquivalent⟩

/-- The retained final root name is equivalent to the original initial root name. -/
@[expose] def rootEquivalent (tour : ClosedBoundaryDoublePath curve) :
    Equivalence.NamedEquivalent
      (ownerName tour.joined.finishOwner) (ownerName tour.joined.data.forwardOwner) := by
  rw [← tour.lastRoot_eq, ← tour.firstRoot_eq]
  exact tour.rootReturn

set_option genInjectivity false in
/-- An inconclusive return check retaining the exact attempted joined tour.

The owner-specific report and rejection equality describe this finite attempt without asserting that the original root
names differ. -/
structure ReturnInconclusive (joined : JoinedBoundaryDoublePath curve) where
  /-- The exact joined tour used in the unsuccessful return attempt. -/ attempted : JoinedBoundaryDoublePath curve
  /-- The retained attempted tour equals the original joined input. -/ attempted_eq : attempted = joined
  /-- The owner-specific inconclusive return-box report. -/ result : RootReturnBox.Inconclusive joined.data.forwardOwner
    joined.finishOwner
  /-- The original owner check returned exactly the retained inconclusive report. -/ rejected : RootReturnBox.check
    joined.data.forwardOwner joined.finishOwner = .error result

constructive_injectivity ReturnInconclusive

/-- Attach the supplied two-owner return certificate to the unchanged joined boundary cycle. -/
@[expose] def ofReturn (joined : JoinedBoundaryDoublePath curve)
    (certificate : RootReturnBox.Certificate joined.data.forwardOwner joined.finishOwner) :
    ClosedBoundaryDoublePath curve :=
  ⟨joined, ownerName joined.data.forwardOwner, ownerName joined.finishOwner, rfl, rfl,
    certificate.comparison _ _⟩

/-- Check and retain root return for the exact joined tour.

A successful observation produces a closed tour with the original banks; an inconclusive observation retains its
complete report and exact check-result identity. -/
@[expose] def checkReturn (joined : JoinedBoundaryDoublePath curve) :
    Except (ReturnInconclusive joined) (ClosedBoundaryDoublePath curve) :=
  let observation := RootReturnBox.observe joined.data.forwardOwner joined.finishOwner
  match checked : observation.outcome with
  | .ok certificate => .ok (ofReturn joined certificate)
  | .error result => .error ⟨joined, rfl, result, observation.inconclusive_readback result checked⟩

/-- A successful return check preserves the original joined boundary tour exactly. -/
theorem checkReturn_joined (joined : JoinedBoundaryDoublePath curve)
    (closed : ClosedBoundaryDoublePath curve) (accepted : checkReturn joined = .ok closed) :
    closed.joined = joined := by
  unfold checkReturn at accepted
  dsimp only [RootReturnBox.observe] at accepted
  split at accepted
  · cases accepted
    rfl
  · cases accepted

/-- A successful underlying owner check produces the corresponding closed boundary tour. -/
theorem checkReturn_of_success (joined : JoinedBoundaryDoublePath curve)
    (certificate : RootReturnBox.Certificate joined.data.forwardOwner joined.finishOwner)
    (accepted : RootReturnBox.check joined.data.forwardOwner joined.finishOwner = .ok certificate) :
    checkReturn joined = .ok (ofReturn joined certificate) := by
  unfold checkReturn
  dsimp only [RootReturnBox.observe]
  split
  · rename_i other observed
    have same := Except.ok.inj (observed.symm.trans accepted)
    cases same
    rfl
  · rename_i failure observed
    cases observed.symm.trans accepted

/-- The retained inconclusive report is exactly the unsuccessful result of the joined-tour check. -/
theorem ReturnInconclusive.check_error {joined : JoinedBoundaryDoublePath curve}
    (failure : ReturnInconclusive joined) : checkReturn joined = .error failure := by
  rcases failure with ⟨attempted, attemptedEq, result, rejected⟩
  cases attemptedEq
  unfold checkReturn
  dsimp only [RootReturnBox.observe]
  split
  · rename_i certificate observed
    cases observed.symm.trans rejected
  · rename_i other observed
    have same := Except.error.inj (observed.symm.trans rejected)
    cases same
    rfl

/-- Prepare a closed boundary tour, accepting a return-box certificate or using the traced fallback.

The fast attempt retains its exact joined banks when successful. An inconclusive return check selects the certified
winding trace construction with the same original connector and initial owner. -/
@[irreducible, expose] def total {leftAmbient rightAmbient connectorAmbient : Purelib.Geometry.Rational.Box}
    (leftState : State.WindingOne.Basic.WindingOneState curve.polynomial leftAmbient)
    (rightState : State.WindingOne.Basic.WindingOneState curve.polynomial rightAmbient)
    (connector : Polynomial.Geometry.ClearPath curve.polynomial connectorAmbient leftState.box.anchor
      rightState.box.anchor)
    (within : connector.WithinAmbient) (owner : Owner (curve.polynomial.eval leftState.box.anchor)) :
    ClosedBoundaryDoublePath curve :=
  let joined := JoinedBoundaryDoublePath.total leftState rightState connector within owner 1 (by decide)
  match checkReturn joined with
  | .ok closed => closed
  | .error _ => ofTraced (TracedBoundaryDoublePath.total leftState rightState connector within owner)

/-- Either total-construction branch retains the exact original initial root owner and parameter. -/
theorem total_initialOwner {leftAmbient rightAmbient connectorAmbient : Purelib.Geometry.Rational.Box}
    (leftState : State.WindingOne.Basic.WindingOneState curve.polynomial leftAmbient)
    (rightState : State.WindingOne.Basic.WindingOneState curve.polynomial rightAmbient)
    (connector : Polynomial.Geometry.ClearPath curve.polynomial connectorAmbient leftState.box.anchor
      rightState.box.anchor)
    (within : connector.WithinAmbient) (owner : Owner (curve.polynomial.eval leftState.box.anchor)) :
    (⟨_, (total leftState rightState connector within owner).joined.data.forwardOwner⟩ :
      (parameter : Basic.Canonical) × Owner parameter) = ⟨_, owner⟩ := by
  unfold total
  dsimp only
  split
  · rename_i closed accepted
    rw [checkReturn_joined _ closed accepted]
    rfl
  · rfl

/-- Either total-construction branch retains the original left anchor as its basepoint. -/
theorem total_base {leftAmbient rightAmbient connectorAmbient : Purelib.Geometry.Rational.Box}
    (leftState : State.WindingOne.Basic.WindingOneState curve.polynomial leftAmbient)
    (rightState : State.WindingOne.Basic.WindingOneState curve.polynomial rightAmbient)
    (connector : Polynomial.Geometry.ClearPath curve.polynomial connectorAmbient leftState.box.anchor
      rightState.box.anchor)
    (within : connector.WithinAmbient) (owner : Owner (curve.polynomial.eval leftState.box.anchor)) :
    (total leftState rightState connector within owner).joined.data.leftState.box.anchor =
      leftState.box.anchor := by
  unfold total
  dsimp only
  split
  · rename_i closed accepted
    rw [checkReturn_joined _ closed accepted]
    rfl
  · rfl

/-- Either total-construction branch retains the original initial root name. -/
theorem total_initialName {leftAmbient rightAmbient connectorAmbient : Purelib.Geometry.Rational.Box}
    (leftState : State.WindingOne.Basic.WindingOneState curve.polynomial leftAmbient)
    (rightState : State.WindingOne.Basic.WindingOneState curve.polynomial rightAmbient)
    (connector : Polynomial.Geometry.ClearPath curve.polynomial connectorAmbient leftState.box.anchor
      rightState.box.anchor)
    (within : connector.WithinAmbient) (owner : Owner (curve.polynomial.eval leftState.box.anchor)) :
    ownerName (total leftState rightState connector within owner).joined.data.forwardOwner = ownerName owner := by
  unfold total
  dsimp only
  split
  · rename_i closed accepted
    rw [checkReturn_joined _ closed accepted]
    rfl
  · rfl

/-- Construct the closed boundary tour for the retained branch connector and refinement index. -/
@[expose] def ofConnectorAt (branches : BranchIsolation.Data curve) (degreeGtOne : 1 < curve.polynomial.natDegree)
    (left right : BranchIsolation.Data.Index branches) (refinement : Nat) : ClosedBoundaryDoublePath curve :=
  let startNonzero := Cuts.connectorAt_start_eval_ne_zero branches degreeGtOne left right refinement
  total (Cuts.refinedState branches degreeGtOne left refinement)
    (Cuts.refinedState branches degreeGtOne right refinement)
    (Cuts.connectorAt branches degreeGtOne left right refinement)
    (Cuts.connectorAt_withinAmbient branches degreeGtOne left right refinement)
    (SquareRootContinuationChain.Owner.independent startNonzero 0)

end ClosedBoundaryDoublePath

end Purelib.Riemann.Readings.PreparedBoundaryClosure
