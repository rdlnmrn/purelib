module

import Purelib.System.FilePath

import Purelib.Data.Json.Codec
import Purelib.Data.Json.Basic
import Purelib.Data.String.Basic
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Riemann.Paths.PreparedPathGluing
import Purelib.Riemann.Readings.PreparedBoundaryGluing
import Purelib.Riemann.RootContinuation.RootReturnBox
import Purelib.Riemann.Topology.PreparedCycleModels
import scripts.checkpoint.RootRefinement
import scripts.checkpoint.RootState
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
public import Purelib.Curves.Hyperelliptic.Integration.Surface.PreparedCycleReplay.Readiness
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.RootIsolation.State.WindingOne.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.RootIsolation.SquareRoot.Preparation.Bank.Adaptive
import Purelib.RootIsolation.SquareRoot.Preparation.Bank.Cache
import Purelib.RootIsolation.SquareRoot.Replay.PreparedTrackReplay
import Purelib.RootIsolation.SquareRoot.Replay.QuadraticTrackReplay
public import Purelib.Riemann.Topology.PreparedCycleBankReplay
public import scripts.checkpoint.PreparedBank
import scripts.checkpoint.PreparedCenter
public import Purelib.Riemann.Readings.PreparedBoundaryClosure
import Init.Prelude
import Init.System.FilePath
import Init.System.IO
import Mathlib.Order.Basic
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Power.Gaussian
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Paths.PreparedDyadicTrace
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance
import Purelib.RootIsolation.SquareRoot.Clearance.QuadraticAxisElimination
import Purelib.RootIsolation.SquareRoot.Replay.MovingRecenterReplay
import Purelib.RootIsolation.Track.Basic
import scripts.checkpoint.Integration

open Purelib.Curves

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Integration.Surface.PreparedCycleReplay

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Polynomial.Geometry

open Purelib.RootIsolation.SquareRoot.Preparation.Bank

open Purelib.RootIsolation.SquareRoot.Replay

open Purelib.RootIsolation.State

open Purelib.RootIsolation.SquareRoot.Preparation

open Purelib

open Purelib.Data (Json)
open scoped Purelib.Data.String
open Purelib.Data.Json (toJson)

public section

/-! Disk-backed assembly of the original A-boundary and paired B-bridge banks. -/

open Purelib.Riemann.Transport Purelib.Riemann.RootContinuation Purelib.Riemann.Integration
open Purelib.Riemann.Branches Purelib.Riemann.Readings Purelib.Riemann.Paths Purelib.Riemann.Topology

namespace PreparedCycleCheckpoint

variable {m : Type → Type} [Monad m] [MonadLiftT IO m] [MonadLiftT BaseIO m]
  [MonadExceptOf IO.Error m] [MonadStateOf RootRefinementCheckpoint.Counts m]

open Purelib.Riemann
open PreparedCycleBankReplay

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus}

/-- Restore the four original ordered boundary banks with their complete source equality. -/
@[expose] def boundary (input : BoundaryInput curve) (control : RootRefinementCheckpoint.Control)
    (directory : System.FilePath) :
    m {value : PreparedCycleModels.PreparedBoundaryDoublePath curve // value = input.original} := do
  let forward ← PreparedBankCheckpoint.select input.forward input.diameter input.positive control
    ((Purelib.System.FilePath.join directory (System.FilePath.mk ("forward"))))
  let right ← PreparedBankCheckpoint.select input.right input.diameter input.positive control
    ((Purelib.System.FilePath.join directory (System.FilePath.mk ("right"))))
  let backward ← PreparedBankCheckpoint.select input.backward input.diameter input.positive control
    ((Purelib.System.FilePath.join directory (System.FilePath.mk ("backward"))))
  let left ← PreparedBankCheckpoint.select input.left input.diameter input.positive control
    ((Purelib.System.FilePath.join directory (System.FilePath.mk ("left"))))
  return ⟨input.restore forward.val right.val backward.val left.val,
    input.restore_eq forward.val right.val backward.val left.val forward.property right.property backward.property
      left.property⟩

/-- Restore the original paired bridge bank from its checked retained task selection. -/
@[expose] def bridge (input : BridgeInput curve) (control : RootRefinementCheckpoint.Control)
    (directory : System.FilePath) : m {value : PreparedCycleModels.PreparedDoublePath curve // value = input.original}
      := do
  let selected ← PreparedBankCheckpoint.select input.tasks input.diameter input.positive control directory
  return ⟨input.restore selected.val, input.restore_eq selected.val selected.property⟩

end PreparedCycleCheckpoint

/-!
Checked reload of the standard tour's sequential owner banks. The existing
bank loader checks exact requests and selected spines. Independent endpoint
bank artifacts are not silently identified with these root-closed tours.
-/

namespace RootClosedCycleCheckpoint

variable {m : Type → Type} [Monad m] [MonadLiftT IO m] [MonadLiftT BaseIO m]
  [MonadExceptOf IO.Error m] [MonadStateOf RootRefinementCheckpoint.Counts m]

open Purelib.Riemann
open _root_.Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients renaming CoefficientPolynomial ->
  GaussianPolynomial
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open _root_.Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Geometry.Rational (Box)
open Purelib.Data.Rat.Fraction (Rational)
open PreparedCycleModels (Gaussian)
open PreparedDyadicTrace.PreparedCycleModels (TracedFinishedDyadic)
open PreparedBoundaryGluing (FinishedDyadic)
open PreparedBoundaryClosure (ClosedBoundaryDoublePath TracedBoundaryDoublePath)
open PreparedDyadicTrace.PreparedClearPathModels (PathTraceBudgets)
open SquareRootContinuationChain (Owner)

/-- Restore one traced dyadic path from the original owner and retained movement budget.

The continuation receives the exact original total construction, including its selected depth, cached bank and terminal
owner. -/
@[expose] def withTraced {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
  {ambient :
  Rational.Box} {start finish : Gaussian}
    (path : Polynomial.Geometry.ClearPath polynomial ambient start finish) (within : path.WithinAmbient)
    (owner : Owner (polynomial.eval start)) (budgets : PathTraceBudgets path)
    (diameter : Fraction.Rational) (positive : 0 < diameter) (small : diameter ≤ budgets.diameter)
    (control : RootRefinementCheckpoint.Control) (directory : System.FilePath)
    (use : (value : TracedFinishedDyadic path owner diameter positive) →
      value = TracedFinishedDyadic.total path within owner budgets diameter positive small →
      m Unit) : m Unit := do
  let selected ← PreparedBankCheckpoint.selectFrom
    [Bank.Adaptive.Task.ofPath path within owner] diameter positive budgets.movementDepth control directory
  let certificate := (Bank.Cache.DyadicBank.cache selected.val.banks.head)
  let bank : FinishedDyadic path owner diameter positive :=
    ⟨selected.val.depth, certificate, (PreparedPathGluing.finishOwner certificate.prepared), rfl⟩
  let value := TracedFinishedDyadic.ofBank budgets bank selected.val.minimum_le small
  have equal : value = TracedFinishedDyadic.total path within owner budgets diameter positive small := by
    exact congrArg (fun selected : Bank.Adaptive.Selected
        [Bank.Adaptive.Task.ofPath path within owner] diameter positive budgets.movementDepth =>
      let certificate := (Bank.Cache.DyadicBank.cache selected.banks.head)
      TracedFinishedDyadic.ofBank budgets
        (⟨selected.depth, certificate, (PreparedPathGluing.finishOwner certificate.prepared), rfl⟩ :
          FinishedDyadic path owner diameter positive) selected.minimum_le small) selected.property
  use value equal

/-- Restore the original four-bank traced boundary through its sequential owner handoffs.

Each restored bank supplies the next initial owner and the final value retains equality to the original traced total. -/
@[expose] def withTracedBoundary {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {leftAmbient rightAmbient connectorAmbient : Rational.Box}
    (leftState : WindingOne.Basic.WindingOneState curve.polynomial leftAmbient)
    (rightState : WindingOne.Basic.WindingOneState curve.polynomial rightAmbient)
    (connector : Polynomial.Geometry.ClearPath curve.polynomial connectorAmbient leftState.box.anchor
      rightState.box.anchor)
    (within : connector.WithinAmbient) (owner : Owner (curve.polynomial.eval leftState.box.anchor))
    (control : RootRefinementCheckpoint.Control) (directory : System.FilePath)
    (use : (value : ClosedBoundaryDoublePath curve) →
      value = ClosedBoundaryDoublePath.ofTraced
        (TracedBoundaryDoublePath.total leftState rightState connector within owner) →
      m Unit) : m Unit := do
  let forwardBudget := PathTraceBudgets.build connector
  let rightPath := BranchCutLifts.ownerBoundaryPath rightState
  let rightBudget := PathTraceBudgets.build rightPath
  let backwardPath := BranchCutLifts.ClearPath.reverse connector
  let backwardBudget := PathTraceBudgets.build backwardPath
  let leftPath := BranchCutLifts.ownerBoundaryPath leftState
  let leftBudget := PathTraceBudgets.build leftPath
  let diameter := min (min forwardBudget.diameter rightBudget.diameter)
    (min backwardBudget.diameter leftBudget.diameter)
  have positive : 0 < diameter := Fraction.Order.Basic.lt_min
    (Fraction.Order.Basic.lt_min forwardBudget.diameter_positive rightBudget.diameter_positive)
    (Fraction.Order.Basic.lt_min backwardBudget.diameter_positive leftBudget.diameter_positive)
  withTraced connector within owner forwardBudget diameter positive
    ((Fraction.Order.Basic.min_le_left _ _).trans (Fraction.Order.Basic.min_le_left _ _)) control
      ((Purelib.System.FilePath.join directory (System.FilePath.mk ("forward")))) fun forward forwardEq =>
    withTraced rightPath (BranchCutLifts.ownerBoundaryPath_withinAmbient rightState)
      forward.bank.finishOwner rightBudget diameter positive
      ((Fraction.Order.Basic.min_le_left _ _).trans (Fraction.Order.Basic.min_le_right _ _)) control
        ((Purelib.System.FilePath.join directory (System.FilePath.mk ("right")))) fun right rightEq =>
      withTraced backwardPath (BranchCutLifts.ClearPath.reverse_withinAmbient connector within)
        right.bank.finishOwner backwardBudget diameter positive
        ((Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_left _ _)) control
          ((Purelib.System.FilePath.join directory (System.FilePath.mk ("backward")))) fun backward backwardEq =>
        withTraced leftPath (BranchCutLifts.ownerBoundaryPath_withinAmbient leftState)
          backward.bank.finishOwner leftBudget diameter positive
          ((Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_right _ _)) control
            ((Purelib.System.FilePath.join directory (System.FilePath.mk ("left")))) fun left leftEq => do
          let value := ClosedBoundaryDoublePath.ofTraced
            (TracedBoundaryDoublePath.ofFinished leftState rightState connector owner diameter positive
              forward right backward left)
          have equal : value = ClosedBoundaryDoublePath.ofTraced
              (TracedBoundaryDoublePath.total leftState rightState connector within owner) := by
            cases forwardEq
            cases rightEq
            cases backwardEq
            cases leftEq
            rfl
          use value equal

/-- Restore a unit-diameter dyadic path bank with its original terminal owner and source equation. -/
@[expose] def withFinished {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
  {ambient :
  Rational.Box} {start finish : Gaussian}
    (path : Polynomial.Geometry.ClearPath polynomial ambient start finish) (within : path.WithinAmbient)
    (owner : Owner (polynomial.eval start))
    (control : RootRefinementCheckpoint.Control) (directory : System.FilePath)
    (use : (value : FinishedDyadic path owner 1 (by decide)) →
      value = FinishedDyadic.total path within owner 1 (by decide) → m Unit) : m Unit := do
  let selected ← PreparedBankCheckpoint.select
    [Bank.Adaptive.Task.ofPath path within owner] 1 (by decide) control directory
  let certificate := (Bank.Cache.DyadicBank.cache selected.val.banks.head)
  let value : FinishedDyadic path owner 1 (by decide) :=
    ⟨selected.val.depth, certificate, (PreparedPathGluing.finishOwner certificate.prepared), rfl⟩
  have equal : value = FinishedDyadic.total path within owner 1 (by decide) := by
    exact congrArg (fun selected : Bank.Adaptive.Selected
        [Bank.Adaptive.Task.ofPath path within owner] 1 (by decide) =>
      let certificate := (Bank.Cache.DyadicBank.cache selected.banks.head)
      (⟨selected.depth, certificate, (PreparedPathGluing.finishOwner certificate.prepared), rfl⟩ :
        FinishedDyadic path owner 1 (by decide))) selected.property
  use value equal

/-- Restore the four sequential ordinary boundary banks and their exact joined-path equation. -/
@[expose] def withJoined {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {leftAmbient rightAmbient connectorAmbient : Rational.Box}
    (leftState : WindingOne.Basic.WindingOneState curve.polynomial leftAmbient)
    (rightState : WindingOne.Basic.WindingOneState curve.polynomial rightAmbient)
    (connector : Polynomial.Geometry.ClearPath curve.polynomial connectorAmbient leftState.box.anchor
      rightState.box.anchor)
    (within : connector.WithinAmbient) (owner : Owner (curve.polynomial.eval leftState.box.anchor))
    (control : RootRefinementCheckpoint.Control) (directory : System.FilePath)
    (use : (value : PreparedBoundaryGluing.JoinedBoundaryDoublePath curve) →
      value = PreparedBoundaryGluing.JoinedBoundaryDoublePath.total
        leftState rightState connector within owner 1 (by decide) → m Unit) : m Unit :=
  withFinished connector within owner control ((Purelib.System.FilePath.join directory (System.FilePath.mk
    ("forward")))) fun forward forwardEq =>
    withFinished (BranchCutLifts.ownerBoundaryPath rightState)
      (BranchCutLifts.ownerBoundaryPath_withinAmbient rightState) forward.finishOwner
      control ((Purelib.System.FilePath.join directory (System.FilePath.mk ("right")))) fun right rightEq =>
      withFinished (BranchCutLifts.ClearPath.reverse connector)
        (BranchCutLifts.ClearPath.reverse_withinAmbient connector within) right.finishOwner
        control ((Purelib.System.FilePath.join directory (System.FilePath.mk ("backward")))) fun backward backwardEq =>
        withFinished (BranchCutLifts.ownerBoundaryPath leftState)
          (BranchCutLifts.ownerBoundaryPath_withinAmbient leftState) backward.finishOwner
          control ((Purelib.System.FilePath.join directory (System.FilePath.mk ("left")))) fun left leftEq => do
          let value := PreparedBoundaryGluing.JoinedBoundaryDoublePath.ofFinished
            leftState rightState connector owner 1 (by decide) forward right backward left
          have equal : value = PreparedBoundaryGluing.JoinedBoundaryDoublePath.total
              leftState rightState connector within owner 1 (by decide) := by
            cases forwardEq
            cases rightEq
            cases backwardEq
            cases leftEq
            rfl
          use value equal

/-- Restore unchanged ordinary banks from their retained source directory, then answer the finite endpoint-return plan
using checked winding witnesses. A separate directory owns the new closure result and any traced fallback. -/
@[expose] def withBoundary {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {leftAmbient rightAmbient connectorAmbient : Rational.Box}
    (leftState : WindingOne.Basic.WindingOneState curve.polynomial leftAmbient)
    (rightState : WindingOne.Basic.WindingOneState curve.polynomial rightAmbient)
    (connector : Polynomial.Geometry.ClearPath curve.polynomial connectorAmbient leftState.box.anchor
      rightState.box.anchor)
    (within : connector.WithinAmbient) (owner : Owner (curve.polynomial.eval leftState.box.anchor))
    (control : RootRefinementCheckpoint.Control)
    (ordinaryDirectory directory : System.FilePath)
    (use : (value : ClosedBoundaryDoublePath curve) →
      value = ClosedBoundaryDoublePath.total leftState rightState connector within owner → m Unit) : m Unit :=
  withJoined leftState rightState connector within owner control ordinaryDirectory fun joined joinedEq => do
    let windingControl : WindingCheckpoint.Control m := ⟨control.savedOnly, pure ()⟩
    let replayed ← MovingResetCheckpoint.runPlan windingControl MovingResetCheckpoint.sharedPool
      ((Purelib.System.FilePath.join directory (System.FilePath.mk ("root-return")))) (RootReturnBox.replay
        joined.data.forwardOwner joined.finishOwner)
    let endpoints :=
      [("initialBox", toJson (RootStateCheckpoint.boxData joined.data.forwardOwner.track.initial.box)),
       ("finalBox", toJson (RootStateCheckpoint.boxData joined.finishOwner.track.initial.box)),
       ("ordinaryBankDirectory", toJson ordinaryDirectory.toString)]
    match found : replayed.val with
    | .ok certificate =>
        let closed := ClosedBoundaryDoublePath.ofReturn joined certificate
        have checked : ClosedBoundaryDoublePath.checkReturn joined = .ok closed :=
          ClosedBoundaryDoublePath.checkReturn_of_success joined certificate (replayed.property.symm.trans found)
        let evidence := match certificate with
          | .lastInside _ => [("method", toJson "final window strictly inside initial window")]
          | .firstInside _ => [("method", toJson "initial window strictly inside final window")]
          | .common attempt winding _ _ _ _ =>
              [("method", toJson "one checked winding-one box contains both endpoint windows"),
               ("commonBox", toJson (RootStateCheckpoint.boxData attempt.box)),
               ("quadrupledWinding", toJson winding), ("windingQueries", toJson (1 : Nat))]
        IntegrationCheckpoint.saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk
          ("return-check.json")))) (Json.mkObj
          ([("outcome", toJson "certified return of the original endpoint roots")] ++ endpoints ++ evidence))
        have equal : closed = ClosedBoundaryDoublePath.total leftState rightState connector within owner := by
          unfold ClosedBoundaryDoublePath.total
          dsimp only
          rw [← joinedEq, checked]
        use closed equal
    | .error failure =>
        let rejected : ClosedBoundaryDoublePath.ReturnInconclusive joined :=
          ⟨joined, rfl, failure, replayed.property.symm.trans found⟩
        have checked := rejected.check_error
        let reason := match failure.reason with
          | .leftZero _ => [("condition", toJson "common box left-axis determinant is zero")]
          | .rightZero .. => [("condition", toJson "common box right-axis determinant is zero")]
          | .bottomZero .. => [("condition", toJson "common box bottom-axis determinant is zero")]
          | .topZero .. => [("condition", toJson "common box top-axis determinant is zero")]
          | .windingMiss _ _ _ _ winding _ _ =>
              [("condition", toJson "common box quadrupled winding differs from four"),
               ("quadrupledWinding", toJson winding)]
        IntegrationCheckpoint.saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk
          ("return-check.json")))) (Json.mkObj
          ([("outcome", toJson "inconclusive finite return check; total constructor uses traced fallback"),
            ("commonBox", toJson (RootStateCheckpoint.boxData failure.attempt.box)),
            ("windingBudget", toJson failure.windingBudget),
            ("windingQueries", toJson failure.reason.windingQueries)] ++ endpoints ++ reason))
        withTracedBoundary leftState rightState connector within owner control
          ((Purelib.System.FilePath.join directory (System.FilePath.mk ("traced-fallback")))) fun traced tracedEq => do
          have equal : traced = ClosedBoundaryDoublePath.total leftState rightState connector within owner := by
            unfold ClosedBoundaryDoublePath.total
            dsimp only
            rw [← joinedEq, checked]
            exact tracedEq
          use traced equal

/-- The checked first-attempt law is preserved along the actual prepared path and its owner handoffs. -/
private theorem pathReady {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
  {ambient :
  Rational.Box} :
    ∀ {start finish : Gaussian} {path : Polynomial.Geometry.ClearPath polynomial ambient start finish}
      {owner : Owner (polynomial.eval start)} (prepared : PreparedClearPathModels.PreparedPath path owner),
      QuadraticTrackReplay.Ready owner → QuadraticTrackReplay.Ready (PreparedPathGluing.finishOwner prepared)
  | _, _, _, _, .nil _ _, ready => ready
  | _, _, _, _, .cons _ _ _ _ first rest, ready =>
      pathReady rest (PreparedTrackReplay.finishOwner first ready)

/-- The original checked-first-step law follows the actual retained handoffs. No endpoint family is independently
reacquired to centre a later bank. -/
theorem ready {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (tour : ClosedBoundaryDoublePath curve) (initial : QuadraticTrackReplay.Ready tour.joined.data.forwardOwner) :
    Readiness.CycleReady curve (.finiteCut tour.joined.data) := by
  have right : QuadraticTrackReplay.Ready tour.joined.data.rightBoundaryOwner := by
    rw [tour.joined.rightOwner_eq]
    exact pathReady tour.joined.data.forward initial
  have backward : QuadraticTrackReplay.Ready tour.joined.data.backwardOwner := by
    rw [tour.joined.backwardOwner_eq]
    exact pathReady tour.joined.data.rightBoundary right
  have left : QuadraticTrackReplay.Ready tour.joined.data.leftBoundaryOwner := by
    rw [tour.joined.leftOwner_eq]
    exact pathReady tour.joined.data.backward backward
  exact ⟨initial, right, backward, left⟩

end RootClosedCycleCheckpoint
