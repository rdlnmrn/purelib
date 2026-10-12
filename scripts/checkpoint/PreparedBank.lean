module
import Purelib.Data.Nat.Subtraction
import Purelib.Data.Nat.Order

import Purelib.System.FilePath

meta import Purelib.Elab.ConstructiveInjectivity
meta import Purelib.Elab.Deriving.Json
import Purelib.Data.Json.Codec
import Purelib.Data.Json.Basic
import Purelib.Data.Json.Printer
import Purelib.Data.String.Basic
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Integration.CheckedDirectGeometry
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.Paths.PreparedTraceBudget
import Purelib.Riemann.Readings.BoundedPreparedBanks
import Purelib.Riemann.Readings.BoundedPreparedSource
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.RootContinuation.SquareRootReconditioning
import Purelib.Riemann.Topology.SquareRootContinuationChain
import scripts.checkpoint.RootRefinement
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.RootIsolation.Exact.Ownership.Radius
import Purelib.RootIsolation.Residual.Global.Replay
import Purelib.RootIsolation.SquareRoot.Owner.Transport
public import Purelib.Integration.Path.Dyadic.DyadicRequestCursor

import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance
import Purelib.RootIsolation.SquareRoot.Clearance.QuadraticCoefficientClearance
import Purelib.RootIsolation.SquareRoot.Grid.RootEdges
import Purelib.RootIsolation.SquareRoot.Preparation.Bank.Adaptive
import Purelib.RootIsolation.SquareRoot.Preparation.Terminal
import Purelib.RootIsolation.SquareRoot.Replay.BoundedPreparedSourceReplay
import Purelib.RootIsolation.SquareRoot.Replay.MovingRecenterReplay
import Purelib.RootIsolation.SquareRoot.Replay.PreparedOwnerTransportReplay
public import Purelib.RootIsolation.SquareRoot.Replay.PreparedRetainedTransportReplay
import Purelib.RootIsolation.SquareRoot.Replay.PreparedRootStateReplay
import Purelib.RootIsolation.SquareRoot.Replay.PreparedSourceReplay
import Purelib.RootIsolation.SquareRoot.Replay.UniformPreparationReplay
public import Purelib.Riemann.Transport.BoundedPreparedBankReplay
public import Purelib.Riemann.Transport.AdaptivePreparedBankReplay
public import Purelib.Riemann.Transport.CheckedDirectGeometryReplay
public import Purelib.RootIsolation.SquareRoot.Replay.ReconditioningAssignmentReplay
public import Purelib.Riemann.RootContinuation.RootTransportReplay
public import Purelib.RootIsolation.SquareRoot.Replay.TracedSegmentReplay
public import Purelib.RootIsolation.SquareRoot.Replay.TerminalAcquisitionReplay
public import scripts.checkpoint.DiameterPreparation
public import scripts.checkpoint.InitialExtraction
public import Purelib.RootIsolation.SquareRoot.Replay.BoundedMovingReplay
import Init.Core
import Init.Data.Repr
import Init.Prelude
import Init.System.FilePath
import Init.System.IO
import Init.System.IOError
import Mathlib.Order.Basic
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Polynomial.Power.Gaussian
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.Riemann.Branches.PreparedSheetContinuation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.RootContinuation.CheckedSquareRootPreparation
import Purelib.Riemann.RootContinuation.RootPathTransport
import Purelib.Riemann.RootContinuation.SquareRootContinuation
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.RootIsolation.FTA.Squarefree.Input
import Purelib.RootIsolation.FTA.Squarefree.Prepare
import Purelib.RootIsolation.Owner.Local.Basic
import Purelib.RootIsolation.SquareRoot.Clearance.QuadraticLineClearance
import Purelib.RootIsolation.SquareRoot.Replay.CheckedDiameterReplay
import Purelib.RootIsolation.SquareRoot.Replay.PreparedBoundaryReplay
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic
import Purelib.RootIsolation.Track.Newton.Refinement
import scripts.checkpoint.Integration
import Purelib.Tactic.QuotientFreeOmega

open Purelib

open Purelib.Curves

open Purelib.Curves.Hyperelliptic

open Purelib.Geometry

open Purelib.Polynomial

open Purelib.Approximation

open Purelib.RootIsolation

open Purelib.Integration

open Purelib.Data (Json)
open scoped Purelib.Data.String
open Purelib.Data.Json (toJson)

public section

/-!
Rebuild the original bounded bank scan while loading its expensive diameter
proposals and moving-reset windings from disk. Every returned success or
depth miss carries equality to that scan. Canonical terminal acquisitions
and traced paths retain equality to their preferred/safe constructors.
Missing replay branches retain their checked operands and stop; they never
become failed depth trials.
-/

/-! Atomic winding checkpoints for the original finite moving-reset plan.
A shared pool reuses identical polynomial/box calculations across rejected
bank depths. Full request comparison and exact division checking establish
compatibility; the directory hash is only a lookup key. -/

namespace MovingResetCheckpoint

variable {m : Type → Type} [Monad m] [MonadLiftT IO m] [MonadLiftT BaseIO m]
  [MonadExceptOf IO.Error m] [MonadStateOf RootRefinementCheckpoint.Counts m]

open IntegrationCheckpoint Purelib.Riemann
open Purelib.Riemann.Transport Purelib.Riemann.RootContinuation Purelib.Riemann.Integration
open Purelib.Riemann.Branches Purelib.Riemann.Readings Purelib.Riemann.Paths Purelib.Riemann.Topology
open _root_.Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients renaming CoefficientPolynomial -> Dense
open Purelib.Geometry.Rational (Box)

set_option genInjectivity false in
/-- The exact serialized polynomial and box of a moving-reset winding request.

The schema version, original polynomial and ordered box bounds retain one
exact winding request. Equality checking compares those same fields before
reusing completed work. -/
structure RequestData where
  /-- The winding-request serialization version. -/ schema : Nat := 1
  /-- The ordered exact real and imaginary coefficient encodings. -/ polynomial : List (String × String)
  /-- The exact box bounds in lower-x, upper-x, lower-y, upper-y order. -/ box : List String
deriving DecidableEq, Json.ToJson, Json.FromJson

constructive_injectivity RequestData

/-- Serialize the original polynomial and box used by a winding calculation. -/
@[expose] def requestData (polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
  (box : Rational.Box) :
  RequestData :=
  ⟨1, polynomial.coeffs.map (fun z => (fractionText z.re, fractionText z.im)),
    [fractionText box.xLower, fractionText box.xUpper, fractionText box.yLower, fractionText box.yUpper]⟩

set_option genInjectivity false in
/-- A saved winding request certified different from the requested original data. -/
structure Mismatch (expected : RequestData) where
  /-- The actual saved winding request. -/ actual : RequestData
  /-- The saved request differs from the expected polynomial or box. -/ different : actual ≠ expected

constructive_injectivity Mismatch

/-- Decide exact winding-request equality and retain either its proof or the mismatching data. -/
@[expose] def checkRequest (expected actual : RequestData) :
    Except (Mismatch expected) {value : RequestData // value = expected} :=
  if same : actual = expected then .ok ⟨actual, same⟩ else .error ⟨actual, same⟩

/-- Save an original winding request or verify exact compatibility with the saved request.

On mismatch, retain both requests and stop before consuming incompatible winding data. -/
@[expose] def retainRequest (directory : System.FilePath) (expected : RequestData) : m Unit := do
  IO.FS.createDirAll directory
  let path := (Purelib.System.FilePath.join directory (System.FilePath.mk ("request.json")))
  if ← path.pathExists then
    let actual : RequestData ← loadJson path
    match checkRequest expected actual with
    | .ok _ => pure ()
    | .error failure =>
        saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("invalid-request.json")))) (Json.mkObj
          [("condition", toJson "saved polynomial and box must equal this original winding request"),
           ("actual", toJson failure.actual), ("expected", toJson expected)])
        throw (IO.userError "incompatible moving-reset winding checkpoint; both requests retained")
  else saveJson path expected

/-- Shared immutable witnesses remain usable when a later depth reaches the same reset. Every hit is checked against its
complete request and divisions. -/
@[expose] def sharedPool : System.FilePath := ".lake/period-checkpoints/checked-moving-windings-v1"

/-- Interpret the finite moving-reset plan using checked disk-backed winding replies.

The shared pool is keyed for lookup only; every hit is checked against the complete original polynomial and box before
continuing. -/
@[expose] def runPlan {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
  {Result : Type} {budget : Nat}
    (control : WindingCheckpoint.Control m) (pool : System.FilePath) (directory : System.FilePath) :
    SquareRoot.Replay.MovingRecenterReplay.Plan polynomial Result budget → m Result
  | .done value => pure value
  | .query box next => do
      let expected := requestData polynomial box
      retainRequest directory expected
      let cache := (Purelib.System.FilePath.join pool (System.FilePath.mk (toString (hash (toJson expected).compress))))
      retainRequest cache expected
      let winding ← WindingCheckpoint.box control cache polynomial box
      saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("reply.json")))) (Json.mkObj
        [("request", toJson expected), ("winding", toJson winding.val),
         ("requestBudget", toJson budget), ("cache", toJson cache.toString)])
      runPlan control pool ((Purelib.System.FilePath.join directory (System.FilePath.mk ("next")))) (next winding)

end MovingResetCheckpoint

namespace PreparedBankCheckpoint

variable {m : Type → Type} [Monad m] [MonadLiftT IO m] [MonadLiftT BaseIO m]
  [MonadExceptOf IO.Error m] [MonadStateOf RootRefinementCheckpoint.Counts m]

open IntegrationCheckpoint
open Purelib.Riemann
open Purelib.Riemann.Transport Purelib.Riemann.RootContinuation Purelib.Riemann.Integration
open Purelib.Riemann.Branches Purelib.Riemann.Readings Purelib.Riemann.Paths Purelib.Riemann.Topology
open PreparedSheetContinuation
open _root_.Purelib.Polynomial.Geometry (ClearPath)
open _root_.Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open PreparedClearPathModels (zeroEndpoint ownerAtStart)
open BoundedPreparedBankReplay (StepChecked PathChecked Requests)

attribute [local irreducible] PreparedSheetContinuation.advanceCached
  PreparedSheetContinuation.retainedAtReserve

set_option genInjectivity false in
/-- Only the finite unvisited interval stack is serialized. Its exact full request-list interpretation is certified by
`DyadicRequestCursor.Head`.

The current request, index, remaining count and ordered interval frames retain
the same finite unvisited stack. The serialized fields are checked against its
original request-list interpretation before resuming traversal. -/
structure CursorData where
  /-- The finite cursor serialization version. -/ schema : Nat := 1
  /-- The current step index in the original bank traversal. -/ index : Nat
  /-- The exact current source parameter. -/ current : String
  /-- The exact requested endpoint parameter. -/ endpoint : String
  /-- The exact requested root diameter. -/ diameter : String
  /-- The certified number of requests represented by the remaining cursor. -/ remainingCount : Nat
  /-- The ordered unvisited interval frames with their remaining depths and exact endpoints. -/ intervals : List (Nat ×
    String × String)
deriving DecidableEq, Json.ToJson, Json.FromJson

constructive_injectivity CursorData

set_option genInjectivity false in
/-- A saved finite request cursor certified different from the original source cursor. -/
structure CursorMismatch (expected : CursorData) where
  /-- The actual saved cursor record. -/ actual : CursorData
  /-- The actual cursor differs from the expected source cursor. -/ different : actual ≠ expected

constructive_injectivity CursorMismatch

/-- Decide exact cursor-record equality and retain a proof or certified mismatch. -/
@[expose] def checkCursor (expected actual : CursorData) :
    Except (CursorMismatch expected) {value : CursorData // value = expected} :=
  if equal : actual = expected then .ok ⟨actual, equal⟩ else .error ⟨actual, equal⟩

/-- Serialize the retained dyadic cursor head and its finite unvisited interval stack. -/
@[expose] def cursorData {diameter positive cursor} (index : Nat) (current : Endpoint)
    (head : Path.Dyadic.DyadicRequestCursor.Head diameter positive cursor) : CursorData :=
  { index := index, current := fractionText current.parameter,
    endpoint := fractionText head.request.endpoint.parameter,
    diameter := fractionText head.request.rootDiameter,
    remainingCount := Path.Dyadic.DyadicRequestCursor.count head.remaining,
    intervals := cursor.map fun frame =>
      (frame.depth, fractionText frame.left.parameter, fractionText frame.right.parameter) }

/-- Save the original finite cursor or require equality with its saved representation.

A mismatch retains both complete cursor records and stops the replay. -/
@[expose] def retainCursor (directory : System.FilePath) (expected : CursorData) : m Unit := do
  IO.FS.createDirAll directory
  let path := (Purelib.System.FilePath.join directory (System.FilePath.mk ("request-cursor.json")))
  if ← path.pathExists then
    let actual : CursorData ← loadJson path
    match checkCursor expected actual with
    | .ok _ => pure ()
    | .error failure =>
        saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("invalid-request-cursor.json"))))
          (Json.mkObj
          [("condition", toJson "saved finite request cursor must equal the original source cursor"),
           ("actual", toJson failure.actual), ("expected", toJson expected)])
        throw (IO.userError "saved request cursor differs from the original source; both cursors retained")
  else saveJson path expected

/-- Serialize a pending moving reset with its original request, bounds and source states. -/
@[expose] def movesReport {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
  {ambient : Rational.Box}
  {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish} {current : Endpoint}
    {owner : Owner (polynomial.eval (segment.pointAt current.parameter))} {request : StepRequest}
    (pending : SquareRoot.Replay.BoundedPreparedSourceReplay.PendingMoves segment current owner request) : Json :=
  Json.mkObj
    [("kind", toJson "original bounded source checks before moving-reset replay"),
     ("parameter", toJson (fractionData current.parameter)),
     ("endpoint", toJson (fractionData request.endpoint.parameter)),
     ("diameter", toJson (fractionData request.rootDiameter)),
     ("movement", toJson (fractionData pending.movement)),
     ("originalBound", toJson (fractionData pending.readiness.clearance)),
     ("strengthenedBound", toJson (fractionData pending.strengthened.track.initial.clearance.bound)),
     ("movingBudget", toJson pending.movingBudget),
     ("sourceState", InitialExtractionCheckpoint.stateData owner.track.initial),
     ("strengthenedState", InitialExtractionCheckpoint.stateData pending.strengthened.track.initial)]

/-- Replay one original bounded source check from saved winding or diameter witnesses.

Return a checked result for that exact source request, preserving the distinction between accepted preparation and a
certified bounded miss. -/
@[expose] def source {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
  {ambient : Rational.Box} {start
  finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter))) (request : StepRequest)
    (inputs : SquareRoot.Replay.PreparedSourceReplay.Inputs segment request.rootDiameter)
    (control : RootRefinementCheckpoint.Control) (directory : System.FilePath) :
    m (SquareRoot.Replay.BoundedPreparedSourceReplay.Checked segment current owner request) := do
  match SquareRoot.Replay.BoundedPreparedSourceReplay.begin segment current owner request inputs with
  | .checked result => return result
  | .moving pending =>
      saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("moving-request.json")))) (movesReport
        pending)
      let windingControl : WindingCheckpoint.Control m := ⟨control.savedOnly, pure ()⟩
      let first ← MovingResetCheckpoint.runPlan windingControl MovingResetCheckpoint.sharedPool
        ((Purelib.System.FilePath.join directory (System.FilePath.mk ("first-reset"))))
          (SquareRoot.Replay.MovingRecenterReplay.moving owner)
      return ← MovingResetCheckpoint.runPlan windingControl MovingResetCheckpoint.sharedPool
        ((Purelib.System.FilePath.join directory (System.FilePath.mk ("later-reset"))))
        (SquareRoot.Replay.BoundedMovingReplay.finishMoves segment current owner request pending first)
  | .diameter readiness notReady =>
      have originalNotReady : ¬ AlreadyPrepared segment current owner request :=
        fun ready => notReady (readiness.ready_iff.mpr ready)
      let replay ← DiameterPreparationCheckpoint.run segment current.parameter owner request.rootDiameter
        control ((Purelib.System.FilePath.join directory (System.FilePath.mk ("diameter"))))
      match replay.outcome with
      | .error failure => return (SquareRoot.Replay.BoundedPreparedSourceReplay.finishDiameter segment current owner
        request
          originalNotReady none failure.equation (fun _ =>
            failure.diagnostic segment current.parameter owner request.rootDiameter replay.proposal
              ⟨replay.trace, replay.steps, replay.execution⟩ replay.proposal_eq replay.warmup))
      | .ok accepted => return (SquareRoot.Replay.BoundedPreparedSourceReplay.finishDiameter segment current owner
        request
          originalNotReady (some accepted.result) accepted.equation (fun impossible => nomatch impossible))

/-- Serialize a transport failure with its exact source, target, reserve and failed bounds. -/
@[expose] def transportReport {parameter target : Gaussian} {ambient : Rational.Box}
    {state : SquareRoot.Replay.PreparedRootStateReplay.State parameter ambient} {reserve : Coordinate}
    (failure : SquareRoot.Replay.PreparedOwnerTransportReplay.Failure state target reserve) : Json :=
  let common := [("source", toJson (gaussianData parameter)), ("target", toJson (gaussianData target)),
    ("reserve", toJson (fractionData reserve)), ("state", InitialExtractionCheckpoint.stateData state)]
  Json.mkObj (common ++ match failure with
    | .sourceZero _ => [("kind", toJson "invalid zero transport source")]
    | .targetZero _ => [("kind", toJson "invalid zero transport target")]
    | .stationary _ => [("kind", toJson "stationary transport requires original-owner branch")]
    | .clearance field displacement _ _ =>
        [("kind", toJson "inconclusive replay: transport fallback required"),
         ("field", toJson (reprStr field)), ("displacement", toJson (fractionData displacement)),
         ("bound", toJson (fractionData (field.bound state)))]
    | .reserve displacement _ _ carried _ _ =>
        [("kind", toJson "inconclusive replay: reserved-transport fallback required"),
         ("displacement", toJson (fractionData displacement)),
         ("carried", toJson (fractionData carried))])

/-- Retain a stationary owner at the requested reserve or report an unresolved reset.

Reuse the original owner when sufficient, then try its coefficient strengthening; success is equal to the original
retention operation. -/
@[expose] public def retainStationary {parameter : Gaussian} (owner : Owner parameter) (floor : Coordinate)
    (directory : System.FilePath) : m {value : Owner parameter // value = retainedAtReserve owner floor} := do
  if enough : floor ≤ owner.track.initial.clearance.bound then
    return ⟨owner, (retainedAtReserve_eq_self owner floor enough).symm⟩
  else
    let refreshed := SquareRoot.Clearance.QuadraticCoefficientClearance.strengthen owner
    if refreshedEnough : floor ≤ refreshed.track.initial.clearance.bound then
      return ⟨refreshed, (retainedAtReserve_eq_coefficientStrengthening owner floor enough refreshedEnough).symm⟩
    else
      saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("inconclusive-retention.json"))))
        (Json.mkObj
        [("kind", toJson "inconclusive replay: stationary owner requires retention reset"),
         ("floor", toJson (fractionData floor)),
         ("originalState", InitialExtractionCheckpoint.stateData owner.track.initial),
         ("refreshedState", InitialExtractionCheckpoint.stateData refreshed.track.initial)])
      throw (IO.userError "stationary bank retention reset needs replay; original owner and failed bounds retained")

/-- Restore the exact retained successor of an accepted bounded source step.

Stationary and moving transport keep the original owner equation; unresolved transport or retention is recorded without
becoming a failed bank depth. -/
@[expose] def successor {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
  {ambient : Rational.Box}
  {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) (within : segment.WithinAmbient)
    (current : Endpoint) (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest) (accepted : BoundedPreparedSource.Accepted segment current owner request)
    (inputs : SquareRoot.Replay.PreparedSourceReplay.Inputs segment request.rootDiameter)
    (directory : System.FilePath) :
    m {next : Owner (polynomial.eval (segment.pointAt request.endpoint.parameter)) //
      next = advanceCached segment within current owner request accepted.cached accepted.small} := do
  let preparedOwner := accepted.cached.preparedOwner
  let restored : SquareRoot.Replay.PreparedRootStateReplay.Checked _ preparedOwner.ambient
      (SquareRoot.Replay.PreparedRootStateReplay.capture preparedOwner.track.initial) := ⟨preparedOwner.track.initial,
        rfl⟩
  let target := polynomial.eval (segment.pointAt request.endpoint.parameter)
  let reserve := transportReserve segment current request
  if same : polynomial.eval (segment.pointAt current.parameter) = target then
    let carried : Owner target := SquareRoot.Owner.Transport.castOwnerParameter same preparedOwner
    let floor := inputs.predicted
    have exactTransport := BoundedPreparedBankReplay.advanceCached_stationary segment within current owner request
      accepted same
    let retained ← retainStationary carried floor directory
    return ⟨retained.val, by
      exact retained.property.trans
        ((congrArg (retainedAtReserve carried) inputs.predicted_eq).trans exactTransport.symm)⟩
  match SquareRoot.Replay.PreparedOwnerTransportReplay.check restored.state target reserve with
  | .error failure =>
      saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("inconclusive-transport.json"))))
        (transportReport failure)
      throw (IO.userError "bank transport replay unresolved; exact operands saved, not a failed depth")
  | .ok transport =>
      let floor := inputs.predicted
      match SquareRoot.Replay.PreparedRetainedTransportReplay.retain transport floor with
      | .error pending =>
          saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("inconclusive-retention.json"))))
            (Json.mkObj
            [("kind", toJson "inconclusive replay: endpoint retention reset required"),
             ("target", toJson (gaussianData target)), ("floor", toJson (fractionData floor)),
             ("originalBound", toJson (fractionData pending.originalBound)),
             ("refreshedBound", toJson (fractionData pending.refreshedBound)),
             ("originalState", InitialExtractionCheckpoint.stateData transport.value.track.initial),
             ("refreshedState", InitialExtractionCheckpoint.stateData pending.refreshed.track.initial)])
          throw (IO.userError "bank endpoint retention needs reset replay; checked operands saved")
      | .ok retained => return ⟨retained.value, by
          unfold advanceCached
          exact (retained.eq_original preparedOwner restored).trans
            (congrArg (retainedAtReserve
              (SquareRoot.Clearance.ExactQuadraticOwnerClearance.reservedTransport preparedOwner transport.targetNonzero
                (transport.originalSmall preparedOwner restored) reserve)) inputs.predicted_eq)⟩

/-- Replay the original bounded scan through a finite dyadic request cursor.

Preserve request order, saved source checks and retained successors; termination follows the certified count of
unvisited requests. -/
@[expose] def steps {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient
  : Rational.Box} {start
  finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) (within : segment.WithinAmbient)
    (control : RootRefinementCheckpoint.Control) (directory : System.FilePath)
    (diameter : Coordinate) (positive : 0 < diameter)
    (inputs : SquareRoot.Replay.PreparedSourceReplay.Inputs segment diameter) :
    (current : Endpoint) → (owner : Owner (polynomial.eval (segment.pointAt current.parameter))) →
      (index : Nat) → (cursor : Path.Dyadic.DyadicRequestCursor.Cursor) →
        m (StepChecked segment within current owner (Path.Dyadic.DyadicRequestCursor.requests diameter positive cursor))
  | current, owner, _, [] => return BoundedPreparedBankReplay.stop segment within current owner
  | current, owner, index, frame :: frames => do
      let head := Path.Dyadic.DyadicRequestCursor.expose diameter positive frame.depth frame.left frame.right frames
      let request := head.request
      let requests : Thunk (List StepRequest) := .mk fun _ =>
        Path.Dyadic.DyadicRequestCursor.requests diameter positive head.remaining
      let stepDirectory := (Purelib.System.FilePath.join directory (System.FilePath.mk (s!"step-{index}")))
      IO.FS.createDirAll stepDirectory
      retainCursor stepDirectory (cursorData index current head)
      let action : m (StepChecked segment within current owner (request :: requests.get)) := do
        if ordered : current.parameter ≤ request.endpoint.parameter then
          let result ← source segment current owner request (head.rootDiameter_eq.symm ▸ inputs) control stepDirectory
          match found : result.value with
          | .error failure =>
              saveJson ((Purelib.System.FilePath.join stepDirectory (System.FilePath.mk ("outcome.json")))) (Json.mkObj
                [("kind", toJson "certified miss of original bounded source check"),
                 ("parameter", toJson (fractionData current.parameter)),
                 ("endpoint", toJson (fractionData request.endpoint.parameter)),
                 ("movement", toJson (fractionData failure.variation)),
                 ("sourceState", InitialExtractionCheckpoint.stateData owner.track.initial)])
              return BoundedPreparedBankReplay.rejected (requests := .mk fun _ => request :: requests.get) (.mk fun _ =>
                .unresolved current owner request requests.get ordered failure)
          | .ok accepted =>
              let next ← successor segment within current owner request accepted
                (head.rootDiameter_eq.symm ▸ inputs) stepDirectory
              saveJson ((Purelib.System.FilePath.join stepDirectory (System.FilePath.mk ("outcome.json")))) (Json.mkObj
                [("kind", toJson "accepted original bounded source and retained successor"),
                 ("parameter", toJson (fractionData current.parameter)),
                 ("endpoint", toJson (fractionData request.endpoint.parameter)),
                 ("prepared", InitialExtractionCheckpoint.stateData accepted.cached.preparedOwner.track.initial),
                 ("successor", InitialExtractionCheckpoint.stateData next.val.track.initial)])
              let tail ← steps segment within control directory diameter positive inputs request.endpoint
                next.val (index + 1) head.remaining
              return BoundedPreparedBankReplay.prepend segment within current owner request requests ordered
                accepted (result.equation.trans found) next.val next.property tail
        else return BoundedPreparedBankReplay.rejected (requests := .mk fun _ => request :: requests.get) (.mk fun _ =>
           .unordered current owner request requests.get ordered)
      let checked ← action
      return cast (congrArg (StepChecked segment within current owner) head.equation.symm) checked
termination_by _ _ _ cursor => Path.Dyadic.DyadicRequestCursor.count cursor
decreasing_by exact head.decreases

/-- Continue only the canonical uniform-window branch justified by the retained bounded diameter miss. Other unresolved
source branches keep their original diagnostic; they are not silently replaced by another preparation. -/
@[expose] def uniformAfterMiss {polynomial :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient :
  Rational.Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter))) (request : StepRequest)
    (control : RootRefinementCheckpoint.Control) (directory : System.FilePath)
    (failure : BoundedPreparedSource.Inconclusive segment current owner request) :
    m (BoundedPreparedSource.Accepted segment current owner request) := by
  rcases failure with ⟨sourceOwner, sourceEq, endpoint, endpointEq, requested, requestEq,
    variation, variationEq, movingBudget, movingBudgetEq, reason⟩
  cases sourceEq
  cases requestEq
  cases variationEq
  cases reason with
  | proposalMiss notReady candidate found miss => exact do
      let saved ← UniformSampleCheckpoint.restore segment current.parameter owner request.rootDiameter
        control ((Purelib.System.FilePath.join directory (System.FilePath.mk ("uniform-sample"))))
      let value := SquareRoot.Replay.UniformPreparationReplay.strengthened segment current.parameter current.inside
        owner
        request.rootDiameter request.rootDiameterPositive saved
      if carries : ClearSheetContinuation.variationBound segment current.parameter request.endpoint.parameter <
          value.track.initial.clearance.bound then
        let cached := SquareRoot.Replay.UniformPreparationReplay.cachedOfMiss segment current owner request
          notReady candidate found miss saved carries
        return ⟨cached, carries⟩
      else
        saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("inconclusive-uniform.json"))))
          (Json.mkObj
          [("kind", toJson "uniform window misses edge; moving retry fallback unresolved"),
           ("window", InitialExtractionCheckpoint.stateData value.track.initial),
           ("movement", toJson (fractionData (ClearSheetContinuation.variationBound segment
             current.parameter request.endpoint.parameter)))])
        throw (IO.userError "uniform source does not carry edge; retained moving retry required")
  | proposalUnavailable _ _ _ => exact do
      throw (IO.userError "canonical unavailable-proposal fallback requires replay; diameter trace retained")
  | strengthened => exact do
      throw (IO.userError "canonical moving fallback requires replay; source comparisons retained")

/-- Restore the terminal acquisition, including the certified uniform-window fallback. Any other unresolved source
branch is not a declined mesh. -/
@[expose] def terminalSteps {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
  {ambient : Rational.Box}
  {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) (within : segment.WithinAmbient)
    (control : RootRefinementCheckpoint.Control) (directory : System.FilePath) :
    (current : Endpoint) → (owner : Owner (polynomial.eval (segment.pointAt current.parameter))) →
      (index : Nat) → (requests : List StepRequest) →
      m (SquareRoot.Replay.TerminalAcquisitionReplay.Checked segment within current owner requests)
  | current, owner, _, [] => return SquareRoot.Replay.TerminalAcquisitionReplay.stop segment within current owner
  | current, owner, index, request :: requests => do
      let stepDirectory := (Purelib.System.FilePath.join directory (System.FilePath.mk (s!"step-{index}")))
      IO.FS.createDirAll stepDirectory
      if ordered : current.parameter ≤ request.endpoint.parameter then
        let inputs := SquareRoot.Replay.PreparedSourceReplay.Inputs.capture segment request.rootDiameter
        let result ← source segment current owner request inputs control stepDirectory
        let accepted ← match result.value with
          | .error failure => uniformAfterMiss segment current owner request control stepDirectory failure
          | .ok accepted => pure accepted
        let next ← successor segment within current owner request accepted inputs stepDirectory
        let tail ← terminalSteps segment within control directory request.endpoint next.val (index + 1) requests
        return SquareRoot.Replay.TerminalAcquisitionReplay.prepend segment within current owner
          request requests accepted.cached ordered accepted.small next.val next.property tail
      else
        return SquareRoot.Replay.TerminalAcquisitionReplay.unordered segment within current owner request requests
          ordered

/-- Restore the terminal acquisition result at one original dyadic depth. -/
@[expose] def terminalDepth {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
  {ambient : Rational.Box}
  {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) (within : segment.WithinAmbient)
    (owner : Owner (polynomial.eval start)) (depth : Nat) (diameter : Coordinate) (positive : 0 < diameter)
    (control : RootRefinementCheckpoint.Control) (directory : System.FilePath) :
    m (SquareRoot.Replay.TerminalAcquisitionReplay.DepthResult segment within owner diameter positive depth) := do
  let saved ← terminalSteps segment within control directory zeroEndpoint (ownerAtStart segment owner) 0
    (Requests depth diameter positive)
  return SquareRoot.Replay.TerminalAcquisitionReplay.atDepth segment within owner diameter positive depth saved

/-- Preserve the original preferred-depth decision and its proved safe fallback. Each returned acquisition identifies
the canonical constructor. -/
@[expose] def terminalAcquire {polynomial :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient :
  Rational.Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) (within : segment.WithinAmbient)
    (owner : Owner (polynomial.eval start)) (diameter : Coordinate) (positive : 0 < diameter)
    (preferred safeDepth : Nat)
    (safe : Subdivision.DyadicMeshSafe segment zeroEndpoint PreparedClearPathModels.oneEndpoint
      (ownerAtStart segment owner) safeDepth diameter positive)
    (control : RootRefinementCheckpoint.Control) (directory : System.FilePath) :
    m {value : SquareRoot.Preparation.Terminal.AcquiredDyadic segment within owner diameter positive //
      value = (SquareRoot.Preparation.Terminal.AcquiredDyadic.acquire segment within owner diameter positive preferred
        safeDepth safe).val} := do
  let acquireSafe : System.FilePath → m {value : SquareRoot.Preparation.Terminal.AcquiredDyadic
      segment within owner diameter positive // value.depth = safeDepth} := fun path => do
    let result ← terminalDepth segment within owner safeDepth diameter positive control path
    match result with
    | .accepted value same => pure (⟨value, same⟩ : {value : SquareRoot.Preparation.Terminal.AcquiredDyadic
        segment within owner diameter positive // value.depth = safeDepth})
    | .declined failed => (by
        have success := Subdivision.tryDyadic_eq_some_checkedDyadic segment within zeroEndpoint
          PreparedClearPathModels.oneEndpoint (ownerAtStart segment owner) safeDepth diameter positive safe
        rw [failed] at success
        cases success)
  if shorter : preferred < safeDepth then
    let result ← terminalDepth segment within owner preferred diameter positive control directory
    match result with
    | .accepted value same =>
        return ⟨value, SquareRoot.Replay.TerminalAcquisitionReplay.acquired_eq_preferred segment within
          owner diameter positive preferred safeDepth safe shorter value same⟩
    | .declined failed =>
        let value ← acquireSafe ((Purelib.System.FilePath.join directory (System.FilePath.mk ("safe-fallback"))))
        return ⟨value.val, SquareRoot.Replay.TerminalAcquisitionReplay.acquired_eq_after_decline
          segment within owner diameter positive preferred safeDepth safe shorter failed value.val value.property⟩
  else
    let value ← acquireSafe directory
    return ⟨value.val, SquareRoot.Replay.TerminalAcquisitionReplay.acquired_eq_without_preferred
      segment within owner diameter positive preferred safeDepth safe shorter value.val value.property⟩

/-- Restore a segment trace equal to its canonical preferred-depth and safe-fallback construction. -/
@[expose] def tracedSegment {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
  {ambient : Rational.Box}
  {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) (within : segment.WithinAmbient)
    (owner : Owner (polynomial.eval start))
    (control : RootRefinementCheckpoint.Control) (directory : System.FilePath) :
    m {value : PreparedPathTrace.TracedSegment segment within owner //
      value = PreparedPathTrace.TracedSegment.build segment within owner} := do
  let budget := Riemann.Paths.PreparedTraceBudget.build segment zeroEndpoint PreparedClearPathModels.oneEndpoint
  let acquired ← terminalAcquire segment within owner budget.rootDiameter budget.rootDiameter_positive
    (Rational.Geometric.Search.firstQuarterBelow budget.variation 0 budget.movementBudget) budget.depth
    (budget.meshSafe (ownerAtStart segment owner) (by decide)) control directory
  return ⟨SquareRoot.Replay.TracedSegmentReplay.restore segment within owner budget acquired.val acquired.property,
    SquareRoot.Replay.TracedSegmentReplay.restore_eq segment within owner budget rfl acquired.val acquired.property⟩

/-- Restore a complete path trace while passing each exact retained endpoint owner to the next segment. -/
@[expose] def tracedPath {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
  {ambient : Rational.Box}
    (control : RootRefinementCheckpoint.Control) (directory : System.FilePath) :
    {start finish : Gaussian} → (path : Polynomial.Geometry.ClearPath polynomial ambient start finish) →
      (within : path.WithinAmbient) → (owner : Owner (polynomial.eval start)) → (index : Nat) →
      m {value : PreparedPathTrace.TracedPath path owner //
        value = PreparedPathTrace.TracedPath.build path within owner}
  | _, _, .nil point, within, owner, _ =>
      return ⟨PreparedPathTrace.TracedPath.build (.nil point) within owner, rfl⟩
  | _, _, .cons head tail, within, owner, index => do
      let first ← tracedSegment head within.head owner control ((Purelib.System.FilePath.join directory
        (System.FilePath.mk (s!"segment-{index}"))))
      let rest ← tracedPath control directory tail within.tail first.val.finishOwner (index + 1)
      return ⟨PreparedPathTrace.TracedPath.cons first.val rest.val,
        SquareRoot.Replay.TracedSegmentReplay.cons_eq head tail within owner first.val first.property
          rest.val rest.property⟩

/-- Replay the original bounded preparation of every segment at a fixed depth and diameter.

A rejected head retains its source failure; accepted heads pass their exact terminal owners into the remaining path. -/
@[expose] def path {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient
  : Rational.Box}
    (depth : Nat) (diameter : Coordinate) (positive : 0 < diameter)
    (control : RootRefinementCheckpoint.Control) (directory : System.FilePath) :
    {start finish : Gaussian} → (path : Polynomial.Geometry.ClearPath polynomial ambient start finish) →
      (within : path.WithinAmbient) → (owner : Owner (polynomial.eval start)) →
      (index : Nat) → m (PathChecked depth diameter positive path within owner)
  | _, _, .nil point, _, owner, _ => return ⟨.ok ⟨.nil point owner, rfl⟩, rfl⟩
  | _, _, .cons segment rest, within, owner, index => do
      let inputs := SquareRoot.Replay.PreparedSourceReplay.Inputs.capture segment diameter
      let scanned ← steps segment within.head control ((Purelib.System.FilePath.join directory (System.FilePath.mk
        (s!"segment-{index}")))) diameter positive inputs
        zeroEndpoint (ownerAtStart segment owner) 0
        (Path.Dyadic.DyadicRequestCursor.initial depth zeroEndpoint PreparedClearPathModels.oneEndpoint)
      let first : StepChecked segment within.head zeroEndpoint (ownerAtStart segment owner)
          (Requests depth diameter positive) :=
        cast (congrArg (StepChecked segment within.head zeroEndpoint (ownerAtStart segment owner))
          (Path.Dyadic.DyadicRequestCursor.initial_eq depth zeroEndpoint PreparedClearPathModels.oneEndpoint diameter
            positive)) scanned
      match found : first.val with
      | .error failure => return BoundedPreparedBankReplay.pathRejected (.mk fun _ =>
          .head segment rest within owner failure.get)
      | .ok accepted =>
          let complete := BoundedPreparedBankReplay.head segment within.head owner depth diameter positive accepted
          let tail ← path depth diameter positive control directory rest within.tail complete.finishOwner (index + 1)
          return BoundedPreparedBankReplay.pathPrepend depth diameter positive segment rest within owner
            accepted (first.property.trans (congrArg BoundedPreparedBankReplay.forceFailure found)) tail

/-- Replay one complete bounded bank trial over the original ordered task list.

Retain the first certified miss or all accepted preparations with their original attempt equations. -/
@[expose] def trial {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (depth :
  Nat) (diameter : Coordinate) (positive :
  0 < diameter)
    (control : RootRefinementCheckpoint.Control) (directory : System.FilePath) :
    (tasks : List (SquareRoot.Preparation.Bank.Adaptive.Task polynomial)) → (index : Nat) →
      m (AdaptivePreparedBankReplay.Trial depth diameter positive tasks)
  | [], _ => return .nil
  | task :: tasks, index => do
      let result ← path depth diameter positive control ((Purelib.System.FilePath.join directory (System.FilePath.mk
        (s!"task-{index}")))) task.path task.within task.owner 0
      match found : result.val with
      | .error failure => return .miss (.mk fun _ => ⟨depth, rfl, diameter, rfl, failure.get⟩)
      | .ok accepted =>
          have exactAttempt : BoundedPreparedBanks.attempt depth diameter positive task.path task.within task.owner =
              .ok accepted := by
            unfold BoundedPreparedBanks.attempt
            rw [result.property, found]
            rfl
          let rest ← trial depth diameter positive control directory tasks (index + 1)
          return .cons accepted exactAttempt rest

/-- Replay the original bounded bank-depth search and certify its selected result.

Only certified trial misses advance the depth; a missing sufficient-depth replay is retained as inconclusive and never
treated as a rejected bank. -/
@[expose] def search {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (tasks
  : List
  (SquareRoot.Preparation.Bank.Adaptive.Task polynomial))
    (diameter : Coordinate) (positive : 0 < diameter)
    (control : RootRefinementCheckpoint.Control) (directory : System.FilePath)
    (minimum upper : Nat) (upperEq : upper = max (SquareRoot.Preparation.Bank.Adaptive.maximumDepth diameter tasks)
      minimum) :
    (depth : Nat) → (minimumLe : minimum ≤ depth) → (remaining : Nat) → (bound : upper = depth + remaining) →
      m {value : SquareRoot.Preparation.Bank.Adaptive.Selected tasks diameter positive minimum //
        AdaptivePreparedBankReplay.search tasks diameter positive minimum upper upperEq depth minimumLe remaining bound
          = value}
  | depth, _, 0, _ => do
      saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("inconclusive.json")))) (Json.mkObj
        [("kind", toJson "inconclusive replay: sufficient-depth fallback needs a checkpoint loader"),
         ("depth", toJson depth), ("upperDepth", toJson upper), ("minimumDepth", toJson minimum),
         ("diameter", toJson (fractionData diameter)), ("taskCount", toJson tasks.length)])
      throw (IO.userError "canonical sufficient-depth fallback reached; not a failed bank or invalid input")
  | depth, minimumLe, remaining + 1, bound => do
      profile directory s!"BEGIN checked bank depth {depth} of {upper}"
      let checked ← trial depth diameter positive control ((Purelib.System.FilePath.join directory (System.FilePath.mk
        (s!"depth-{depth}")))) tasks 0
      saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("proposal-counts.json")))) (←
        RootRefinementCheckpoint.Execution.counts)
      match found : checked.value with
      | some banks =>
          saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("selected.json")))) (depth, upper,
            minimum, fractionData diameter)
          profile directory s!"END original selected bank depth {depth}"
          return ⟨AdaptivePreparedBankReplay.selected tasks diameter positive minimum upper upperEq
            depth minimumLe remaining bound banks,
            AdaptivePreparedBankReplay.search_accept tasks diameter positive minimum upper upperEq
              depth minimumLe remaining bound checked banks found⟩
      | none =>
          saveJson ((Purelib.System.FilePath.join (Purelib.System.FilePath.join directory (System.FilePath.mk
            (s!"depth-{depth}"))) (System.FilePath.mk ("miss.json"))))
            ("certified miss of original bounded bank trial; per-step evidence retained", depth, upper)
          let tail ← search tasks diameter positive control directory minimum upper upperEq
            (depth + 1) (Nat.le_succ_of_le minimumLe) remaining (by clear upperEq; omega)
          return ⟨tail.val, (AdaptivePreparedBankReplay.search_miss tasks diameter positive minimum upper upperEq
            depth minimumLe remaining bound checked found).trans tail.property⟩

/-- Restore the canonical bank selection from the requested minimum depth. -/
@[expose] def selectFrom {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
  (tasks : List
  (SquareRoot.Preparation.Bank.Adaptive.Task polynomial))
    (diameter : Coordinate) (positive : 0 < diameter) (minimum : Nat)
    (control : RootRefinementCheckpoint.Control) (directory : System.FilePath) :
    m {value : SquareRoot.Preparation.Bank.Adaptive.Selected tasks diameter positive minimum //
      value = SquareRoot.Preparation.Bank.Adaptive.selectFrom tasks diameter positive minimum} := do
  IO.FS.createDirAll directory
  let upper := max (SquareRoot.Preparation.Bank.Adaptive.maximumDepth diameter tasks) minimum
  let result ← search tasks diameter positive control directory minimum upper rfl minimum (Nat.le_refl _)
    (upper - minimum)
    ((Data.Nat.Subtraction.add_sub_of_le (Data.Nat.Order.le_max_right _ _)).symm)
  return ⟨result.val, ((AdaptivePreparedBankReplay.selectFrom_eq tasks diameter positive minimum).trans
    result.property).symm⟩

/-- Restore the canonical bank selection beginning at depth zero. -/
@[expose] def select {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (tasks
  : List
  (SquareRoot.Preparation.Bank.Adaptive.Task polynomial))
    (diameter : Coordinate) (positive : 0 < diameter)
    (control : RootRefinementCheckpoint.Control) (directory : System.FilePath) :
    m {value : SquareRoot.Preparation.Bank.Adaptive.Selected tasks diameter positive //
      value = SquareRoot.Preparation.Bank.Adaptive.select tasks diameter positive} :=
  selectFrom tasks diameter positive 0 control directory

end PreparedBankCheckpoint

namespace DirectMeshCheckpoint

variable {m : Type → Type} [Monad m] [MonadLiftT IO m] [MonadLiftT BaseIO m]
  [MonadExceptOf IO.Error m] [MonadStateOf RootRefinementCheckpoint.Counts m]

open IntegrationCheckpoint Purelib.Riemann
open Purelib.Riemann.Transport Purelib.Riemann.RootContinuation Purelib.Riemann.Integration
open Purelib.Riemann.Branches Purelib.Riemann.Readings Purelib.Riemann.Paths Purelib.Riemann.Topology
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open PreparedSubdivisionModelCore (PreparedEdge)
open PreparedSheetContinuation (Coordinate Endpoint)
open CheckedDirectGeometry (midpoint)

set_option genInjectivity false in
/-- Bind each saved traversal node to its original finite request. Expensive diameter witnesses have their own checked
source headers below this node.

The schema version, depth, endpoint encodings and root diameter retain one
exact mesh request. Equality checking compares those same fields before
reusing the original traversal node. -/
structure RequestData where
  /-- The direct-mesh request serialization version. -/ schema : Nat := 1
  /-- The remaining dyadic traversal depth. -/ depth : Nat
  /-- The exact left endpoint parameter. -/ left : String
  /-- The exact right endpoint parameter. -/ right : String
  /-- The exact requested root diameter. -/ diameter : String
deriving DecidableEq, Json.ToJson, Json.FromJson

constructive_injectivity RequestData

set_option genInjectivity false in
/-- A saved direct-mesh request certified different from the original traversal node. -/
structure InvalidRequest (expected : RequestData) where
  /-- The saved traversal-node request. -/ actual : RequestData
  /-- The saved request is not the expected original node. -/ different : actual ≠ expected

constructive_injectivity InvalidRequest

/-- Decide exact direct-mesh request equality, preserving either the equation or the mismatch. -/
@[expose] def checkRequest (expected actual : RequestData) :
    Except (InvalidRequest expected) {value : RequestData // value = expected} :=
  if equal : actual = expected then .ok ⟨actual, equal⟩ else .error ⟨actual, equal⟩

/-- Save a direct-mesh node request or reject its incompatible saved counterpart.

Retain both requests before stopping on a mismatch. -/
@[expose] public def retainRequest (directory : System.FilePath) (expected : RequestData) : m Unit := do
  IO.FS.createDirAll directory
  let path := (Purelib.System.FilePath.join directory (System.FilePath.mk ("mesh-request.json")))
  if ← path.pathExists then
    let actual : RequestData ← loadJson path
    match checkRequest expected actual with
    | .ok _ => pure ()
    | .error failure =>
        saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("invalid-mesh-request.json"))))
          (Json.mkObj
          [("condition", toJson "saved mesh request must equal the original source request"),
           ("actual", toJson failure.actual), ("expected", toJson expected)])
        throw (IO.userError "saved mesh request differs from the original source; both requests retained")
  else saveJson path expected

/-- Replay the original left-first geometry traversal. All completed root proposals are saved before proceeding to
another child. A missing replay branch preserves its accepted prefix and cannot become a rejected depth. -/
@[expose] def run {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Differentials.Basic.Differential genus}
    (parent : PreparedEdge curve differential)
    (proper : parent.left.parameter < parent.request.endpoint.parameter)
    (diameter : Coordinate) (positive : 0 < diameter)
    (inputs : SquareRoot.Replay.PreparedSourceReplay.Inputs parent.segment diameter)
    (control : RootRefinementCheckpoint.Control) :
    (depth : Nat) → (left right : Endpoint) →
    (lower : parent.left.parameter ≤ left.parameter) →
    (upper : right.parameter ≤ parent.request.endpoint.parameter) →
    (localProper : left.parameter < right.parameter) →
    (directory : System.FilePath) →
    m (Except (CheckedDirectGeometryReplay.Pending parent proper diameter positive
        depth left right lower upper localProper)
      (CheckedDirectGeometryReplay.Checked parent proper diameter positive
        depth left right lower upper localProper))
  | 0, left, right, lower, upper, localProper, directory => do
      retainRequest directory ⟨1, 0, fractionText left.parameter, fractionText right.parameter,
        fractionText diameter⟩
      let position := CheckedDirectGeometryReplay.position parent proper left right lower upper localProper
      match observed : CheckedDirectGeometryReplay.queryOwner parent left position with
      | .error failure =>
          saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("inconclusive-transport.json"))))
            (PreparedBankCheckpoint.transportReport failure)
          return .error (.transport failure observed)
      | .ok owner =>
          let source ← PreparedBankCheckpoint.source parent.segment left owner.val
              (PreparedEdgeRecasting.directRequest right diameter positive) inputs control directory
          let checked := CheckedDirectGeometryReplay.leaf parent proper diameter positive left right
            lower upper localProper owner.val owner.property source
          let outcome := match source.value with
            | .error failure => Json.mkObj
                [("kind", toJson "certified miss of original mesh leaf"),
                 ("variation", toJson (fractionData failure.variation)),
                 ("owner", InitialExtractionCheckpoint.stateData owner.val.track.initial)]
            | .ok accepted => Json.mkObj
                [("kind", toJson "accepted original mesh leaf"),
                 ("owner", InitialExtractionCheckpoint.stateData owner.val.track.initial),
                 ("prepared", InitialExtractionCheckpoint.stateData accepted.cached.preparedOwner.track.initial)]
          saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("mesh-outcome.json")))) outcome
          return .ok checked
  | depth + 1, left, right, lower, upper, localProper, directory => do
      retainRequest directory ⟨1, depth + 1, fractionText left.parameter, fractionText right.parameter,
        fractionText diameter⟩
      have firstProper := CheckedDirectGeometry.left_lt_midpoint localProper
      have secondProper := CheckedDirectGeometry.midpoint_lt_right localProper
      match ← run parent proper diameter positive inputs control depth left (midpoint left right)
          lower (secondProper.le.trans upper) firstProper ((Purelib.System.FilePath.join directory (System.FilePath.mk
            ("left")))) with
      | .error pending => return .error (.first pending)
      | .ok first =>
          match found : first.val with
          | .error failure =>
              return .ok (CheckedDirectGeometryReplay.firstFailed parent proper diameter positive depth
                left right lower upper localProper failure (first.property.trans found))
          | .ok accepted =>
              match ← run parent proper diameter positive inputs control depth (midpoint left right) right
                  (lower.trans firstProper.le) upper secondProper ((Purelib.System.FilePath.join directory
                    (System.FilePath.mk ("right")))) with
              | .error pending => return .error (.second accepted (first.property.trans found) pending)
              | .ok tail =>
                  return .ok (CheckedDirectGeometryReplay.second parent proper diameter positive depth
                    left right lower upper localProper accepted (first.property.trans found) tail)

end DirectMeshCheckpoint
namespace RootTransportCheckpoint

variable {m : Type → Type} [Monad m] [MonadLiftT IO m] [MonadLiftT BaseIO m]
  [MonadExceptOf IO.Error m] [MonadStateOf RootRefinementCheckpoint.Counts m]

open Purelib.Polynomial.Geometry.ClearPath (GaussianPolynomial)

open IntegrationCheckpoint
open Purelib.Riemann
open Purelib.Riemann.Transport Purelib.Riemann.RootContinuation Purelib.Riemann.Integration
open Purelib.Riemann.Branches Purelib.Riemann.Readings Purelib.Riemann.Paths Purelib.Riemann.Topology
open RootOwnerFrames (OwnerFrame)
open RootPathTransport (TransportRow PathTransport)

/-- An endpoint owner classifier returning the original frame-selection result with its exact equation. -/
abbrev Classifier {parameter : Data.Gaussian.Basic.Canonical} (frame : OwnerFrame parameter) :=
  (owner : SquareRootContinuationChain.Owner parameter) → RootRefinementCheckpoint.Control → System.FilePath →
    m {value : RootOwnerFrames.OwnerSelection frame.owners owner // value = frame.select owner}

/-- Restore the canonical owner assignment using its original sample and checked refinement.

Retain the sample, refinement state and selected finite owner index, with equality to the original frame classifier. -/
@[expose] def classify {parameter : Data.Gaussian.Basic.Canonical} (nonzero : parameter ≠ 0) (frame : OwnerFrame
  parameter)
    (frameEq : frame = OwnerFrame.build nonzero) : Classifier (m := m) frame := fun owner control directory => do
  IO.FS.createDirAll directory
  profile directory "BEGIN original reconditioning sample"
  let sample : SquareRoot.Replay.ReconditioningAssignmentReplay.Sample nonzero owner := ⟨SquareRootReconditioning.sample
    nonzero owner, rfl⟩
  saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("sample.json")))) (gaussianData sample.val)
  profile directory "END original reconditioning sample; BEGIN checked assignment refinement"
  let input := SquareRootReconditioning.isolationInput nonzero
  let track := Residual.Global.Replay.track input sample.val
    (SquareRoot.Replay.ReconditioningAssignmentReplay.inside nonzero owner sample)
    (SquareRootReconditioning.requestedRadius_positive owner)
    (SquareRoot.Replay.ReconditioningAssignmentReplay.residual nonzero owner sample)
  let radius := Exact.Ownership.Radius.assignmentRadius _ _ input.isolation
  let rawControl ← PolynomialInverseCheckpoint.Control.create control.savedOnly control.killAfterWrites
  let refinementAction : PolynomialInverseCheckpoint.Execution
      (SquareRoot.Replay.ReconditioningAssignmentReplay.Refined nonzero owner sample) :=
    NewtonExtractionCheckpoint.refineState input.degreeAtLeastTwo input.squarefree input.elimination
      track.initial radius (Exact.Ownership.Radius.assignmentRadius_pos _ _ input.isolation)
      rawControl ((Purelib.System.FilePath.join directory (System.FilePath.mk ("refinement"))))
  let (refinementResult, refinementCounts) ← PolynomialInverseCheckpoint.Execution.run refinementAction {}
  let refined ← (@IO.ofExcept IO.Error _ ⟨Purelib.System.IO.Error.toString⟩) refinementResult
  let saved : SquareRoot.Replay.ReconditioningAssignmentReplay.Refined nonzero owner sample := refined
  let value := SquareRoot.Replay.ReconditioningAssignmentReplay.select nonzero owner frame frameEq sample saved
  saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("selected-index.json")))) value.index.val
  saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("refinement-counts.json")))) refinementCounts
  profile directory "END checked assignment refinement and canonical selection"
  return ⟨value, SquareRoot.Replay.ReconditioningAssignmentReplay.select_eq nonzero owner frame frameEq sample saved⟩

/-- Restore the original path before running its canonical endpoint classifier. The saved classification is a readback
check, not a replacement classifier. -/
@[expose] def row {p : GaussianPolynomial} {box : Rational.Box} {start finish :
  Data.Gaussian.Basic.Canonical}
    (path : Polynomial.Geometry.ClearPath p box start finish) (within : path.WithinAmbient)
    (first : OwnerFrame (p.eval start)) (last : OwnerFrame (p.eval finish)) (index : Fin 2) (classifyLast : Classifier
      (m := m) last)
    (control : RootRefinementCheckpoint.Control) (directory : System.FilePath) :
    m {value : TransportRow path first last index // value = TransportRow.build path within first last index} := do
  IO.FS.createDirAll directory
  let traced ← PreparedBankCheckpoint.tracedPath control ((Purelib.System.FilePath.join directory (System.FilePath.mk
    ("path")))) path within (first.owners index) 0
  profile directory "BEGIN canonical endpoint classifier; restored path retained"
  let selected ← classifyLast traced.val.finishOwner control ((Purelib.System.FilePath.join directory
    (System.FilePath.mk ("classification"))))
  let value := RootContinuation.RootTransportReplay.row path first last index traced.val selected.val
  let actual := Json.mkObj [("source", toJson index.val), ("target", toJson value.target.val)]
  let savedPath := (Purelib.System.FilePath.join directory (System.FilePath.mk ("selection.json")))
  if ← savedPath.pathExists then
    let saved : Json ← loadJson savedPath
    unless saved == actual do
      saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("invalid-selection.json")))) (saved,
        actual)
      throw (IO.userError "endpoint classifier changed the retained canonical row")
  else saveJson savedPath actual
  profile directory "END canonical endpoint classifier"
  return ⟨value, RootContinuation.RootTransportReplay.row_eq path within first last index traced.val traced.property
    selected.val selected.property⟩

/-- Restore both finite owner rows of the original path transport. -/
@[expose] def transport {p : GaussianPolynomial} {box : Rational.Box} {start finish :
  Data.Gaussian.Basic.Canonical}
    (path : Polynomial.Geometry.ClearPath p box start finish) (within : path.WithinAmbient)
    (first : OwnerFrame (p.eval start)) (last : OwnerFrame (p.eval finish)) (classifyLast : Classifier (m := m) last)
    (control : RootRefinementCheckpoint.Control) (directory : System.FilePath) :
    m {value : PathTransport path first last // value = PathTransport.build path within first last} := do
  let zero ← row path within first last 0 classifyLast control ((Purelib.System.FilePath.join directory
    (System.FilePath.mk ("zero"))))
  let one ← row path within first last 1 classifyLast control ((Purelib.System.FilePath.join directory
    (System.FilePath.mk ("one"))))
  return ⟨RootContinuation.RootTransportReplay.transport path first last zero.val one.val,
    RootContinuation.RootTransportReplay.transport_eq path within first last zero.val one.val zero.property
      one.property⟩

/-- Restore the original root edge from its separately checked forward and reverse path transports. -/
@[expose] def edge {p : GaussianPolynomial} {box : Rational.Box} {start finish :
  Data.Gaussian.Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment p box start finish) (within : segment.WithinAmbient)
    (first : OwnerFrame (p.eval start)) (last : OwnerFrame (p.eval finish))
    (classifyFirst : Classifier (m := m) first) (classifyLast : Classifier (m := m) last)
    (control : RootRefinementCheckpoint.Control) (directory : System.FilePath) :
    m {value : SquareRoot.Grid.RootEdges.RootEdge (ambient := box) first last //
      value = SquareRoot.Grid.RootEdges.RootEdge.build segment within first last} := do
  let forward ← transport (.cons segment (.nil finish)) (.cons within (.nil finish))
    first last classifyLast control ((Purelib.System.FilePath.join directory (System.FilePath.mk ("forward"))))
  let backward ← transport (.cons (Branches.BranchCutLifts.ClearSegment.reverse segment) (.nil start))
    (.cons (Branches.BranchCutLifts.ClearSegment.reverse_withinAmbient segment within) (.nil start))
    last first classifyFirst control ((Purelib.System.FilePath.join directory (System.FilePath.mk ("backward"))))
  return ⟨RootContinuation.RootTransportReplay.edge segment first last forward.val backward.val,
    RootContinuation.RootTransportReplay.edge_eq segment within first last forward.val backward.val forward.property
      backward.property⟩

end RootTransportCheckpoint
