module

meta import Purelib.Elab.ConstructiveInjectivity

import Purelib.System.FilePath

import Purelib.Data.Json.Codec
import Purelib.Data.Json.Basic
import Purelib.Data.String.Basic
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.RootContinuation.SquareRootReconditioning
import Purelib.Polynomial.Dense.Gaussian.Derivative.Evaluation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.RootContinuation.UniformSquareRootPreparation
import Purelib.Riemann.Topology.SquareRootContinuationChain
import scripts.checkpoint.RootState
import Purelib.Approximation.Rational.SquareRoot.Radius.Dyadic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Grid.Replay
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Rounding.Floor
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.RootIsolation.Newton.Search.Replay.Input
import Purelib.RootIsolation.Newton.Search.Execution.Uniqueness
public import Purelib.RootIsolation.SquareRoot.Newton.Replay.Input

import Purelib.RootIsolation.SquareRoot.Clearance.QuadraticAxisElimination
import Purelib.RootIsolation.SquareRoot.Clearance.QuadraticLineClearance
import Purelib.RootIsolation.SquareRoot.Replay.PreparedRawStateReplay
import Purelib.RootIsolation.SquareRoot.Replay.PreparedSourceReplay
public import Purelib.RootIsolation.SquareRoot.Replay.CheckedDiameterReplay
import Purelib.RootIsolation.SquareRoot.Replay.PreparedRawSourceReplay
public import Purelib.RootIsolation.SquareRoot.Replay.UniformPreparationReplay
public import scripts.checkpoint.RootRefinement
import Purelib.RootIsolation.SquareRoot.Newton.Replay.Trace
import Purelib.RootIsolation.SquareRoot.Newton.Search
import Purelib.RootIsolation.SquareRoot.Newton.Replay.Step
import Purelib.Riemann.RootContinuation.CheckedSquareRootPreparation.Uniqueness
import Init.Core
import Init.Prelude
import Init.System.FilePath
import Init.System.IO
import Init.System.IOError
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Grid.Box
import Purelib.Approximation.Gaussian.Grid.Nearest.Basic
import Purelib.Approximation.Gaussian.Grid.Nearest.Replay
import Purelib.CCL.Progressive.IntegrationQueries
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Inverse.Check
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Newton.Basic
import Purelib.Polynomial.Power.Gaussian
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.RootIsolation.Refinement.Basic
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.State.WindingOne.Raw
import Purelib.RootIsolation.Track.Basic
import scripts.checkpoint.Integration

open Purelib

open Purelib.Approximation.Gaussian.Grid

open Purelib.Approximation.Rational.SquareRoot.Radius.Dyadic

open Purelib.Data.Rat

open Purelib.Data.Rat.Rounding

open Purelib.Geometry

open Purelib.Polynomial.Dense.Gaussian.Derivative

open Purelib.Polynomial.Geometry

open Purelib.RootIsolation.Newton.Search

open Purelib.RootIsolation.Newton.Search.Replay

open Purelib.RootIsolation.SquareRoot.Clearance

open Purelib.RootIsolation.SquareRoot.Clearance.QuadraticLineClearance

open Purelib.RootIsolation.SquareRoot.Replay

open Purelib.Data (Json)
open scoped Purelib.Data.String
open Purelib.Data.Json (toJson)

public section

/-!
Checked, incremental restoration of the unchanged first diameter attempt.
The two preliminary Newton updates and their rounded outputs are saved before
the ordinary six-candidate trace.  Reload checks identities and inequalities;
it never regenerates a completed proposal.  Original source association remains
an explicit proof at the raw-state boundary, not an inference from disk data.
-/

namespace DiameterPreparationCheckpoint

variable {m : Type → Type} [Monad m] [MonadLiftT IO m] [MonadLiftT BaseIO m]
  [MonadExceptOf IO.Error m] [MonadStateOf RootRefinementCheckpoint.Counts m]

open IntegrationCheckpoint RootRefinementCheckpoint
open Purelib.Riemann
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.Branches Purelib.Riemann.Integration Purelib.Riemann.Topology
open CheckedSquareRootPreparation (Coordinate Gaussian GaussianPolynomial Box Owner)

/-- Each recursion checks and retains one of the two canonical warm-up updates without regenerating saved work. -/
@[expose] def warmup (control : Control) (directory : System.FilePath)
    (polynomial : GaussianPolynomial) (box : Box) (epsilon : Coordinate) :
    (steps index : Nat) → (center : Gaussian) →
      m (CheckedSquareRootPreparation.ProposalTrace polynomial box epsilon steps center)
  | 0, _, center => pure ⟨center, [], .done, rfl⟩
  | steps + 1, index, center => do
      let derivative := Data.Gaussian.Basic.value (Evaluation.derivativeEval polynomial center)
      if zero : derivative = 0 then
        return ⟨center, [.stationary center derivative], .stationary rfl zero, by
          rw [CheckedSquareRootPreparation.centeredProposal, if_pos zero]⟩
      else
        let proposed ← loadNewton control directory index polynomial center
        let next ← checkIO directory index "warm-up Newton update"
          (CheckedDiameterReplay.checkNewton polynomial center proposed derivative
            (Evaluation.value_derivativeEval polynomial center) zero)
        let witness ← loadRounding control directory index box epsilon 0 next.val
        let rounded ← checkIO directory index "warm-up rounding" (Input.checkRounded box epsilon 0 next.val witness)
        let tail ← warmup control directory polynomial box epsilon steps (index + 1) rounded.val
        return ⟨tail.seed, .updated center derivative next.val rounded.val :: tail.steps,
          .updated rfl zero next.property rounded.property tail.execution, by
            rw [CheckedSquareRootPreparation.centeredProposal, if_neg zero]
            rw [tail.seed_eq, rounded.property, next.property]⟩

variable {polynomial : GaussianPolynomial} {ambient : Box} {start finish : Gaussian}
  (segment : ClearPath.ClearSegment polynomial ambient start finish) (parameter :
    Coordinate)
  (owner : Owner (polynomial.eval (segment.pointAt parameter))) (diameter : Coordinate)

set_option genInjectivity false in
/-- The checked original diameter proposal, retained finite search trace and typed outcome. -/
structure Replay where
  /-- The original rounded warm-up proposal. -/ proposal : Gaussian
  /-- The retained proposal equals the canonical original diameter-attempt proposal. -/ proposal_eq : proposal =
    CheckedDiameterReplay.initialProposal segment parameter owner diameter
  /-- The exact completed finite search from the retained owner state and proposal. -/ trace : Trace.Finished
    (QuadraticAxisElimination.quadraticAxisElimination _)
    owner.track.initial.raw (CheckedDiameterReplay.epsilon diameter)
    (Owner.quadraticAxisClearances _) proposal
  /-- The certified accepted result or original bounded-search/postcheck failure. -/ outcome : Except
    (CheckedDiameterReplay.Failure segment parameter owner diameter proposal trace)
    (CheckedDiameterReplay.Accepted segment parameter owner diameter)
  /-- The exact checked two-proposal numerical warm-up history and retained seed. -/
  warmup : CheckedSquareRootPreparation.Warmup segment parameter owner diameter
  /-- The exact ordered checked six-search numerical history. -/
  steps : List (Trace.Attempted owner.track.initial.raw (CheckedDiameterReplay.epsilon diameter))
  /-- The retained numerical steps belong to the same original search and selected refinement. -/
  execution : Trace.DataExecution (QuadraticAxisElimination.quadraticAxisElimination _)
    owner.track.initial.raw (CheckedDiameterReplay.epsilon diameter) (Owner.quadraticAxisClearances _)
    6 0 proposal steps trace.value

constructive_injectivity Replay

/-- Equality of replay constructors identifies every retained executable cache and dependent result. -/
theorem Replay.initialData_of_eq {proposal proposal' : Gaussian}
    {proposalEq : proposal = CheckedDiameterReplay.initialProposal segment parameter owner diameter}
    {proposalEq' : proposal' = CheckedDiameterReplay.initialProposal segment parameter owner diameter}
    {trace : Trace.Finished (QuadraticAxisElimination.quadraticAxisElimination _) owner.track.initial.raw
      (CheckedDiameterReplay.epsilon diameter) (Owner.quadraticAxisClearances _) proposal}
    {trace' : Trace.Finished (QuadraticAxisElimination.quadraticAxisElimination _) owner.track.initial.raw
      (CheckedDiameterReplay.epsilon diameter) (Owner.quadraticAxisClearances _) proposal'}
    {outcome : Except (CheckedDiameterReplay.Failure segment parameter owner diameter proposal trace)
      (CheckedDiameterReplay.Accepted segment parameter owner diameter)}
    {outcome' : Except (CheckedDiameterReplay.Failure segment parameter owner diameter proposal' trace')
      (CheckedDiameterReplay.Accepted segment parameter owner diameter)}
    {warmup warmup' : CheckedSquareRootPreparation.Warmup segment parameter owner diameter}
    {steps steps' : List (Trace.Attempted owner.track.initial.raw (CheckedDiameterReplay.epsilon diameter))}
    {execution : Trace.DataExecution (QuadraticAxisElimination.quadraticAxisElimination _)
      owner.track.initial.raw (CheckedDiameterReplay.epsilon diameter) (Owner.quadraticAxisClearances _)
      6 0 proposal steps trace.value}
    {execution' : Trace.DataExecution (QuadraticAxisElimination.quadraticAxisElimination _)
      owner.track.initial.raw (CheckedDiameterReplay.epsilon diameter) (Owner.quadraticAxisClearances _)
      6 0 proposal' steps' trace'.value}
    (equal : Replay.mk proposal proposalEq trace outcome warmup steps execution =
      Replay.mk proposal' proposalEq' trace' outcome' warmup' steps' execution') :
    proposal = proposal' ∧ HEq trace trace' ∧ HEq outcome outcome' := by
  cases equal
  exact ⟨rfl, HEq.rfl, HEq.rfl⟩

/-- Replay constructor equality keeps its original proposal, finished trace and outcome equivalence.

The added certified numerical caches are uniquely determined by their original
inputs, so their retention does not add a new equality obligation. -/
theorem Replay.eq_iff_initialData {proposal proposal' : Gaussian}
    {proposalEq : proposal = CheckedDiameterReplay.initialProposal segment parameter owner diameter}
    {proposalEq' : proposal' = CheckedDiameterReplay.initialProposal segment parameter owner diameter}
    {trace : Trace.Finished (QuadraticAxisElimination.quadraticAxisElimination _) owner.track.initial.raw
      (CheckedDiameterReplay.epsilon diameter) (Owner.quadraticAxisClearances _) proposal}
    {trace' : Trace.Finished (QuadraticAxisElimination.quadraticAxisElimination _) owner.track.initial.raw
      (CheckedDiameterReplay.epsilon diameter) (Owner.quadraticAxisClearances _) proposal'}
    {outcome : Except (CheckedDiameterReplay.Failure segment parameter owner diameter proposal trace)
      (CheckedDiameterReplay.Accepted segment parameter owner diameter)}
    {outcome' : Except (CheckedDiameterReplay.Failure segment parameter owner diameter proposal' trace')
      (CheckedDiameterReplay.Accepted segment parameter owner diameter)}
    {warmup warmup' : CheckedSquareRootPreparation.Warmup segment parameter owner diameter}
    {steps steps' : List (Trace.Attempted owner.track.initial.raw (CheckedDiameterReplay.epsilon diameter))}
    {execution : Trace.DataExecution (QuadraticAxisElimination.quadraticAxisElimination _)
      owner.track.initial.raw (CheckedDiameterReplay.epsilon diameter) (Owner.quadraticAxisClearances _)
      6 0 proposal steps trace.value}
    {execution' : Trace.DataExecution (QuadraticAxisElimination.quadraticAxisElimination _)
      owner.track.initial.raw (CheckedDiameterReplay.epsilon diameter) (Owner.quadraticAxisClearances _)
      6 0 proposal' steps' trace'.value} :
    (Replay.mk proposal proposalEq trace outcome warmup steps execution =
      Replay.mk proposal' proposalEq' trace' outcome' warmup' steps' execution') ↔
      proposal = proposal' ∧ HEq trace trace' ∧ HEq outcome outcome' := by
  constructor
  · exact Replay.initialData_of_eq segment parameter owner diameter
  · intro equal
    cases equal with
    | intro proposalEqual rest =>
        cases proposalEqual
        cases rest with
        | intro traceEqual rest =>
            have sameTrace := eq_of_heq traceEqual
            cases sameTrace
            have sameOutcome := eq_of_heq rest
            cases sameOutcome
            have sameWarmup := CheckedSquareRootPreparation.ProposalTrace.unique warmup warmup'
            cases sameWarmup
            have sameSteps := execution.steps_unique execution'
            cases sameSteps
            rfl

/-- Serialize an actual initial proposal's derivative, exact Newton update and rounding. -/
@[expose] def proposalStepReport : CheckedSquareRootPreparation.ProposalStep → Json
  | .stationary center derivative => Json.mkObj
      [("kind", toJson "zero derivative"), ("center", toJson (gaussianData center)),
       ("derivative", toJson (gaussianData derivative))]
  | .updated center derivative newton rounded => Json.mkObj
      [("kind", toJson "updated"), ("center", toJson (gaussianData center)),
       ("derivative", toJson (gaussianData derivative)), ("newton", toJson (gaussianData newton)),
       ("rounded", toJson (gaussianData rounded))]

/-- Serialize the original failed diameter attempt with its exact trace, window and bounds. -/
@[expose] def failureReport (proposal : Gaussian)
    (trace : Trace.Finished
      (QuadraticAxisElimination.quadraticAxisElimination _)
      owner.track.initial.raw (CheckedDiameterReplay.epsilon diameter)
      (Owner.quadraticAxisClearances _) proposal) :
    CheckedDiameterReplay.Failure segment parameter owner diameter proposal trace → Json
  | .search _ _ => Json.mkObj
      [("kind", toJson "inconclusive: bounded search missed; fallback unresolved"),
       ("trace", finishedReport _ _ _ _ _ trace)]
  | .postcheck _ _ window miss _ => Json.mkObj
      [("kind", toJson (match miss with
          | .diameter _ => "inconclusive: candidate diameter too large"
          | .clearance _ _ => "inconclusive: candidate clearance too small"
          | .ambient _ _ _ => "inconclusive: candidate outside required ambient")),
       ("diameter", toJson (fractionData diameter)),
       ("width", toJson (fractionData window.width)),
       ("requiredFloor", toJson (fractionData window.requiredFloor)),
       ("actualFloor", toJson (fractionData window.actualFloor)),
       ("requiredAmbient", toJson (RootStateCheckpoint.boxData window.requiredAmbient)),
       ("candidate", toJson (RootStateCheckpoint.capture window.value.track.initial)),
       ("trace", finishedReport _ _ _ _ _ trace)]

/-- Replay the two original warm-up updates and bounded diameter search.

Check saved request identity and each numerical witness, then retain the exact canonical outcome without regenerating
completed proposals. -/
@[expose] def run (control : Control) (directory : System.FilePath) :
    m (Replay segment parameter owner diameter) := do
  IO.FS.createDirAll ((Purelib.System.FilePath.join directory (System.FilePath.mk ("warmup"))))
  let rootPolynomial := SquareRootReconditioning.rootPolynomial
    (polynomial.eval (segment.pointAt parameter))
  let box := owner.track.initial.box
  let epsilon := CheckedDiameterReplay.epsilon diameter
  let header := Json.mkObj
    [("format", toJson "ccl-diameter-preparation-v1"),
     ("polynomial", toJson (rootPolynomial.coeffs.map gaussianData)),
     ("box", toJson (RootStateCheckpoint.boxData box)),
     ("diameter", toJson (fractionData diameter)),
     ("epsilon", toJson (fractionData epsilon)),
     ("warmupSteps", toJson (2 : Nat)), ("searchBudget", toJson (6 : Nat))]
  let path := (Purelib.System.FilePath.join directory (System.FilePath.mk ("request.json")))
  if ← path.pathExists then
    let saved : Json ← loadJson path
    unless saved == header do
      saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("invalid-request.json")))) (saved, header)
      throw (IO.userError "diameter request differs from saved inputs; both retained")
  else
    if control.savedOnly then throw (IO.userError "missing diameter request; generation forbidden")
    saveJson path header
  let proposal ← warmup control ((Purelib.System.FilePath.join directory (System.FilePath.mk ("warmup"))))
    rootPolynomial box epsilon 2 0
    ⟨(box.xLower + box.xUpper) / 2, (box.yLower + box.yUpper) / 2⟩
  let trace ← RootRefinementCheckpoint.runFrom
    (QuadraticAxisElimination.quadraticAxisElimination _)
    owner.track.initial.raw epsilon
    (Owner.quadraticAxisClearances _) proposal.seed
    (.direct _ _)
    control ((Purelib.System.FilePath.join directory (System.FilePath.mk ("search"))))
  have proposalEq : proposal.seed = CheckedDiameterReplay.initialProposal segment parameter owner diameter := by
    rw [CheckedDiameterReplay.initialProposal, ← CheckedDiameterReplay.warmup_eq]
    exact proposal.seed_eq
  saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("warmup-retained.json")))) (Json.mkObj
    [("budget", toJson (2 : Nat)), ("seed", toJson (gaussianData proposal.seed)),
     ("steps", toJson (proposal.steps.map proposalStepReport))])
  let outcome := CheckedDiameterReplay.complete segment parameter owner diameter
    proposal.seed trace.finished proposalEq
  match outcome with
  | .ok result => saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("result.json")))) (Json.mkObj
      [("kind", toJson "accepted: exact canonical diameter attempt"),
       ("owner", toJson (RootStateCheckpoint.capture result.result.value.track.initial))])
  | .error failure =>
      saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("result.json"))))
        (failureReport segment parameter owner diameter proposal.seed trace.finished failure)
  return ⟨proposal.seed, proposalEq, trace.finished, outcome, proposal, trace.steps, trace.execution⟩

section RawSource

open Purelib.RootIsolation.SquareRoot.Replay.PreparedSourceReplay (Endpoint Readiness)

variable (current : Endpoint)
  (source : Owner (polynomial.eval (segment.pointAt current.parameter)))
  (request : PreparedSheetContinuation.StepRequest) {rootAmbient : Box}
  (restored : Purelib.RootIsolation.SquareRoot.Replay.PreparedRawStateReplay.Checked _ rootAmbient
    (Purelib.RootIsolation.SquareRoot.Replay.PreparedRawStateReplay.capture source.track.initial))

set_option genInjectivity false in
/-- A retained original readiness, finite-attempt or movement-clearance obstruction. -/
inductive RawFailure where
  /-- The restored representative already satisfies the original readiness request. -/ | alreadyReady
      (data : Readiness segment current request
        (PreparedRawSourceReplay.representative segment current source restored))
      (ready : data.Ready)
  /-- The not-ready representative's retained original diameter attempt failed. -/ | attemptMiss
      (data : Readiness segment current request
        (PreparedRawSourceReplay.representative segment current source restored))
      (notReady : ¬ data.Ready)
      (replay : Replay segment current.parameter
        (PreparedRawSourceReplay.representative segment current source restored) request.rootDiameter)
      (failure : CheckedDiameterReplay.Failure segment current.parameter
        (PreparedRawSourceReplay.representative segment current source restored) request.rootDiameter
        replay.proposal replay.trace)
  /-- The accepted candidate's actual clearance fails to carry the retained movement bound. -/ | doesNotCarry
      (candidate : CheckedDiameterReplay.Accepted segment current.parameter
        (PreparedRawSourceReplay.representative segment current source restored) request.rootDiameter)
      (movement : Coordinate)
      (movement_eq : movement = ClearSheetContinuation.variationBound segment current.parameter
        request.endpoint.parameter)
      (failed : ¬ movement < candidate.result.value.track.initial.clearance.bound)

constructive_injectivity RawFailure

/-- The incoming source is only a proof index. All executable preparation uses the restored representative and checked
disk trace. -/
@[expose] def replayRaw (sameAmbient : rootAmbient = source.ambient)
    (control : Control) (directory : System.FilePath) :
    m (Except (RawFailure segment current source request restored)
      (PreparedSourceReplay.Accepted segment current source request)) := do
  let owner := PreparedRawSourceReplay.representative segment current source restored
  let data := Readiness.capture segment current request owner (PreparedSourceReplay.Inputs.capture segment
    request.rootDiameter)
  if ready : data.Ready then
    return .error (.alreadyReady data ready)
  else
    have notReady : ¬ PreparedSheetContinuation.AlreadyPrepared segment current source request :=
      fun originalReady => ready (data.ready_iff.mpr
        ((PreparedRawSourceReplay.ready_iff segment current source request restored sameAmbient).mpr originalReady))
    let replay ← run segment current.parameter owner request.rootDiameter control directory
    match replay.outcome with
    | .error failure => return .error (.attemptMiss data ready replay failure)
    | .ok candidate =>
        let movement := ClearSheetContinuation.variationBound segment current.parameter request.endpoint.parameter
        if carries : movement < candidate.result.value.track.initial.clearance.bound then
          return .ok
            { cached :=
                { preparedOwner := candidate.result.value
                  preparedOwner_eq := by
                    apply (PreparedRawSourceReplay.prepared_eq_of_attempt_value segment current source request
                      notReady candidate.result.value ?_ carries).symm
                    rw [← PreparedRawSourceReplay.attempt_values_eq segment current source request restored sameAmbient]
                    rw [candidate.equation]
                    rfl }
              movement := movement
              movement_eq := rfl
              clearance := candidate.result.value.track.initial.clearance.bound
              clearance_eq := rfl
              carries := carries }
        else return .error (.doesNotCarry candidate movement rfl carries)

end RawSource

end DiameterPreparationCheckpoint

namespace UniformSampleCheckpoint

variable {m : Type → Type} [Monad m] [MonadLiftT IO m] [MonadLiftT BaseIO m]
  [MonadExceptOf IO.Error m] [MonadStateOf RootRefinementCheckpoint.Counts m]

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open _root_.Purelib.RootIsolation.SquareRoot.Newton.Replay (Trace)
open Purelib.RootIsolation.SquareRoot.Newton.Replay.Input (checkRounded checkInverse)
open Purelib.RootIsolation.SquareRoot.Newton.Search (select)
open Purelib.RootIsolation.SquareRoot.Newton.Replay.Step (advance)

open IntegrationCheckpoint
open Purelib.Riemann
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.Branches Purelib.Riemann.Integration Purelib.Riemann.Topology
open Purelib.CCL.Geometry.CheckedSquareRootNewton
open Replay

/-- Generate the two exact rounded integer coordinates of the uniform sample proposal. -/
@[expose, noinline] def generateRounded (grid : Fraction.Rational) (proposal : Data.Gaussian.Basic.Canonical) :
  Replay.Witness :=
  dbg_trace "UNIFORM_SAMPLE_ROUNDING_GENERATOR_FORCED"
  ⟨Floor.floor (proposal.re / grid + 1 / 2),
    Floor.floor (proposal.im / grid + 1 / 2)⟩

/-- Generate the exact inverse candidate with a diagnostic marker. -/
@[expose, noinline] def generateInverse (point : Data.Gaussian.Basic.Canonical) : Gaussian :=
  dbg_trace "UNIFORM_SAMPLE_INVERSE_GENERATOR_FORCED"
  point⁻¹

/-- Serialize the original rounding or inverse-product invalidity with its actual operands. -/
@[expose] def invalidReport : RootIsolation.SquareRoot.Newton.Replay.Input.Invalid → Json
  | .rounding failure => RootRefinementCheckpoint.invalidReport failure
  | .zeroInverse candidate _ => Json.mkObj
      [("kind", toJson "nonzero proposed inverse of zero"), ("candidate", toJson (gaussianData candidate))]
  | .inverse point candidate _ => Json.mkObj
      [("kind", toJson "inverse product differs from one"), ("point", toJson (gaussianData point)),
       ("candidate", toJson (gaussianData candidate))]

/-- Return checked uniform-sample data or persist the exact failed comparison before stopping. -/
@[expose] def checked {α : Type} (directory : System.FilePath) (result : Except
  RootIsolation.SquareRoot.Newton.Replay.Input.Invalid α) : IO α := do
  match result with
  | .ok value => return value
  | .error failure =>
      saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("invalid.json")))) (invalidReport failure)
      throw (IO.userError "uniform sample witness invalid; exact failed comparison retained")

/-- Restore the original bounded uniform Newton search with its dependent trace.

Each stage validates request identity, rounding and inverse witnesses; saved-only replay preserves the exact proposal
order and completed-work counts. -/
@[expose] def search (parameter : Data.Gaussian.Basic.Canonical) (acceptable : Data.Gaussian.Basic.Canonical → Prop)
  [DecidablePred acceptable]
    (control : RootRefinementCheckpoint.Control) (directory : System.FilePath) :
    (fuel : Nat) → (grid : Fraction.Rational) → (proposal : Data.Gaussian.Basic.Canonical) → m (Trace parameter
      acceptable fuel grid proposal)
  | 0, grid, proposal => return .exhausted grid proposal
  | fuel + 1, grid, proposal => do
      IO.FS.createDirAll directory
      let header := toJson (fuel + 1, fractionData grid, gaussianData proposal, gaussianData parameter)
      let path := (Purelib.System.FilePath.join directory (System.FilePath.mk ("request-v1.json")))
      if ← path.pathExists then
        let expected : Json ← loadJson path
        unless header == expected do
          saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("invalid-request.json")))) (header,
            expected)
          throw (IO.userError "uniform search checkpoint request differs; both operands retained")
      else
        if control.savedOnly then throw (IO.userError "uniform search request missing; generation forbidden")
        saveJson path header
      let path := (Purelib.System.FilePath.join directory (System.FilePath.mk ("rounding-v1.json")))
      let witness ← if ← path.pathExists then do
        let raw : RootRefinementCheckpoint.RawWitness ← loadJson path
        let witness ← IntegrationCheckpoint.checked "uniform sample rounding" (RootRefinementCheckpoint.decode raw)
        RootRefinementCheckpoint.Execution.update fun counts => { counts with reusedRounding := counts.reusedRounding +
          1 }
        pure witness
      else do
        if control.savedOnly then throw (IO.userError "uniform sample rounding missing; generation forbidden")
        let witness := generateRounded grid proposal
        saveJson path (RootRefinementCheckpoint.encode witness)
        RootRefinementCheckpoint.Execution.update fun counts => { counts with generatedRounding :=
          counts.generatedRounding + 1 }
        RootRefinementCheckpoint.afterWrite control
        pure witness
      let point ← checked directory (checkRounded grid proposal witness)
      match selected : select parameter acceptable point.val with
      | some value => return .accepted point value selected
      | none =>
          let path := (Purelib.System.FilePath.join directory (System.FilePath.mk ("inverse-v1.json")))
          let candidate ← if ← path.pathExists then do
            let raw : GaussianData ← loadJson path
            let value ← IntegrationCheckpoint.checked "uniform sample inverse" (decodeGaussian raw)
            RootRefinementCheckpoint.Execution.update fun counts => { counts with reusedNewton := counts.reusedNewton +
              1 }
            pure value
          else do
            if control.savedOnly then throw (IO.userError "uniform sample inverse missing; generation forbidden")
            let value := generateInverse point.val
            saveJson path (gaussianData value)
            RootRefinementCheckpoint.Execution.update fun counts => { counts with generatedNewton :=
              counts.generatedNewton + 1 }
            RootRefinementCheckpoint.afterWrite control
            pure value
          let inverse ← checked directory (checkInverse point.val candidate)
          let tail ← search parameter acceptable control ((Purelib.System.FilePath.join directory (System.FilePath.mk
            ("next")))) fuel (grid / 4)
            (advance parameter point.val inverse)
          return .next point selected inverse tail

/-- Restore one accepted original uniform-preparation sample from its eight-candidate trace.

A finite miss retains the actual source state, target and budget and leaves the original track fallback explicitly
unresolved. -/
@[expose] def restore {polynomial : ClearPath.GaussianPolynomial} {ambient : Rational.Box} {start finish
  : Data.Gaussian.Basic.Canonical}
    (segment : ClearPath.ClearSegment polynomial ambient start finish) (parameter : Fraction.Rational)
    (owner : SquareRootContinuationChain.Owner (polynomial.eval (segment.pointAt parameter))) (diameter :
      Fraction.Rational)
    (control : RootRefinementCheckpoint.Control) (directory : System.FilePath) :
    m (UniformPreparationReplay.Saved segment parameter owner diameter) := do
  let target := UniformSquareRootPreparation.sampleResidualTarget segment owner diameter
  let trace ← search (polynomial.eval (segment.pointAt parameter))
    (UniformSquareRootPreparation.SampleAcceptable segment owner diameter) control directory 8
    (CheckedSquareRootNewton.gridFor target) (UniformSquareRootPreparation.ownerMidpoint owner.track.initial.box)
  match found : trace.result with
  | some accepted =>
    return UniformPreparationReplay.sampleFromTrace segment parameter owner diameter trace accepted found
  | none =>
      saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("inconclusive.json")))) (Json.mkObj
        [("kind", toJson "eight original uniform sample candidates exhausted; track-sample fallback unresolved"),
         ("budget", toJson (8 : Nat)), ("target", toJson (fractionData target)),
         ("source", toJson (RootStateCheckpoint.capture owner.track.initial))])
      throw (IO.userError "uniform sample track fallback requires replay; finite attempts retained")

end UniformSampleCheckpoint
