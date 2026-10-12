module
public import Purelib.System.IO
import Purelib.Data.String.Basic
public import Purelib.Data.String.Parsing
public import Purelib.Data.List.ToString
public import Purelib.Data.Int.Decimal
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Task.Parallel
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Integration.Path.Dyadic.DyadicRequestCursor
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Riemann.Readings.BoundedPreparedBanks
import Purelib.Riemann.Readings.BoundedPreparedSource
import Purelib.Riemann.RootContinuation.CoherentRoot
import Purelib.Riemann.RootContinuation.SquareRootOwnerFamily
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Accelerated

import Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration
import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
public import Purelib.Curves.Hyperelliptic.Preparation.Polynomial
public import Purelib.Riemann.Topology.PreparedCycleModels
import Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance
import Purelib.RootIsolation.SquareRoot.Clearance.QuadraticAxisElimination
import Purelib.RootIsolation.SquareRoot.Clearance.QuadraticLineClearance
import Purelib.RootIsolation.SquareRoot.Preparation.Bank.Adaptive
import Init.Core
import Init.Prelude
import Init.System.IO
import Init.System.IOError
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Polynomial.Dense.Gaussian.Squarefree.SquareFactor.Basic
import Purelib.Polynomial.Power.Gaussian
import Purelib.Riemann.RootContinuation.CheckedSquareRootPreparation
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.RootIsolation.SquareRoot.Clearance.QuadraticCoefficientClearance
import Purelib.RootIsolation.Track.Basic

set_option backward.match.sparseCases false

open scoped Purelib.Data.String Purelib.Data.Int.Decimal Purelib.Data.List

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Preparation

open Purelib.Data.Rat

open Purelib.Data.Task

open Purelib.Geometry

open Purelib.Integration.Path.Dyadic

open Purelib.Polynomial.Geometry

open Purelib.Riemann.Branches

open Purelib.Riemann.Paths

open Purelib.Riemann.Readings

open Purelib.Riemann.Readings.BoundedPreparedBanks

open Purelib.Riemann.RootContinuation

open Purelib.RootIsolation.SquareRoot.Clearance

open Purelib.RootIsolation.SquareRoot.Clearance.QuadraticLineClearance

open Purelib.RootIsolation.SquareRoot.Preparation.Bank

open Purelib.RootIsolation.State

open Purelib.RootIsolation.Track

open Purelib.Riemann.Topology

open Purelib.RootIsolation.SquareRoot.Preparation

section
public section

/-!
Shortest-iteration diagnostics for canonical preparation, without numerical
period programs or generated coefficient banks.  Use the same raw repeated-
factor input and computed curve as PolynomialPeriodObservationHarness.
`sequential` times individual pieces; `parallel` uses the production parallel
constructor; `owners` stops after the shared endpoint isolations.  Printed
exact endpoint parameters can be passed to `endpoint` to profile one quadratic
without repeating the cubic branch isolation.  No mode is an observation
acceptance test.  Run under explicit SIGKILL timeout and systemd memory limits.
`endpoint-step` retains that same canonical family, tries the checked first
refinement, then times the original first refinement.  Both start from the
identical initial state; this does not change the production owner or assert
that their later boxes or cached clearances are identical.
`parallel-checked-owners` is a diagnostic alternative: keep each canonical
initial state and use checked shrinking with its original track as fallback.
It tests complete bank preparation before changing any production root API;
it is not the unchanged canonical preparation or an observation acceptance.
`trace` and `trace-checked-owners` evaluate the canonical or diagnostic four
bank selections with individual start/end messages, exposing unfinished pieces.
`first-requests` inspects only each bank's initial
depth-zero request, including the existing finite Newton proposal or up to two
checked moving resets and the coefficient fallback.  It reports whether that bounded branch carries the
edge without entering uniform preparation or recursive moving retries.
It reads the original initial
owners, not their later shrinking strategy.  A miss is not non-certifiability.
`first-depths` scans only the first request at depths zero through 32, stopping
at the first carrying source.  It follows one midpoint chain rather than
allocating exponentially many dyadic requests, and never advances an owner.
`first-advances` then performs exactly that first accepted canonical advance,
with separate transport and retention checkpoints.  It never builds a bank.
`first-steps` traces at most sixteen actual requests at the first carrying
depth, retaining the sequential owner chain.  Its midpoint-prefix generator
does not allocate the untested remainder of a potentially large mesh.
`bank-depths MAX_DEPTH` instead tries complete banks at successive displayed
depths, stopping at the first accepted bank or the explicit depth budget.  It
prints each actual failed attempt's completed segment/edge prefix and retained
obligation without rerunning preparation to explain a miss.  Four workers
share the canonical setup.  This mode has no sufficient-depth fallback and
does not replace the full production preparation or observation acceptance.
-/

namespace CanonicalPeriodPreparationHarness

open _root_.Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients renaming CoefficientPolynomial ->
  GaussianPolynomial
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Branches.PreparedSheetContinuation (Endpoint StepRequest)
open Purelib.Curves.Hyperelliptic.Branches.Cuts
  (connectorAt_start_eval_ne_zero connectorAt_finish_eval_ne_zero)
open Purelib.Integration.Path.Dyadic.DyadicRequestCursor (firstDyadicEndpoint)

/-- Evaluate the retained thunk while emitting its runtime diagnostic message. -/
@[never_extract, extern "lean_dbg_trace", expose] def tracedValue {α : Type u} (message : String) (work : Unit → α) : α
  := work ()

/-- The displayed cubic Gaussian polynomial with its retained trailing-zero representation. -/
@[expose] def polynomial : GaussianPolynomial := ⟨[1, 0, 0, 1, 0, 0]⟩

/-- Print and flush one preparation diagnostic message. -/
@[expose] def report (message : String) : IO Unit := do
  Purelib.System.IO.println message
  (← IO.getStdout).flush

/-- Evaluate a thunk through IO without inlining the timing boundary. -/
@[noinline, expose] def evaluate {α : Type} (work : Unit → α) : IO α := pure (work ())

/-- Time the forced retained computation and print its supplied summary. -/
@[expose] def timed {α : Type u} (label : String) (work : Thunk α) (summarize : α → String) : IO Unit := do
  report s!"starting {label}"
  let start ← IO.monoMsNow
  let summary ← evaluate fun _ => summarize work.get
  report s!"finished {label}: {(← IO.monoMsNow) - start} ms; {summary}"

/-- Force one retained thunk between start and completion markers without changing its result. -/
@[noinline, expose] def traced {α : Type u} (label : String) (work : Thunk α)
    (summarize : α → String) : α :=
  tracedValue s!"START {label}" fun _ =>
    let result := work.get
    tracedValue s!"END {label}: {summarize result}" fun _ => result

/-- Render the exact Gaussian coordinates as numerator/denominator command arguments. -/
@[expose] def parameterText (parameter : Gaussian) : String :=
  s!"{parameter.re.num} {parameter.re.den} {parameter.im.num} {parameter.im.den}"

/-- Render the four exact box bounds as numerator/denominator command arguments. -/
@[expose] def boxArguments (box : Rational.Box) : String :=

    s!"{box.xLower.num} {box.xLower.den} {box.xUpper.num} {box.xUpper.den} {box.yLower.num} {box.yLower.den} \
      {box.yUpper.num} {box.yUpper.den}"

/-- Summarize the original owner's anchor and clearance representation sizes. -/
@[expose] def ownerText {parameter : Gaussian} (owner : Owner parameter) : String :=
  let box := owner.track.initial.box
  let bound := owner.track.initial.clearance.bound

  s!"anchor={parameterText box.anchor}; clearance numerator/denominator \
      bits={bound.num.natAbs.log2 + 1}/{bound.den.log2 + 1}"

/-- Summarize the retained root state's anchor and exact squared diagonal. -/
@[expose] def stateText {polynomial : GaussianPolynomial} {ambient : Rational.Box}
    (state : WindingOne.Basic.WindingOneState polynomial ambient) : String :=
  s!"anchor={parameterText state.box.anchor}; diagonalSq={state.box.diagonalSq.num}/{state.box.diagonalSq.den}"

/-- Summarize the two original independent sheet owners in index order. -/
@[expose] def familyText {parameter : Gaussian} (family : SquareRootOwnerFamily.IndependentFamily parameter) : String :=
  s!"sheet 0 {ownerText (family.owner 0)}; sheet 1 {ownerText (family.owner 1)}"

/-- Accelerate the original track with checked quadratic shrinking while retaining its initial state and fallback. -/
@[expose] def checkedOwner {parameter : Gaussian} (owner : Owner parameter) : Owner parameter where
  parameterNonzero := owner.parameterNonzero
  ambient := owner.ambient
  track := Accelerated.accelerate
    (QuadraticAxisElimination.quadraticAxisElimination parameter) owner.track (Owner.quadraticAxisClearances parameter)

/-- Checked acceleration preserves the original owner's initial box. -/
theorem checkedOwner_initial_box {parameter : Gaussian} (owner : Owner parameter) :
    (checkedOwner owner).track.initial.box = owner.track.initial.box := rfl

/-- Summarize the selected dyadic depth and retained prepared cell count. -/
@[expose] def bankText {polynomial : GaussianPolynomial}
    {task : Bank.Adaptive.Task polynomial} {minimum : Nat}
    (bank : Bank.Adaptive.Selected [task] 1 (by decide) minimum) : String :=
  s!"depth={bank.depth}; cells={bank.banks.head.prepared.stepCount}"

/-- The first original dyadic endpoint request at the supplied depth and unit diameter. -/
@[expose] def firstRequest (depth : Nat) : StepRequest :=
  ⟨firstDyadicEndpoint depth PreparedClearPathModels.zeroEndpoint
    PreparedClearPathModels.oneEndpoint, 1, by decide⟩

/-- The displayed first request is the actual head of the original dyadic request list. -/
theorem firstRequest_eq (depth : Nat) :
    (PreparedSheetContinuation.Subdivision.dyadicRequests depth
      PreparedClearPathModels.zeroEndpoint
      PreparedClearPathModels.oneEndpoint 1 (by decide)).head? =
        some (firstRequest depth) := by
  have attach : ∀ endpoints : List Endpoint,
      (PreparedSheetContinuation.Subdivision.requestsAtDiameter 1 (by decide) endpoints).head? =
        endpoints.head?.map (fun endpoint => (⟨endpoint, 1, by decide⟩ : StepRequest)) := by
    intro endpoints
    cases endpoints <;> rfl
  rw [PreparedSheetContinuation.Subdivision.dyadicRequests, attach, DyadicRequestCursor.firstDyadicEndpoint_eq]
  rfl

/-- Construct only the requested finite prefix of original dyadic endpoint requests. -/
@[expose] def firstRequests (depth count : Nat) : List StepRequest :=
  PreparedSheetContinuation.Subdivision.requestsAtDiameter 1 (by decide)
    (DyadicRequestCursor.firstDyadicEndpoints depth count PreparedClearPathModels.zeroEndpoint
      PreparedClearPathModels.oneEndpoint)

/-- The directly constructed finite request prefix equals the original full list's prefix. -/
theorem firstRequests_eq (depth count : Nat) :
    firstRequests depth count =
      (Purelib.Riemann.Branches.PreparedSheetContinuation.Subdivision.dyadicRequests depth
        PreparedClearPathModels.zeroEndpoint
        PreparedClearPathModels.oneEndpoint 1 (by decide)).take count := by
  have attach : ∀ endpoints : List Endpoint, ∀ count : Nat,
      PreparedSheetContinuation.Subdivision.requestsAtDiameter 1 (by decide)
          (endpoints.take count) =
        (PreparedSheetContinuation.Subdivision.requestsAtDiameter 1 (by decide) endpoints).take count := by
    intro endpoints
    induction endpoints with
    | nil => intro count; cases count <;> rfl
    | cons head tail ih =>
      intro count
      cases count with
      | zero => rfl
      | succ count =>
        simp only [-eq_self, -iff_self, List.take,
          PreparedSheetContinuation.Subdivision.requestsAtDiameter, ih]
        rfl
  unfold firstRequests PreparedSheetContinuation.Subdivision.dyadicRequests
  rw [DyadicRequestCursor.firstDyadicEndpoints_eq, attach]

/-- Split the actual canonical advance only for diagnostic checkpoints. The transported owner is cached and passed
directly to retention. -/
@[expose] def tracedAdvance {polynomial : GaussianPolynomial} {ambient : Rational.Box}
    {start finish : Gaussian} (label : String)
    (segment : ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest)
    (accepted : BoundedPreparedSource.Accepted segment current owner request) :
    Owner (polynomial.eval (segment.pointAt request.endpoint.parameter)) :=
  let transported := traced s!"{label}: first reserved transport" (Thunk.mk fun _ =>
    ExactQuadraticOwnerClearance.reservedTransport accepted.cached.preparedOwner
      (segment.pointAt_eval_ne_zero request.endpoint.parameter request.endpoint.inside)
      ((ClearSheetContinuation.evaluation_variation_le segment within
        current.parameter request.endpoint.parameter current.inside request.endpoint.inside).trans_lt
          accepted.small)
      (PreparedSheetContinuation.transportReserve segment current request)) ownerText
  traced s!"{label}: first endpoint retention" (Thunk.mk fun _ =>
    PreparedSheetContinuation.retainedAtReserve transported
      (PreparedSheetContinuation.preparedClearanceLower segment current request)) ownerText

/-- The traced transport and retention steps equal the original cached canonical advance. -/
theorem tracedAdvance_eq {polynomial : GaussianPolynomial} {ambient : Rational.Box}
    {start finish : Gaussian} (label : String)
    (segment : ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (request : StepRequest)
    (accepted : BoundedPreparedSource.Accepted segment current owner request) :
    tracedAdvance label segment within current owner request accepted =
      PreparedSheetContinuation.advanceCached segment within current owner request
        accepted.cached accepted.small := rfl

/-- Describe the retained moving-proposal absence, readiness failure or carrying failure. -/
@[expose] def moveMissText {polynomial : GaussianPolynomial} {ambient : Rational.Box}
    {start finish : Gaussian} {segment : ClearPath.ClearSegment polynomial ambient start finish}
    {current : Endpoint} {owner : Owner (polynomial.eval (segment.pointAt current.parameter))}
    {request : StepRequest} {variation : PreparedSheetContinuation.Coordinate} :
    BoundedPreparedSource.MoveMiss segment current owner request variation → String
  | .unavailable _ => "moving proposal unavailable"
  | .notReady candidate _ _ => s!"moving proposal not ready; {ownerText candidate.owner}"
  | .notCarrying candidate _ _ _ => s!"moving proposal ready but does not carry; {ownerText candidate.owner}"

/-- Describe the retained second-moving-reset obstruction. -/
@[expose] def laterMissText {polynomial : GaussianPolynomial} {ambient : Rational.Box}
    {start finish : Gaussian} {segment : ClearPath.ClearSegment polynomial ambient start finish}
    {current : Endpoint} {owner : Owner (polynomial.eval (segment.pointAt current.parameter))}
    {request : StepRequest} {variation : PreparedSheetContinuation.Coordinate} :
    BoundedPreparedSource.LaterMiss segment current owner request variation → String
  | .notReady _ => "second move skipped: first owner not ready"
  | .exhausted _ strengthened _ _ moving =>
      s!"first-reset strengthening misses: {ownerText strengthened}; second: {moveMissText moving}"

/-- Describe the retained coefficient-refresh readiness or carrying obstruction. -/
@[expose] def movedCoefficientMissText {polynomial : GaussianPolynomial} {ambient : Rational.Box}
    {start finish : Gaussian} {segment : ClearPath.ClearSegment polynomial ambient start finish}
    {current : Endpoint} {owner : Owner (polynomial.eval (segment.pointAt current.parameter))}
    {request : StepRequest} {variation : PreparedSheetContinuation.Coordinate} :
    BoundedPreparedSource.MovedCoefficientMiss segment current owner request variation → String
  | .notReady _ => "first-reset coefficient refresh skipped: owner not ready"
  | .notCarrying _ value _ _ => s!"first-reset coefficient bound misses: {ownerText value}"

/-- Describe a finite source-preparation miss and its exact replayable numerical request. -/
@[expose] def sourceMissText {polynomial : GaussianPolynomial} {ambient : Rational.Box}
    {start finish : Gaussian} {segment : ClearPath.ClearSegment polynomial ambient start finish}
    {current : Endpoint} {owner : Owner (polynomial.eval (segment.pointAt current.parameter))}
    {request : StepRequest}
    (report : BoundedPreparedSource.Inconclusive segment current owner request) : String :=
  let reason := match report.reason with
    | .strengthened _ _ _ _ _ coefficient _ _ moving later movedCoefficient =>

          s!"inherited, direct and coefficient bounds miss; first: {moveMissText moving}; {laterMissText later}; \
            coefficient: {ownerText coefficient}; {movedCoefficientMissText movedCoefficient}"
    | .proposalUnavailable _ _ diagnostic =>
        let stopped := match diagnostic.reason with
          | .search .. => "bounded search unavailable"
          | .candidate _ _ _ miss => match miss with
              | .diameter _ => "candidate diameter fails"
              | .clearance _ _ => "diameter passes; predicted clearance fails"
              | .ambient _ _ _ => "diameter and clearance pass; ambient containment fails"
        s!"{stopped}; retained warmup={diagnostic.warmup.steps.length}/2; search={diagnostic.steps.length}/6"
    | .proposalMiss .. => "bounded diameter proposal does not carry"
  let parameter := polynomial.eval (segment.pointAt report.endpoint.parameter)
  let replay :=
    s!".lake/build/bin/moving_reset_harness reset {parameterText parameter} \
      {boxArguments report.source.track.initial.box} {report.variation.num} {report.variation.den}"
  s!"{reason}; moving budget={report.movingBudget}; no diagnostic replacement owner was used\nRESET-REPLAY {replay}"

/-- Locate the failed edge within the retained request prefix and report its actual obstruction. -/
@[expose] def stepFailureText {polynomial : GaussianPolynomial} {ambient : Rational.Box}
    {start finish : Gaussian} {segment : ClearPath.ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {current : Endpoint} {owner : Owner (polynomial.eval (segment.pointAt current.parameter))}
    {requests : List StepRequest} (index : Nat)
    (failure : BoundedPreparedBanks.StepFailure segment within current owner requests) : String :=
  StepFailure.casesOn
    (motive := fun _ _ _ _ => Nat → String) failure
    (fun current _ request _ _ index =>

        s!"edge={index}; unordered parameters {current.parameter.num}/{current.parameter.den} -> \
          {request.endpoint.parameter.num}/{request.endpoint.parameter.den}")
    (fun current owner request _ _ failure index =>

        s!"edge={index}; parameters {current.parameter.num}/{current.parameter.den} -> \
          {request.endpoint.parameter.num}/{request.endpoint.parameter.den}; {ownerText owner}; \
          {sourceMissText failure}")
    (fun _ _ _ _ _ _ _ rest index => stepFailureText (index + 1) rest) index
termination_by structural failure

/-- Locate the failed segment within the retained prepared-path prefix. -/
@[expose] def pathFailureText {polynomial : GaussianPolynomial} {ambient : Rational.Box}
    {depth : Nat} {diameter : PreparedSheetContinuation.Coordinate}
    {positive : 0 < diameter}
    {start finish : Gaussian} {path : ClearPath polynomial ambient start finish}
    {within : path.WithinAmbient} {owner : Owner (polynomial.eval start)} (index : Nat)
    (failure : BoundedPreparedBanks.PathFailure depth diameter positive path within owner) : String :=
  PathFailure.casesOn
    (motive := fun {_ _} _ _ _ _ => Nat → String) failure
    (fun _ _ _ _ failure index => s!"segment={index}; {stepFailureText 0 failure}")
    (fun _ _ _ _ _ _ rest index => pathFailureText (index + 1) rest) index
termination_by structural failure

/-- Each displayed result is the original bounded bank checker on the full path, with the actual accepted or failed
prefix retained by that checker. -/
@[expose] def bankDepthsText {polynomial : GaussianPolynomial} {ambient : Rational.Box}
    {start finish : Gaussian} (label : String) (maximumDepth : Nat)
    (path : ClearPath polynomial ambient start finish)
    (within : path.WithinAmbient) (owner : Owner (polynomial.eval start)) : String :=
  let rec scan : Nat → Nat → String
    | depth, 0 => s!"{depth} complete-bank attempts exhausted; no sufficient-depth fallback was requested"
    | depth, remaining + 1 =>
        tracedValue s!"START {label}: full bank depth={depth}; cells per segment={2 ^ depth}" fun _ =>
          have positive : (0 : PreparedSheetContinuation.Coordinate) < 1 := by decide
          let outcome : Except
              (BoundedPreparedBanks.Inconclusive depth 1 positive path within owner)
              (BoundedPreparedBanks.PathSuccess depth 1 positive path within owner) :=
            BoundedPreparedBanks.attempt depth 1 positive path within owner
          match outcome with
          | .error failure =>
              tracedValue
                s!"END {label}: full bank depth={depth}; certified inconclusive: {pathFailureText 0 failure.failure}"
                fun _ =>
                scan (depth + 1) remaining
          | .ok accepted =>
              let summary := s!"complete bounded bank accepted at depth={depth}; cells={accepted.prepared.stepCount}"
              tracedValue s!"END {label}: {summary}" fun _ => summary
  scan 0 (maximumDepth + 1)

/-- Diagnostic traversal of the actual finite request prefix. Every successful edge uses the shared certified source and
the exact canonical advance above. Stopping at a miss or the prefix limit is not a bank result. -/
@[expose] def tracePrefix {polynomial : GaussianPolynomial} {ambient : Rational.Box}
    {start finish : Gaussian} (label : String)
    (segment : ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) (current : Endpoint)
    (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
    (index : Nat) : List StepRequest → String
  | [] => s!"tested prefix completed after {index} edges; no complete bank was requested"
  | request :: remaining =>
      tracedValue s!"{label}: edge {index} bounded source; {ownerText owner}" fun _ =>
        match BoundedPreparedSource.check segment current owner request with
        | .error report =>
            s!"stopped at edge {index}: {sourceMissText report}"
        | .ok accepted =>
            let next := tracedAdvance s!"{label}: edge {index}" segment within current owner request accepted
            tracePrefix label segment within request.endpoint next (index + 1) remaining

/-- Search the first request at up to thirty-three dyadic depths and optionally trace the retained accepted prefix.

The diagnostic preserves the original sequential owner chain and reports only its explicitly bounded work. -/
@[expose] def firstDepthText {polynomial : GaussianPolynomial} {ambient : Rational.Box}
    (label : String) (advanceFirst traceSteps : Bool) : {start finish : Gaussian} →
      (path : ClearPath polynomial ambient start finish) →
      path.WithinAmbient → Owner (polynomial.eval start) → String
  | _, _, .nil _, _, _ => "empty path; no first request"
  | _, _, .cons head _, within, initialOwner =>
      let owner := PreparedClearPathModels.ownerAtStart head initialOwner
      let left := PreparedClearPathModels.zeroEndpoint
      let rec scan : Nat → Nat → String
        | depth, 0 => s!"no carrying first source in the {depth} tested depths; no continuation was attempted"
        | depth, remaining + 1 =>
            tracedValue s!"{label}: first-source depth {depth}" fun _ =>
              match BoundedPreparedSource.check head left owner (firstRequest depth) with
              | .ok accepted =>
                  let summary :=
                    s!"first carrying source at depth={depth}; full mesh would have {2 ^ depth} cells per segment"
                  if traceSteps then
                    tracedValue s!"{label}: {summary}" fun _ =>
                      let result := tracePrefix label head within.head left owner 0 (firstRequests depth 16)
                      s!"{summary}; {result}"
                  else if advanceFirst then
                    tracedValue s!"{label}: {summary}" fun _ =>
                      let next := tracedAdvance label head within.head left owner (firstRequest depth) accepted
                      s!"{summary}; first canonical advance completed: {ownerText next}; no bank was constructed"
                  else s!"{summary}; no continuation was attempted"
              | .error _ => scan (depth + 1) remaining
      scan 0 33

/-- Report the depth-zero original request's exact bounded source-preparation outcome. -/
@[expose] def firstRequestText {polynomial : GaussianPolynomial} {ambient : Rational.Box}
    (label : String) : {start finish : Gaussian} →
      ClearPath polynomial ambient start finish →
      Owner (polynomial.eval start) → String
  | _, _, .nil _, _ => "empty path; no request"
  | _, _, .cons head _, initialOwner =>
      let owner := PreparedClearPathModels.ownerAtStart head initialOwner
      let left := PreparedClearPathModels.zeroEndpoint
      let request := firstRequest 0
      tracedValue s!"{label}: checking bounded source preparation" fun _ =>
        match BoundedPreparedSource.check head left owner request with
        | .ok _ => "bounded source preparation carries the depth-zero edge"
        | .error report =>
            let variation := s!"{report.variation.num}/{report.variation.den}"
            match report.reason with
            | .strengthened _ _ candidate _ _ coefficient _ _ moving later movedCoefficient =>
                let inherited := report.source.track.initial.clearance.bound
                let strengthened := candidate.track.initial.clearance.bound
                let coefficientBound := coefficient.track.initial.clearance.bound

                s!"ready owner and same-box strengthening miss: variation={variation}; \
                    inherited={inherited.num}/{inherited.den}; direct={strengthened.num}/{strengthened.den}; \
                    coefficient={coefficientBound.num}/{coefficientBound.den}; first: {moveMissText moving}; \
                    {laterMissText later}; {movedCoefficientMissText movedCoefficient}; moving \
                    budget={report.movingBudget}"
            | .proposalUnavailable _ _ _ =>
                s!"finite Newton proposal returned no accepted owner; unresolved variation={variation}"
            | .proposalMiss _ candidate _ _ =>
                let clearance := candidate.value.track.initial.clearance.bound
                s!"finite Newton proposal misses: variation={variation}; clearance={clearance.num}/{clearance.den}"

/-- Inspect canonical branch and endpoint preparation using the selected finite diagnostic mode.

Retain shared original owners and caches, distinguish checked-owner alternatives, and report only the bank or prefix
actually evaluated. -/
@[expose] def prepared (mode : String) {source : GaussianPolynomial}
    (input : Polynomial.Prepared source) (cycle : Fin input.genus)
    (maximumDepth : Nat := 16) : IO Unit := do
  let curve := input.curve
  let branchesCache := Thunk.mk fun _ => BranchIsolation.data curve
  timed "canonical cubic branch isolation" branchesCache fun branches =>

      s!"sites={branches.siteCount}; \
        anchors={List.ofFn fun index : Fin branches.siteCount => parameterText (branches.anchorAt index)}"
  let branches := branchesCache.get
  let higher := BranchCutLifts.degreeGtOne_of_cycleIndex curve cycle
  let geometry := (BranchConfiguration.configurationOfData curve branches).branches
  let left := BranchConfiguration.basisPairLeftIndexOfData curve branches cycle
  let right := BranchConfiguration.basisPairRightIndexOfData curve branches cycle
  let leftStateCache := Thunk.mk fun _ => Cuts.refinedState geometry higher left 0
  let rightStateCache := Thunk.mk fun _ => Cuts.refinedState geometry higher right 0
  let connectorCache := Thunk.mk fun _ => Cuts.connectorAt geometry higher left right 0
  timed "left branch state" leftStateCache fun state => s!"anchor={parameterText state.box.anchor}"
  timed "right branch state" rightStateCache fun state => s!"anchor={parameterText state.box.anchor}"
  timed "canonical connector" connectorCache fun path => s!"segments={path.segmentCount}"
  let leftState := leftStateCache.get
  let rightState := rightStateCache.get
  let connector := connectorCache.get
  let within := Cuts.connectorAt_withinAmbient geometry higher left right 0
  let leftNonzero := Cuts.connectorAt_start_eval_ne_zero geometry higher left right 0
  let rightNonzero := Cuts.connectorAt_finish_eval_ne_zero geometry higher left right 0
  report s!"left endpoint command: endpoint {parameterText (curve.polynomial.eval leftState.box.anchor)}"
  report s!"right endpoint command: endpoint {parameterText (curve.polynomial.eval rightState.box.anchor)}"
  let leftFamily := Thunk.mk fun _ => SquareRootOwnerFamily.independentFamily leftNonzero
  let rightFamily := Thunk.mk fun _ => SquareRootOwnerFamily.independentFamily rightNonzero
  if mode == "sequential" then
    timed "left shared two-sheet isolation" leftFamily familyText
    timed "right shared two-sheet isolation" rightFamily familyText
  let families := Thunk.mk fun _ => Parallel.two
    (fun _ => leftFamily.get) (fun _ => rightFamily.get)
  timed "joined endpoint families" families fun pair => s!"left: {familyText pair.1}; right: {familyText pair.2}"
  if mode == "owners" then return
  let useChecked := mode == "parallel-checked-owners" || mode == "trace-checked-owners"
  if useChecked then
    report "Diagnostic checked-owner variant: canonical initial states unchanged; later refinements may differ."
  let configure := fun {parameter : Gaussian} (owner : Owner parameter) =>
    if useChecked then checkedOwner owner else owner
  let forwardOwner := configure (families.get.1.owner 0)
  let rightOwner := configure (families.get.2.owner 0)
  let backwardOwner := configure (families.get.2.owner 1)
  let leftOwner := configure (families.get.1.owner 1)
  if mode == "bank-depths" then
    let rightPath := BranchCutLifts.ownerBoundaryPath rightState
    let leftPath := BranchCutLifts.ownerBoundaryPath leftState
    let attempts := Thunk.mk fun _ => Parallel.four
      (fun _ => bankDepthsText "forward" maximumDepth connector within forwardOwner)
      (fun _ => bankDepthsText "right" maximumDepth rightPath
        (BranchCutLifts.ownerBoundaryPath_withinAmbient rightState) rightOwner)
      (fun _ => bankDepthsText "backward" maximumDepth
        (BranchCutLifts.ClearPath.reverse connector)
        (BranchCutLifts.ClearPath.reverse_withinAmbient connector within) backwardOwner)
      (fun _ => bankDepthsText "left" maximumDepth leftPath
        (BranchCutLifts.ownerBoundaryPath_withinAmbient leftState) leftOwner)
    timed s!"four complete-bank depth scans through {maximumDepth}" attempts fun result =>
      s!"forward: {result.1}; right: {result.2.1}; backward: {result.2.2.1}; left: {result.2.2.2}"
  else if mode == "first-requests" || mode == "first-depths" || mode == "first-advances" || mode == "first-steps" then
    let rightPath := BranchCutLifts.ownerBoundaryPath rightState
    let leftPath := BranchCutLifts.ownerBoundaryPath leftState
    if mode == "first-depths" || mode == "first-advances" || mode == "first-steps" then
      let advanceFirst := mode == "first-advances"
      let traceSteps := mode == "first-steps"
      let first := Thunk.mk fun _ => Parallel.four
        (fun _ => firstDepthText "forward" advanceFirst traceSteps connector within forwardOwner)
        (fun _ => firstDepthText "right" advanceFirst traceSteps rightPath
          (BranchCutLifts.ownerBoundaryPath_withinAmbient rightState) rightOwner)
        (fun _ => firstDepthText "backward" advanceFirst traceSteps
          (BranchCutLifts.ClearPath.reverse connector)
          (BranchCutLifts.ClearPath.reverse_withinAmbient connector within) backwardOwner)
        (fun _ => firstDepthText "left" advanceFirst traceSteps leftPath
          (BranchCutLifts.ownerBoundaryPath_withinAmbient leftState) leftOwner)
      timed (if traceSteps then "four bounded canonical request prefixes (no bank)"
        else if advanceFirst then "four first-source scans and canonical advances (no bank)"
        else "four first-source depth scans (no continuation)") first fun result =>
        s!"forward: {result.1}; right: {result.2.1}; backward: {result.2.2.1}; left: {result.2.2.2}"
    else
      let first := Thunk.mk fun _ => Parallel.four
        (fun _ => firstRequestText "forward" connector forwardOwner)
        (fun _ => firstRequestText "right" rightPath rightOwner)
        (fun _ => firstRequestText "backward"
          (BranchCutLifts.ClearPath.reverse connector) backwardOwner)
        (fun _ => firstRequestText "left" leftPath leftOwner)
      timed "four first-request diagnostics (no uniform fallback)" first fun result =>
        s!"forward: {result.1}; right: {result.2.1}; backward: {result.2.2.1}; left: {result.2.2.2}"
  else if mode == "sequential" || mode == "trace" || mode == "trace-checked-owners" then
    let forward := Thunk.mk fun _ => Bank.Adaptive.select
      [Bank.Adaptive.Task.ofPath connector within forwardOwner] 1 (by decide)
    let rightPath := BranchCutLifts.ownerBoundaryPath rightState
    let rightBank := Thunk.mk fun _ => Bank.Adaptive.select
      [Bank.Adaptive.Task.ofPath rightPath
        (BranchCutLifts.ownerBoundaryPath_withinAmbient rightState) rightOwner] 1 (by decide)
    let backward := Thunk.mk fun _ => Bank.Adaptive.select
      [Bank.Adaptive.Task.ofPath (BranchCutLifts.ClearPath.reverse connector)
        (BranchCutLifts.ClearPath.reverse_withinAmbient connector within) backwardOwner] 1 (by decide)
    let leftPath := BranchCutLifts.ownerBoundaryPath leftState
    let leftBank := Thunk.mk fun _ => Bank.Adaptive.select
      [Bank.Adaptive.Task.ofPath leftPath
        (BranchCutLifts.ownerBoundaryPath_withinAmbient leftState) leftOwner] 1 (by decide)
    if mode == "sequential" then
      timed "forward bank" forward bankText
      timed "right boundary bank" rightBank bankText
      timed "backward bank" backward bankText
      timed "left boundary bank" leftBank bankText
    else
      let all := Thunk.mk fun _ => Parallel.four
        (fun _ => traced "forward bank" forward bankText)
        (fun _ => traced "right boundary bank" rightBank bankText)
        (fun _ => traced "backward bank" backward bankText)
        (fun _ => traced "left boundary bank" leftBank bankText)
      timed (if useChecked then "four traced diagnostic banks" else "four traced canonical banks") all fun result =>

          s!"forward {bankText result.1}; right {bankText result.2.1}; backward {bankText result.2.2.1}; left \
            {bankText result.2.2.2}"
  else
    let banks := Thunk.mk fun _ => PreparedCycleModels.PreparedBoundaryDoublePath.total
      leftState rightState connector within forwardOwner rightOwner backwardOwner leftOwner 1 (by decide)
    timed (if useChecked then "four parallel banks with diagnostic checked owners"
      else "four production parallel banks") banks fun result =>

        s!"depths={result.forwardDepth},{result.rightBoundaryDepth},{result.backwardDepth},{result.leftBoundaryDepth}; \
          cells={result.forwardChecked.prepared.stepCount},{result.rightBoundaryChecked.prepared.stepCount},\
          {result.backwardChecked.prepared.stepCount},{result.leftBoundaryChecked.prepared.stepCount}"
  report "Preparation diagnostics complete; no period observation or replay has been evaluated."

/-- Prepare the displayed polynomial and run the requested diagnostic on its first existing cycle. -/
@[expose] def run (mode : String) (maximumDepth : Nat := 16) : IO Unit := do
  match Polynomial.prepare polynomial with
  | .regular _ input =>
      if valid : 0 < input.genus then
        report s!"computed genus={input.genus}; normalized standard differential dx/z"
        prepared mode input ⟨0, valid⟩ maximumDepth
      else throw (IO.userError "computed curve has no standard cycle")
  | _ => throw (IO.userError "raw repeated-factor input did not produce a regular curve")

/-- Parse an exact nonzero parameter and inspect its original two-sheet owner family.

Optional first-step comparison starts both refiners from the identical initial owner and checks containment and target
accuracy. -/
@[expose] def endpoint (reNum reDen imNum imDen : String) (compareStep : Bool := false)
    (sheet : Fin 2 := 0) : IO Unit := do
  let some rn := Purelib.Data.String.toInt? reNum | throw (IO.userError "invalid real numerator")
  let some rd := Purelib.Data.String.toNat? reDen | throw (IO.userError "invalid real denominator")
  let some inum := Purelib.Data.String.toInt? imNum | throw (IO.userError "invalid imaginary numerator")
  let some iden := Purelib.Data.String.toNat? imDen | throw (IO.userError "invalid imaginary denominator")
  unless 0 < rd ∧ 0 < iden do throw (IO.userError "denominators must be positive")
  let parameter : Gaussian :=
    ⟨Fraction.Cast.fromInt rn / Fraction.Cast.fromInt rd,
      Fraction.Cast.fromInt inum / Fraction.Cast.fromInt iden⟩
  if nonzero : parameter ≠ 0 then
    let family := Thunk.mk fun _ => SquareRootOwnerFamily.independentFamily nonzero
    timed s!"endpoint {parameterText parameter}" family familyText
    if compareStep then
      let owner := family.get.owner sheet
      let target := CoherentRoot.stepTarget owner.track 0
      report s!"first refinement: sheet={sheet.val}; target={target.num}/{target.den}"
      let checked := Accelerated.accelerate
        (QuadraticAxisElimination.quadraticAxisElimination parameter) owner.track (Owner.quadraticAxisClearances
          parameter)
      let checkedState := Thunk.mk fun _ => CoherentRoot.state checked 1
      timed "checked first refinement, same initial owner" checkedState stateText
      unless decide (checkedState.get.box.StrictInterior owner.track.initial.box ∧
          checkedState.get.box.diagonalSq ≤ target ^ 2) do
        throw (IO.userError "checked first refinement lost containment or requested accuracy")
      let originalState := Thunk.mk fun _ => CoherentRoot.state owner.track 1
      timed "original first refinement" originalState stateText
      unless decide (originalState.get.box.StrictInterior owner.track.initial.box ∧
          originalState.get.box.diagonalSq ≤ target ^ 2) do
        throw (IO.userError "original first refinement lost containment or requested accuracy")
      report "First-refinement diagnostics complete; no period preparation or observation was substituted."
  else throw (IO.userError "zero parameter has no two distinct square-root owners")

end CanonicalPeriodPreparationHarness

/-- Parse the requested canonical preparation, endpoint or bounded-depth diagnostic mode. -/
@[expose] def main (arguments : List String) : IO Unit := do
  match arguments with
  | ["bank-depths", maximumText] =>
      let some maximum := Purelib.Data.String.toNat? maximumText | throw (IO.userError
        "maximum depth must be a natural number")
      CanonicalPeriodPreparationHarness.run "bank-depths" maximum
  | ["endpoint", rn, rd, inum, iden] => CanonicalPeriodPreparationHarness.endpoint rn rd inum iden
  | ["endpoint-step", sheetText, rn, rd, inum, iden] =>
      let some sheet := Purelib.Data.String.toNat? sheetText | throw (IO.userError "sheet must be 0 or 1")
      if valid : sheet < 2 then CanonicalPeriodPreparationHarness.endpoint rn rd inum iden true ⟨sheet, valid⟩
      else throw (IO.userError "sheet must be 0 or 1")
  | [mode] =>
      if mode == "sequential" || mode == "parallel" || mode == "trace" || mode == "owners" ||
          mode == "parallel-checked-owners" || mode == "trace-checked-owners" ||
          mode == "first-requests" || mode == "first-depths" || mode == "first-advances" || mode == "first-steps" then
        CanonicalPeriodPreparationHarness.run mode
      else throw (IO.userError "unknown preparation diagnostic mode")
  | _ => throw (IO.userError
    "usage: canonical_period_preparation_harness sequential|parallel|trace|owners|parallel-checked-owners|\
      trace-checked-owners|first-requests|first-depths|first-advances|first-steps | bank-depths MAX_DEPTH | endpoint \
      RE_NUM RE_DEN IM_NUM IM_DEN | endpoint-step SHEET RE_NUM RE_DEN IM_NUM IM_DEN")

end
