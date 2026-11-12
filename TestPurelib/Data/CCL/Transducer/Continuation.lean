module

import Purelib.System.IO.Reference

import Purelib.System.IO
-- Reduce Init.Util.dbgTrace only in the native source-call probes, preserving
-- the original logical process equations while marking compiled callbacks.
import all Init.Util
import Init.Data.List.Basic
import Purelib.Data.CCL.Transducer.Machine.Continuation
import Purelib.Data.CCL.Transducer.Machine.Semantics.Step
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Approximation.Gaussian.Process.Route
import Purelib.Approximation.Gaussian.Process.Route.Request
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Approximation.Gaussian.Process.Gamma.Upscale
import Purelib.Approximation.Gaussian.Process.Gamma.Downscale
import Purelib.Approximation.Gaussian.Process.Sector.Residual
import Purelib.Approximation.Gaussian.Process.Observation
import Purelib.Approximation.Gaussian.Observation.Transcript
import Purelib.Data.CCL.Transducer.Emission.Initial
import Purelib.Data.CCL.Transducer.Emission.Initial.Budget
import Purelib.Data.CCL.Transducer.Emission.Low
import Purelib.Data.CCL.Transducer.Emission.Loop
import Purelib.Data.CCL.Transducer.Emission.Residual
import Purelib.Data.CCL.Transducer.Emission.Step
import Purelib.Data.CCL.Transducer.Machine.Preparation
import Purelib.Data.CCL.Transducer.Machine.History
import Purelib.Data.CCL.Progressive.Cursor.Request
import Purelib.Data.CCL.Encoding.Padding.Residual
import Purelib.Data.CCL.Transducer.Mode.Observation
import TestPurelib.Approximation.Gaussian.Observation.Enclosure

open Purelib.Data.CCL.Transducer.Mode.Semantics

/-! # Exact productive cursor phase and queue boundaries -/

namespace TestPurelib.Data.CCL.Transducer.Continuation

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Data.CCL
open Purelib.Data.CCL.Transducer
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Data.CCL.Progressive
open Purelib.Geometry.Projective
open Purelib.Approximation.Gaussian.Observation (Request)
open TestPurelib.Approximation.Gaussian.Observation.Enclosure (looseProcess)
open Purelib.Data.ComplexContinuedFraction.Encoding

/-- Every finite future advance of the actual replacement preserves the original cursor certificate. -/
theorem future_cursor {origin : Process} {originState : origin.State} {machine : Machine}
    (cursor : Machine.Semantics.Basic.ExactCursor origin originState machine) (count : Nat) :
    Machine.Semantics.Basic.ExactCursor origin originState
      (Machine.Advance.advance (Machine.Continuation.ofMachine machine).machine count) :=
  ((Machine.Continuation.ofMachine machine).exactCursor cursor).advance count

/-- Every finite future advance represents the same computed affine reading at its exact singleton origin. -/
theorem future_reading {origin : Process} {originState : origin.State} {machine : Machine}
    (cursor : Machine.Semantics.Basic.ExactCursor origin originState machine) (count : Nat) :
    let result := Machine.Continuation.ofMachine machine
    let reading := result.read cursor
    Machine.Semantics.Basic.ExactCursor (Process.exact reading.value) ()
      (Machine.Advance.advance result.machine count) :=
  ((Machine.Continuation.ofMachine machine).read cursor).exactCursor.advance count

/-- A low mode retaining its original normalization count and strict singleton upper bound. -/
private def low : Mode := .low
  { count := 3
    process := Process.exact 1
    state := ()
    upperBound := by
      intro candidate equal
      change candidate = (1 : Basic.Canonical) at equal
      cases equal
      rewrite [Norm.Basic.normSq_one, ← Nat.cast_ofNat (R := Fraction.Rational) (n := 43),
        ← Nat.cast_ofNat (R := Fraction.Rational) (n := 20)]
      rewrite [Fraction.Cast.natCast_eq_fromInt 43, Fraction.Cast.natCast_eq_fromInt 20]
      decide }

/-- A loop mode with an explicit retained lower quadrance, weight, kind and count. -/
private def loop (kind : Mode.Basic.RegularKind) : Mode := .loop
  { kind := kind
    count := 4
    process := Process.exact 2
    state := ()
    domain :=
      { lowerSq := 2
        weight := 2
        weightPositive := by decide
        coefficient_lt := by decide
        lower := by
          intro _ candidate equal
          change candidate = (2 : Basic.Canonical) at equal
          cases equal
          decide } }

/-- The zero-residual mode retains productive unary padding at its actual finite count. -/
private def zeroResidual : Mode := .residual
  { process := Process.exact 0
    state := ()
    count := 4
    upper := 0
    upperStrict := Encoding.Padding.Residual.paddingTarget_pos 4
    upperBound := by
      intro candidate equal
      change candidate = (0 : Basic.Canonical) at equal
      cases equal
      decide }

/-- A nonzero residual remains in its original homogeneous inverse chart. -/
private def nonzeroResidual : Mode := .residual
  { process := Process.exact (⟨1 / 16, 0⟩ : Basic.Canonical)
    state := ()
    count := 2
    upper := 1 / 256
    upperStrict := by
      unfold Encoding.Padding.Residual.paddingTarget
      rewrite [← Nat.cast_ofNat (R := Fraction.Rational) (n := 256)]
      rewrite [Fraction.Cast.natCast_eq_fromInt 256]
      decide
    upperBound := by
      intro candidate equal
      change candidate = (⟨1 / 16, 0⟩ : Basic.Canonical) at equal
      cases equal
      rewrite [← Nat.cast_ofNat (R := Fraction.Rational) (n := 256),
        ← Nat.cast_ofNat (R := Fraction.Rational) (n := 16)]
      rewrite [Fraction.Cast.natCast_eq_fromInt 256, Fraction.Cast.natCast_eq_fromInt 16]
      decide }

/-- Compare the actual replacement phase, selected tail and exact homogeneous parser coordinates. -/
private def checkMode (original : Mode) : IO Unit := do
  let result := Mode.Exact.ofMode original
  let interpreted := result.code.interpret result.valid
  let decoded := SemanticMode.witness interpreted
  unless decide (decoded.val = result.value) do
    throw (IO.userError "finite mode interpreter changed the original selected rational tail")
  let selected := SemanticMode.witness result.mode
  unless decide (selected.val = result.value) &&
      decide (Mode.Grammar.modeRawPhase result.mode = Mode.Grammar.modeRawPhase original) do
    throw (IO.userError "exact mode changed its original phase or selected rational reading")
  let before := SemanticMode.parserTail original result.value
  let after := SemanticMode.parserTail result.mode result.value
  unless decide (before.p = after.p) && decide (before.q = after.q) do
    throw (IO.userError "exact mode changed its complete homogeneous parser tail")

/-- Compare observable cached data while retaining a certificate for the complete original preparation.

The source payment belongs to the earlier refinement receipt. Only further
calls are charged by the retained emission constructor, including inverse work.
-/
private def checkPrepared {source : Process} (retained original : Emission.Prepared source)
    (paid expected : Nat)
    (same : original = { retained with sourceCalls := paid + retained.sourceCalls }) :
    IO Unit := do
  let completed : { value : Emission.Prepared source // value = original } :=
    ⟨{ retained with sourceCalls := paid + retained.sourceCalls }, same.symm⟩
  unless paid == 3 && retained.sourceCalls == expected &&
      completed.val.sourceCalls == original.sourceCalls &&
      decide (retained.emission.bits = original.emission.bits) &&
      decide (Mode.Grammar.modeRawPhase retained.emission.next = Mode.Grammar.modeRawPhase original.emission.next) &&
      decide (retained.observation.ball.center = original.observation.ball.center) &&
      decide (retained.observation.ball.radiusSq = original.observation.ball.radiusSq) &&
      decide (retained.observation.witness.val = original.observation.witness.val) do
    throw (IO.userError s!"retained refinement changed its original emission, observation or separated payment: \
      paid={paid}, remaining={retained.sourceCalls}, expected={expected}, original={original.sourceCalls}")

/-- Supply one actual original refinement to each mode's retained constructor. -/
private def checkRetainedMode {source : Process} : (mode : Mode) →
    Process.Route source mode.process → Nat → IO Unit
  | .initial current, route, expected =>
      let receipt := route.refine current.state Emission.Initial.Budget.initialRadiusSq
        Emission.Initial.Budget.initialRadiusSq_pos
      checkPrepared (Emission.Initial.fromRefinement current route receipt)
        (Emission.Initial.prepare current route) receipt.sourceCalls expected
        (Emission.Initial.prepare_eq_fromRefinement current route receipt)
  | .low current, route, expected =>
      let receipt := route.refine current.state Emission.Initial.Budget.initialRadiusSq
        Emission.Initial.Budget.initialRadiusSq_pos
      checkPrepared (Emission.Low.fromRefinement current route receipt)
        (Emission.Low.prepare current route) receipt.sourceCalls expected
        (Emission.Low.prepare_eq_fromRefinement current route receipt)
  | .loop current, route, expected =>
      let receipt := route.refine current.state current.domain.decisionTarget current.domain.decisionTarget_pos
      checkPrepared (Emission.Loop.fromRefinement current route receipt)
        (Emission.Loop.prepare current route) receipt.sourceCalls expected
        (Emission.Loop.prepare_eq_fromRefinement current route receipt)
  | .residual current, route, expected =>
      let target := Encoding.Padding.Residual.paddingTarget (current.count + 1)
      have positive := Fraction.Order.Field.div_pos_direct
        (Encoding.Padding.Residual.paddingTarget_pos (current.count + 1))
        (show (0 : Fraction.Rational) < 6 by decide)
      let receipt := route.refine current.state (target / 6) positive
      checkPrepared (Emission.Residual.fromRefinement current route positive receipt)
        (Emission.Residual.prepare current route) receipt.sourceCalls expected
        (Emission.Residual.prepare_eq_fromRefinement current route positive receipt)

/-- Exercise retained refinements through every productive phase and an original routed inverse transition.

The positive-radius source returns a changed numerical state. Exact sources
cover low, both loop kinds and residual padding; the selected-sector route
retains its original parent while the apart branch pays its remaining four calls.
-/
public def retainedRefinements : IO Unit := do
  checkRetainedMode (.initial ⟨Process.exact 0, ()⟩) .input 0
  checkRetainedMode low .input 0
  checkRetainedMode (loop .initialHigh) .input 0
  checkRetainedMode (loop .loop) .input 0
  checkRetainedMode zeroResidual .input 0
  checkRetainedMode nonzeroResidual .input 0
  checkRetainedMode (.initial ⟨looseProcess, Request.ofPositive 1 (by decide)⟩) .input 0
  let current : Mode.Basic.InitialState := ⟨Process.exact ⟨1, 1 / 2⟩, ()⟩
  let route : Process.Route current.process current.process := .input
  let receipt := route.refine current.state Emission.Initial.Budget.initialRadiusSq
    Emission.Initial.Budget.initialRadiusSq_pos
  let first := Emission.Initial.fromRefinement current route receipt
  checkPrepared first (Emission.Initial.prepare current route) receipt.sourceCalls 0
    (Emission.Initial.prepare_eq_fromRefinement current route receipt)
  checkRetainedMode first.emission.next first.route 4
  IO.print "retained cursor refinements: original preparations, observations, routes and separated payments agree\n"

/-- Mark the original source interfaces while preserving their exact logical operations. -/
private def markedSource (source : Process) : Process :=
  { source with
    ball := fun state => Id.run do
      dbg_trace "SOURCE_REQUEST_BALL"
      pure (source.ball state)
    witness := fun state => Id.run do
      dbg_trace "SOURCE_REQUEST_WITNESS"
      pure (source.witness state)
    refine := fun state target positive => Id.run do
      dbg_trace "SOURCE_REQUEST_REFINE"
      pure (source.refine state target positive) }

/-- Flush the boundary before interpreting the original source-call markers. -/
private def sourcePhase (name phase : String) : IO Unit := do
  System.IO.println s!"SOURCE_ROUTE {name} {phase}"
  let output ← IO.getStdout
  output.flush

/-- Compare the original complete numerical observation without invoking any process interface. -/
private def sameObservation {source current : Process} {route : Process.Route source current}
    {before after : current.State} {target : Fraction.Rational} {positive : 0 < target}
    (left : Process.Route.Refinement route before target positive)
    (right : Process.Route.Refinement route after target positive) : Bool :=
  decide (left.observation.ball.center = right.observation.ball.center) &&
    decide (left.observation.ball.radiusSq = right.observation.ball.radiusSq) &&
    decide (left.observation.witness.val = right.observation.witness.val)

/-- Execute fresh and cached original source handlers through one retained chart route.

The source-state view compares the actual returned data with the original pure
refinement. Cached handlers check the complete original state/target key before
transporting their retained receipt. Flushed markers distinguish handler work
from state reconstruction and observation-cache lifting.
-/
private def checkSourceRequest {source current : Process} (name : String)
    (route : Process.Route source current) (before : current.State) (view : source.State → Fraction.Rational)
    (stateEquality : DecidableEq source.State) : IO Unit := do
  let target : Fraction.Rational := 1 / Fraction.Cast.fromInt 64
  have positive : 0 < target :=
    Fraction.Order.Field.div_pos_direct (by decide)
      (show (0 : Fraction.Rational) < Fraction.Cast.fromInt 64 by decide)
  let original := route.refine before target positive
  let expected := view (route.sourceState original.state)
  System.IO.println s!"SOURCE_ROUTE {name} BASELINE_READY {expected.den} {original.observation.ball.radiusSq.den}"
  let storedBefore ← System.IO.mkRef before
  let requests ← System.IO.mkRef ([] : List (Fraction.Rational × Fraction.Rational))
  sourcePhase name "CONSTRUCT_BEGIN"
  let context ← System.IO.Ref.get storedBefore
  let question := route.request context target positive
  System.IO.println s!"SOURCE_ROUTE {name} CONSTRUCT_VALUE {question.sourceTarget.den}"
  sourcePhase name "CONSTRUCT_END"
  let sourceBefore := route.sourceState context
  let expectedRequests := [(view sourceBefore, question.sourceTarget)]
  sourcePhase name "STATE_FRESH_BEGIN"
  let stateBefore ← System.IO.Ref.get storedBefore
  let state ← route.refineStateWith (fun state epsilon certificate => do
    System.IO.Ref.modify requests (fun earlier => earlier ++ [(view state, epsilon)])
    pure ⟨source.refine state epsilon certificate, rfl⟩) stateBefore target positive
  unless decide (view (route.sourceState state.val) = expected) &&
      decide ((← System.IO.Ref.get requests) = expectedRequests) do
    throw (IO.userError "state-only routing changed the original source state, target or handler count")
  sourcePhase name "STATE_FRESH_END"
  sourcePhase name "FULL_FRESH_BEGIN"
  requests.set []
  let fullBefore ← System.IO.Ref.get storedBefore
  let full ← route.refineWith (fun state epsilon certificate => do
    System.IO.Ref.modify requests (fun earlier => earlier ++ [(view state, epsilon)])
    pure ((Process.Route.input : Process.Route source source).refine state epsilon certificate))
    fullBefore target positive
  unless decide (view (route.sourceState full.state) = expected) && sameObservation full original &&
      decide ((← System.IO.Ref.get requests) = expectedRequests) do
    throw (IO.userError "observed routing changed the original state, cache, target or handler count")
  sourcePhase name "FULL_FRESH_END"
  let saved := (Process.Route.input : Process.Route source source).refine sourceBefore
    question.sourceTarget question.sourcePositive
  let storedReply ← System.IO.mkRef saved
  System.IO.println s!"SOURCE_ROUTE {name} CACHE_READY {saved.observation.ball.radiusSq.den} {(view saved.state).den}"
  let cachedHandler (state : source.State) (epsilon : Fraction.Rational) (certificate : 0 < epsilon) :
      IO (Process.Route.Refinement (Process.Route.input : Process.Route source source) state epsilon certificate) := do
    System.IO.Ref.modify requests (fun earlier => earlier ++ [(view state, epsilon)])
    match stateEquality state sourceBefore with
    | .isTrue stateEq =>
      if targetEq : epsilon = question.sourceTarget then
        let retained ← System.IO.Ref.get storedReply
        pure (by cases stateEq; cases targetEq; exact retained)
      else throw (IO.userError "cached source target does not match its retained request")
    | .isFalse _ => throw (IO.userError "cached source input state does not match its retained request")
  sourcePhase name "STATE_CACHED_BEGIN"
  requests.set []
  let cachedBefore ← System.IO.Ref.get storedBefore
  let cachedState ← route.refineStateWith (fun state epsilon certificate => do
    let reply ← cachedHandler state epsilon certificate
    pure ⟨reply.state, reply.stateEq⟩) cachedBefore target positive
  unless decide (view (route.sourceState cachedState.val) = expected) &&
      decide ((← System.IO.Ref.get requests) = expectedRequests) do
    throw (IO.userError "cached state-only routing changed its original request or returned state")
  sourcePhase name "STATE_CACHED_END"
  sourcePhase name "FULL_CACHED_BEGIN"
  requests.set []
  let cachedFullBefore ← System.IO.Ref.get storedBefore
  let cachedFull ← route.refineWith cachedHandler cachedFullBefore target positive
  unless decide (view (route.sourceState cachedFull.state) = expected) && sameObservation cachedFull original &&
      decide ((← System.IO.Ref.get requests) = expectedRequests) do
    throw (IO.userError "cached observed routing changed its original request, state or observation")
  sourcePhase name "FULL_CACHED_END"
  sourcePhase name "FINISH_CACHED_BEGIN"
  let retained ← System.IO.Ref.get storedReply
  let finished := question.finish retained
  unless decide (view (route.sourceState finished.state) = expected) && sameObservation finished original do
    throw (IO.userError "retained source completion changed its original state or observation")
  sourcePhase name "FINISH_CACHED_END"

/-- Detect the original inverse constructor under the actual returned owned chart chain. -/
private def containsInverse {source : Process} : {current : Process} → Process.Route source current → Bool
  | _, .input => false
  | _, .upscale earlier _ _ | _, .downscale earlier _ | _, .residual earlier _ _ => containsInverse earlier
  | _, .inverse _ _ _ _ => true

/-- Check original source requests through every owned chart and the actual residual inverse route.

The positive-radius source retains each requested scalar in its state. The
inverse case uses the original selected-sector transition and its actual next
route, including its apart-state and normalization parents.
-/
public def sourceRefinementRequests : IO Unit := do
  let source := markedSource looseProcess
  let before := Request.ofPositive 1 (by decide)
  let equality : DecidableEq source.State := fun left right => by
    exact if same : left.targetSq = right.targetSq then
      .isTrue (by cases left; cases right; cases same; rfl)
    else .isFalse (fun equal => same (congrArg Request.targetSq equal))
  let view : source.State → Fraction.Rational := fun state => state.targetSq
  checkSourceRequest "input" (.input : Process.Route source source) before view equality
  let up := Process.Gamma.Upscale.upscaledProcess source before 3
  let upBefore := Process.Gamma.Upscale.upscaledInitial source before 3
  let upRoute : Process.Route source up := .upscale (.input : Process.Route source source) before 3
  checkSourceRequest "upscale" upRoute upBefore view equality
  checkSourceRequest "downscale" (.downscale (.input : Process.Route source source) before)
    (Process.Gamma.Downscale.unaryScaledInitial source before) view equality
  let sector := Sector.select (⟨1, 0⟩ : Basic.Canonical)
  checkSourceRequest "residual" (.residual (.input : Process.Route source source) before sector)
    (Process.Sector.Residual.residualInitial source before sector) view equality
  let residual := Process.Sector.Residual.residualProcess up upBefore sector
  let residualBefore := Process.Sector.Residual.residualInitial up upBefore sector
  let residualRoute : Process.Route source residual := .residual upRoute upBefore sector
  checkSourceRequest "composite" (.downscale residualRoute residualBefore)
    (Process.Gamma.Downscale.unaryScaledInitial residual residualBefore) view equality
  let inverseSource := markedSource (Process.exact (⟨1, 1 / 2⟩ : Basic.Canonical))
  let first := Emission.Initial.prepare ⟨inverseSource, ()⟩ .input
  let second := Emission.Step.prepare first.emission.next first.route
  unless containsInverse second.route do
    throw (IO.userError "the original selected-sector fixture did not retain its actual inverse route")
  checkSourceRequest "inverse" second.route second.emission.next.state (fun _ => 0)
    (fun left right => .isTrue (@Subsingleton.elim Unit inferInstance left right))
  IO.print "source refinement requests: all owned charts retained exact requests and single-call handlers\n"

/-- One retained state-only reply keyed by its exact original source state and positive accuracy. -/
private abbrev SavedState (source : Process) :=
  (before : source.State) × (target : { value : Fraction.Rational // 0 < value }) ×
    { state : source.State // state = source.refine before target.val target.property }

/-- One retained complete observation reply keyed by its exact original source state and positive accuracy. -/
private abbrev SavedObservation (source : Process) :=
  (before : source.State) × (target : { value : Fraction.Rational // 0 < value }) ×
    Process.Route.Refinement (.input : Process.Route source source) before target.val target.property

/-- Collect the exact original replies separately for state-only and observed source requests. -/
private def collectingHandlers (source : Process) (states : IO.Ref (List (SavedState source)))
    (observations : IO.Ref (List (SavedObservation source))) :
    Process.Route.StateHandler IO source × Process.Route.Handler IO source :=
  let stateHandler (before : source.State) (target : Fraction.Rational) (positive : 0 < target) :
      IO { state : source.State // state = source.refine before target positive } := do
    let reply := (⟨source.refine before target positive, rfl⟩ :
      { state : source.State // state = source.refine before target positive })
    System.IO.Ref.modify states (fun earlier => earlier ++ [⟨before, ⟨target, positive⟩, reply⟩])
    pure reply
  let handler (before : source.State) (target : Fraction.Rational) (positive : 0 < target) :
      IO (Process.Route.Refinement (.input : Process.Route source source) before target positive) := do
    let reply := (.input : Process.Route source source).refine before target positive
    System.IO.Ref.modify observations (fun earlier => earlier ++ [⟨before, ⟨target, positive⟩, reply⟩])
    pure reply
  (stateHandler, handler)

/-- Consume the saved ordered replies after checking their same original source states and positive targets. -/
private def cachedHandlers (source : Process) (equality : DecidableEq source.State)
    (states : IO.Ref (List (SavedState source))) (observations : IO.Ref (List (SavedObservation source))) :
    Process.Route.StateHandler IO source × Process.Route.Handler IO source :=
  let cachedState (before : source.State) (target : Fraction.Rational) (positive : 0 < target) :
      IO { state : source.State // state = source.refine before target positive } := do
    match ← System.IO.Ref.get states with
    | [] => throw (IO.userError "state-only replay exhausted its exact original reply store")
    | saved :: rest =>
        states.set rest
        match equality before saved.1 with
        | .isFalse _ => throw (IO.userError "state-only replay changed its original source state")
        | .isTrue stateEq =>
            if targetEq : target = saved.2.1.val then
              pure (by cases stateEq; cases targetEq; exact saved.2.2)
            else throw (IO.userError "state-only replay changed its original positive accuracy target")
  let cachedObservation (before : source.State) (target : Fraction.Rational) (positive : 0 < target) :
      IO (Process.Route.Refinement (.input : Process.Route source source) before target positive) := do
    match ← System.IO.Ref.get observations with
    | [] => throw (IO.userError "observed replay exhausted its exact original reply store")
    | saved :: rest =>
        observations.set rest
        match equality before saved.1 with
        | .isFalse _ => throw (IO.userError "observed replay changed its original source state")
        | .isTrue stateEq =>
            if targetEq : target = saved.2.1.val then
              pure (by cases stateEq; cases targetEq; exact saved.2.2)
            else throw (IO.userError "observed replay changed its original positive accuracy target")
  (cachedState, cachedObservation)

/-- Check complete preparation identity and its executable original next-state and observation readbacks. -/
private def checkHandledPreparation {source : Process} (actual original : Emission.Prepared source)
    (equality : DecidableEq source.State) (expected : Nat) (same : actual = original) : IO Unit := do
  let bound : { value : Emission.Prepared source // value = original } := ⟨actual, same⟩
  unless bound.val.sourceCalls == expected && bound.val.sourceCalls == original.sourceCalls &&
      decide (bound.val.emission.bits = original.emission.bits) &&
      decide (Mode.Grammar.modeRawPhase bound.val.emission.next = Mode.Grammar.modeRawPhase original.emission.next) &&
      decide (bound.val.observation.ball.center = original.observation.ball.center) &&
      decide (bound.val.observation.ball.radiusSq = original.observation.ball.radiusSq) &&
      decide (bound.val.observation.witness.val = original.observation.witness.val) do
    throw (IO.userError "handled emission changed its original chunk, phase, observation or paid source work")
  match equality (actual.route.sourceState actual.emission.next.state)
      (original.route.sourceState original.emission.next.state) with
  | .isTrue _ => pure ()
  | .isFalse _ => throw (IO.userError "handled emission changed its actual retained original source state")

/-- Exercise fresh and cached exact handlers through the original emission and empty-queue bit preparation.

Separate reply stores preserve state-only inverse setup. Replay consumes the
same ordered requests and checks both original states and positive targets;
no source callback is available to repair a mismatching cache entry.
-/
private def checkHandledEmission {source : Process} (name : String) (mode : Mode)
    (route : Process.Route source mode.process) (equality : DecidableEq source.State) (expected : Nat) : IO Unit := do
  let original := Emission.Step.prepare mode route
  let machine : Machine := ⟨mode, [], []⟩
  let observation := route.observe mode.state
  let originalBit := Machine.Step.prepare machine route observation
  System.IO.println s!"SOURCE_ROUTE {name} BASELINE_READY {original.emission.bits.length} \
    {original.observation.ball.radiusSq.den} {original.observation.witness.val.re.num} \
    {originalBit.result.2.emitted.length} {originalBit.observation.ball.radiusSq.den}"
  let states ← System.IO.mkRef ([] : List (SavedState source))
  let observations ← System.IO.mkRef ([] : List (SavedObservation source))
  let (stateHandler, handler) := collectingHandlers source states observations
  sourcePhase name "EMISSION_FRESH_BEGIN"
  Emission.Step.withPreparation stateHandler handler mode route fun prepared same =>
    checkHandledPreparation prepared original equality expected same
  sourcePhase name "EMISSION_FRESH_END"
  let savedStates ← System.IO.Ref.get states
  let savedObservations ← System.IO.Ref.get observations
  unless savedStates.length == (if expected == 7 then 1 else 0) &&
      savedObservations.length == (if expected == 7 then 2 else 1) do
    throw (IO.userError "handled emission changed the ordered state-only and observed request counts")
  let (cachedState, cachedObservation) := cachedHandlers source equality states observations
  sourcePhase name "EMISSION_CACHED_BEGIN"
  Emission.Step.withPreparation cachedState cachedObservation mode route fun prepared same =>
    checkHandledPreparation prepared original equality expected same
  unless (← System.IO.Ref.get states).isEmpty && (← System.IO.Ref.get observations).isEmpty do
    throw (IO.userError "emission replay left an original source request unconsumed")
  sourcePhase name "EMISSION_CACHED_END"
  states.set savedStates
  observations.set savedObservations
  sourcePhase name "MACHINE_CACHED_BEGIN"
  Machine.Step.withPreparation cachedState cachedObservation machine route observation fun prepared same => do
    let bound : { value : Machine.Step.Prepared source machine // value = originalBit } := ⟨prepared, same⟩
    unless bound.val.sourceCalls == expected &&
        decide (bound.val.result.1 = originalBit.result.1) &&
        decide (bound.val.result.2.emitted = originalBit.result.2.emitted) &&
        decide (bound.val.result.2.pending = originalBit.result.2.pending) &&
        decide (bound.val.observation.ball.center = originalBit.observation.ball.center) &&
        decide (bound.val.observation.ball.radiusSq = originalBit.observation.ball.radiusSq) &&
        decide (bound.val.observation.witness.val = originalBit.observation.witness.val) do
      throw (IO.userError "handled bit changed its original result, queue, observation or source payment")
  unless (← System.IO.Ref.get states).isEmpty && (← System.IO.Ref.get observations).isEmpty do
    throw (IO.userError "bit replay left an original source request unconsumed")
  sourcePhase name "MACHINE_CACHED_END"

/-- Mark one mode's original process callbacks while preserving its original quantitative data. -/
private def markedMode : Mode → Mode
  | .initial current => .initial { current with process := markedSource current.process }
  | .low current => .low { current with process := markedSource current.process }
  | .loop current => .loop { current with process := markedSource current.process }
  | .residual current => .residual { current with process := markedSource current.process }

/-- Check every original emission phase, exact inverse setup and pending queue through retained source handlers. -/
public def handledEmissions : IO Unit := do
  let unitEquality : DecidableEq Unit := fun left right => .isTrue (Subsingleton.elim left right)
  checkHandledEmission "initial" (markedMode (.initial ⟨Process.exact 0, ()⟩)) .input unitEquality 3
  checkHandledEmission "low" (markedMode low) .input unitEquality 3
  checkHandledEmission "initial-high" (markedMode (loop .initialHigh)) .input unitEquality 3
  checkHandledEmission "loop" (markedMode (loop .loop)) .input unitEquality 3
  checkHandledEmission "zero-residual" (markedMode zeroResidual) .input unitEquality 3
  checkHandledEmission "small-residual" (markedMode nonzeroResidual) .input unitEquality 3
  let loose := markedSource looseProcess
  let equality : DecidableEq loose.State := fun left right =>
    if same : left.targetSq = right.targetSq then .isTrue (by cases left; cases right; cases same; rfl)
    else .isFalse (fun sameState => same (congrArg Request.targetSq sameState))
  checkHandledEmission "positive-radius" (.initial ⟨loose, Request.ofPositive 1 (by decide)⟩) .input equality 3
  let source := markedSource (Process.exact (⟨1, 1 / 2⟩ : Basic.Canonical))
  let first := Emission.Initial.prepare ⟨source, ()⟩ .input
  checkHandledEmission "routed-inverse" first.emission.next first.route unitEquality 7
  let queuedSource := markedSource (Process.exact 0)
  let machine := Machine.initial queuedSource ()
  let initialObservation := (Process.Route.input : Process.Route queuedSource queuedSource).observe ()
  let firstBit := Machine.Step.prepare machine .input initialObservation
  let queued := firstBit.result.2
  unless !queued.pending.isEmpty do
    throw (IO.userError "the original initial-low emission did not retain its real pending queue")
  System.IO.println s!"SOURCE_ROUTE pending BASELINE_READY {queued.pending.length} \
    {firstBit.observation.ball.radiusSq.den} {firstBit.observation.witness.val.re.num}"
  sourcePhase "pending" "QUEUE_BEGIN"
  Machine.Step.withPreparation
    (fun _ _ _ => throw (IO.userError "pending bit invoked the state-only source handler"))
    (fun _ _ _ => throw (IO.userError "pending bit invoked the observed source handler"))
    queued firstBit.route firstBit.observation fun prepared _same => do
      unless prepared.sourceCalls == 0 && prepared.result.2.emitted.length == queued.emitted.length + 1 &&
          prepared.result.2.pending.isEmpty do
        throw (IO.userError "handled pending bit lost its original bit, queue or zero source payment")
  sourcePhase "pending" "QUEUE_END"
  IO.print "handled emissions: original modes, inverse setup, exact cached requests and pending queue agree\n"

/-- Read the exact ordered bit/refinement requests without discarding repeated targets or occurrences. -/
private def actionData (actions : List Machine.Action) : List (Bool × Fraction.Rational) :=
  actions.map fun | .bit => (false, 0) | .refine target _ => (true, target)

/-- Compare every retained chronological cache while consuming complete original history equality. -/
private def checkHandledHistory {initial : Machine.Snapshot} (actual original : Machine.History initial)
    (same : actual = original) : IO Unit := do
  let bound : { value : Machine.History initial // value = original } := ⟨actual, same⟩
  unless decide (actionData bound.val.actions = actionData original.actions) &&
      bound.val.snapshots.length == original.snapshots.length && bound.val.sourceCalls == original.sourceCalls do
    throw (IO.userError "handled history changed its ordered requests, original occurrences or cumulative payment")
  for pair in bound.val.snapshots.zip original.snapshots do
    let left := pair.1
    let right := pair.2
    unless decide (left.machine.emitted = right.machine.emitted) &&
        decide (left.machine.pending = right.machine.pending) && left.sourceCalls == right.sourceCalls &&
        decide (Mode.Grammar.modeRawPhase left.machine.mode = Mode.Grammar.modeRawPhase right.machine.mode) &&
        decide (left.frame.parser = right.frame.parser) &&
        decide (left.frame.normalization = right.frame.normalization) &&
        decide (left.frame.matrix = right.frame.matrix) && decide (left.frame.adjugate = right.frame.adjugate) &&
        decide (left.ball.center = right.ball.center) && decide (left.ball.radiusSq = right.ball.radiusSq) &&
        decide (left.observation.witness.val = right.observation.witness.val) &&
        decide (left.observation.generic.witness = right.observation.generic.witness) &&
        decide (left.observation.generic.spread = right.observation.generic.spread) do
      throw (IO.userError "handled history changed an original word, frame, observation or snapshot payment")

/-- Execute consecutive original counted cylinder requests and their exact saved-source replay.

The second request consumes the first complete history, followed by a zero-bit
accuracy request. Replay checks every original source state and target in
order. The same final cached witness realizes the retained chronological
observations without another source callback.
-/
private def checkHistoryRequests (name : String) (source : Process) (before : source.State)
    (equality : DecidableEq source.State) (expected : Basic.Canonical) (inverse : Bool) : IO Unit := do
  let machine := Machine.initial source before
  let cursor := Machine.Semantics.Basic.ExactCursor.initial source before
  let initial := Machine.Snapshot.ofFrame (Cursor.Image.Machine.Frame.ofMachine machine)
    (Machine.Grammar.initial_invariant source before)
  let history := Machine.History.start initial
  have historySource : history.current.source = source :=
    congrArg Machine.Snapshot.source (Machine.History.start_current initial)
  let quarter : Fraction.Rational := 1 / Fraction.Cast.fromInt 4
  have quarterPositive : 0 < quarter := Fraction.Order.Field.div_pos_direct (by decide) (by decide)
  let sixteenth : Fraction.Rational := 1 / Fraction.Cast.fromInt 16
  have sixteenthPositive : 0 < sixteenth := Fraction.Order.Field.div_pos_direct (by decide) (by decide)
  let originalFirst := history.request 1 (by decide) 3
  let originalSecond := originalFirst.request quarter quarterPositive 4
  let originalThird := originalSecond.request sixteenth sixteenthPositive 0
  System.IO.println s!"SOURCE_ROUTE {name} BASELINE_READY {originalThird.sourceCalls} \
    {originalThird.current.ball.radiusSq.den} {originalThird.current.observation.witness.val.re.num} \
    {originalThird.snapshots.length}"
  let states ← System.IO.mkRef ([] : List (SavedState source))
  let observations ← System.IO.mkRef ([] : List (SavedObservation source))
  let run (stateHandler : Process.Route.StateHandler IO source) (handler : Process.Route.Handler IO source) :
      IO Unit :=
    let answer := Machine.History.withRequest (initial := initial) (α := Unit) stateHandler handler
    answer history historySource 1 (by decide) 3 fun first firstEq firstSource => do
      checkHandledHistory first originalFirst firstEq
      answer first firstSource quarter quarterPositive 4
        fun second secondEq secondSource => do
          have completeSecond : second = originalSecond :=
            secondEq.trans (congrArg (fun value => Machine.History.request value quarter quarterPositive 4) firstEq)
          checkHandledHistory second originalSecond completeSecond
          unless second.current.machine.emitted.length == 7 &&
              decide (second.current.machine.emitted.take 3 = first.current.machine.emitted) do
            throw (IO.userError "consecutive handled requests lost their original three/seven-bit prefix")
          answer second secondSource sixteenth sixteenthPositive 0
            fun third thirdEq _thirdSource => do
              have completeThird : third = originalThird :=
                thirdEq.trans (congrArg (fun value => Machine.History.request value sixteenth sixteenthPositive 0)
                  completeSecond)
              checkHandledHistory third originalThird completeThird
              let survivor := third.survive
              let reading := survivor.read cursor
              unless third.current.machine.emitted.length == 7 && third.actions.length == 10 &&
                  third.snapshots.length == 11 && survivor.realizations.length == 11 &&
                  decide (reading.value = expected) do
                throw (IO.userError "handled request lost its zero-bit accuracy step or common original reading")
              System.IO.println s!"SOURCE_ROUTE {name} PAYMENT {third.sourceCalls - initial.sourceCalls}"
  let (stateHandler, handler) := collectingHandlers source states observations
  sourcePhase name "REQUEST_FRESH_BEGIN"
  run stateHandler handler
  sourcePhase name "REQUEST_FRESH_END"
  if inverse && (← System.IO.Ref.get states).isEmpty then
    throw (IO.userError "the original selected-sector history did not exercise its real inverse setup")
  unless !(← System.IO.Ref.get observations).isEmpty do
    throw (IO.userError "the original history did not retain its real observed refinement requests")
  let (cachedState, cachedObservation) := cachedHandlers source equality states observations
  sourcePhase name "REQUEST_CACHED_BEGIN"
  run cachedState cachedObservation
  unless (← System.IO.Ref.get states).isEmpty && (← System.IO.Ref.get observations).isEmpty do
    throw (IO.userError "history replay left an original ordered source reply unconsumed")
  sourcePhase name "REQUEST_CACHED_END"

/-- Check original persistent bit/cylinder requests through exact handlers and complete chronological cache replay. -/
public def handledHistories : IO Unit := do
  let unitEquality : DecidableEq Unit := fun left right => .isTrue (Subsingleton.elim left right)
  checkHistoryRequests "history-zero" (markedSource (Process.exact 0)) () unitEquality 0 false
  checkHistoryRequests "history-one" (markedSource (Process.exact 1)) () unitEquality 1 false
  checkHistoryRequests "history-two" (markedSource (Process.exact 2)) () unitEquality 2 false
  let selected : Basic.Canonical := ⟨1, 1 / 2⟩
  checkHistoryRequests "history-inverse" (markedSource (Process.exact selected)) () unitEquality selected true
  let source := markedSource looseProcess
  let equality : DecidableEq source.State := fun left right =>
    if same : left.targetSq = right.targetSq then .isTrue (by cases left; cases right; cases same; rfl)
    else .isFalse (fun sameState => same (congrArg Request.targetSq sameState))
  checkHistoryRequests "history-positive-radius" source (Request.ofPositive 1 (by decide)) equality 0 false
  IO.print "handled histories: original persistent requests, all chronological caches and exact source replay agree\n"

/-- Find an actual pending sector queue by bounded traversal of the original exact bit controller. -/
private def queued : Nat → Machine → Except String Machine
  | 0, _ => .error "no sector queue reached within the finite fixture budget"
  | budget + 1, machine =>
      match machine.pending with
      | [] => queued budget (Machine.Step.nextBit machine).2
      | _ :: _ => .ok machine

/-- Check all mode phases, residual-zero infinity, the actual pending queue and further productive growth. -/
public def run : IO Unit := do
  checkMode (.initial ⟨Process.exact 0, ()⟩)
  checkMode low
  checkMode (loop .initialHigh)
  checkMode (loop .loop)
  checkMode zeroResidual
  checkMode nonzeroResidual
  let zero := Mode.Exact.ofMode zeroResidual
  let tail := SemanticMode.parserTail zero.mode zero.value
  unless decide (tail.p = (1 : Basic.Canonical)) && decide (tail.q = (0 : Basic.Canonical)) do
    throw (IO.userError "productive zero residual lost its homogeneous infinity convention")
  match queued 16 (Machine.initial (Process.exact 1) ()) with
  | .error message => throw (IO.userError message)
  | .ok original =>
      let result := Machine.Continuation.ofMachine original
      unless decide (result.machine.emitted = original.emitted) &&
          decide (result.machine.pending = original.pending) do
        throw (IO.userError "cursor replacement changed its exposed prefix or pending sector queue")
      let extended := Machine.Advance.advance result.machine 24
      unless extended.emitted.length == original.emitted.length + 24 &&
          decide (extended.emitted.take original.emitted.length = original.emitted) do
        throw (IO.userError "exact productive continuation did not extend the actual earlier exposed word")
  let origin := Process.exact 1
  let original := Machine.Advance.advance (Machine.initial origin ()) 3
  let cursor := (Machine.Semantics.Basic.ExactCursor.initial origin ()).advance 3
  let result := Machine.Continuation.ofMachine original
  let reading := result.read cursor
  unless decide (reading.value = (1 : Basic.Canonical)) && decide (reading.image.q ≠ 0) do
    throw (IO.userError "computed cursor image did not retain its original affine rational reading")
  let extended := Machine.Advance.advance result.machine 24
  let selected := SemanticMode.witness extended.mode
  let image := Cursor.Image.Machine.image extended selected.val
  unless decide (image.q ≠ 0) && decide (Line.Gaussian.Proj.affineReading image = reading.value) do
    throw (IO.userError "future productive output changed its fixed affine rational reading")
  IO.print "exact productive cursor: six phases, zero residual, pending queue and future growth passed\n"

end TestPurelib.Data.CCL.Transducer.Continuation
