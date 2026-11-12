module

public import Purelib.Data.CCL.Transducer.Machine.Transition
public import Purelib.Data.CCL.Transducer.Machine.Code
public import Purelib.Data.CCL.Transducer.Mode.Observation
public import Purelib.Data.CCL.Transducer.Machine.Preparation
import Purelib.Data.CCL.Progressive.Cursor.Refinement
import Purelib.Data.CCL.Transducer.Machine.Grammar.Step
public import Purelib.Data.CCL.Progressive.Cursor.Request
import Purelib.Data.List.Append
import Purelib.Data.List.Map
import Purelib.Data.List.Membership
import Purelib.Approximation.Gaussian.Process.Route.Request

open Purelib.Data.CCL.Transducer.Mode.Semantics

/-!
# Finite chronological histories of retained productive cursors

Every checkpoint keeps its actual machine, image-frame caches, numerical
ball and grammar certificate. The ordered elementary actions bind those
checkpoints to the original executed state sequence. Semantic transports
relate every earlier checkpoint to the actual current one.
-/

public section

namespace Purelib.Data.CCL.Transducer.Machine

open Purelib.Data.CCL.Progressive.Cursor

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Data.CCL.Transducer
open Purelib.Data.CCL.Progressive
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Projective

set_option genInjectivity false in
/-- An actual cursor checkpoint retaining its original machine, caches and numerical tail enclosure. -/
structure Snapshot where
  /-- The original quantitative mode, emitted word and pending queue at this checkpoint. -/ machine : Machine
  /-- The exact retained parser and chart caches of that same machine. -/ frame : Image.Machine.Frame machine
  /-- The original supplied process boundary retained through its owned chart changes. -/ source : Process
  /-- The exact original route from that boundary to this mode's nominal process. -/ route :
    Process.Route source machine.mode.process
  /-- The original retained mode observation, including its actual ball and possible witness. -/ observation :
    Mode.Observation machine.mode
  /-- Original supplied-source interface calls from actual setup and preceding cursor work. -/
  sourceCalls : Nat
  /-- The actual numerical tail ball read once at the same retained mode state. -/ ball : Enclosure.Ball
  /-- The numerical ball is the same retained observation readback. -/ observationBall : observation.ball = ball
  /-- The cached ball is the original mode's actual enclosure. -/ ballEq :
    ball = Cursor.Refinement.Mode.ball machine.mode
  /-- The original committed word has the exact current mode phase. -/ grammar : Grammar.Invariant machine

namespace Snapshot

/-- Cache the actual ball and possible witness of an already retained original cursor frame. -/
@[expose] def ofFrame {machine : Machine} (frame : Image.Machine.Frame machine)
    (grammar : Grammar.Invariant machine) : Snapshot :=
  let observation := Mode.Observation.build machine.mode
  let ball := observation.ball
  ⟨machine, frame, machine.mode.process, .input, observation, 2, ball, rfl,
    observation.ballEq.trans (Cursor.Refinement.Mode.process_ball machine.mode), grammar⟩

/-- Fresh frame observation pays exactly the two actual original ball and witness calls. -/
theorem ofFrame_sourceCalls {machine : Machine} (frame : Image.Machine.Frame machine)
    (grammar : Grammar.Invariant machine) : (ofFrame frame grammar).sourceCalls = 2 := rfl

/-- Reuse the exact cached observation across a new frame whose original mode is unchanged.

The same retained ball and witness are transported to the original new machine.
No process refinement, ball read or witness read is performed.
-/
@[expose] def withFrame (snapshot : Snapshot) (machine : Machine)
    (modeEq : machine.mode = snapshot.machine.mode) (frame : Image.Machine.Frame machine)
    (grammar : Grammar.Invariant machine) : Snapshot :=
  let observation : Mode.Observation machine.mode := modeEq.symm ▸ snapshot.observation
  let observationBall :=
    (Mode.Observation.transport_ball snapshot.machine.mode machine.mode modeEq snapshot.observation).trans
      snapshot.observationBall
  ⟨machine, frame, snapshot.source, (congrArg Mode.process modeEq).symm ▸ snapshot.route,
    observation, snapshot.sourceCalls, snapshot.ball, observationBall,
    snapshot.ballEq.trans (congrArg Cursor.Refinement.Mode.ball modeEq).symm, grammar⟩

/-- Retain the exact next observation and source route already prepared by the original bit transition.

The frame receipt consumes the same actual complete result. This constructor
transports the prepared cache without source refinement, ball or witness calls.
-/
@[expose] def ofStep (snapshot : Snapshot) (prepared : Step.Prepared snapshot.source snapshot.machine)
    (receipt : Image.Machine.Frame.Step snapshot.frame) (same : receipt.result = prepared.result)
    (grammar : Grammar.Invariant receipt.result.2) : Snapshot :=
  let modeEq := congrArg (fun result : Bool × Machine => result.2.mode) same
  let observation : Mode.Observation receipt.result.2.mode := modeEq.symm ▸ prepared.observation
  let route : Process.Route snapshot.source receipt.result.2.mode.process :=
    (congrArg Mode.process modeEq).symm ▸ prepared.route
  let ball := observation.ball
  ⟨receipt.result.2, receipt.after, snapshot.source, route, observation,
    snapshot.sourceCalls + prepared.sourceCalls, ball, rfl,
    observation.ballEq.trans (Cursor.Refinement.Mode.process_ball receipt.result.2.mode), grammar⟩

/-- Transport the original source route to the same retained refined machine's process. -/
@[expose] def refinementRoute (snapshot : Snapshot) (target : Fraction.Rational) (positive : 0 < target)
    (receipt : Image.Machine.Frame.Refinement snapshot.frame target positive) :
    Process.Route snapshot.source receipt.machine.mode.process :=
  let processEq := (congrArg (fun machine : Machine => machine.mode.process) receipt.machineEq).trans
    (Cursor.Refinement.Mode.refine_process snapshot.machine.mode target positive)
  processEq.symm ▸ snapshot.route

/-- Retain an original refined frame and its same already supplied numerical observation.

The source route, ball, witness and image-frame caches belong to this exact
returned machine. Construction makes no source callback and retains the
earlier refinement's original three-call payment.
-/
@[expose] def ofRefinementWithObservation (snapshot : Snapshot) (target : Fraction.Rational) (positive : 0 < target)
    (receipt : Image.Machine.Frame.Refinement snapshot.frame target positive)
    (observation : Mode.Observation receipt.machine.mode) (grammar : Grammar.Invariant receipt.machine) : Snapshot :=
  let ball := observation.ball
  ⟨receipt.machine, receipt.after, snapshot.source, snapshot.refinementRoute target positive receipt,
    observation, snapshot.sourceCalls + (snapshot.route.calls + snapshot.route.observeSourceCalls), ball, rfl,
    observation.ballEq.trans (Cursor.Refinement.Mode.process_ball receipt.machine.mode), grammar⟩

/-- Observe one already retained original refinement through the same source route once.

The frame receipt has already computed the actual refined state. Its exact
state is observed directly, without repeating refinement or any owned chart's
ball or witness callback. The cached chart factors remain with that receipt.
-/
@[expose] def ofRefinement (snapshot : Snapshot) (target : Fraction.Rational) (positive : 0 < target)
    (receipt : Image.Machine.Frame.Refinement snapshot.frame target positive)
    (grammar : Grammar.Invariant receipt.machine) : Snapshot :=
  let route := snapshot.refinementRoute target positive receipt
  let observation := route.observe receipt.machine.mode.state
  snapshot.ofRefinementWithObservation target positive receipt observation grammar

/-- Read the same cached original possible witness without calling the source again. -/
@[expose] def witness (snapshot : Snapshot) :
    { value : Basic.Canonical // SemanticMode.possible snapshot.machine.mode value } :=
  snapshot.observation.candidate

/-- The cached witness is exactly the original mode's selected process witness. -/
theorem witness_eq (snapshot : Snapshot) :
    snapshot.witness = SemanticMode.witness snapshot.machine.mode := snapshot.observation.candidate_eq

/-- Every possible tail at the original mode lies in the exact cached numerical ball. -/
theorem possible_inside (snapshot : Snapshot) {value : Basic.Canonical}
    (possible : SemanticMode.possible snapshot.machine.mode value) : snapshot.ball.Contains value :=
  snapshot.ballEq.symm ▸ Cursor.Refinement.Mode.possible_inside snapshot.machine.mode possible

end Snapshot

set_option genInjectivity false in
/-- One finite elementary cursor action with its actual positive refinement target when present. -/
inductive Action where
  /-- Return one actual pending or newly emitted bit. -/ | bit
  /-- Refine the same current mode at the displayed positive squared-radius target. -/ | refine
      (target : Fraction.Rational) (positive : 0 < target)

namespace Action

/-- Apply one elementary action to the original retained machine. -/
@[expose] def apply (action : Action) (machine : Machine) : Machine :=
  match action with
  | .bit => (Step.nextBit machine).2
  | .refine target positive => Refinement.Machine.refine machine target positive

/-- Execute an ordered finite action path from the original machine. -/
@[expose] def run : Machine → List Action → Machine
  | machine, [] => machine
  | machine, action :: rest => run (action.apply machine) rest

/-- Retain every actual machine on the same finite action path, including both endpoints. -/
@[expose] def states : Machine → List Action → List Machine
  | machine, [] => [machine]
  | machine, action :: rest => machine :: states (action.apply machine) rest

/-- An appended finite action path continues from the actual earlier final machine. -/
theorem run_append (machine : Machine) (earlier later : List Action) :
    run machine (earlier ++ later) = run (run machine earlier) later := by
  induction earlier generalizing machine with
  | nil => rfl
  | cons action rest induction => exact induction _

/-- Appending one action adds exactly its actual resulting machine to the retained state sequence. -/
theorem states_append_single (machine : Machine) (actions : List Action) (action : Action) :
    states machine (actions ++ [action]) = states machine actions ++ [action.apply (run machine actions)] := by
  induction actions generalizing machine with
  | nil => rfl
  | cons head rest induction => exact congrArg (List.cons machine) (induction _)

/-- Each elementary action preserves the original Gaussian source and dependent origin state of an exact cursor. -/
theorem exactCursor {origin : Process} {originState : origin.State} {machine : Machine}
    (action : Action) (cursor : Semantics.Basic.ExactCursor origin originState machine) :
    Semantics.Basic.ExactCursor origin originState (action.apply machine) := by
  cases action with
  | bit => exact cursor.nextBit
  | refine target positive => exact Cursor.Request.ExactCursor.refine cursor target positive

/-- The actual finite action path preserves exact cursor semantics relative to the same original source state. -/
theorem run_exactCursor {origin : Process} {originState : origin.State} {machine : Machine}
    (cursor : Semantics.Basic.ExactCursor origin originState machine) (actions : List Action) :
    Semantics.Basic.ExactCursor origin originState (run machine actions) := by
  induction actions generalizing machine with
  | nil => exact cursor
  | cons action rest induction => exact induction (action.exactCursor cursor)

end Action

set_option genInjectivity false in
/-- A chronological cursor history binds all original cached snapshots to their exact executed action path. -/
structure History (initial : Snapshot) where
  /-- The actual current cached checkpoint. -/ current : Snapshot
  /-- All elementary actions in their original execution order. -/ actions : List Action
  /-- The current machine is the actual result of those same actions. -/ currentEq :
    current.machine = Action.run initial.machine actions
  /-- The actual original checkpoints in order, including both endpoints. -/ snapshots : List Snapshot
  /-- The same actual current checkpoint is retained among those original occurrences. -/ currentMember :
    current ∈ snapshots
  /-- Every retained machine is exactly its occurrence in the original executed state sequence. -/ statesEq :
    snapshots.map Snapshot.machine = Action.states initial.machine actions
  /-- Every earlier checkpoint transports possible tails from the same actual current checkpoint. -/ compatible :
    ∀ snapshot ∈ snapshots, Transition snapshot.frame current.frame

namespace History

/-- Read the cumulative original supplied-source calls retained by the actual current checkpoint.

The count includes its original observation setup and all preceding paid
cursor actions. Starting a history at an existing snapshot preserves that
snapshot's total and performs no source callback.
-/
@[expose] def sourceCalls {initial : Snapshot} (history : History initial) : Nat := history.current.sourceCalls

/-- Begin a chronological history at its actual original cached checkpoint. -/
def start (initial : Snapshot) : History initial :=
  { current := initial
    actions := []
    currentEq := rfl
    snapshots := [initial]
    currentMember := List.Mem.head []
    statesEq := rfl
    compatible := by
      intro snapshot member
      have equal := Data.List.Membership.mem_singleton.mp member
      cases equal
      exact ⟨fun possible => ⟨_, possible, Line.Proj.Equivalent.refl _⟩⟩ }

/-- Append an actual certified action and preserve all earlier cached checkpoints and transports. -/
def extend {initial : Snapshot} (history : History initial) (action : Action) (next : Snapshot)
    (machineEq : next.machine = action.apply history.current.machine)
    (transition : Transition history.current.frame next.frame) : History initial := by
  have currentEq : next.machine = Action.run initial.machine (history.actions ++ [action]) := by
    rewrite [Action.run_append]
    exact machineEq.trans (congrArg action.apply history.currentEq)
  have statesEq : (history.snapshots ++ [next]).map Snapshot.machine =
      Action.states initial.machine (history.actions ++ [action]) := by
    rewrite [Data.List.Map.map_append]
    change history.snapshots.map Snapshot.machine ++ [next.machine] = _
    rewrite [history.statesEq, Action.states_append_single]
    exact congrArg (List.append (Action.states initial.machine history.actions))
      (congrArg (fun machine => [machine]) (machineEq.trans (congrArg action.apply history.currentEq)))
  exact
    { current := next
      actions := history.actions ++ [action]
      currentEq := currentEq
      snapshots := history.snapshots ++ [next]
      currentMember := Data.List.Membership.mem_append.mpr (Or.inr (List.Mem.head []))
      statesEq := statesEq
      compatible := by
        intro snapshot member
        cases Data.List.Membership.mem_append.mp member with
        | inl earlier => exact (history.compatible snapshot earlier).compose transition
        | inr final =>
            have equal := Data.List.Membership.mem_singleton.mp final
            cases equal
            exact ⟨fun possible => ⟨_, possible, Line.Proj.Equivalent.refl _⟩⟩ }

/-- The start constructor retains the exact original checkpoint and empty action path. -/
private theorem start_specification (initial : Snapshot) :
    (start initial).current = initial ∧ (start initial).actions = [] := ⟨rfl, rfl⟩

/-- The starting history's current checkpoint is the original supplied cached snapshot. -/
theorem start_current (initial : Snapshot) : (start initial).current = initial := (start_specification initial).1

/-- A newly started history has the exact empty action path. -/
theorem start_actions (initial : Snapshot) : (start initial).actions = [] := (start_specification initial).2

/-- Extend the original history using one already retained complete bit preparation.

The actual bit result supplies its frame once. Its original next observation,
route and payment are retained; no source step or observation is repeated.
-/
def ofStep {initial : Snapshot} (history : History initial)
    (prepared : Step.Prepared history.current.source history.current.machine) : History initial :=
  let receipt := history.current.frame.ofResult prepared.result prepared.resultEq
  let grammar := (congrArg Prod.snd receipt.resultEq).symm ▸
    Grammar.Step.nextBit_invariant history.current.machine history.current.grammar
  let next := Snapshot.ofStep history.current prepared receipt
    (history.current.frame.ofResult_result prepared.result prepared.resultEq) grammar
  history.extend .bit next (congrArg Prod.snd receipt.resultEq)
    (Transition.ofStep receipt history.current.grammar)

/-- Extend the history by one original cached next-bit receipt and its actual numerical checkpoint. -/
def nextBit {initial : Snapshot} (history : History initial) : History initial :=
  history.ofStep (Step.prepare history.current.machine history.current.route history.current.observation)

/-- A complete original bit preparation reconstructs the complete original chronological extension. -/
theorem ofStep_eq_nextBit {initial : Snapshot} (history : History initial)
    (prepared : Step.Prepared history.current.source history.current.machine)
    (same : prepared = Step.prepare history.current.machine history.current.route history.current.observation) :
    history.ofStep prepared = history.nextBit := by
  cases same
  rfl

/-- Extend the original history from its retained refined frame and same cached numerical observation. -/
def ofFrameRefinement {initial : Snapshot} (history : History initial)
    (target : Fraction.Rational) (positive : 0 < target)
    (receipt : Image.Machine.Frame.Refinement history.current.frame target positive)
    (observation : Mode.Observation receipt.machine.mode) : History initial :=
  let grammar := receipt.machineEq.symm ▸
    Refinement.Machine.refine_grammar history.current.machine target positive history.current.grammar
  let next := Snapshot.ofRefinementWithObservation history.current target positive receipt observation grammar
  history.extend (.refine target positive) next receipt.machineEq (Transition.ofRefinement receipt)

/-- Extend the history by one original cached refinement receipt with the same earlier chart data. -/
def refine {initial : Snapshot} (history : History initial) (target : Fraction.Rational) (positive : 0 < target) :
    History initial :=
  let receipt := history.current.frame.refine target positive
  let route := history.current.refinementRoute target positive receipt
  history.ofFrameRefinement target positive receipt (route.observe receipt.machine.mode.state)

/-- A retained original frame and observation reconstruct the complete original chronological refinement. -/
theorem ofFrameRefinement_eq_refine {initial : Snapshot} (history : History initial)
    (target : Fraction.Rational) (positive : 0 < target)
    (receipt : Image.Machine.Frame.Refinement history.current.frame target positive)
    (observation : Mode.Observation receipt.machine.mode)
    (same : receipt = history.current.frame.refine target positive) :
    history.ofFrameRefinement target positive receipt observation = history.refine target positive := by
  cases same
  have observedEq : observation =
      (history.current.refinementRoute target positive (history.current.frame.refine target positive)).observe
        (history.current.frame.refine target positive).machine.mode.state :=
    Process.Observation.unique _ _
  cases observedEq
  rfl

/-- Reconstruct the complete original history refinement from its exact returned process state and observation.

The mode constructor consumes that state, the frame transports its original
caches, and the snapshot consumes the supplied observation. The source refiner,
ball and witness are not called while assembling this same original history.
-/
def ofRefinement {initial : Snapshot} (history : History initial)
    (target : Fraction.Rational) (positive : 0 < target)
    (reply : Process.Route.Refinement history.current.route history.current.machine.mode.state target positive) :
    { value : History initial // value = history.refine target positive } :=
  let retained := (⟨reply.state, reply.stateEq⟩ : { state : history.current.machine.mode.process.State //
    state = history.current.machine.mode.process.refine history.current.machine.mode.state target positive })
  let machine := Refinement.Machine.fromState history.current.machine target positive retained
  have machineEq := Refinement.Machine.fromState_eq history.current.machine target positive retained
  let receipt := history.current.frame.ofRefinement target positive machine machineEq
  have returnedEq : receipt.machine = machine := receipt.machineEq.trans machineEq.symm
  let observation : Mode.Observation receipt.machine.mode :=
    (congrArg Machine.mode returnedEq).symm ▸
      Cursor.Refinement.Mode.observationFromState history.current.machine.mode target positive retained
        reply.observation
  let value := history.ofFrameRefinement target positive receipt observation
  ⟨value, history.ofFrameRefinement_eq_refine target positive receipt observation
    (history.current.frame.ofRefinement_eq target positive machine machineEq)⟩

/-- A bit extension retains its original source process owner. -/
theorem nextBit_source {initial : Snapshot} (history : History initial) :
    history.nextBit.current.source = history.current.source := (rfl)

/-- A numerical history refinement retains its original source process owner. -/
theorem refine_source {initial : Snapshot} (history : History initial)
    (target : Fraction.Rational) (positive : 0 < target) :
    (history.refine target positive).current.source = history.current.source := (rfl)

/-- Execute one original bit action through exact source handlers and retain its complete chronological extension. -/
def withNextBit {m : Type → Type} [Monad m] {α : Type} {initial : Snapshot} (history : History initial)
    (stateHandler : Process.Route.StateHandler m history.current.source)
    (handler : Process.Route.Handler m history.current.source)
    (use : (next : History initial) → next = history.nextBit → m α) : m α :=
  Step.withPreparation stateHandler handler history.current.machine history.current.route history.current.observation
    fun prepared same => use (history.ofStep prepared) (history.ofStep_eq_nextBit prepared same)

/-- Execute one original numerical action through its exact source handler and retain the same complete history. -/
def withRefinement {m : Type → Type} [Monad m] {α : Type} {initial : Snapshot} (history : History initial)
    (handler : Process.Route.Handler m history.current.source)
    (target : Fraction.Rational) (positive : 0 < target)
    (use : (next : History initial) → next = history.refine target positive → m α) : m α := do
  let reply ← history.current.route.refineWith handler history.current.machine.mode.state target positive
  let next := history.ofRefinement target positive reply
  use next.val next.property

/-- The starting history retains its original snapshot's exact paid-call field. -/
private theorem start_sourceCalls_specification (initial : Snapshot) :
    (start initial).sourceCalls = initial.sourceCalls := rfl

/-- Starting a new chronological view preserves all work already retained by its exact snapshot. -/
theorem start_sourceCalls (initial : Snapshot) : (start initial).sourceCalls = initial.sourceCalls :=
  start_sourceCalls_specification initial

/-- The actual bit constructor adds its same retained preparation payment. -/
private theorem nextBit_sourceCalls_specification {initial : Snapshot} (history : History initial) :
    history.nextBit.sourceCalls = history.sourceCalls +
      (Step.prepare history.current.machine history.current.route history.current.observation).sourceCalls := rfl

/-- One bit action adds the actual retained preparation payment, including zero for a queued bit. -/
theorem nextBit_sourceCalls {initial : Snapshot} (history : History initial) :
    history.nextBit.sourceCalls = history.sourceCalls +
      (Step.prepare history.current.machine history.current.route history.current.observation).sourceCalls :=
  nextBit_sourceCalls_specification history

/-- A bit action never removes previously paid original source work. -/
theorem nextBit_sourceCalls_mono {initial : Snapshot} (history : History initial) :
    history.sourceCalls ≤ history.nextBit.sourceCalls := by
  rewrite [nextBit_sourceCalls]
  exact Nat.le_add_right _ _

/-- Every bit action adds at most the seven actual calls of an inverse transition. -/
theorem nextBit_sourceCalls_le {initial : Snapshot} (history : History initial) :
    history.nextBit.sourceCalls ≤ history.sourceCalls + 7 := by
  rewrite [nextBit_sourceCalls]
  apply Nat.add_le_add_left
  rcases Step.prepare_sourceCalls history.current.machine history.current.route history.current.observation with
    zero | three | seven
  · rewrite [zero]; decide
  · rewrite [three]; decide
  · rewrite [seven]; exact Nat.le_refl _

/-- An actual numerical refinement adds one original source refinement, ball read and witness read. -/
theorem refine_sourceCalls {initial : Snapshot} (history : History initial)
    (target : Fraction.Rational) (positive : 0 < target) :
    (history.refine target positive).sourceCalls = history.sourceCalls + 3 := by
  change history.sourceCalls + (history.current.route.calls + history.current.route.observeSourceCalls) = _
  rewrite [history.current.route.calls_eq_one, history.current.route.observeSourceCalls_eq]
  rfl

/-- A numerical refinement preserves all previously paid original source work. -/
theorem refine_sourceCalls_mono {initial : Snapshot} (history : History initial)
    (target : Fraction.Rational) (positive : 0 < target) :
    history.sourceCalls ≤ (history.refine target positive).sourceCalls := by
  rewrite [refine_sourceCalls]
  exact Nat.le_add_right _ _

/-- Execute a finite numerical action list by consuming each actual current cached checkpoint once. -/
def execute {initial : Snapshot} : History initial → List Action → History initial
  | history, [] => history
  | history, .bit :: rest => execute history.nextBit rest
  | history, .refine target positive :: rest => execute (history.refine target positive) rest

/-- The actual next-bit builder appends exactly one bit action to the earlier path. -/
private theorem nextBit_actions_specification {initial : Snapshot} (history : History initial) :
    history.nextBit.actions = history.actions ++ [.bit] := rfl

/-- The actual refinement builder appends its exact retained positive target to the earlier path. -/
private theorem refine_actions_specification {initial : Snapshot} (history : History initial)
    (target : Fraction.Rational) (positive : 0 < target) :
    (history.refine target positive).actions = history.actions ++ [.refine target positive] := rfl

/-- The original earlier snapshot occurrence survives one actual bit extension. -/
private theorem nextBit_earlier_specification {initial : Snapshot} (history : History initial)
    (snapshot : Snapshot) (member : snapshot ∈ history.snapshots) : snapshot ∈ history.nextBit.snapshots :=
  Data.List.Membership.mem_append.mpr (Or.inl member)

/-- The original earlier snapshot occurrence survives one actual refinement. -/
private theorem refine_earlier_specification {initial : Snapshot} (history : History initial)
    (target : Fraction.Rational) (positive : 0 < target)
    (snapshot : Snapshot) (member : snapshot ∈ history.snapshots) :
    snapshot ∈ (history.refine target positive).snapshots :=
  Data.List.Membership.mem_append.mpr (Or.inl member)

/-- The same earlier cached snapshot remains in the actual refined history. -/
theorem refine_earlier {initial : Snapshot} (history : History initial)
    (target : Fraction.Rational) (positive : 0 < target)
    (snapshot : Snapshot) (member : snapshot ∈ history.snapshots) :
    snapshot ∈ (history.refine target positive).snapshots :=
  refine_earlier_specification history target positive snapshot member

/-- The actual bit builder's current machine is the original same next-bit result. -/
private theorem nextBit_machine_specification {initial : Snapshot} (history : History initial) :
    history.nextBit.current.machine = (Step.nextBit history.current.machine).2 :=
  let prepared := Step.prepare history.current.machine history.current.route history.current.observation
  congrArg Prod.snd (history.current.frame.ofResult prepared.result prepared.resultEq).resultEq

/-- The actual refinement builder preserves both words and chart and meets its exact positive target. -/
private theorem refine_specification {initial : Snapshot} (history : History initial)
    (target : Fraction.Rational) (positive : 0 < target) :
    let next := history.refine target positive
    next.current.machine = Refinement.Machine.refine history.current.machine target positive ∧
      next.current.machine.emitted = history.current.machine.emitted ∧
      next.current.machine.pending = history.current.machine.pending ∧
      next.current.frame.matrix = history.current.frame.matrix ∧ next.current.ball.radiusSq < target := by
  let receipt := history.current.frame.refine target positive
  have accurate : (Cursor.Refinement.Mode.ball receipt.machine.mode).radiusSq < target := by
    rewrite [receipt.machineEq]
    exact Cursor.Refinement.Mode.refine_ball_radiusSq_lt history.current.machine.mode target positive
  exact ⟨receipt.machineEq,
    (congrArg emitted receipt.machineEq).trans
      (Refinement.Machine.refine_emitted history.current.machine target positive),
    (congrArg pending receipt.machineEq).trans
      (Refinement.Machine.refine_pending history.current.machine target positive), receipt.matrixEq,
    (history.refine target positive).current.ballEq.symm ▸ accurate⟩

/-- The refined history retains the complete original machine refinement result. -/
theorem refine_machine {initial : Snapshot} (history : History initial)
    (target : Fraction.Rational) (positive : 0 < target) :
    (history.refine target positive).current.machine =
      Refinement.Machine.refine history.current.machine target positive :=
  (refine_specification history target positive).1

/-- The original refinement preserves the exact retained chart matrix. -/
theorem refine_matrix {initial : Snapshot} (history : History initial)
    (target : Fraction.Rational) (positive : 0 < target) :
    (history.refine target positive).current.frame.matrix = history.current.frame.matrix :=
  (refine_specification history target positive).2.2.2.1

/-- The actual refined cached ball pays its same positive squared-radius request. -/
theorem refine_accurate {initial : Snapshot} (history : History initial)
    (target : Fraction.Rational) (positive : 0 < target) :
    (history.refine target positive).current.ball.radiusSq < target :=
  (refine_specification history target positive).2.2.2.2

/-- Refinement retains both the exact already exposed word and its pending queue. -/
theorem refine_words {initial : Snapshot} (history : History initial)
    (target : Fraction.Rational) (positive : 0 < target) :
    (history.refine target positive).current.machine.emitted = history.current.machine.emitted ∧
      (history.refine target positive).current.machine.pending = history.current.machine.pending :=
  ⟨(refine_specification history target positive).2.1, (refine_specification history target positive).2.2.1⟩

/-- Advance the current original cached cursor by a requested finite number of actual returned bits. -/
def advance {initial : Snapshot} : History initial → Nat → History initial
  | history, 0 => history
  | history, count + 1 => advance history.nextBit count

/-- Handle the exact requested finite bit advance while retaining every original chronological cache.

The supplied source equality transports the same fixed handlers through each
original snapshot. Each continuation receives the complete original advanced
history and its unchanged source owner, including all preceding paid work.
-/
def withAdvance {m : Type → Type} [Monad m] {α : Type} {initial : Snapshot} {source : Process}
    (stateHandler : Process.Route.StateHandler m source) (handler : Process.Route.Handler m source) :
    (history : History initial) → history.current.source = source → (count : Nat) →
      ((next : History initial) → next = history.advance count → next.current.source = source → m α) → m α
  | history, sourceEq, 0, use => use history rfl sourceEq
  | history, sourceEq, count + 1, use =>
      history.withNextBit (sourceEq.symm ▸ stateHandler) (sourceEq.symm ▸ handler) fun next same =>
        withAdvance stateHandler handler next
          (((congrArg (fun value : History initial => value.current.source) same).trans history.nextBit_source).trans
            sourceEq) count fun final finalEq finalSource =>
          use final (finalEq.trans (congrArg (fun value : History initial => value.advance count) same)) finalSource

/-- A counted bit traversal retains all original source work paid before it began. -/
theorem advance_sourceCalls_mono {initial : Snapshot} (history : History initial) (count : Nat) :
    history.sourceCalls ≤ (history.advance count).sourceCalls := by
  induction count generalizing history with
  | zero => exact Nat.le_refl _
  | succ count induction => exact history.nextBit_sourceCalls_mono.trans (induction history.nextBit)

/-- A counted traversal pays at most seven original source calls per requested bit.

The exact retained payment remains zero, three or seven at each actual step;
this bound does not identify a bit with one source callback.
-/
theorem advance_sourceCalls_le {initial : Snapshot} (history : History initial) (count : Nat) :
    (history.advance count).sourceCalls ≤ history.sourceCalls + 7 * count := by
  induction count generalizing history with
  | zero => exact Nat.le_refl _
  | succ count induction =>
      calc
        (history.advance (count + 1)).sourceCalls ≤ history.nextBit.sourceCalls + 7 * count :=
          induction history.nextBit
        _ ≤ (history.sourceCalls + 7) + 7 * count := Nat.add_le_add_right history.nextBit_sourceCalls_le _
        _ = history.sourceCalls + 7 * (count + 1) := by
          rewrite [Nat.mul_succ, Nat.add_assoc]
          exact congrArg (Nat.add history.sourceCalls) (Nat.add_comm 7 (7 * count))

/-- Every original earlier checkpoint survives the actual counted bit traversal. -/
private theorem advance_earlier_specification {initial : Snapshot} (history : History initial)
    (count : Nat) (snapshot : Snapshot) (member : snapshot ∈ history.snapshots) :
    snapshot ∈ (history.advance count).snapshots := by
  induction count generalizing history with
  | zero => exact member
  | succ count induction => exact induction history.nextBit (nextBit_earlier_specification history snapshot member)

/-- Every original cached checkpoint remains in the counted later history at its same occurrence. -/
theorem advance_earlier {initial : Snapshot} (history : History initial)
    (count : Nat) (snapshot : Snapshot) (member : snapshot ∈ history.snapshots) :
    snapshot ∈ (history.advance count).snapshots := advance_earlier_specification history count snapshot member

/-- Counted history advancement follows the same original raw bit-machine sequence. -/
private theorem advance_machine_specification {initial : Snapshot} (history : History initial) (count : Nat) :
    (history.advance count).current.machine = Advance.advance history.current.machine count := by
  induction count generalizing history with
  | zero => rfl
  | succ count induction =>
      exact (induction history.nextBit).trans
        (congrArg (fun machine => Advance.advance machine count) (nextBit_machine_specification history))

/-- The counted cached history producer has the original bit controller's exact final machine. -/
theorem advance_machine {initial : Snapshot} (history : History initial) (count : Nat) :
    (history.advance count).current.machine = Advance.advance history.current.machine count :=
  advance_machine_specification history count

/-- Advance the original retained history, then refine its same current cylinder using the cached image matrix. -/
def request {initial : Snapshot} (history : History initial)
    (epsilonSq : Fraction.Rational) (positive : 0 < epsilonSq) (count : Nat) : History initial :=
  let advanced := history.advance count
  advanced.refine (advanced.current.frame.cylinderBallTarget epsilonSq)
    (advanced.current.frame.cylinderBallTarget_pos positive)

/-- A retained history request has the complete original persistent cursor request machine. -/
theorem request_machine {initial : Snapshot} (history : History initial)
    (epsilonSq : Fraction.Rational) (positive : 0 < epsilonSq) (count : Nat) :
    (history.request epsilonSq positive count).current.machine =
      Cursor.Request.Machine.refineCylinder (Advance.advance history.current.machine count) epsilonSq positive := by
  let advanced := history.advance count
  let cached : { target : Fraction.Rational // 0 < target } :=
    ⟨advanced.current.frame.cylinderBallTarget epsilonSq, advanced.current.frame.cylinderBallTarget_pos positive⟩
  let original : { target : Fraction.Rational // 0 < target } :=
    ⟨Cursor.Request.Machine.cylinderBallTarget advanced.current.machine epsilonSq,
      Cursor.Request.Machine.cylinderBallTarget_pos advanced.current.machine positive⟩
  have targetEq : cached = original :=
    Subtype.ext (advanced.current.frame.cylinderBallTarget_eq epsilonSq)
  exact ((advanced.refine_machine cached.val cached.property).trans
    (congrArg (fun target : { value : Fraction.Rational // 0 < value } =>
      Refinement.Machine.refine advanced.current.machine target.val target.property) targetEq)).trans
    (congrArg (fun machine => Cursor.Request.Machine.refineCylinder machine epsilonSq positive)
      (history.advance_machine count))

/-- Handle one complete original persistent cursor request using its retained history and matrix caches.

The requested bits consume each actual predecessor. The final cylinder target
comes from the advanced retained frame, and its observed reply reconstructs
the same original refinement. Both the complete resulting history and fixed
original source identity are supplied to the continuation.
-/
def withRequest {m : Type → Type} [Monad m] {α : Type} {initial : Snapshot} {source : Process}
    (stateHandler : Process.Route.StateHandler m source) (handler : Process.Route.Handler m source)
    (history : History initial) (sourceEq : history.current.source = source)
    (epsilonSq : Fraction.Rational) (positive : 0 < epsilonSq) (count : Nat)
    (use : (next : History initial) → next = history.request epsilonSq positive count →
      next.current.source = source → m α) : m α :=
  withAdvance stateHandler handler history sourceEq count fun advanced advancedEq advancedSource =>
    advanced.withRefinement (advancedSource.symm ▸ handler) (advanced.current.frame.cylinderBallTarget epsilonSq)
      (advanced.current.frame.cylinderBallTarget_pos positive) fun next same =>
        use next (by cases advancedEq; exact same)
          ((congrArg (fun value : History initial => value.current.source) same).trans
            ((advanced.refine_source _ _).trans advancedSource))

/-- Counted cached advancement preserves the exact earlier prefix and increases its length by the supplied count. -/
theorem advance_word {initial : Snapshot} (history : History initial) (count : Nat) :
    history.current.machine.emitted.IsPrefix (history.advance count).current.machine.emitted ∧
      (history.advance count).current.machine.emitted.length = history.current.machine.emitted.length + count := by
  rewrite [history.advance_machine count]
  exact Advance.productive history.current.machine count

/-- Finite history execution appends the supplied numerical control path exactly. -/
private theorem execute_actions_specification {initial : Snapshot} (history : History initial)
    (actions : List Action) : (history.execute actions).actions = history.actions ++ actions := by
  induction actions generalizing history with
  | nil => exact (Data.List.Append.append_nil history.actions).symm
  | cons action rest induction =>
      cases action with
      | bit =>
          exact (induction history.nextBit).trans
            ((congrArg (fun actions => actions ++ rest) (nextBit_actions_specification history)).trans
              (Data.List.Append.append_assoc history.actions [.bit] rest))
      | refine target positive =>
          exact (induction (history.refine target positive)).trans
            ((congrArg (fun actions => actions ++ rest) (refine_actions_specification history target positive)).trans
              (Data.List.Append.append_assoc history.actions [.refine target positive] rest))

/-- The history producer retains the exact supplied action sequence after the original earlier path. -/
theorem execute_actions {initial : Snapshot} (history : History initial) (actions : List Action) :
    (history.execute actions).actions = history.actions ++ actions := execute_actions_specification history actions

/-- The actual current checkpoint retains the same original Gaussian source and dependent origin state. -/
theorem exactCursor {initial : Snapshot} (history : History initial) {origin : Process} {originState : origin.State}
    (initialCursor : Semantics.Basic.ExactCursor origin originState initial.machine) :
    Semantics.Basic.ExactCursor origin originState history.current.machine :=
  history.currentEq.symm ▸ Action.run_exactCursor initialCursor history.actions

set_option genInjectivity false in
/-- A cached rational tail realizes one original snapshot at a supplied common projective image. -/
structure Realization (snapshot : Snapshot) (image : Line.GaussianLine) where
  /-- The actual original-chart pullback coordinates, computed once. -/ pulled : Line.GaussianLine
  /-- The coordinates consume the original snapshot's retained adjugate and common image. -/ pulledEq :
    pulled = snapshot.frame.pullback image
  /-- The original-chart pulled denominator is nonzero. -/ denominatorNonzero : pulled.q ≠ 0
  /-- The computed rational tail in this original mode's coordinate. -/ value : Basic.Canonical
  /-- The tail is the quotient of the same cached pulled coordinates. -/ valueEq :
    value = Line.Gaussian.Proj.affineReading pulled
  /-- This tail was possible at the original retained mode state. -/ possible :
    SemanticMode.possible snapshot.machine.mode value
  /-- The same computed tail satisfies the exact cached original numerical ball. -/ inside :
    snapshot.ball.Contains value
  /-- The original snapshot chart realizes this same projective reading. -/ represented :
    image.Equivalent (snapshot.frame.image value)

namespace Realization

set_option genInjectivity false in
/-- A realized old snapshot has a finite cursor description with its same rational tail, words and chart caches. -/
structure Continuation {snapshot : Snapshot} {image : Line.GaussianLine}
    (realization : Realization snapshot image) where
  /-- The original mode's exact counterpart at this actual computed earlier tail. -/ mode :
    Mode.Exact.Realization snapshot.machine.mode
  /-- The counterpart retains this same cached computed rational tail. -/ valueEq : mode.value = realization.value
  /-- The finite cursor description consumes the original snapshot frame and exact counterpart. -/ description :
    Code.Description snapshot.frame mode

/-- Describe the exact cursor continuation of an earlier realization using its existing word and chart caches. -/
def continueCursor {snapshot : Snapshot} {image : Line.GaussianLine} (realization : Realization snapshot image) :
    Continuation realization :=
  let mode := Mode.Exact.ofPossible snapshot.machine.mode realization.value realization.possible
  let description := Code.ofRealization snapshot.frame mode snapshot.grammar
  ⟨mode, Mode.Exact.ofPossible_value snapshot.machine.mode realization.value realization.possible, description⟩

namespace Continuation

/-- An earlier realized affine reading gives its finite-code cursor the same fixed exact singleton origin. -/
theorem exactCursor {snapshot : Snapshot} {image : Line.GaussianLine} {realization : Realization snapshot image}
    (continuation : Continuation realization) (value : Basic.Canonical)
    (represented : (snapshot.frame.image realization.value).Equivalent (Line.Proj.affine value)) :
    Semantics.Basic.ExactCursor (Process.exact value) ()
      (continuation.description.code.interpret continuation.description.valid) :=
  continuation.description.exactCursor value (continuation.valueEq.symm ▸ represented)

end Continuation

end Realization

/-- Realize an earlier checkpoint using a later possible tail and its already cached common image. -/
def realize {initial : Snapshot} (history : History initial) (snapshot : Snapshot)
    (member : snapshot ∈ history.snapshots) (tail : Basic.Canonical)
    (possible : SemanticMode.possible history.current.machine.mode tail)
    (image : Line.GaussianLine) (imageEq : image = history.current.frame.image tail) : Realization snapshot image := by
  let predecessor := (history.compatible snapshot member).pullbackImage tail possible image imageEq
  have sameImage : predecessor.image = image := predecessor.imageEq.trans imageEq.symm
  exact
    { pulled := predecessor.pulled
      pulledEq := predecessor.pulledEq.trans (congrArg snapshot.frame.pullback sameImage)
      denominatorNonzero := predecessor.denominatorNonzero
      value := predecessor.value
      valueEq := predecessor.valueEq
      possible := predecessor.possible
      inside := snapshot.possible_inside predecessor.possible
      represented := sameImage ▸ predecessor.represented }

/-- Realize each original retained checkpoint in order without rereading its ball or rebuilding its chart. -/
private def realizeSnapshots {initial : Snapshot} (history : History initial) (tail : Basic.Canonical)
    (possible : SemanticMode.possible history.current.machine.mode tail)
    (image : Line.GaussianLine) (imageEq : image = history.current.frame.image tail) :
    (snapshots : List Snapshot) → (∀ snapshot ∈ snapshots, snapshot ∈ history.snapshots) →
      List ((snapshot : Snapshot) × Realization snapshot image)
  | [], _ => []
  | snapshot :: remaining, retained =>
      let realization := history.realize snapshot (retained snapshot (List.Mem.head remaining))
        tail possible image imageEq
      ⟨snapshot, realization⟩ :: realizeSnapshots history tail possible image imageEq remaining
        (fun entry member => retained entry (List.Mem.tail snapshot member))

/-- The realization builder preserves the exact original checkpoint sequence, including repeated occurrences. -/
private theorem realizeSnapshots_projection {initial : Snapshot} (history : History initial) (tail : Basic.Canonical)
    (possible : SemanticMode.possible history.current.machine.mode tail)
    (image : Line.GaussianLine) (imageEq : image = history.current.frame.image tail) :
    (snapshots : List Snapshot) → (retained : ∀ snapshot ∈ snapshots, snapshot ∈ history.snapshots) →
      (realizeSnapshots history tail possible image imageEq snapshots retained).map Sigma.fst = snapshots
  | [], _ => rfl
  | snapshot :: remaining, retained =>
      congrArg (List.cons snapshot)
        (realizeSnapshots_projection history tail possible image imageEq remaining
          (fun entry member => retained entry (List.Mem.tail snapshot member)))

set_option genInjectivity false in
/-- One actual final rational witness and its common image realize every original checkpoint in the finite history. -/
structure Survivor {initial : Snapshot} (history : History initial) where
  /-- The actual possible rational tail selected at the original current mode state. -/ tail : Basic.Canonical
  /-- That selected tail belongs to the same actual final mode. -/ possible :
    SemanticMode.possible history.current.machine.mode tail
  /-- The actual final chart image computed once and shared by every earlier realization. -/ image : Line.GaussianLine
  /-- The image uses the same final frame and selected tail. -/ imageEq : image = history.current.frame.image tail
  /-- The final homogeneous pair has a nonzero coordinate. -/ imageValid : Line.Gaussian.Proj.HasNonzeroCoordinate image
  /-- Each cached earlier realization retains its original checkpoint parent. -/ realizations :
    List ((snapshot : Snapshot) × Realization snapshot image)
  /-- The original ordered snapshot sequence is retained exactly. -/ snapshotsEq :
    realizations.map Sigma.fst = history.snapshots

/-- Select one final witness and construct compatible rational tails for every original numerical checkpoint.

The final witness is projected from the actual current observation without
reading the source again. The common final image is computed once. Every earlier tail consumes its
original inverse-chart cache and is proved inside its cached original ball.
Both exposed and pending words remain with their actual snapshot owners;
no independent rational encoding is substituted for those words.
-/
def survive {initial : Snapshot} (history : History initial) : Survivor history :=
  let selected := history.current.witness
  let image := history.current.frame.image selected.val
  let realizations := realizeSnapshots history selected.val selected.property image rfl history.snapshots
    (fun _ member => member)
  ⟨selected.val, selected.property, image, rfl,
    Line.Matrix.Gaussian.Mat2.act_hasNonzeroCoordinate history.current.frame.determinantNonzero
      (Line.Gaussian.Proj.affine_hasNonzeroCoordinate selected.val),
    realizations, realizeSnapshots_projection history selected.val selected.property image rfl history.snapshots
      (fun _ member => member)⟩

namespace Survivor

set_option genInjectivity false in
/-- The common history image has an explicit affine rational reading possible at its original Gaussian source state. -/
structure Reading {initial : Snapshot} {history : History initial} (survivor : Survivor history)
    (origin : Process) (originState : origin.State) where
  /-- The same original source-state certificate at the starting checkpoint. -/ initialCursor :
    Semantics.Basic.ExactCursor origin originState initial.machine
  /-- The actual shared final image has a nonzero affine denominator. -/ denominatorNonzero : survivor.image.q ≠ 0
  /-- The rational reading computed from the existing shared image cache. -/ value : Basic.Canonical
  /-- The reading is the quotient of that exact cached image. -/ valueEq :
    value = Line.Gaussian.Proj.affineReading survivor.image
  /-- The computed reading was possible at the same original dependent source state. -/ originalPossible :
    origin.Possible originState value
  /-- The shared image represents the computed affine rational reading. -/ represented :
    survivor.image.Equivalent (Line.Proj.affine value)

/-- Compute the Gaussian rational reading of the shared final image and prove its original-state possibility.

No parser or matrix cache is recomputed. The original exact-cursor law
proves denominator nonvanishing and correctness of the explicit quotient;
its existential source witness is used solely as proof evidence.
-/
def read {initial : Snapshot} {history : History initial} (survivor : Survivor history)
    {origin : Process} {originState : origin.State}
    (initialCursor : Semantics.Basic.ExactCursor origin originState initial.machine) :
    Reading survivor origin originState := by
  have currentCursor := history.exactCursor initialCursor
  have imageEq : survivor.image = Cursor.Image.Machine.image history.current.machine survivor.tail :=
    survivor.imageEq.trans (history.current.frame.imageEq survivor.tail)
  have affine : ∃ value : Basic.Canonical,
      origin.Possible originState value ∧ survivor.image.Equivalent (Line.Proj.affine value) := by
    rcases currentCursor.exact survivor.possible with ⟨value, possible, represented⟩
    exact ⟨value, possible, imageEq.symm ▸ represented⟩
  have denominatorNonzero : survivor.image.q ≠ 0 := by
    rcases affine with ⟨value, _possible, represented⟩
    exact Line.Gaussian.Proj.denominator_ne_zero_of_equivalent_affine survivor.imageValid represented
  let value := Line.Gaussian.Proj.affineReading survivor.image
  have originalPossible : origin.Possible originState value := by
    rcases affine with ⟨previous, possible, represented⟩
    have equal : value = previous :=
      Line.Gaussian.Proj.affineReading_eq_of_equivalent denominatorNonzero represented
    exact equal.symm ▸ possible
  exact ⟨initialCursor, denominatorNonzero, value, rfl, originalPossible,
    Line.Gaussian.Proj.equivalent_affineReading survivor.image denominatorNonzero⟩

namespace Reading

/-- Every realized earlier chart represents the same affine rational reading as the shared final image. -/
theorem snapshot_represented {initial : Snapshot} {history : History initial} {survivor : Survivor history}
    {origin : Process} {originState : origin.State} (reading : Reading survivor origin originState)
    {snapshot : Snapshot} (realization : Realization snapshot survivor.image) :
    (snapshot.frame.image realization.value).Equivalent (Line.Proj.affine reading.value) :=
  Line.Gaussian.Proj.equivalent_trans (Line.Proj.Equivalent.symm realization.represented) reading.represented
    survivor.imageValid (Line.Gaussian.Proj.affine_hasNonzeroCoordinate reading.value)

end Reading

end Survivor

end History

end Purelib.Data.CCL.Transducer.Machine

end
