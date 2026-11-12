module
public import Purelib.Approximation.Gaussian.Process.Coordinate
public import Purelib.Computation.Query.Program
import Purelib.Approximation.AccuracyRequest
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Observing paired Gaussian coordinate requests

The original Gaussian process and retained state are fixed inputs. The
displayed requests are the actual state refinements and ball readbacks; each
returned state and ball is consumed directly by the coordinate construction.
Replay requires decidable equality of the original finite state type.
-/

public section

namespace Purelib.Approximation.Gaussian.Process.Coordinate.Observation

open Purelib.Approximation
open Purelib.Approximation.Gaussian.Enclosure
open Purelib.Computation.Query
open Purelib.Data.Gaussian
open Purelib.Data.Rat

set_option genInjectivity false in
/-- One actual Gaussian state refinement or ball readback. -/
inductive Request (State : Type) where
  /-- Refine the displayed original state to a positive squared target. -/ | refine
      (previous : State) (target : Fraction.Rational) (positive : 0 < target)
  /-- Read the original Gaussian ball at the displayed state. -/ | ball (state : State)
  deriving @[expose] DecidableEq

constructive_injectivity Request

/-- A returned state or ball certified against the exact original process request. -/
@[expose] def Response (process : Process) : Request process.State → Type
  | .refine previous target positive => {next : process.State // next = process.refine previous target positive}
  | .ball state => {ball : Ball // ball = process.ball state}

/-- An original request paired with its certified state or ball reply. -/
abbrev Reply (process : Process) := Σ request : Request process.State, Response process request

set_option genInjectivity false in
/-- A reply to a different original Gaussian process request. -/
structure Invalid (State : Type) where
  /-- The request actually made by the paired construction. -/ requested : Request State
  /-- The request identified by the returned reply. -/ reported : Request State
  /-- The returned reply does not belong to the requested operation. -/ different : reported ≠ requested

constructive_injectivity Invalid

/-- Execute one original Gaussian process request and retain its exact reply. -/
@[expose] def original (process : Process) : (request : Request process.State) → Reply process
  | .refine previous target positive =>
      ⟨.refine previous target positive, ⟨process.refine previous target positive, rfl⟩⟩
  | .ball state => ⟨.ball state, ⟨process.ball state, rfl⟩⟩

/-- The original process reply identifies exactly the request that produced it. -/
theorem original_request (process : Process) (request : Request process.State) :
    (original process request).1 = request := by
  cases request <;> rfl

/-- Make one displayed request and reject a reply belonging to a different request. -/
@[expose] def checked (process : Process) [DecidableEq process.State] (request : Request process.State) :
    Program (Request process.State) (Reply process) (Except (Invalid process.State) (Response process request)) :=
  .request request fun reply =>
    if same : reply.1 = request then .pure (.ok (same ▸ reply.2))
    else .pure (.error ⟨request, reply.1, same⟩)

/-- Original-source execution returns the actual state or ball from one checked request. -/
theorem checked_original (process : Process) [DecidableEq process.State] (request : Request process.State) :
    ((checked process request).protocol.run (original process)).value =
      .ok (original_request process request ▸ (original process request).2) := by
  unfold checked
  change (((if same : (original process request).1 = request then
    (Program.pure (.ok (same ▸ (original process request).2)) :
      Program (Request process.State) (Reply process) (Except (Invalid process.State) (Response process request)))
    else Program.pure (.error ⟨request, (original process request).1, same⟩)).protocol).run
      (original process)).value = _
  rewrite [dif_pos (original_request process request)]
  rfl

/-- One original checked request records exactly its original request and returned reply. -/
theorem checked_original_trace (process : Process) [DecidableEq process.State] (request : Request process.State) :
    ((checked process request).protocol.run (original process)).trace = [⟨request, original process request⟩] := by
  unfold checked
  change ⟨request, original process request⟩ :: ((if same : (original process request).1 = request then
    (Program.pure (.ok (same ▸ (original process request).2)) :
      Program (Request process.State) (Reply process) (Except (Invalid process.State) (Response process request)))
    else Program.pure (.error ⟨request, (original process request).1, same⟩)).protocol.run (original process)).trace = _
  rewrite [dif_pos (original_request process request)]
  rfl

/-- A coordinate state certified as the complete original request from its retained predecessor. -/
abbrev CertifiedState {process : Process} {origin : process.State} {read : Basic.Canonical → Fraction.Rational}
    (coordinateSq : ∀ value center, (read value - read center) ^ 2 ≤ Norm.Basic.normSq (value - center))
    (previous : State process origin read) (tolerance : Fraction.Rational) (positive : 0 < tolerance) :=
  {next : State process origin read // next = State.request coordinateSq previous tolerance positive}

/-- The exact squared-error request associated with a coordinate tolerance. -/
@[expose] def refinementRequest {process : Process} {origin : process.State}
    {read : Basic.Canonical → Fraction.Rational}
    (previous : State process origin read) (tolerance : Fraction.Rational) (positive : 0 < tolerance) :
    Request process.State :=
  .refine previous.current ((tolerance / 4) ^ 2)
    (Fraction.Order.Arithmetic.pow_pos_direct (Bounds.Quarter.quarter_pos positive) 2)

/-- The original process state returned by a coordinate's squared-error request. -/
abbrev ReturnedState {process : Process} {origin : process.State} {read : Basic.Canonical → Fraction.Rational}
    (previous : State process origin read) (tolerance : Fraction.Rational) (positive : 0 < tolerance) :=
  Response process (refinementRequest previous tolerance positive)

/-- Assemble a coordinate from the already returned original process state and ball. -/
@[expose] def assembleState {process : Process} {origin : process.State} {read : Basic.Canonical → Fraction.Rational}
    (coordinateSq : ∀ value center, (read value - read center) ^ 2 ≤ Norm.Basic.normSq (value - center))
    (previous : State process origin read) (tolerance : Fraction.Rational) (positive : 0 < tolerance)
    (next : ReturnedState previous tolerance positive) (ball : Response process (.ball next.val)) :
    CertifiedState coordinateSq previous tolerance positive :=
  ⟨State.requestWith coordinateSq previous tolerance positive next.val next.property ball.val ball.property,
    State.requestWith_eq coordinateSq previous tolerance positive next.val next.property ball.val ball.property⟩

set_option genInjectivity false in
/-- A failed coordinate request retains a successful refinement when its ball readback fails. -/
inductive CoordinateFailure {process : Process} {origin : process.State}
    {read : Basic.Canonical → Fraction.Rational}
    (previous : State process origin read) (tolerance : Fraction.Rational) (positive : 0 < tolerance)
    (Error : Type) where
  /-- The original refinement did not produce a valid response. -/
  | refinement (reason : Error)
  /-- The exact returned refinement was saved before its ball response failed. -/
  | ball (next : ReturnedState previous tolerance positive) (reason : Error)

constructive_injectivity CoordinateFailure

/-- Execute the shared coordinate branches using the caller's checked original operations. -/
@[expose] def coordinateWith {process : Process} {origin : process.State}
    {read : Basic.Canonical → Fraction.Rational} {Question Reply Error : Type}
    (ask : (operation : Request process.State) →
      Program Question Reply (Except Error (Response process operation)))
    (coordinateSq : ∀ value center, (read value - read center) ^ 2 ≤ Norm.Basic.normSq (value - center))
    (previous : State process origin read) (tolerance : Fraction.Rational) (positive : 0 < tolerance) :
    Program Question Reply
      (Except (CoordinateFailure previous tolerance positive Error)
        (CertifiedState coordinateSq previous tolerance positive)) :=
  (ask (refinementRequest previous tolerance positive)).bind fun refined =>
    match refined with
    | .error invalid => .pure (.error (.refinement invalid))
    | .ok next => (ask (.ball next.val)).map fun observed =>
      match observed with
      | .error invalid => .error (.ball next invalid)
      | .ok ball => .ok (assembleState coordinateSq previous tolerance positive next ball)

/-- Equal actual checked-operation executions yield equal coordinate executions. -/
theorem coordinateWith_run_eq {process : Process} {origin : process.State}
    {read : Basic.Canonical → Fraction.Rational} {Question Reply Error : Type} [DecidableEq Question]
    (first second : (operation : Request process.State) →
      Program Question Reply (Except Error (Response process operation)))
    (coordinateSq : ∀ value center, (read value - read center) ^ 2 ≤ Norm.Basic.normSq (value - center))
    (previous : State process origin read) (tolerance : Fraction.Rational) (positive : 0 < tolerance)
    (oracle : Question → Reply)
    (same : ∀ operation, ((first operation).protocol.run oracle) = ((second operation).protocol.run oracle)) :
    ((coordinateWith first coordinateSq previous tolerance positive).protocol.run oracle) =
      ((coordinateWith second coordinateSq previous tolerance positive).protocol.run oracle) := by
  unfold coordinateWith
  rw [Program.bind_execution, Program.bind_execution]
  apply Protocol.bind_execution_eq _ _ _ _ oracle (same (refinementRequest previous tolerance positive))
  cases ((second (refinementRequest previous tolerance positive)).protocol.run oracle).value with
  | error invalid => rfl
  | ok next =>
      rw [Program.map_execution, Program.map_execution]
      exact Protocol.map_execution_eq _ _ _ oracle (same (.ball next.val))

/-- Original operation replies reconstruct the exact original coordinate state. -/
theorem coordinateWith_original {process : Process} {origin : process.State}
    {read : Basic.Canonical → Fraction.Rational} {Question Reply Error : Type} [DecidableEq Question]
    (ask : (operation : Request process.State) →
      Program Question Reply (Except Error (Response process operation)))
    (coordinateSq : ∀ value center, (read value - read center) ^ 2 ≤ Norm.Basic.normSq (value - center))
    (previous : State process origin read) (tolerance : Fraction.Rational) (positive : 0 < tolerance)
    (oracle : Question → Reply)
    (answers : ∀ operation, ((ask operation).protocol.run oracle).value =
      .ok (original_request process operation ▸ (original process operation).2)) :
    ((coordinateWith ask coordinateSq previous tolerance positive).protocol.run oracle).value =
      .ok ⟨State.request coordinateSq previous tolerance positive, rfl⟩ := by
  unfold coordinateWith
  rw [Program.bind_execution, Protocol.bind_run_value, answers]
  dsimp only [original, original_request]
  rw [Program.map_execution, Protocol.map_run_value, answers]
  apply congrArg Except.ok
  apply Subtype.ext
  rfl

/-- Complete a retained successful refinement by reading its actual original ball. -/
@[expose] def resumeWith {process : Process} {origin : process.State}
    {read : Basic.Canonical → Fraction.Rational} {Question Reply Error : Type}
    (ask : (operation : Request process.State) →
      Program Question Reply (Except Error (Response process operation)))
    (coordinateSq : ∀ value center, (read value - read center) ^ 2 ≤ Norm.Basic.normSq (value - center))
    (previous : State process origin read) (tolerance : Fraction.Rational) (positive : 0 < tolerance)
    (next : ReturnedState previous tolerance positive) :
    Program Question Reply
      (Except (CoordinateFailure previous tolerance positive Error)
        (CertifiedState coordinateSq previous tolerance positive)) :=
  (ask (.ball next.val)).map fun observed =>
    match observed with
    | .error invalid => .error (.ball next invalid)
    | .ok ball => .ok (assembleState coordinateSq previous tolerance positive next ball)

/-- Original ball replies complete the retained refinement as the original coordinate state. -/
theorem resumeWith_original {process : Process} {origin : process.State}
    {read : Basic.Canonical → Fraction.Rational} {Question Reply Error : Type} [DecidableEq Question]
    (ask : (operation : Request process.State) →
      Program Question Reply (Except Error (Response process operation)))
    (coordinateSq : ∀ value center, (read value - read center) ^ 2 ≤ Norm.Basic.normSq (value - center))
    (previous : State process origin read) (tolerance : Fraction.Rational) (positive : 0 < tolerance)
    (next : ReturnedState previous tolerance positive) (oracle : Question → Reply)
    (answers : ∀ operation, ((ask operation).protocol.run oracle).value =
      .ok (original_request process operation ▸ (original process operation).2)) :
    ((resumeWith ask coordinateSq previous tolerance positive next).protocol.run oracle).value =
      .ok ⟨State.request coordinateSq previous tolerance positive, rfl⟩ := by
  unfold resumeWith
  rw [Program.map_execution, Protocol.map_run_value, answers]
  apply congrArg Except.ok
  apply Subtype.ext
  exact (assembleState coordinateSq previous tolerance positive next _).property

/-- Observe one coordinate refinement through its actual state request and returned ball readback. -/
@[expose] def coordinate {process : Process} [DecidableEq process.State]
    {origin : process.State} {read : Basic.Canonical → Fraction.Rational}
    (coordinateSq : ∀ value center, (read value - read center) ^ 2 ≤ Norm.Basic.normSq (value - center))
    (previous : State process origin read) (tolerance : Fraction.Rational) (positive : 0 < tolerance) :
    Program (Request process.State) (Reply process)
      (Except (Invalid process.State) (CertifiedState coordinateSq previous tolerance positive)) :=
  (coordinateWith (checked process) coordinateSq previous tolerance positive).map fun result =>
    match result with
    | .error (.refinement invalid) => .error invalid
    | .error (.ball _ invalid) => .error invalid
    | .ok next => .ok next

/-- Original-source execution returns the same complete coordinate state and original predecessor. -/
theorem coordinate_original {process : Process} [DecidableEq process.State]
    {origin : process.State} {read : Basic.Canonical → Fraction.Rational}
    (coordinateSq : ∀ value center, (read value - read center) ^ 2 ≤ Norm.Basic.normSq (value - center))
    (previous : State process origin read) (tolerance : Fraction.Rational) (positive : 0 < tolerance) :
    ((coordinate coordinateSq previous tolerance positive).protocol.run (original process)).value =
      .ok ⟨State.request coordinateSq previous tolerance positive, rfl⟩ := by
  unfold coordinate coordinateWith
  rw [Program.map_execution, Protocol.map_run_value, Program.bind_execution, Protocol.bind_run_value, checked_original]
  dsimp only [original, original_request]
  rw [Program.map_execution, Protocol.map_run_value, checked_original]
  apply congrArg Except.ok
  apply Subtype.ext
  rfl

/-- One coordinate request records its actual refinement followed by its returned state's ball readback. -/
theorem coordinate_original_trace {process : Process} [DecidableEq process.State]
    {origin : process.State} {read : Basic.Canonical → Fraction.Rational}
    (coordinateSq : ∀ value center, (read value - read center) ^ 2 ≤ Norm.Basic.normSq (value - center))
    (previous : State process origin read) (tolerance : Fraction.Rational) (positive : 0 < tolerance) :
    ((coordinate coordinateSq previous tolerance positive).protocol.run (original process)).trace =
      [⟨refinementRequest previous tolerance positive,
          original process (refinementRequest previous tolerance positive)⟩,
        ⟨.ball (State.request coordinateSq previous tolerance positive).current,
          original process (.ball (State.request coordinateSq previous tolerance positive).current)⟩] := by
  unfold coordinate coordinateWith
  rw [Program.map_execution, Protocol.map_run_trace, Program.bind_execution, Protocol.bind_run_trace,
    checked_original, checked_original_trace]
  dsimp only [original, original_request]
  rw [Program.map_execution, Protocol.map_run_trace, checked_original_trace]
  rfl

/-- Any oracle preserves the original first-failure and returned-state behavior. -/
theorem coordinate_value {process : Process} [DecidableEq process.State]
    {origin : process.State} {read : Basic.Canonical → Fraction.Rational}
    (coordinateSq : ∀ value center, (read value - read center) ^ 2 ≤ Norm.Basic.normSq (value - center))
    (previous : State process origin read) (tolerance : Fraction.Rational) (positive : 0 < tolerance)
    (oracle : Request process.State → Reply process) :
    ((coordinate coordinateSq previous tolerance positive).protocol.run oracle).value =
      match ((checked process (refinementRequest previous tolerance positive)).protocol.run oracle).value with
      | .error invalid => .error invalid
      | .ok next => (((checked process (.ball next.val)).protocol.run oracle).value).map
          (assembleState coordinateSq previous tolerance positive next) := by
  unfold coordinate coordinateWith
  rw [Program.map_execution, Protocol.map_run_value, Program.bind_execution, Protocol.bind_run_value]
  cases ((checked process (refinementRequest previous tolerance positive)).protocol.run oracle).value with
  | error invalid => rfl
  | ok next =>
      rw [Program.map_execution, Protocol.map_run_value]
      cases observed : ((checked process (.ball next.val)).protocol.run oracle).value with
      | error invalid =>
          change .error invalid =
            (((checked process (.ball next.val)).protocol.run oracle).value).map
              (assembleState coordinateSq previous tolerance positive next)
          exact congrArg (Except.map (assembleState coordinateSq previous tolerance positive next)) observed.symm
      | ok ball =>
          change .ok (assembleState coordinateSq previous tolerance positive next ball) =
            (((checked process (.ball next.val)).protocol.run oracle).value).map
              (assembleState coordinateSq previous tolerance positive next)
          exact congrArg (Except.map (assembleState coordinateSq previous tolerance positive next)) observed.symm

/-- Any oracle retains the original ordered refinement and, on success, ball readback. -/
theorem coordinate_trace {process : Process} [DecidableEq process.State]
    {origin : process.State} {read : Basic.Canonical → Fraction.Rational}
    (coordinateSq : ∀ value center, (read value - read center) ^ 2 ≤ Norm.Basic.normSq (value - center))
    (previous : State process origin read) (tolerance : Fraction.Rational) (positive : 0 < tolerance)
    (oracle : Request process.State → Reply process) :
    ((coordinate coordinateSq previous tolerance positive).protocol.run oracle).trace =
      ((checked process (refinementRequest previous tolerance positive)).protocol.run oracle).trace ++
        match ((checked process (refinementRequest previous tolerance positive)).protocol.run oracle).value with
        | .error _ => []
        | .ok next => ((checked process (.ball next.val)).protocol.run oracle).trace := by
  unfold coordinate coordinateWith
  rw [Program.map_execution, Protocol.map_run_trace, Program.bind_execution, Protocol.bind_run_trace]
  cases ((checked process (refinementRequest previous tolerance positive)).protocol.run oracle).value with
  | error invalid => rfl
  | ok next => rw [Program.map_execution, Protocol.map_run_trace]

/-- A paired state certified as the original construction from its retained real coordinate. -/
abbrev CertifiedFromReal {process : Process} {origin : process.State}
    (real : State process origin Basic.Canonical.re) :=
  {paired : Paired process origin // paired = Paired.fromReal real}

/-- Construct the original paired state from the supplied original origin-ball reply. -/
@[expose] def assembleFromReal {process : Process} {origin : process.State}
    (real : State process origin Basic.Canonical.re) (observed : Response process (.ball origin)) :
    CertifiedFromReal real :=
  ⟨Paired.fromRealWith real observed.val observed.property, Paired.fromRealWith_eq real observed.val observed.property⟩

/-- A retained original origin-ball reply and the pair constructed from that same reply. -/
abbrev CachedFromReal {process : Process} {origin : process.State}
    (real : State process origin Basic.Canonical.re) :=
  Σ observed : Response process (.ball origin),
    {paired : Paired process origin // paired = Paired.fromRealWith real observed.val observed.property}

/-- Assemble the retained origin ball and the pair that consumes it. -/
@[expose] def assembleCachedFromReal {process : Process} {origin : process.State}
    (real : State process origin Basic.Canonical.re) (observed : Response process (.ball origin)) :
    CachedFromReal real :=
  ⟨observed, ⟨Paired.fromRealWith real observed.val observed.property, rfl⟩⟩

/-- Observe the origin ball once and consume its certified original reply. -/
@[expose] def observeOrigin {process : Process} [DecidableEq process.State] {origin : process.State}
    {Result : Type} (consume : Response process (.ball origin) → Result) :
    Program (Request process.State) (Reply process) (Except (Invalid process.State) Result) :=
  (checked process (.ball origin)).map fun result => result.map consume

/-- Observe and retain the origin ball together with the pair constructed from that exact reply. -/
@[expose] def fromRealCached {process : Process} [DecidableEq process.State] {origin : process.State}
    (real : State process origin Basic.Canonical.re) :
    Program (Request process.State) (Reply process) (Except (Invalid process.State) (CachedFromReal real)) :=
  observeOrigin (assembleCachedFromReal real)

/-- Observe the original origin ball once when attaching the imaginary coordinate to a real state. -/
@[expose] def fromReal {process : Process} [DecidableEq process.State] {origin : process.State}
    (real : State process origin Basic.Canonical.re) :
    Program (Request process.State) (Reply process) (Except (Invalid process.State) (CertifiedFromReal real)) :=
  observeOrigin (assembleFromReal real)

/-- Original execution retains the exact origin ball and its paired construction. -/
theorem fromRealCached_original {process : Process} [DecidableEq process.State] {origin : process.State}
    (real : State process origin Basic.Canonical.re) :
    ((fromRealCached real).protocol.run (original process)).value =
      .ok ⟨⟨process.ball origin, rfl⟩, ⟨Paired.fromReal real, rfl⟩⟩ := by
  unfold fromRealCached observeOrigin
  rw [Program.map_execution, Protocol.map_run_value, checked_original]
  rfl

/-- The retained origin ball is obtained by exactly one original process request. -/
theorem fromRealCached_trace {process : Process} [DecidableEq process.State] {origin : process.State}
    (real : State process origin Basic.Canonical.re) (oracle : Request process.State → Reply process) :
    ((fromRealCached real).protocol.run oracle).trace = [⟨.ball origin, oracle (.ball origin)⟩] := by
  unfold fromRealCached observeOrigin
  rw [Program.map_execution, Protocol.map_run_trace]
  unfold checked
  change ⟨.ball origin, oracle (.ball origin)⟩ ::
    (((if same : (oracle (.ball origin)).1 = .ball origin then
      (Program.pure (.ok (same ▸ (oracle (.ball origin)).2)) :
        Program (Request process.State) (Reply process)
          (Except (Invalid process.State) (Response process (.ball origin))))
    else .pure (.error ⟨.ball origin, (oracle (.ball origin)).1, same⟩)).protocol).run oracle).trace = _
  split <;> rfl

/-- Exact replay retains the original origin ball without another readback. -/
theorem fromRealCached_replay {process : Process} [DecidableEq process.State] {origin : process.State}
    (real : State process origin Basic.Canonical.re) :
    (fromRealCached real).protocol.replayExact ((fromRealCached real).protocol.run (original process)).trace =
      .ok (.ok ⟨⟨process.ball origin, rfl⟩, ⟨Paired.fromReal real, rfl⟩⟩) := by
  rw [(fromRealCached real).protocol.replayExact_run, fromRealCached_original]

/-- Original execution returns the exact paired state attached to the retained real coordinate. -/
theorem fromReal_original {process : Process} [DecidableEq process.State] {origin : process.State}
    (real : State process origin Basic.Canonical.re) :
    ((fromReal real).protocol.run (original process)).value = .ok ⟨Paired.fromReal real, rfl⟩ := by
  unfold fromReal observeOrigin
  rw [Program.map_execution, Protocol.map_run_value, checked_original]
  apply congrArg Except.ok
  apply Subtype.ext
  exact (assembleFromReal real _).property

/-- The origin-ball observer retains its single actual request for every supplied reply function. -/
theorem fromReal_trace {process : Process} [DecidableEq process.State] {origin : process.State}
    (real : State process origin Basic.Canonical.re) (oracle : Request process.State → Reply process) :
    ((fromReal real).protocol.run oracle).trace = [⟨.ball origin, oracle (.ball origin)⟩] := by
  unfold fromReal observeOrigin
  rw [Program.map_execution, Protocol.map_run_trace]
  unfold checked
  change ⟨.ball origin, oracle (.ball origin)⟩ ::
    (((if same : (oracle (.ball origin)).1 = .ball origin then
      (Program.pure (.ok (same ▸ (oracle (.ball origin)).2)) :
        Program (Request process.State) (Reply process)
          (Except (Invalid process.State) (Response process (.ball origin))))
    else .pure (.error ⟨.ball origin, (oracle (.ball origin)).1, same⟩)).protocol).run oracle).trace = _
  split <;> rfl

/-- A reply to another operation is reported and no later Gaussian operation is attempted. -/
theorem fromReal_invalid {process : Process} [DecidableEq process.State] {origin : process.State}
    (real : State process origin Basic.Canonical.re) (oracle : Request process.State → Reply process)
    (different : (oracle (.ball origin)).1 ≠ .ball origin) :
    ((fromReal real).protocol.run oracle).value =
      .error ⟨.ball origin, (oracle (.ball origin)).1, different⟩ := by
  unfold fromReal observeOrigin
  rw [Program.map_execution, Protocol.map_run_value]
  unfold checked
  change Except.map (assembleFromReal real)
    (((if same : (oracle (.ball origin)).1 = .ball origin then
      (Program.pure (.ok (same ▸ (oracle (.ball origin)).2)) :
        Program (Request process.State) (Reply process)
          (Except (Invalid process.State) (Response process (.ball origin))))
    else .pure (.error ⟨.ball origin, (oracle (.ball origin)).1, same⟩)).protocol).run oracle).value = _
  rw [dif_neg different]
  rfl

/-- Exact replay reconstructs the paired state without another origin-ball readback. -/
theorem fromReal_replay {process : Process} [DecidableEq process.State] {origin : process.State}
    (real : State process origin Basic.Canonical.re) :
    let program := fromReal real
    program.protocol.replayExact (program.protocol.run (original process)).trace =
      .ok (.ok ⟨Paired.fromReal real, rfl⟩) := by
  let program := fromReal real
  change program.protocol.replayExact (program.protocol.run (original process)).trace = _
  rw [program.protocol.replayExact_run, fromReal_original]

/-- Replies outside the displayed origin-ball request preserve the complete result and trace. -/
theorem fromReal_payload_erasure {process : Process} [DecidableEq process.State] {origin : process.State}
    (real : State process origin Basic.Canonical.re) {Payload : Type} (payload : Payload)
    (outside : Payload → Request process.State → Reply process) :
    let program := fromReal real
    program.protocol.run (Boundary.Trace.overlay (program.protocol.run (original process)).trace (outside payload)) =
      program.protocol.run (original process) :=
  (fromReal real).protocol.annotation_erasure (original process) payload outside

/-- Every possible reading of the returned real request remains possible at the prior shared state. -/
theorem realPrevious {process : Process} {origin : process.State} (paired : Paired process origin)
    (tolerance : Fraction.Rational) (positive : 0 < tolerance)
    (real : CertifiedState Norm.Coordinates.re_sub_sq_le_basic_normSq paired.realBase tolerance positive) :
    ∀ {value}, process.Possible real.val.current value → process.Possible paired.current value := by
  intro value possible
  have state_eq := congrArg (fun state : State process origin Basic.Canonical.re => state.current) real.property
  change real.val.current = process.refine paired.current ((tolerance / 4) ^ 2)
    (Fraction.Order.Arithmetic.pow_pos_direct (Bounds.Quarter.quarter_pos positive) 2) at state_eq
  rw [state_eq] at possible
  exact process.refine_persists paired.current _ _ possible

/-- Every possible reading of the returned imaginary request remains possible at its actual real predecessor. -/
theorem imaginaryPrevious {process : Process} {origin : process.State} (paired : Paired process origin)
    (realTolerance : Fraction.Rational) (realPositive : 0 < realTolerance)
    (real : CertifiedState Norm.Coordinates.re_sub_sq_le_basic_normSq paired.realBase realTolerance realPositive)
    (imaginaryTolerance : Fraction.Rational) (imaginaryPositive : 0 < imaginaryTolerance)
    (imaginary : CertifiedState Norm.Coordinates.im_sub_sq_le_basic_normSq
      (paired.imaginaryBase real.val (realPrevious paired realTolerance realPositive real))
      imaginaryTolerance imaginaryPositive) :
    ∀ {value}, process.Possible imaginary.val.current value → process.Possible real.val.current value := by
  intro value possible
  have state_eq := congrArg (fun state : State process origin Basic.Canonical.im => state.current) imaginary.property
  change imaginary.val.current = process.refine real.val.current ((imaginaryTolerance / 4) ^ 2)
    (Fraction.Order.Arithmetic.pow_pos_direct (Bounds.Quarter.quarter_pos imaginaryPositive) 2) at state_eq
  rw [state_eq] at possible
  exact process.refine_persists real.val.current _ _ possible

/-- A returned imaginary-only state remains possible at the original shared Gaussian state. -/
theorem imaginaryOnlyPrevious {process : Process} {origin : process.State} (paired : Paired process origin)
    (tolerance : Fraction.Rational) (positive : 0 < tolerance)
    (imaginary : CertifiedState Norm.Coordinates.im_sub_sq_le_basic_normSq paired.imaginaryAtCurrent
      tolerance positive) :
    ∀ {value}, process.Possible imaginary.val.current value → process.Possible paired.current value := by
  intro value possible
  have state_eq := congrArg (fun state : State process origin Basic.Canonical.im => state.current) imaginary.property
  change imaginary.val.current = process.refine paired.current ((tolerance / 4) ^ 2)
    (Fraction.Order.Arithmetic.pow_pos_direct (Bounds.Quarter.quarter_pos positive) 2) at state_eq
  rw [state_eq] at possible
  exact process.refine_persists paired.current _ _ possible

/-- A paired state certified as the original imaginary-only request. -/
abbrev CertifiedImaginary {process : Process} {origin : process.State} (paired : Paired process origin)
    (tolerance : Fraction.Rational) (positive : 0 < tolerance) :=
  {next : Paired process origin // next = paired.requestImaginary tolerance positive}

/-- Attach the returned imaginary state while retaining the exact original real coordinate. -/
@[expose] def assembleImaginary {process : Process} {origin : process.State} (paired : Paired process origin)
    (tolerance : Fraction.Rational) (positive : 0 < tolerance)
    (imaginary : CertifiedState Norm.Coordinates.im_sub_sq_le_basic_normSq paired.imaginaryAtCurrent
      tolerance positive) : CertifiedImaginary paired tolerance positive := by
  let result := paired.withImaginary imaginary.val (imaginaryOnlyPrevious paired tolerance positive imaginary)
  have same : result = paired.requestImaginary tolerance positive := by
    cases imaginary with
    | mk imaginary imaginary_eq =>
      cases imaginary_eq
      rfl
  exact ⟨result, same⟩

/-- Observe only the imaginary refinement and ball readback from the retained shared state. -/
@[expose] def imaginaryOnly {process : Process} [DecidableEq process.State] {origin : process.State}
    (saved : Paired process origin) (tolerance : Fraction.Rational) (positive : 0 < tolerance) :
    Program (Request process.State) (Reply process)
      (Except (Invalid process.State) (CertifiedImaginary saved tolerance positive)) :=
  (coordinate Norm.Coordinates.im_sub_sq_le_basic_normSq saved.imaginaryAtCurrent tolerance positive).map
    (fun result => result.map (assembleImaginary saved tolerance positive))

/-- Original execution retains the exact real state and the original imaginary-only result. -/
theorem imaginaryOnly_original {process : Process} [DecidableEq process.State] {origin : process.State}
    (saved : Paired process origin) (tolerance : Fraction.Rational) (positive : 0 < tolerance) :
    ((imaginaryOnly saved tolerance positive).protocol.run (original process)).value =
      .ok ⟨saved.requestImaginary tolerance positive, rfl⟩ := by
  unfold imaginaryOnly
  rw [Program.map_execution, Protocol.map_run_value, coordinate_original]
  apply congrArg Except.ok
  apply Subtype.ext
  exact (assembleImaginary saved tolerance positive _).property

/-- The imaginary-only observer records exactly one refinement and its actual ball readback. -/
theorem imaginaryOnly_trace {process : Process} [DecidableEq process.State] {origin : process.State}
    (saved : Paired process origin) (tolerance : Fraction.Rational) (positive : 0 < tolerance) :
    ((imaginaryOnly saved tolerance positive).protocol.run (original process)).trace =
      [⟨refinementRequest saved.imaginaryAtCurrent tolerance positive,
          original process (refinementRequest saved.imaginaryAtCurrent tolerance positive)⟩,
        ⟨.ball (saved.requestImaginary tolerance positive).current,
          original process (.ball (saved.requestImaginary tolerance positive).current)⟩] := by
  unfold imaginaryOnly
  rw [Program.map_execution, Protocol.map_run_trace, coordinate_original_trace]
  rfl

/-- Exact replay recovers the same imaginary-only result without repeating either original process call. -/
theorem imaginaryOnly_replay {process : Process} [DecidableEq process.State] {origin : process.State}
    (saved : Paired process origin) (tolerance : Fraction.Rational) (positive : 0 < tolerance) :
    let program := imaginaryOnly saved tolerance positive
    program.protocol.replayExact (program.protocol.run (original process)).trace =
      .ok (.ok ⟨saved.requestImaginary tolerance positive, rfl⟩) := by
  let program := imaginaryOnly saved tolerance positive
  change program.protocol.replayExact (program.protocol.run (original process)).trace = _
  rw [program.protocol.replayExact_run, imaginaryOnly_original]

/-- Replies outside the displayed imaginary-only requests preserve the complete result and ordered trace. -/
theorem imaginaryOnly_payload_erasure {process : Process} [DecidableEq process.State] {origin : process.State}
    (saved : Paired process origin) (tolerance : Fraction.Rational) (positive : 0 < tolerance)
    {Payload : Type} (payload : Payload) (outside : Payload → Request process.State → Reply process) :
    let program := imaginaryOnly saved tolerance positive
    program.protocol.run (Boundary.Trace.overlay (program.protocol.run (original process)).trace (outside payload)) =
      program.protocol.run (original process) :=
  (imaginaryOnly saved tolerance positive).protocol.annotation_erasure (original process) payload outside

/-- A paired state certified as the exact request from its original shared Gaussian predecessor. -/
abbrev CertifiedPaired {process : Process} {origin : process.State} (paired : Paired process origin)
    (realTolerance : Fraction.Rational) (realPositive : 0 < realTolerance)
    (imaginaryTolerance : Fraction.Rational) (imaginaryPositive : 0 < imaginaryTolerance) :=
  {next : Paired process origin //
    next = paired.request realTolerance realPositive imaginaryTolerance imaginaryPositive}

/-- Assemble the paired result from the two actual returned coordinate states. -/
@[expose] def assemblePaired {process : Process} {origin : process.State} (paired : Paired process origin)
    (realTolerance : Fraction.Rational) (realPositive : 0 < realTolerance)
    (real : CertifiedState Norm.Coordinates.re_sub_sq_le_basic_normSq paired.realBase realTolerance realPositive)
    (imaginaryTolerance : Fraction.Rational) (imaginaryPositive : 0 < imaginaryTolerance)
    (imaginary : CertifiedState Norm.Coordinates.im_sub_sq_le_basic_normSq
      (paired.imaginaryBase real.val (realPrevious paired realTolerance realPositive real))
      imaginaryTolerance imaginaryPositive) :
    CertifiedPaired paired realTolerance realPositive imaginaryTolerance imaginaryPositive := by
  let result : Paired process origin :=
    { real := real.val
      imaginary := imaginary.val
      current := imaginary.val.current
      real_persists := imaginaryPrevious paired realTolerance realPositive real imaginaryTolerance imaginaryPositive
        imaginary
      imaginary_persists := fun possible => possible }
  have same : result = paired.request realTolerance realPositive imaginaryTolerance imaginaryPositive := by
    cases real with
    | mk real real_eq =>
      cases real_eq
      cases imaginary with
      | mk imaginary imaginary_eq =>
        cases imaginary_eq
        rfl
  exact ⟨result, same⟩

/-- Observe the actual paired Gaussian request, using the returned real state as the imaginary predecessor. -/
@[expose] def paired {process : Process} [DecidableEq process.State] {origin : process.State}
    (saved : Paired process origin) (realTolerance : Fraction.Rational) (realPositive : 0 < realTolerance)
    (imaginaryTolerance : Fraction.Rational) (imaginaryPositive : 0 < imaginaryTolerance) :
    Program (Request process.State) (Reply process)
      (Except (Invalid process.State) (CertifiedPaired saved realTolerance realPositive imaginaryTolerance
        imaginaryPositive)) :=
  (coordinate Norm.Coordinates.re_sub_sq_le_basic_normSq saved.realBase realTolerance realPositive).bind fun real =>
    match real with
    | .error invalid => .pure (.error invalid)
    | .ok realNext =>
        (coordinate Norm.Coordinates.im_sub_sq_le_basic_normSq
          (saved.imaginaryBase realNext.val (realPrevious saved realTolerance realPositive realNext))
          imaginaryTolerance imaginaryPositive).map fun imaginary =>
            imaginary.map (assemblePaired saved realTolerance realPositive realNext
              imaginaryTolerance imaginaryPositive)

/-- Original-source execution returns the complete paired state built from the same two actual refinements. -/
theorem paired_original {process : Process} [DecidableEq process.State] {origin : process.State}
    (saved : Paired process origin) (realTolerance : Fraction.Rational) (realPositive : 0 < realTolerance)
    (imaginaryTolerance : Fraction.Rational) (imaginaryPositive : 0 < imaginaryTolerance) :
    ((paired saved realTolerance realPositive imaginaryTolerance imaginaryPositive).protocol.run
      (original process)).value =
      .ok ⟨saved.request realTolerance realPositive imaginaryTolerance imaginaryPositive, rfl⟩ := by
  unfold paired
  rw [Program.bind_execution, Protocol.bind_run_value, coordinate_original]
  rw [Program.map_execution, Protocol.map_run_value, coordinate_original]
  apply congrArg Except.ok
  apply Subtype.ext
  exact (assemblePaired saved realTolerance realPositive _ imaginaryTolerance imaginaryPositive _).property

/-- The paired trace is the real request trace followed by the imaginary trace from that returned real state. -/
theorem paired_original_trace {process : Process} [DecidableEq process.State] {origin : process.State}
    (saved : Paired process origin) (realTolerance : Fraction.Rational) (realPositive : 0 < realTolerance)
    (imaginaryTolerance : Fraction.Rational) (imaginaryPositive : 0 < imaginaryTolerance) :
    let real := State.request Norm.Coordinates.re_sub_sq_le_basic_normSq saved.realBase realTolerance realPositive
    let certified : CertifiedState Norm.Coordinates.re_sub_sq_le_basic_normSq saved.realBase realTolerance
      realPositive := ⟨real, rfl⟩
    ((paired saved realTolerance realPositive imaginaryTolerance imaginaryPositive).protocol.run
      (original process)).trace =
      ((coordinate Norm.Coordinates.re_sub_sq_le_basic_normSq saved.realBase realTolerance realPositive).protocol.run
        (original process)).trace ++
      ((coordinate Norm.Coordinates.im_sub_sq_le_basic_normSq
        (saved.imaginaryBase real (realPrevious saved realTolerance realPositive certified))
        imaginaryTolerance imaginaryPositive).protocol.run (original process)).trace := by
  unfold paired
  rw [Program.bind_execution, Protocol.bind_run_trace, coordinate_original]
  dsimp only
  rw [Program.map_execution, Protocol.map_run_trace]

/-- Return the original paired state from the actual two coordinate requests. -/
@[expose] def computation {process : Process} [DecidableEq process.State] {origin : process.State}
    (saved : Paired process origin) (realTolerance : Fraction.Rational) (realPositive : 0 < realTolerance)
    (imaginaryTolerance : Fraction.Rational) (imaginaryPositive : 0 < imaginaryTolerance) :
    Program (Request process.State) (Reply process) (Except (Invalid process.State) (Paired process origin)) :=
  (paired saved realTolerance realPositive imaginaryTolerance imaginaryPositive).map
    (fun result => result.map Subtype.val)

/-- Original-source execution returns the complete actual paired Gaussian state. -/
theorem computation_original {process : Process} [DecidableEq process.State] {origin : process.State}
    (saved : Paired process origin) (realTolerance : Fraction.Rational) (realPositive : 0 < realTolerance)
    (imaginaryTolerance : Fraction.Rational) (imaginaryPositive : 0 < imaginaryTolerance) :
    ((computation saved realTolerance realPositive imaginaryTolerance imaginaryPositive).protocol.run
      (original process)).value =
        .ok (saved.request realTolerance realPositive imaginaryTolerance imaginaryPositive) := by
  unfold computation
  rw [Program.map_execution, Protocol.map_run_value, paired_original]
  rfl

/-- A paired request makes exactly two refinement requests and two corresponding ball readbacks. -/
theorem computation_original_count {process : Process} [DecidableEq process.State] {origin : process.State}
    (saved : Paired process origin) (realTolerance : Fraction.Rational) (realPositive : 0 < realTolerance)
    (imaginaryTolerance : Fraction.Rational) (imaginaryPositive : 0 < imaginaryTolerance) :
    ((computation saved realTolerance realPositive imaginaryTolerance imaginaryPositive).protocol.run
      (original process)).trace.length = 4 := by
  unfold computation
  rw [Program.map_execution, Protocol.map_run_trace, paired_original_trace]
  rw [coordinate_original_trace, coordinate_original_trace]
  rfl

/-- Exact replay returns the complete paired state without repeating either refinement or ball readback. -/
theorem computation_replay {process : Process} [DecidableEq process.State] {origin : process.State}
    (saved : Paired process origin) (realTolerance : Fraction.Rational) (realPositive : 0 < realTolerance)
    (imaginaryTolerance : Fraction.Rational) (imaginaryPositive : 0 < imaginaryTolerance) :
    let program := computation saved realTolerance realPositive imaginaryTolerance imaginaryPositive
    program.protocol.replayExact (program.protocol.run (original process)).trace =
      .ok (.ok (saved.request realTolerance realPositive imaginaryTolerance imaginaryPositive)) := by
  let program := computation saved realTolerance realPositive imaginaryTolerance imaginaryPositive
  change program.protocol.replayExact (program.protocol.run (original process)).trace = _
  rw [program.protocol.replayExact_run, computation_original]

/-- Replies outside the actual paired request trace preserve its complete result and ordered source trace. -/
theorem payload_erasure {process : Process} [DecidableEq process.State] {origin : process.State}
    (saved : Paired process origin) (realTolerance : Fraction.Rational) (realPositive : 0 < realTolerance)
    (imaginaryTolerance : Fraction.Rational) (imaginaryPositive : 0 < imaginaryTolerance)
    {Payload : Type} (payload : Payload) (outside : Payload → Request process.State → Reply process) :
    let program := computation saved realTolerance realPositive imaginaryTolerance imaginaryPositive
    program.protocol.run (Boundary.Trace.overlay (program.protocol.run (original process)).trace (outside payload)) =
      program.protocol.run (original process) :=
  (computation saved realTolerance realPositive imaginaryTolerance imaginaryPositive).protocol.annotation_erasure
    (original process) payload outside

end Purelib.Approximation.Gaussian.Process.Coordinate.Observation

end
