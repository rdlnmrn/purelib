module

public import Purelib.Integration.Exponential.Real
public import Purelib.Integration.Cell.Numerical.Continuous.Observation.Continuation
public import Purelib.Approximation.Gaussian.Exponential.Horner.Real.State
public import Purelib.Approximation.Gaussian.Process.Coordinate.Observation
public import Purelib.Computation.Query.Program
import Purelib.Approximation.Bound.Process
import Purelib.Approximation.Gaussian.Sequence.Process
import Purelib.Integration.Cell.Numerical
import Purelib.Integration.Cell.Numerical.Common.Observation
import Purelib.Integration.Cell.Numerical.Continuous.Observation
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Gaussian operations behind real exponential point requests

Each rational unit tag owns its original finite Gaussian Horner process.
Displayed requests retain that tag together with the exact refinement or ball
readback. Checked responses cannot silently change the point or operation.
-/

public section

namespace Purelib.Integration.Exponential.Real.Observation

open Purelib.Approximation
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Exponential
open Purelib.Approximation.Gaussian.Process
open Purelib.Computation.Query
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Integration.NumericalFrontier
open Purelib.Integration.NumericalFrontier.Continuous
open Purelib.Integration.NumericalFrontier.Continuous.Observation

/-- An original rational exponential point inside the unit integration interval. -/
abbrev Point := {point : Fraction.Rational // 0 ≤ point ∧ point ≤ 1}

/-- The exact Gaussian finite process attached to an original rational unit point. -/
@[expose] def process (point : Point) : Gaussian.Process :=
  (Horner.Real.approximation point.val point.property).toProcess

/-- The original finite Gaussian process index has executable equality. -/
instance processStateDecidableEq (point : Point) : DecidableEq (process point).State :=
  Sequence.ApproximationData.stateDecidableEq (Horner.Real.approximation point.val point.property)

/-- A tagged original Gaussian refinement or ball readback. -/
abbrev Query := Point × Coordinate.Observation.Request Nat

/-- A reply retains the rational point owning its original Gaussian operation. -/
abbrev Reply := Σ point : Point, Coordinate.Observation.Reply (process point)

set_option genInjectivity false in
/-- A Gaussian reply identifies a different rational point or a different original operation. -/
inductive Failure where
  /-- The reply belongs to a different rational point. -/
  | point (requested reported : Point) (different : reported ≠ requested)
  /-- The returned operation is not the original refinement or ball request. -/
  | operation (point : Point) (invalid : Coordinate.Observation.Invalid Nat)

constructive_injectivity Failure

/-- Execute the original finite Gaussian operation at its retained rational point. -/
@[expose] def original (query : Query) : Reply :=
  ⟨query.1, Coordinate.Observation.original (process query.1) query.2⟩

/-- Display one Gaussian operation and reject a response owned by another rational point. -/
@[expose] def pointHandler (point : Point) (question : Coordinate.Observation.Request Nat) :
    Program Query Reply (Except Failure (Coordinate.Observation.Reply (process point))) :=
  .request (point, question) fun reply =>
    if same : reply.1 = point then .pure (.ok (same ▸ reply.2))
    else .pure (.error (.point point reply.1 same))

/-- Check one tagged Gaussian reply through a caller's original outer handler. -/
@[expose] def pointWith {OuterQuestion OuterReply Error : Type}
    (point : Point) (handler : Query → Program OuterQuestion OuterReply (Except Error Reply))
    (invalid : Failure → Error) (operation : Coordinate.Observation.Request Nat) :
    Program OuterQuestion OuterReply (Except Error (Coordinate.Observation.Reply (process point))) :=
  ((pointHandler point operation).substituteChecked handler).map fun result =>
    match result with
    | .error error => .error error
    | .ok execution => execution.value.mapError invalid

/-- Check one actual Gaussian operation through a caller's tagged outer handler.

The same original point and operation checks reject wrong owners or replies;
the returned state or ball remains indexed by that exact operation. -/
@[expose] def checkedWith {OuterQuestion OuterReply Error : Type}
    (point : Point) (handler : Query → Program OuterQuestion OuterReply (Except Error Reply))
    (invalid : Failure → Error) (operation : Coordinate.Observation.Request (process point).State) :
    Program OuterQuestion OuterReply (Except Error (Coordinate.Observation.Response (process point) operation)) :=
  ((Coordinate.Observation.checked (process point) operation).substituteChecked (pointWith point handler invalid)).map
    fun result => match result with
      | .error error => .error error
      | .ok execution => execution.value.mapError (fun error => invalid (.operation point error))

/-- Original Gaussian execution returns the reply owned by the requested point and operation. -/
theorem pointHandler_original (point : Point) (question : Coordinate.Observation.Request Nat) :
    ((pointHandler point question).protocol.run original).value =
      .ok (Coordinate.Observation.original (process point) question) := by
  unfold pointHandler
  change (((if same : (original (point, question)).1 = point then
    (Program.pure (.ok (same ▸ (original (point, question)).2)) :
      Program Query Reply (Except Failure (Coordinate.Observation.Reply (process point))))
    else Program.pure (.error (.point point (original (point, question)).1 same))).protocol).run original).value = _
  have same : (original (point, question)).1 = point := rfl
  rw [dif_pos same]
  rfl

/-- A checked tagged reply records exactly its original question and actual reply. -/
theorem pointHandler_trace (point : Point) (question : Coordinate.Observation.Request Nat) (oracle : Query → Reply) :
    ((pointHandler point question).protocol.run oracle).trace =
      [⟨(point, question), oracle (point, question)⟩] := by
  unfold pointHandler
  change ⟨(point, question), oracle (point, question)⟩ ::
    ((if same : (oracle (point, question)).1 = point then
      (Program.pure (.ok (same ▸ (oracle (point, question)).2)) :
        Program Query Reply (Except Failure (Coordinate.Observation.Reply (process point))))
    else .pure (.error (.point point (oracle (point, question)).1 same))).protocol.run oracle).trace = _
  by_cases same : (oracle (point, question)).1 = point
  · rw [dif_pos same]
    rfl
  · rw [dif_neg same]
    rfl

/-- Original outer replies return the exact original point-owned Gaussian reply. -/
theorem pointWith_original {OuterQuestion OuterReply Error : Type} [DecidableEq OuterQuestion]
    (point : Point) (handler : Query → Program OuterQuestion OuterReply (Except Error Reply))
    (invalid : Failure → Error) (operation : Coordinate.Observation.Request (process point).State)
    (oracle : OuterQuestion → OuterReply)
    (answers : ∀ question, ((handler question).protocol.run oracle).value = .ok (original question)) :
    ((pointWith point handler invalid operation).protocol.run oracle).value =
      .ok (Coordinate.Observation.original (process point) operation) := by
  unfold pointWith
  rw [Program.map_execution, Protocol.map_run_value]
  rw [Program.substituteChecked_value handler (pointHandler point operation) oracle original answers]
  dsimp only
  rw [pointHandler_original]
  rfl

/-- Original outer replies return the exact response of the original Gaussian operation. -/
theorem checkedWith_original {OuterQuestion OuterReply Error : Type} [DecidableEq OuterQuestion]
    (point : Point) (handler : Query → Program OuterQuestion OuterReply (Except Error Reply))
    (invalid : Failure → Error) (operation : Coordinate.Observation.Request (process point).State)
    (oracle : OuterQuestion → OuterReply)
    (answers : ∀ question, ((handler question).protocol.run oracle).value = .ok (original question)) :
    ((checkedWith point handler invalid operation).protocol.run oracle).value =
      .ok (Coordinate.Observation.original_request (process point) operation ▸
        (Coordinate.Observation.original (process point) operation).2) := by
  unfold checkedWith
  rw [Program.map_execution, Protocol.map_run_value]
  rw [Program.substituteChecked_value (pointWith point handler invalid)
    (Coordinate.Observation.checked (process point) operation) oracle (Coordinate.Observation.original (process point))
    (pointWith_original point handler invalid · oracle answers)]
  dsimp only
  exact congrArg (Except.mapError (fun invalidOperation => invalid (.operation point invalidOperation)))
    (Coordinate.Observation.checked_original (process point) operation)

/-- A tagged point check records exactly the original requested operation. -/
theorem pointWith_trace {OuterQuestion OuterReply Error : Type} [DecidableEq OuterQuestion]
    (point : Point) (handler : Query → Program OuterQuestion OuterReply (Except Error Reply))
    (invalid : Failure → Error) (operation : Coordinate.Observation.Request Nat)
    (oracle : OuterQuestion → OuterReply) :
    ((pointWith point handler invalid operation).protocol.run oracle).trace =
      ((handler (point, operation)).protocol.run oracle).trace := by
  let next : Reply → Program Query Reply
      (Except Failure (Coordinate.Observation.Reply (process point))) := fun reply =>
    if same : reply.1 = point then .pure (.ok (same ▸ reply.2))
    else .pure (.error (.point point reply.1 same))
  have empty (reply : Reply) :
      (((next reply).substituteChecked handler).protocol.run oracle).trace = [] := by
    dsimp only [next]
    by_cases same : reply.1 = point
    · rw [dif_pos same]
      rfl
    · rw [dif_neg same]
      rfl
  have actual := Program.substituteChecked_request_trace handler
    (point, operation) next oracle empty
  unfold pointWith pointHandler
  rw [Program.map_execution, Protocol.map_run_trace]
  exact actual

/-- A checked tagged Gaussian operation records exactly its one requested reply. -/
theorem checkedWith_trace {OuterQuestion OuterReply Error : Type} [DecidableEq OuterQuestion]
    (point : Point) (handler : Query → Program OuterQuestion OuterReply (Except Error Reply))
    (invalid : Failure → Error) (operation : Coordinate.Observation.Request (process point).State)
    (oracle : OuterQuestion → OuterReply) :
    ((checkedWith point handler invalid operation).protocol.run oracle).trace =
      ((handler (point, operation)).protocol.run oracle).trace := by
  let next : Coordinate.Observation.Reply (process point) →
      Program (Coordinate.Observation.Request (process point).State)
        (Coordinate.Observation.Reply (process point))
        (Except (Coordinate.Observation.Invalid (process point).State)
          (Coordinate.Observation.Response (process point) operation)) := fun reply =>
    if same : reply.1 = operation then .pure (.ok (same ▸ reply.2))
    else .pure (.error ⟨operation, reply.1, same⟩)
  have empty (reply : Coordinate.Observation.Reply (process point)) :
      (((next reply).substituteChecked (pointWith point handler invalid)).protocol.run oracle).trace = [] := by
    dsimp only [next]
    by_cases same : reply.1 = operation
    · rw [dif_pos same]
      rfl
    · rw [dif_neg same]
      rfl
  have actual := Program.substituteChecked_request_trace (pointWith point handler invalid) operation next oracle empty
  unfold checkedWith Coordinate.Observation.checked
  rw [Program.map_execution, Protocol.map_run_trace]
  exact actual.trans (pointWith_trace point handler invalid operation oracle)


/-- Observe the original real-coordinate request through its tagged Gaussian operations.

The returned execution retains the coordinate request's original ordered
refinement and ball replies. A wrong point stops before later operations. -/
@[expose] def coordinate (point : Point) (previous : Coordinate.State (process point) (0 : Nat) Basic.Canonical.re)
    (request : AccuracyRequest) :=
  (Coordinate.Observation.coordinate Norm.Coordinates.re_sub_sq_le_basic_normSq previous
    request.tolerance request.positive).substituteChecked (pointHandler point)

/-- Original tagged Gaussian replies retain the complete original coordinate execution. -/
theorem coordinate_original (point : Point)
    (previous : Coordinate.State (process point) (0 : Nat) Basic.Canonical.re) (request : AccuracyRequest) :
    ((coordinate point previous request).protocol.run original).value =
      .ok ((Coordinate.Observation.coordinate Norm.Coordinates.re_sub_sq_le_basic_normSq previous
        request.tolerance request.positive).protocol.run (Coordinate.Observation.original (process point))) := by
  unfold coordinate
  apply Program.substituteChecked_value
  intro question
  exact pointHandler_original point question

/-- Exact replay preserves the original coordinate execution without repeating Gaussian operations. -/
theorem coordinate_replay (point : Point)
    (previous : Coordinate.State (process point) (0 : Nat) Basic.Canonical.re) (request : AccuracyRequest) :
    (coordinate point previous request).protocol.replayExact
      ((coordinate point previous request).protocol.run original).trace =
        .ok (.ok ((Coordinate.Observation.coordinate Norm.Coordinates.re_sub_sq_le_basic_normSq previous
          request.tolerance request.positive).protocol.run (Coordinate.Observation.original (process point)))) := by
  rw [(coordinate point previous request).protocol.replayExact_run, coordinate_original]

/-- Return the actual coordinate state and its cached interval to the original numerical point request.

The exact source-owner equality transports the same returned state; the
reading is its already constructed coordinate interval. No refinement or
Gaussian ball readback is repeated. -/
@[expose] def requestReply (point : Point) (previous : (Horner.Real.source point.val).State)
    (request : AccuracyRequest)
    (next : Coordinate.Observation.CertifiedState Norm.Coordinates.re_sub_sq_le_basic_normSq
      (Horner.Real.originalState point.val point.property previous) request.tolerance request.positive) :
    (NumericalPoint.Selection.request previous :
      NumericalPoint.Selection Horner.Real.source point.val request).Reply := by
  let same := Horner.Real.source_eq_unit point.val point.property
  let state : (Horner.Real.source point.val).State := same.symm ▸ next.val
  have nextEq : next.val = (Horner.Real.unitProcess point.val point.property).request
      (same ▸ previous) request.tolerance request.positive := next.property
  have stateEq : state = (Horner.Real.source point.val).request previous request.tolerance request.positive :=
    (congrArg (fun value : (Horner.Real.unitProcess point.val point.property).State => same.symm ▸ value) nextEq).trans
      (BoundProcess.request_transport _ _ same previous request.tolerance request.positive)
  have readingEq : next.val.interval = (Horner.Real.source point.val).bound state :=
    BoundProcess.bound_transport _ _ same.symm next.val
  exact ⟨⟨state, stateEq⟩, ⟨next.val.interval, readingEq⟩⟩

/-- The original state and cached interval for one selected numerical point branch. -/
@[expose] def originalSelectionReply (point : Point) (request : AccuracyRequest) :
    (choice : NumericalPoint.Selection Horner.Real.source point.val request) → choice.Reply
  | .reuse _ _ _ => ()
  | .request previous =>
      let state := (Horner.Real.source point.val).request previous request.tolerance request.positive
      let reading := (Horner.Real.source point.val).bound state
      ⟨⟨state, rfl⟩, ⟨reading, rfl⟩⟩

/-- Certified replies for one original point branch have the same state and cached reading. -/
theorem selectionReply_unique (point : Point) (request : AccuracyRequest)
    (choice : NumericalPoint.Selection Horner.Real.source point.val request) (left right : choice.Reply) :
    left = right := by
  cases choice with
  | reuse retained same accurate =>
      cases left
      cases right
      rfl
  | request previous =>
      rcases left with ⟨⟨leftState, leftStateEq⟩, ⟨leftReading, leftReadingEq⟩⟩
      rcases right with ⟨⟨rightState, rightStateEq⟩, ⟨rightReading, rightReadingEq⟩⟩
      have states : leftState = rightState := leftStateEq.trans rightStateEq.symm
      cases states
      have readings : leftReading = rightReading := leftReadingEq.trans rightReadingEq.symm
      cases readings
      rfl

namespace Progress

/-- The exact original numerical predecessor selected at a rational point. -/
@[expose] def Previous (point : Point) := (Horner.Real.source point.val).State

/-- The exact bank-selection branch that requested this predecessor. -/
@[expose] def Selected (point : Point) (request : AccuracyRequest)
    (choice : NumericalPoint.Selection Horner.Real.source point.val request) (previous : Previous point) : Prop :=
  choice = .request previous

/-- The original Gaussian refinement response for that selected predecessor. -/
@[expose] def Refined (point : Point) (request : AccuracyRequest) (previous : Previous point) :=
  Coordinate.Observation.ReturnedState (Horner.Real.originalState point.val point.property previous)
    request.tolerance request.positive

section
attribute [local irreducible] Previous Selected Refined

set_option genInjectivity false in
/-- An actual returned refinement and the exact original selected predecessor. -/
structure Pending (point : Point) (request : AccuracyRequest)
    (choice : NumericalPoint.Selection Horner.Real.source point.val request) (Error : Type) where
  /-- The original numerical state supplied to the actual request. -/ previous : Previous point
  /-- The retained point decision requested that exact predecessor. -/ selected : Selected point request choice previous
  /-- The Gaussian state returned by the original refinement. -/ refined : Refined point request previous
  /-- The point, operation or outer-handler failure that interrupted the ball. -/ reason : Error

constructive_injectivity Pending

set_option genInjectivity false in
/-- A failed point decision, retaining its intermediate refinement when available. -/
inductive SelectionFailure (point : Point) (request : AccuracyRequest)
    (choice : NumericalPoint.Selection Horner.Real.source point.val request) (Error : Type) where
  /-- No refinement response was returned. -/ | initial (reason : Error)
  /-- The refinement succeeded and its ball read failed. -/ | pending (receipt : Pending point request choice Error)

constructive_injectivity SelectionFailure
end

/-- Forward a tagged Gaussian question to the same original reply surface. -/
@[expose] def forward (question : Query) : Program Query Reply (Except Failure Reply) :=
  .request question fun reply => .pure (.ok reply)

/-- Direct forwarding preserves the complete point-handler execution for every tagged oracle. -/
theorem pointWith_forward (point : Point) (operation : Coordinate.Observation.Request Nat)
    (oracle : Query → Reply) :
    ((pointWith point forward id operation).protocol.run oracle) =
      ((pointHandler point operation).protocol.run oracle) := by
  apply Basic.Execution.ext
  · unfold pointWith
    rw [Program.map_execution, Protocol.map_run_value]
    rw [Program.substituteChecked_value forward (pointHandler point operation) oracle oracle (fun _ => rfl)]
    dsimp only
    cases ((pointHandler point operation).protocol.run oracle).value <;> rfl
  · rw [pointWith_trace]
    change ([(⟨(point, operation), oracle (point, operation)⟩ : Basic.Exchange Query Reply)] :
      Basic.Trace Query Reply) = _
    exact (pointHandler_trace point operation oracle).symm

/-- Direct checked Gaussian operations preserve the original point and operation checks for every oracle. -/
theorem checkedWith_forward (point : Point) (operation : Coordinate.Observation.Request (process point).State)
    (oracle : Query → Reply) :
    ((checkedWith point forward id operation).protocol.run oracle) =
      ((((Coordinate.Observation.checked (process point) operation).substituteChecked (pointHandler point)).map
        fun result => match result with
          | .error error => Except.error error
          | .ok execution => execution.value.mapError (fun error => Failure.operation point error)).protocol.run
            oracle) := by
  unfold checkedWith
  rw [Program.map_execution, Program.map_execution]
  dsimp only [id]
  have same := Program.substituteChecked_handlers_eq (pointWith point forward id) (pointHandler point)
    (Coordinate.Observation.checked (process point) operation) oracle (pointWith_forward point · oracle)
  apply Basic.Execution.ext
  · rw [Protocol.map_run_value, Protocol.map_run_value, same]
    cases result : (((Coordinate.Observation.checked (process point) operation).substituteChecked
      (pointHandler point)).protocol.run oracle).value with
    | error error => rfl
    | ok execution => cases execution.value <;> rfl
  · rw [Protocol.map_run_trace, Protocol.map_run_trace, same]

/-- The original tagged interpretation of one checked coordinate operation. -/
private def oldOperation (point : Point) (operation : Coordinate.Observation.Request (process point).State) :
    Program Query Reply (Except Failure (Coordinate.Observation.Response (process point) operation)) :=
  ((Coordinate.Observation.checked (process point) operation).substituteChecked (pointHandler point)).map fun result =>
    match result with
    | .error error => .error error
    | .ok execution => execution.value.mapError (Failure.operation point)

/-- The new and original operation interpreters give the same actual coordinate execution. -/
private theorem coordinateWith_oldOperation (point : Point)
    (state : Coordinate.State (process point) (0 : Nat) Basic.Canonical.re) (request : AccuracyRequest)
    (oracle : Query → Reply) :
    ((Coordinate.Observation.coordinateWith (checkedWith point forward id)
      Norm.Coordinates.re_sub_sq_le_basic_normSq state request.tolerance request.positive).protocol.run oracle) =
    ((Coordinate.Observation.coordinateWith (oldOperation point)
      Norm.Coordinates.re_sub_sq_le_basic_normSq state request.tolerance request.positive).protocol.run oracle) := by
  apply Coordinate.Observation.coordinateWith_run_eq
  intro operation
  exact checkedWith_forward point operation oracle

/-- Project the original failure from a coordinate request. -/
private def oldFailure {point : Point} {origin : (process point).State}
    {read : Basic.Canonical → Fraction.Rational}
    {state : Coordinate.State (process point) origin read} {request : AccuracyRequest} :
    Coordinate.Observation.CoordinateFailure state request.tolerance request.positive Failure → Failure
  | .refinement error => error
  | .ball _ error => error

/-- Original whole-coordinate substitution has the same value and ordered trace as its checked operations. -/
private theorem oldCoordinate_execution (point : Point)
    (state : Coordinate.State (process point) (0 : Nat) Basic.Canonical.re) (request : AccuracyRequest)
    (oracle : Query → Reply) :
    (((coordinate point state request).map fun result => match result with
      | .error error => Except.error error
      | .ok execution => execution.value.mapError (Failure.operation point)).protocol.run oracle) =
    (((Coordinate.Observation.coordinateWith (oldOperation point) Norm.Coordinates.re_sub_sq_le_basic_normSq
        state request.tolerance request.positive).map fun result => result.mapError oldFailure).protocol.run
      oracle) := by
  let collapse (result : Except
      (Coordinate.Observation.CoordinateFailure state request.tolerance request.positive
        (Coordinate.Observation.Invalid (process point).State))
      (Coordinate.Observation.CertifiedState Norm.Coordinates.re_sub_sq_le_basic_normSq
        state request.tolerance request.positive)) :=
    match result with
    | .error (.refinement invalid) => Except.error invalid
    | .error (.ball _ invalid) => Except.error invalid
    | .ok next => Except.ok next
  let flatten (result : Except Failure (Except (Coordinate.Observation.Invalid (process point).State)
      (Coordinate.Observation.CertifiedState Norm.Coordinates.re_sub_sq_le_basic_normSq
        state request.tolerance request.positive))) :=
    match result with
    | .error error => Except.error error
    | .ok inner => inner.mapError (Failure.operation point)
  let prog := Coordinate.Observation.coordinateWith (Coordinate.Observation.checked (process point))
    Norm.Coordinates.re_sub_sq_le_basic_normSq state request.tolerance request.positive
  let first := Coordinate.Observation.checked (process point)
    (Coordinate.Observation.refinementRequest state request.tolerance request.positive)
  let view (result : Except Failure (Except
      (Coordinate.Observation.CoordinateFailure state request.tolerance request.positive
        (Coordinate.Observation.Invalid (process point).State))
      (Coordinate.Observation.CertifiedState Norm.Coordinates.re_sub_sq_le_basic_normSq
        state request.tolerance request.positive))) := flatten (result.map collapse)
  unfold coordinate Coordinate.Observation.coordinate
  rw [Program.map_execution]
  refine (Protocol.map_execution_pointwise _ (fun result => flatten (result.map fun execution => execution.value))
    _ oracle ?_).trans ?_
  · dsimp only [flatten]
    split <;> rename_i value same <;> rw [same] <;> rfl
  · rw [← Program.map_execution]
    refine (Program.substituteChecked_map_pointwise_view_execution
      (pointHandler point) _ _ collapse ?_ flatten oracle).trans ?_
    · intro value
      cases value with
      | error error => cases error <;> rfl
      | ok next => rfl
    refine (Program.substituteChecked_map_map_execution (pointHandler point) prog collapse flatten oracle).trans ?_
    let runner := prog.substituteChecked (pointHandler point)
    have normalized : (((runner.map fun result => result.map (fun execution => collapse execution.value)).map
        flatten).protocol.run oracle) =
        ((runner.map fun result => view (result.map (fun execution => execution.value))).protocol.run oracle) := by
      apply Basic.Execution.ext
      · rw [Program.map_execution, Protocol.map_run_value, Program.map_execution, Protocol.map_run_value,
          Program.map_execution, Protocol.map_run_value]
        cases ((runner.protocol.run oracle).value) <;> rfl
      · rw [Program.map_execution, Protocol.map_run_trace, Program.map_execution, Protocol.map_run_trace,
          Program.map_execution, Protocol.map_run_trace]
    refine normalized.trans ?_
    dsimp only [runner, prog, Coordinate.Observation.coordinateWith]
    refine (Program.substituteChecked_bind_map_execution (pointHandler point) _ _ view oracle).trans ?_
    apply Basic.Execution.ext
    · rw [Program.map_execution, Protocol.map_run_value, Program.bind_execution, Protocol.bind_run_value,
        Program.map_execution, Protocol.map_run_value, Program.bind_execution, Protocol.bind_run_value]
      unfold oldOperation
      rw [Program.map_execution, Protocol.map_run_value]
      cases returned : ((first.substituteChecked (pointHandler point)).protocol.run oracle).value with
      | error error => rfl
      | ok execution =>
          cases checked : execution.value with
          | error invalid => dsimp only; rw [checked]; rfl
          | ok next =>
              dsimp only
              rw [checked]
              dsimp only [Except.mapError]
              rw [Program.map_execution, Protocol.map_run_value]
              rw [Program.map_execution, Protocol.map_run_value, Program.map_execution, Protocol.map_run_value]
              let ball := Coordinate.Observation.checked (process point) (.ball next.val)
              have ballValue (function : Except (Coordinate.Observation.Invalid (process point).State)
                  (Coordinate.Observation.Response (process point) (.ball next.val)) →
                  Except (Coordinate.Observation.CoordinateFailure state request.tolerance request.positive
                    (Coordinate.Observation.Invalid (process point).State))
                    (Coordinate.Observation.CertifiedState Norm.Coordinates.re_sub_sq_le_basic_normSq
                      state request.tolerance request.positive)) := by
                have ballDist := Program.substituteChecked_map_map_execution
                  (pointHandler point) ball function view oracle
                have result := congrArg Basic.Execution.value ballDist
                rw [Program.map_execution, Protocol.map_run_value, Program.map_execution, Protocol.map_run_value,
                  Program.map_execution, Protocol.map_run_value] at result
                exact result
              refine (ballValue _).trans ?_
              cases returnedBall : ((ball.substituteChecked (pointHandler point)).protocol.run oracle).value with
              | error error => rfl
              | ok execution =>
                  cases observed : execution.value with
                  | error invalid => dsimp only [view, flatten, collapse, Except.map]; rw [observed]; rfl
                  | ok actualBall => dsimp only [view, flatten, collapse, Except.map]; rw [observed]; rfl
    · rw [Program.map_execution, Protocol.map_run_trace, Program.bind_execution, Protocol.bind_run_trace,
        Program.map_execution, Protocol.map_run_trace, Program.bind_execution, Protocol.bind_run_trace]
      unfold oldOperation
      rw [Program.map_execution, Protocol.map_run_value, Protocol.map_run_trace]
      cases returned : ((first.substituteChecked (pointHandler point)).protocol.run oracle).value with
      | error error => rfl
      | ok execution =>
          cases checked : execution.value with
          | error invalid => dsimp only; rw [checked]; rfl
          | ok next =>
              dsimp only
              rw [checked]
              dsimp only [Except.mapError]
              rw [Program.map_execution, Protocol.map_run_trace, Program.map_execution, Protocol.map_run_trace,
                Program.map_execution, Protocol.map_run_trace]
              let ball := Coordinate.Observation.checked (process point) (.ball next.val)
              have ballTrace (function : Except (Coordinate.Observation.Invalid (process point).State)
                  (Coordinate.Observation.Response (process point) (.ball next.val)) →
                  Except (Coordinate.Observation.CoordinateFailure state request.tolerance request.positive
                    (Coordinate.Observation.Invalid (process point).State))
                    (Coordinate.Observation.CertifiedState Norm.Coordinates.re_sub_sq_le_basic_normSq
                      state request.tolerance request.positive)) := by
                have ballDist := Program.substituteChecked_map_map_execution
                  (pointHandler point) ball function view oracle
                have result := congrArg Basic.Execution.trace ballDist
                rw [Program.map_execution, Protocol.map_run_trace, Program.map_execution, Protocol.map_run_trace,
                  Program.map_execution, Protocol.map_run_trace] at result
                exact result
              exact congrArg (List.append (((first.substituteChecked (pointHandler point)).protocol.run oracle).trace))
                (ballTrace _)


/-- Execute an original point decision while retaining a returned refinement on failure. -/
@[expose] def selectionWith {OuterQuestion OuterReply Error : Type}
    (point : Point) (handler : Query → Program OuterQuestion OuterReply (Except Error Reply))
    (invalid : Failure → Error) (request : AccuracyRequest)
    (choice : NumericalPoint.Selection Horner.Real.source point.val request) :
    Program OuterQuestion OuterReply (Except (SelectionFailure point request choice Error) choice.Reply) := by
  cases choice with
  | reuse retained same accurate => exact .pure (.ok ())
  | request previous =>
      let state := Horner.Real.originalState point.val point.property previous
      exact (Coordinate.Observation.coordinateWith (checkedWith point handler invalid)
        Norm.Coordinates.re_sub_sq_le_basic_normSq state request.tolerance request.positive).map fun result =>
        match result with
        | .error (.refinement invalid) => .error (.initial invalid)
        | .error (.ball refined invalid) => .error (.pending ⟨previous, rfl, refined, invalid⟩)
        | .ok next => .ok (requestReply point previous request next)

/-- Execute the original point decision using its direct tagged Gaussian surface. -/
@[expose] def selection (point : Point) (request : AccuracyRequest)
    (choice : NumericalPoint.Selection Horner.Real.source point.val request) :=
  selectionWith point forward id request choice

/-- Resume an interrupted original point decision through the same tagged outer handler. -/
@[expose] def resumeWith {OuterQuestion OuterReply Error : Type}
    (point : Point) (handler : Query → Program OuterQuestion OuterReply (Except Error Reply))
    (invalid : Failure → Error) (request : AccuracyRequest)
    (choice : NumericalPoint.Selection Horner.Real.source point.val request)
    (pending : Pending point request choice Error) :
    Program OuterQuestion OuterReply (Except (Pending point request choice Error) choice.Reply) :=
  let state : Coordinate.State (process point) (0 : Nat) Basic.Canonical.re :=
    Horner.Real.originalState point.val point.property pending.previous
  let ask : (operation : Coordinate.Observation.Request (process point).State) →
      Program OuterQuestion OuterReply (Except Error (Coordinate.Observation.Response (process point) operation)) :=
    fun operation => checkedWith point handler invalid operation
  let finish := fun result : Except
      (Coordinate.Observation.CoordinateFailure state request.tolerance request.positive Error)
      (Coordinate.Observation.CertifiedState Norm.Coordinates.re_sub_sq_le_basic_normSq
        state request.tolerance request.positive) =>
    match result with
    | .error (.refinement error) => Except.error { pending with reason := error }
    | .error (.ball _ error) => Except.error { pending with reason := error }
    | .ok next => Except.ok (pending.selected.symm ▸ requestReply point pending.previous request next)
  (Coordinate.Observation.resumeWith ask Norm.Coordinates.re_sub_sq_le_basic_normSq
    state request.tolerance request.positive pending.refined).map finish

/-- Retrying a pending point reads only the ball of its returned refinement. -/
theorem resumeWith_trace {OuterQuestion OuterReply Error : Type} [DecidableEq OuterQuestion]
    (point : Point) (handler : Query → Program OuterQuestion OuterReply (Except Error Reply))
    (invalid : Failure → Error) (request : AccuracyRequest)
    (choice : NumericalPoint.Selection Horner.Real.source point.val request)
    (pending : Pending point request choice Error) (oracle : OuterQuestion → OuterReply) :
    ((resumeWith point handler invalid request choice pending).protocol.run oracle).trace =
      ((handler (point, .ball pending.refined.val)).protocol.run oracle).trace := by
  unfold resumeWith Coordinate.Observation.resumeWith
  rw [Program.map_execution, Protocol.map_run_trace, Program.map_execution, Protocol.map_run_trace]
  exact checkedWith_trace point handler invalid (.ball pending.refined.val) oracle

/-- Resume an interrupted point on its direct tagged Gaussian surface. -/
@[expose] def resume (point : Point) (request : AccuracyRequest)
    (choice : NumericalPoint.Selection Horner.Real.source point.val request)
    (pending : Pending point request choice Failure) :=
  resumeWith point forward id request choice pending

section
attribute [local irreducible] checkedWith requestReply

/-- Original tagged replies complete the retained refinement as the original point reply. -/
theorem resumeWith_original {OuterQuestion OuterReply Error : Type} [DecidableEq OuterQuestion]
    (point : Point) (handler : Query → Program OuterQuestion OuterReply (Except Error Reply))
    (invalid : Failure → Error) (request : AccuracyRequest)
    (choice : NumericalPoint.Selection Horner.Real.source point.val request)
    (pending : Pending point request choice Error) (oracle : OuterQuestion → OuterReply)
    (answers : ∀ question, ((handler question).protocol.run oracle).value = .ok (original question)) :
    ((resumeWith point handler invalid request choice pending).protocol.run oracle).value =
      .ok (originalSelectionReply point request choice) := by
  unfold resumeWith
  rw [Program.map_execution, Protocol.map_run_value]
  let state : Coordinate.State (process point) (0 : Nat) Basic.Canonical.re :=
    Horner.Real.originalState point.val point.property pending.previous
  let ask : (operation : Coordinate.Observation.Request (process point).State) →
      Program OuterQuestion OuterReply (Except Error (Coordinate.Observation.Response (process point) operation)) :=
    fun operation => checkedWith point handler invalid operation
  have answer (operation : Coordinate.Observation.Request (process point).State) :
      ((ask operation).protocol.run oracle).value =
        .ok (Coordinate.Observation.original_request (process point) operation ▸
          (Coordinate.Observation.original (process point) operation).2) :=
    checkedWith_original point handler invalid operation oracle answers
  have actual := Coordinate.Observation.resumeWith_original ask
    Norm.Coordinates.re_sub_sq_le_basic_normSq state request.tolerance request.positive pending.refined oracle answer
  let finish := fun result : Except
      (Coordinate.Observation.CoordinateFailure state request.tolerance request.positive Error)
      (Coordinate.Observation.CertifiedState Norm.Coordinates.re_sub_sq_le_basic_normSq
        state request.tolerance request.positive) =>
    match result with
    | .error (.refinement error) => Except.error { pending with reason := error }
    | .error (.ball _ error) => Except.error { pending with reason := error }
    | .ok next => Except.ok (pending.selected.symm ▸ requestReply point pending.previous request next)
  change finish (((Coordinate.Observation.resumeWith ask Norm.Coordinates.re_sub_sq_le_basic_normSq
    state request.tolerance request.positive pending.refined).protocol.run oracle).value) = _
  have same := congrArg finish actual
  refine same.trans ?_
  apply congrArg Except.ok
  exact selectionReply_unique _ _ _ _ _

end

/-- Project the original point or operation error from a retained selection failure. -/
@[expose] def SelectionFailure.failure {point : Point} {request : AccuracyRequest}
    {choice : NumericalPoint.Selection Horner.Real.source point.val request} :
    SelectionFailure point request choice Failure → Failure
  | .initial invalid => invalid
  | .pending receipt => receipt.reason

/-- Original outer replies return the original selected point-decision reply. -/
theorem selectionWith_original {OuterQuestion OuterReply Error : Type} [DecidableEq OuterQuestion]
    (point : Point) (handler : Query → Program OuterQuestion OuterReply (Except Error Reply))
    (invalid : Failure → Error) (request : AccuracyRequest)
    (choice : NumericalPoint.Selection Horner.Real.source point.val request) (oracle : OuterQuestion → OuterReply)
    (answers : ∀ question, ((handler question).protocol.run oracle).value = .ok (original question)) :
    ((selectionWith point handler invalid request choice).protocol.run oracle).value =
      .ok (originalSelectionReply point request choice) := by
  cases choice with
  | reuse retained same accurate => rfl
  | request previous =>
      unfold selectionWith
      rw [Program.map_execution, Protocol.map_run_value]
      let state : Coordinate.State (process point) (0 : Nat) Basic.Canonical.re :=
        Horner.Real.originalState point.val point.property previous
      let ask : (operation : Coordinate.Observation.Request (process point).State) →
          Program OuterQuestion OuterReply (Except Error (Coordinate.Observation.Response (process point) operation)) :=
        checkedWith point handler invalid
      have answer (operation : Coordinate.Observation.Request (process point).State) :
          ((ask operation).protocol.run oracle).value =
            .ok (Coordinate.Observation.original_request (process point) operation ▸
              (Coordinate.Observation.original (process point) operation).2) :=
        checkedWith_original point handler invalid operation oracle answers
      have actual := Coordinate.Observation.coordinateWith_original ask
        Norm.Coordinates.re_sub_sq_le_basic_normSq state request.tolerance request.positive oracle answer
      have same := congrArg (fun result : Except
          (Coordinate.Observation.CoordinateFailure state request.tolerance request.positive Error)
          (Coordinate.Observation.CertifiedState Norm.Coordinates.re_sub_sq_le_basic_normSq
            state request.tolerance request.positive) =>
        match result with
        | .error (.refinement error) => Except.error (SelectionFailure.initial error)
        | .error (.ball next error) => Except.error (SelectionFailure.pending ⟨previous, rfl, next, error⟩)
        | .ok next => Except.ok (requestReply point previous request next)) actual
      refine same.trans ?_
      apply congrArg Except.ok
      exact selectionReply_unique _ _ _ _ _

/-- Original tagged replies return the original point-decision reply. -/
theorem selection_original (point : Point) (request : AccuracyRequest)
    (choice : NumericalPoint.Selection Horner.Real.source point.val request) :
    ((selection point request choice).protocol.run original).value =
      .ok (originalSelectionReply point request choice) :=
  selectionWith_original point forward id request choice original (fun _ => rfl)

end Progress

/-- Execute a retained point decision through its actual tagged Gaussian requests.

An adequate saved point returns without a Gaussian call. Otherwise the
original predecessor is refined once, its returned ball is read once, and
those exact returned data supply the numerical point reply. -/
@[expose] def selection (point : Point) (request : AccuracyRequest)
    (choice : NumericalPoint.Selection Horner.Real.source point.val request) :
    Program Query Reply (Except Failure choice.Reply) :=
  (Progress.selection point request choice).map fun result =>
    result.mapError Progress.SelectionFailure.failure

namespace Progress

/-- The shared selection preserves the previous checked point request on every oracle. -/
theorem selection_previous_execution (point : Point) (request : AccuracyRequest)
    (choice : NumericalPoint.Selection Horner.Real.source point.val request) (oracle : Query → Reply) :
    ((Real.Observation.selection point request choice).protocol.run oracle) =
      (((match choice with
        | .reuse _ _ _ => Program.pure (.ok ())
        | .request previous =>
            (coordinate point (Horner.Real.originalState point.val point.property previous) request).map fun result =>
              match result with
              | .error invalid => .error invalid
              | .ok execution => match execution.value with
                | .error invalid => .error (.operation point invalid)
                | .ok next => .ok (requestReply point previous request next) :
          Program Query Reply (Except Failure choice.Reply)).protocol.run oracle)) := by
  cases choice with
  | reuse retained same accurate => rfl
  | request previous =>
      let state := Horner.Real.originalState point.val point.property previous
      have same := Coordinate.Observation.coordinateWith_run_eq (checkedWith point forward id) (oldOperation point)
        Norm.Coordinates.re_sub_sq_le_basic_normSq state request.tolerance request.positive oracle
        (checkedWith_forward point · oracle)
      have old := oldCoordinate_execution point state request oracle
      have oldVal := congrArg Basic.Execution.value old
      rw [Program.map_execution, Protocol.map_run_value, Program.map_execution, Protocol.map_run_value] at oldVal
      have oldTrace := congrArg Basic.Execution.trace old
      rw [Program.map_execution, Protocol.map_run_trace, Program.map_execution, Protocol.map_run_trace] at oldTrace
      have sameVal := congrArg Basic.Execution.value same
      have sameTrace := congrArg Basic.Execution.trace same
      rw [← sameVal] at oldVal
      rw [← sameTrace] at oldTrace
      unfold Real.Observation.selection selection selectionWith
      apply Basic.Execution.ext
      · rw [Program.map_execution, Protocol.map_run_value, Program.map_execution, Protocol.map_run_value,
          Program.map_execution, Protocol.map_run_value]
        let build := requestReply point previous request
        have sameResult := congrArg (Except.map build) oldVal.symm
        cases newResult : ((Coordinate.Observation.coordinateWith (checkedWith point forward id)
            Norm.Coordinates.re_sub_sq_le_basic_normSq state request.tolerance request.positive).protocol.run
            oracle).value with
        | error failure =>
            rw [newResult] at sameResult
            cases failure <;> dsimp only [Except.map, Except.mapError, oldFailure] at sameResult
            all_goals
              cases oldResult : ((coordinate point state request).protocol.run oracle).value with
              | error error =>
                  rw [oldResult] at sameResult
                  exact sameResult
              | ok execution =>
                  rw [oldResult] at sameResult
                  dsimp only [Except.map, Except.mapError] at sameResult
                  cases observed : execution.value with
                  | error invalid =>
                      rw [observed] at sameResult
                      dsimp only [Except.mapError, SelectionFailure.failure]
                      rw [observed]
                      exact sameResult
                  | ok next =>
                      rw [observed] at sameResult
                      dsimp only [Except.mapError, SelectionFailure.failure]
                      rw [observed]
                      exact sameResult
        | ok next =>
            rw [newResult] at sameResult
            dsimp only [Except.map, Except.mapError, oldFailure] at sameResult
            cases oldResult : ((coordinate point state request).protocol.run oracle).value with
            | error error =>
                rw [oldResult] at sameResult
                exact sameResult
            | ok execution =>
                rw [oldResult] at sameResult
                dsimp only [Except.map, Except.mapError] at sameResult
                cases observed : execution.value with
                | error invalid =>
                    rw [observed] at sameResult
                    dsimp only [Except.mapError, SelectionFailure.failure]
                    rw [observed]
                    exact sameResult
                | ok next =>
                    rw [observed] at sameResult
                    dsimp only [Except.mapError, SelectionFailure.failure]
                    rw [observed]
                    exact sameResult
      · rw [Program.map_execution, Protocol.map_run_trace, Program.map_execution, Protocol.map_run_trace,
          Program.map_execution, Protocol.map_run_trace]
        exact oldTrace.symm

end Progress

/-- Original Gaussian replies return the actual original state and cached interval of the chosen branch. -/
theorem selection_original (point : Point) (request : AccuracyRequest)
    (choice : NumericalPoint.Selection Horner.Real.source point.val request) :
    ((selection point request choice).protocol.run original).value =
      .ok (originalSelectionReply point request choice) := by
  unfold selection
  rw [Program.map_execution, Protocol.map_run_value, Progress.selection_original]
  rfl

/-- A reused numerical point makes no Gaussian refinement or ball request. -/
theorem selection_reused (point : Point) (request : AccuracyRequest)
    (retained : NumericalPoint Horner.Real.source) (same : point.val = retained.point)
    (accurate : retained.reading.width < request.tolerance) (oracle : Query → Reply) :
    ((selection point request (.reuse retained same accurate)).protocol.run oracle).trace = [] := rfl

/-- Exact replay returns the same state and reading without repeating Gaussian operations. -/
theorem selection_replay (point : Point) (request : AccuracyRequest)
    (choice : NumericalPoint.Selection Horner.Real.source point.val request) :
    (selection point request choice).protocol.replayExact
      ((selection point request choice).protocol.run original).trace =
        .ok (.ok (originalSelectionReply point request choice)) := by
  rw [(selection point request choice).protocol.replayExact_run, selection_original]

/-- The original prepared mesh occurrence supplies its rational unit tag. -/
@[expose] def preparedPoint (prepared : Preparation Horner.Real.modulus) (entry : Entry prepared) : Point :=
  let valid := prepared.partition.valid entry.val entry.property
  ⟨entry.val.start, valid.1, valid.2.1.le.trans valid.2.2⟩

/-- The original common-child occurrence supplies its rational unit tag. -/
@[expose] def commonPoint (query : Common.Observation.Query) : Point :=
  ⟨query.val.start, query.property.1, query.property.2.1.le.trans query.property.2.2⟩

/-- Assemble the original fresh-mesh point reply from the same returned Gaussian state and interval. -/
@[expose] def freshPointReply (prepared : Preparation Horner.Real.modulus)
    (cached : List (NumericalPoint Horner.Real.source)) (entry : Entry prepared)
    (reply : (NumericalPoint.selectBank Horner.Real.source cached entry.val.start prepared.pointRequest).Reply) :
    CachedReply prepared cached := by
  let valid := prepared.partition.valid entry.val entry.property
  let choice := NumericalPoint.selectBank Horner.Real.source cached entry.val.start prepared.pointRequest
  let selected := choice.resolveWith entry.val le_rfl valid.2.1.le reply
  have same := NumericalPoint.selectBank_resolveWith_eq_atCached Horner.Real.source cached entry.val
    entry.val.start le_rfl valid.2.1.le prepared.pointRequest reply
  exact ⟨entry, ⟨selected.val, congrArg Subtype.val same⟩⟩

/-- Returned Gaussian data produce the exact original fresh-mesh point reply. -/
theorem freshPointReply_eq (prepared : Preparation Horner.Real.modulus)
    (cached : List (NumericalPoint Horner.Real.source)) (entry : Entry prepared)
    (reply : (NumericalPoint.selectBank Horner.Real.source cached entry.val.start prepared.pointRequest).Reply) :
    freshPointReply prepared cached entry reply = originalCachedReply prepared cached entry := by
  let valid := prepared.partition.valid entry.val entry.property
  have same := NumericalPoint.selectBank_resolveWith_eq_atCached Horner.Real.source cached entry.val
    entry.val.start le_rfl valid.2.1.le prepared.pointRequest reply
  have pointEq :
      ((NumericalPoint.selectBank Horner.Real.source cached entry.val.start prepared.pointRequest).resolveWith
        entry.val le_rfl valid.2.1.le reply).val = (prepared.cachedStart cached entry).val :=
    congrArg (fun observation : NumericalPoint.Observation Horner.Real.source entry.val entry.val.start
      prepared.pointRequest => observation.val) same
  unfold freshPointReply originalCachedReply
  exact congrArg (fun data : CachedPoint prepared cached entry => CachedReply.mk entry data) (Subtype.ext pointEq)

/-- Assemble the original common-child reply from the returned state selected using its actual bank. -/
@[expose] def commonPointReply (cached : List (NumericalPoint Horner.Real.source)) (request : AccuracyRequest)
    (query : Common.Observation.Query)
    (reply : (NumericalPoint.selectBank Horner.Real.source cached query.val.start request).Reply) :
    Common.Observation.Reply cached request := by
  let choice := NumericalPoint.selectBank Horner.Real.source cached query.val.start request
  let selected := choice.resolveWith query.val le_rfl query.property.2.1.le reply
  have same := NumericalPoint.selectBank_resolveWith_eq_atCached Horner.Real.source cached query.val
    query.val.start le_rfl query.property.2.1.le request reply
  exact ⟨query, ⟨selected, same⟩⟩

/-- Returned Gaussian data produce the exact original common-child point reply. -/
theorem commonPointReply_eq (cached : List (NumericalPoint Horner.Real.source)) (request : AccuracyRequest)
    (query : Common.Observation.Query)
    (reply : (NumericalPoint.selectBank Horner.Real.source cached query.val.start request).Reply) :
    commonPointReply cached request query reply = Common.Observation.originalReply cached request query := by
  have same := NumericalPoint.selectBank_resolveWith_eq_atCached Horner.Real.source cached query.val
    query.val.start le_rfl query.property.2.1.le request reply
  unfold commonPointReply Common.Observation.originalReply
  apply congrArg (fun data : Common.Observation.Selected cached request query => Common.Observation.Reply.mk query data)
  apply Subtype.ext
  exact same

/-- Lower one original numerical integration query to its actual tagged Gaussian operations.

The fresh branch uses the supplied effective bank; the common branch uses
the bank carried by that actual query. Both consume the same selected reply
in the original numerical construction. -/
@[expose] def numericalHandler (prepared : Preparation Horner.Real.modulus)
    (cached : List (NumericalPoint Horner.Real.source)) (request : AccuracyRequest)
    (query : Continuation.Query prepared) :
    Program Query Reply (Except Failure (Continuation.Reply prepared cached request)) :=
  match query with
  | .inl entry =>
      let point := preparedPoint prepared entry
      let choice := NumericalPoint.selectBank Horner.Real.source cached point.val prepared.pointRequest
      (selection point prepared.pointRequest choice).map fun result =>
        result.map fun reply => .inl (freshPointReply prepared cached entry reply)
  | .inr (bank, child) =>
      let point := commonPoint child
      let choice := NumericalPoint.selectBank Horner.Real.source bank point.val request
      (selection point request choice).map fun result =>
        result.map fun reply => .inr ⟨bank, commonPointReply bank request child reply⟩

/-- Original tagged Gaussian replies return the exact original numerical reply at each query. -/
theorem numericalHandler_original (prepared : Preparation Horner.Real.modulus)
    (cached : List (NumericalPoint Horner.Real.source)) (request : AccuracyRequest)
    (query : Continuation.Query prepared) :
    ((numericalHandler prepared cached request query).protocol.run original).value =
      .ok (Continuation.originalReplyAll prepared cached request query) := by
  cases query with
  | inl entry =>
      unfold numericalHandler
      rw [Program.map_execution, Protocol.map_run_value, selection_original]
      apply congrArg Except.ok
      apply congrArg Sum.inl
      exact freshPointReply_eq prepared cached entry _
  | inr occurrence =>
      rcases occurrence with ⟨bank, child⟩
      unfold numericalHandler
      rw [Program.map_execution, Protocol.map_run_value, selection_original]
      apply congrArg Except.ok
      change (Sum.inr ⟨bank, commonPointReply bank request child _⟩ : Continuation.Reply prepared cached request) =
        (Sum.inr ⟨bank, Common.Observation.originalReply bank request child⟩ :
          Continuation.Reply prepared cached request)
      exact congrArg (fun point : Common.Observation.Reply bank request =>
        (Sum.inr ⟨bank, point⟩ : Continuation.Reply prepared cached request))
        (commonPointReply_eq bank request child _)

/-- Observe the original saved exponential integration request through its actual Gaussian operations.

The original numerical execution, including its complete result and ordered
point replies, is retained by checked substitution. Gaussian requests carry
their original rational tags and use the same returned point states. -/
@[expose] def history (state : Real.integrationProcess.State) (request : AccuracyRequest) :=
  if adequate : (integralBound state.1.cells).width < request.tolerance then
    Program.pure (.ok ⟨.ok ⟨state.1, RefiningController.History.next state.2 (.reused request adequate)⟩, []⟩)
  else
    let prepared := Preparation.prepare Horner.Real.modulus request
    let producer := NumericalFrontier.Continuous.producer Horner.Real.modulus
    let cached := producer.retainedReadings state.2
    let bank := Producer.effectiveBank state.1 cached
    (Continuation.historyRefiningPrepared Horner.Real.modulus state request prepared rfl cached rfl bank rfl
      adequate).substituteChecked (numericalHandler prepared bank request)

/-- The shared realization retains the original numerical history and checked handler. -/
theorem history_eq (state : Real.integrationProcess.State) (request : AccuracyRequest) :
    history state request =
      (Continuation.historyComputation Horner.Real.modulus state request).substituteChecked
        (numericalHandler (Preparation.prepare Horner.Real.modulus request)
          (Producer.effectiveBank state.1
            ((NumericalFrontier.Continuous.producer Horner.Real.modulus).retainedReadings state.2)) request) := by
  unfold history Continuation.historyComputation Continuation.computationWithBank
    Continuation.certifiedComputationWithBank
  by_cases adequate : (integralBound state.1.cells).width < request.tolerance
  · rw [dif_pos adequate]
    dsimp only
    rw [dif_pos adequate]
    rfl
  · rw [dif_neg adequate]
    dsimp only
    rw [dif_neg adequate]
    rfl

/-- Original Gaussian execution returns the complete original numerical integration execution. -/
theorem history_original (state : Real.integrationProcess.State) (request : AccuracyRequest) :
    let prepared := Preparation.prepare Horner.Real.modulus request
    let producer := NumericalFrontier.Continuous.producer Horner.Real.modulus
    let cached := producer.retainedReadings state.2
    let bank := Producer.effectiveBank state.1 cached
    ((history state request).protocol.run original).value =
      .ok ((Continuation.historyComputation Horner.Real.modulus state request).protocol.run
        (Continuation.originalReplyAll prepared bank request)) := by
  rw [history_eq]
  apply Program.substituteChecked_value
  intro query
  exact numericalHandler_original _ _ request query

/-- Exact replay recovers the complete original numerical execution without repeating Gaussian operations. -/
theorem history_replay (state : Real.integrationProcess.State) (request : AccuracyRequest) :
    let prepared := Preparation.prepare Horner.Real.modulus request
    let producer := NumericalFrontier.Continuous.producer Horner.Real.modulus
    let cached := producer.retainedReadings state.2
    let bank := Producer.effectiveBank state.1 cached
    (history state request).protocol.replayExact ((history state request).protocol.run original).trace =
      .ok (.ok ((Continuation.historyComputation Horner.Real.modulus state request).protocol.run
        (Continuation.originalReplyAll prepared bank request))) := by
  rw [(history state request).protocol.replayExact_run, history_original]

/-- A saved frontier meeting the request makes no tagged Gaussian point call. -/
theorem history_reused (state : Real.integrationProcess.State) (request : AccuracyRequest)
    (adequate : (integralBound state.1.cells).width < request.tolerance) (oracle : Query → Reply) :
    ((history state request).protocol.run oracle).trace = [] := by
  unfold history
  rw [dif_pos adequate]
  rfl

/-- Replies outside the actual tagged Gaussian trace preserve the complete numerical execution and both logs. -/
theorem history_payload_erasure (state : Real.integrationProcess.State) (request : AccuracyRequest)
    {Payload : Type} (payload : Payload) (outside : Payload → Query → Reply) :
    let program := history state request
    program.protocol.run (Boundary.Trace.overlay (program.protocol.run original).trace (outside payload)) =
      program.protocol.run original :=
  (history state request).protocol.annotation_erasure original payload outside

end Purelib.Integration.Exponential.Real.Observation

end
