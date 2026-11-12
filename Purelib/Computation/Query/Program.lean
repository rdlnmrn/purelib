module

public import Purelib.Computation.Query.Boundary
import Purelib.Data.List.Append

/-!
# Composing displayed queries with their internal requests

A query program retains its pure return and actual request continuations.
Compilation uses the original protocol constructors. Expansion replaces a
request by a protocol of its internal requests and retains the complete
outer execution as its result. Each handler runs once; subsequent control
and both logs consume its same reply. No rerun extracts an internal trace.
-/

public section

namespace Purelib.Computation.Query

open Purelib.Data.List

universe u v w x y

set_option genInjectivity false in
/-- An executable query construction with an explicit return or one request followed by its actual continuation.

Concrete constructors supply finite control. The general continuation field
is not a representation theorem for arbitrary host-language functions.
-/
inductive Program (Question : Type u) (Reply : Type v) (Value : Type w) where
  /-- Return the supplied value without requesting a reply. -/ | pure (value : Value)
  /-- Request one displayed question and continue from its same actual reply. -/ | request
      (question : Question) (next : Reply → Program Question Reply Value)

namespace Program

variable {Question : Type u} {Reply : Type v} {Value : Type w} {Result : Type x}

/-- Continue a query program from its returned value, preserving every preceding request. -/
@[expose] def bind (first : Program Question Reply Value)
    (next : Value → Program Question Reply Result) : Program Question Reply Result :=
  match first with
  | .pure value => next value
  | .request question remaining => .request question (fun reply => (remaining reply).bind next)

/-- Transform a returned value without changing its actual requests. -/
@[expose] def map (function : Value → Result) (program : Program Question Reply Value) :
    Program Question Reply Result := program.bind fun value => .pure (function value)

/-- Request one displayed question and return its same reply. -/
@[expose] def query (question : Question) : Program Question Reply Reply := .request question .pure

/-- Request every retained question in order and keep each question paired with its actual reply. -/
@[expose] def record : List Question → Program Question Reply (List (Question × Reply))
  | [] => .pure []
  | question :: remaining => .request question (fun reply =>
      (record remaining).map (fun after => (question, reply) :: after))

/-- Compile the retained construction through the original protocol's pure, query and bind operations. -/
@[expose] def protocol [DecidableEq Question] (program : Program Question Reply Value) :
    Protocol Question Reply Value :=
  match program with
  | .pure value => Protocol.pure value
  | .request question next => (Protocol.query question).bind fun reply => (next reply).protocol

/-- Expansion records internal requests and returns the same complete outer value and ordered outer trace.

The handler's exact reply selects the continuation and is stored in the
outer trace. Its protocol trace is retained by the original bind operation.
-/
@[expose] def expand {InnerQuestion : Type x} {InnerReply : Type y}
    (handlers : Question → Protocol InnerQuestion InnerReply Reply)
    (program : Program Question Reply Value) :
    Protocol InnerQuestion InnerReply (Basic.Execution Question Reply Value) :=
  match program with
  | .pure value => Protocol.pure ⟨value, []⟩
  | .request question next => (handlers question).bind fun reply =>
      ((next reply).expand handlers).map fun after =>
        ⟨after.value, ⟨question, reply⟩ :: after.trace⟩

/-- Expand checked handlers, retaining their concrete failure before executing any later request.

Successful replies select the same outer continuation and are retained in
its log. The inner trace includes every attempted handler, including the
one returning the error.
-/
@[expose] def expandChecked {InnerQuestion : Type x} {InnerReply : Type y} {Error : Type}
    (handlers : Question → Protocol InnerQuestion InnerReply (Except Error Reply))
    (program : Program Question Reply Value) :
    Protocol InnerQuestion InnerReply (Except Error (Basic.Execution Question Reply Value)) :=
  match program with
  | .pure value => Protocol.pure (.ok ⟨value, []⟩)
  | .request question next => (handlers question).bind fun result =>
      match result with
      | .error error => Protocol.pure (.error error)
      | .ok reply => ((next reply).expandChecked handlers).map fun result =>
          result.map fun after => ⟨after.value, ⟨question, reply⟩ :: after.trace⟩

set_option genInjectivity false in
/-- An original program reaches an exact continuation through the retained ordered replies. -/
inductive Reaches : Program Question Reply Value → List (Basic.Exchange Question Reply) →
    Program Question Reply Value → Prop where
  /-- A program reaches itself without consuming a request. -/ | here (current : Program Question Reply Value) :
      Reaches current [] current
  /-- The actual first reply selects the original continuation before the retained tail. -/ | step
      {question : Question} {next : Reply → Program Question Reply Value} {reply : Reply}
      {tail : List (Basic.Exchange Question Reply)} {current : Program Question Reply Value} :
      Reaches (next reply) tail current → Reaches (.request question next) (⟨question, reply⟩ :: tail) current

set_option genInjectivity false in
/-- A failed handler retains its exact original request, continuation and successfully answered prefix. -/
structure CheckedStop (original : Program Question Reply Value) (Error : Question → Type) where
  /-- The actual successful original outer exchanges in order. -/ before : List (Basic.Exchange Question Reply)
  /-- The original outer request whose handler failed. -/ question : Question
  /-- The exact original reply continuation at that request. -/ next : Reply → Program Question Reply Value
  /-- The retained prefix reaches this original request and continuation. -/ reached :
    Reaches original before (.request question next)
  /-- The actual failure and any partial work belonging to this exact request. -/ reason : Error question

/-- Share one checked request's original failure and successful continuation branches. -/
@[expose] def checkedStep {InnerQuestion : Type x} {InnerReply : Type y} {Error Output : Type*}
    (action : Program InnerQuestion InnerReply (Except Error Reply))
    (failure : Error → Program InnerQuestion InnerReply Output)
    (success : Reply → Program InnerQuestion InnerReply Output) : Program InnerQuestion InnerReply Output :=
  action.bind fun returned => match returned with
    | .error error => failure error
    | .ok reply => success reply

/-- Substitute original request handlers while retaining a failed request's exact continuation and prefix.

A handler failure is indexed by its actual question. Earlier replies select
the original continuation and are retained in order; no earlier handler is
run again to construct the stopped value. -/
@[expose] def substituteCheckedProgress {InnerQuestion : Type x} {InnerReply : Type y}
    {Error : Question → Type}
    (handlers : (question : Question) → Program InnerQuestion InnerReply (Except (Error question) Reply)) :
    (program : Program Question Reply Value) → Program InnerQuestion InnerReply
      (Except (CheckedStop program Error) (Basic.Execution Question Reply Value))
  | .pure value => .pure (.ok ⟨value, []⟩)
  | .request question next => checkedStep (handlers question)
      (fun error => .pure (.error ⟨[], question, next, .here _, error⟩)) fun reply =>
        (substituteCheckedProgress handlers (next reply)).map fun result => match result with
          | .error stopped => .error ⟨⟨question, reply⟩ :: stopped.before, stopped.question, stopped.next,
              .step stopped.reached, stopped.reason⟩
          | .ok completed => .ok ⟨completed.value, ⟨question, reply⟩ :: completed.trace⟩

/-- Substitute checked query constructions while retaining the complete outer execution as executable data.

The resulting construction can itself be substituted into another boundary.
Each handler runs once; failure stops the continuation and successful replies
retain their original order and select the same subsequent requests.
-/
@[expose] def substituteChecked {InnerQuestion : Type x} {InnerReply : Type y} {Error : Type}
    (handlers : Question → Program InnerQuestion InnerReply (Except Error Reply))
    (program : Program Question Reply Value) :
    Program InnerQuestion InnerReply (Except Error (Basic.Execution Question Reply Value)) :=
  match program with
  | .pure value => .pure (.ok ⟨value, []⟩)
  | .request question next => checkedStep (handlers question) (fun error => .pure (.error error)) fun reply =>
      ((next reply).substituteChecked handlers).map fun result =>
        result.map fun after => ⟨after.value, ⟨question, reply⟩ :: after.trace⟩

/-- Checked substitution of one request runs its actual handler before its continuation. -/
theorem substituteChecked_request {InnerQuestion : Type x} {InnerReply : Type y} {Error : Type}
    (handlers : Question → Program InnerQuestion InnerReply (Except Error Reply))
    (question : Question) (next : Reply → Program Question Reply Value) :
    (Program.request question next).substituteChecked handlers =
      (handlers question).bind fun result =>
        match result with
        | .error error => .pure (.error error)
        | .ok reply => ((next reply).substituteChecked handlers).map fun result =>
            result.map fun after => ⟨after.value, ⟨question, reply⟩ :: after.trace⟩ := by
  rewrite [substituteChecked, checkedStep]
  rfl

/-- Compilation preserves sequential composition of the complete value and trace. -/
theorem bind_execution [DecidableEq Question] (first : Program Question Reply Value)
    (next : Value → Program Question Reply Result) (oracle : Question → Reply) :
    ((first.bind next).protocol).run oracle =
      ((first.protocol).bind fun value => (next value).protocol).run oracle := by
  induction first with
  | pure value => rfl
  | request question remaining induction =>
      change (let after := ((remaining (oracle question)).bind next).protocol.run oracle
        ; (⟨after.value, [⟨question, oracle question⟩] ++ after.trace⟩ : Basic.Execution Question Reply Result)) = _
      rewrite [induction (oracle question)]
      rfl

/-- Compilation preserves a value transformation and the same complete query trace. -/
theorem map_execution [DecidableEq Question] (function : Value → Result)
    (program : Program Question Reply Value) (oracle : Question → Reply) :
    ((program.map function).protocol).run oracle = ((program.protocol).map function).run oracle :=
  bind_execution program (fun value => .pure (function value)) oracle

/-- Forward one original request to one displayed question and decode its actual reply. -/
@[expose] def forward {InnerQuestion : Type x} {InnerReply : Type y}
    (emit : Question → InnerQuestion) (decode : Question → InnerReply → Reply)
    (question : Question) : Program InnerQuestion InnerReply (Except Empty Reply) :=
  .request (emit question) fun reply => .pure (.ok (decode question reply))

/-- One-request forwarding preserves the original ordered execution while displaying each actual outer reply. -/
theorem substituteChecked_forward_trace {InnerQuestion : Type x} {InnerReply : Type y}
    [DecidableEq Question] [DecidableEq InnerQuestion] (emit : Question → InnerQuestion)
    (decode : Question → InnerReply → Reply) (program : Program Question Reply Value)
    (oracle : InnerQuestion → InnerReply) :
    ((program.substituteChecked (forward emit decode)).protocol.run oracle).trace =
      ((program.protocol.run (fun question => decode question (oracle (emit question)))).trace.map
        (fun exchange => ⟨emit exchange.query, oracle (emit exchange.query)⟩)) := by
  induction program with
  | pure value => rfl
  | request question next induction =>
      rw [substituteChecked_request, bind_execution, Protocol.bind_run_trace]
      let answer := decode question (oracle (emit question))
      let wrap (result : Except Empty (Basic.Execution Question Reply Value)) := result.map fun after =>
        (⟨after.value, ⟨question, answer⟩ :: after.trace⟩ : Basic.Execution Question Reply Value)
      change (⟨emit question, oracle (emit question)⟩ : Basic.Exchange InnerQuestion InnerReply) ::
        ((((next answer).substituteChecked (forward emit decode)).map wrap).protocol.run oracle).trace = _
      rw [map_execution, Protocol.map_run_trace, induction answer]
      rfl

/-- Concatenate two actual original-program paths without comparing continuation functions. -/
theorem Reaches.trans {origin current target : Program Question Reply Value}
    {before after : List (Basic.Exchange Question Reply)}
    (first : Reaches origin before current) (second : Reaches current after target) :
    Reaches origin (before ++ after) target := by
  induction first generalizing target after with
  | here => exact second
  | step previous induction => exact .step (induction second)

/-- Resume the exact stopped continuation with its returned reply and retain its original prefix.

A later failure retains the same original program and concatenates the actual
new exchanges. No handler in the earlier prefix is invoked again. -/
@[expose] def CheckedStop.resume {InnerQuestion : Type x} {InnerReply : Type y}
    {Error : Question → Type} {original : Program Question Reply Value}
    (handlers : (question : Question) → Program InnerQuestion InnerReply (Except (Error question) Reply))
    (stopped : CheckedStop original Error) (reply : Reply) :
    Program InnerQuestion InnerReply (Except (CheckedStop original Error) (Basic.Execution Question Reply Value)) :=
  (substituteCheckedProgress handlers (stopped.next reply)).map fun result => match result with
    | .error later => .error ⟨stopped.before ++ ⟨stopped.question, reply⟩ :: later.before,
        later.question, later.next, stopped.reached.trans (.step later.reached), later.reason⟩
    | .ok completed => .ok ⟨completed.value, stopped.before ++ ⟨stopped.question, reply⟩ :: completed.trace⟩

/-- A progress-bearing request executes the same original checked branch. -/
theorem substituteCheckedProgress_request {InnerQuestion : Type x} {InnerReply : Type y}
    {Error : Question → Type}
    (handlers : (question : Question) → Program InnerQuestion InnerReply (Except (Error question) Reply))
    (question : Question) (next : Reply → Program Question Reply Value) :
    substituteCheckedProgress handlers (.request question next) =
      checkedStep (handlers question)
        (fun error => .pure (.error ⟨[], question, next, .here _, error⟩)) fun reply =>
          (substituteCheckedProgress handlers (next reply)).map fun result => match result with
            | .error stopped => .error ⟨⟨question, reply⟩ :: stopped.before, stopped.question, stopped.next,
                .step stopped.reached, stopped.reason⟩
            | .ok completed => .ok ⟨completed.value, ⟨question, reply⟩ :: completed.trace⟩ := by
  rewrite [substituteCheckedProgress]
  rfl

/-- Original handler replies return the original complete outer execution. -/
theorem substituteCheckedProgress_original {InnerQuestion : Type x} {InnerReply : Type y}
    {Error : Question → Type} [DecidableEq Question] [DecidableEq InnerQuestion]
    (handlers : (question : Question) → Program InnerQuestion InnerReply (Except (Error question) Reply))
    (program : Program Question Reply Value) (oracle : InnerQuestion → InnerReply) (answer : Question → Reply)
    (correct : ∀ question, ((handlers question).protocol.run oracle).value = .ok (answer question)) :
    ((substituteCheckedProgress handlers program).protocol.run oracle).value = .ok (program.protocol.run answer) := by
  induction program with
  | pure value => rfl
  | request question next induction =>
      rw [substituteCheckedProgress_request, checkedStep, Program.bind_execution, Protocol.bind_run_value, correct]
      rw [Program.map_execution, Protocol.map_run_value, induction (answer question)]
      rfl

/-- Original handler replies continue from the exact retained prefix and selected reply. -/
theorem CheckedStop.resume_original {InnerQuestion : Type x} {InnerReply : Type y}
    {Error : Question → Type} {original : Program Question Reply Value}
    [DecidableEq Question] [DecidableEq InnerQuestion]
    (handlers : (question : Question) → Program InnerQuestion InnerReply (Except (Error question) Reply))
    (stopped : CheckedStop original Error) (reply : Reply) (oracle : InnerQuestion → InnerReply)
    (answer : Question → Reply)
    (correct : ∀ question, ((handlers question).protocol.run oracle).value = .ok (answer question)) :
    ((stopped.resume handlers reply).protocol.run oracle).value =
      .ok ⟨((stopped.next reply).protocol.run answer).value,
        stopped.before ++ ⟨stopped.question, reply⟩ :: ((stopped.next reply).protocol.run answer).trace⟩ := by
  unfold CheckedStop.resume
  rw [map_execution, Protocol.map_run_value,
    substituteCheckedProgress_original handlers (stopped.next reply) oracle answer correct]

/-- A resumed stop displays exactly the remaining continuation's requests, without replaying its prefix. -/
theorem CheckedStop.resume_trace {InnerQuestion : Type x} {InnerReply : Type y}
    {Error : Question → Type} {original : Program Question Reply Value} [DecidableEq InnerQuestion]
    (handlers : (question : Question) → Program InnerQuestion InnerReply (Except (Error question) Reply))
    (stopped : CheckedStop original Error) (reply : Reply) (oracle : InnerQuestion → InnerReply) :
    ((stopped.resume handlers reply).protocol.run oracle).trace =
      ((substituteCheckedProgress handlers (stopped.next reply)).protocol.run oracle).trace := by
  unfold CheckedStop.resume
  rw [Program.map_execution, Protocol.map_run_trace]

/-- Exact replay returns the complete successful or stopped original execution for any reply oracle. -/
theorem substituteCheckedProgress_replay {InnerQuestion : Type x} {InnerReply : Type y}
    {Error : Question → Type} [DecidableEq InnerQuestion]
    (handlers : (question : Question) → Program InnerQuestion InnerReply (Except (Error question) Reply))
    (program : Program Question Reply Value) (oracle : InnerQuestion → InnerReply) :
    let observed := substituteCheckedProgress handlers program
    observed.protocol.replayExact (observed.protocol.run oracle).trace = .ok (observed.protocol.run oracle).value :=
  (substituteCheckedProgress handlers program).protocol.replayExact_run oracle

/-- Replies outside the actual displayed trace cannot affect its returned work or ordered execution. -/
theorem substituteCheckedProgress_payload_erasure {InnerQuestion : Type x} {InnerReply : Type y}
    {Error : Question → Type} [DecidableEq InnerQuestion]
    (handlers : (question : Question) → Program InnerQuestion InnerReply (Except (Error question) Reply))
    (program : Program Question Reply Value) (oracle : InnerQuestion → InnerReply)
    {Payload : Type} (payload : Payload) (outside : Payload → InnerQuestion → InnerReply) :
    let observed := substituteCheckedProgress handlers program
    observed.protocol.run (Boundary.Trace.overlay (observed.protocol.run oracle).trace (outside payload)) =
      observed.protocol.run oracle :=
  (substituteCheckedProgress handlers program).protocol.annotation_erasure oracle payload outside

/-- Discarding the stopped prefix preserves the original checked substitution's value and trace. -/
theorem substituteCheckedProgress_erasure {InnerQuestion : Type x} {InnerReply : Type y}
    {Error : Type} [DecidableEq Question] [DecidableEq InnerQuestion]
    (handlers : Question → Program InnerQuestion InnerReply (Except Error Reply))
    (program : Program Question Reply Value) (oracle : InnerQuestion → InnerReply) :
    let progressed := (substituteCheckedProgress handlers program).protocol.run oracle
    let original := (program.substituteChecked handlers).protocol.run oracle
    progressed.value.mapError (fun stopped => stopped.reason) = original.value ∧ progressed.trace = original.trace := by
  induction program with
  | pure value => exact ⟨rfl, rfl⟩
  | request question next induction =>
      rw [substituteCheckedProgress_request, substituteChecked_request]
      unfold checkedStep
      constructor
      · dsimp only
        conv_lhs => rw [Program.bind_execution, Protocol.bind_run_value]
        conv_rhs => rw [Program.bind_execution, Protocol.bind_run_value]
        cases returned : ((handlers question).protocol.run oracle).value with
        | error failure => rfl
        | ok reply =>
            conv_lhs => rw [Program.map_execution, Protocol.map_run_value]
            conv_rhs => rw [Program.map_execution, Protocol.map_run_value]
            have earlier := (induction reply).1
            cases nextResult : ((substituteCheckedProgress handlers (next reply)).protocol.run oracle).value with
            | error stopped =>
                rw [nextResult] at earlier
                rewrite [← earlier]
                rfl
            | ok completed =>
                rw [nextResult] at earlier
                rw [← earlier]
                rfl
      · dsimp only
        conv_lhs => rw [Program.bind_execution, Protocol.bind_run_trace]
        conv_rhs => rw [Program.bind_execution, Protocol.bind_run_trace]
        cases returned : ((handlers question).protocol.run oracle).value with
        | error failure => rfl
        | ok reply =>
            conv_lhs => rw [Program.map_execution, Protocol.map_run_trace]
            conv_rhs => rw [Program.map_execution, Protocol.map_run_trace]
            exact congrArg (List.append ((handlers question).protocol.run oracle).trace) (induction reply).2

/-- Pointwise compatible question-indexed handlers preserve the original checked value and trace.

The retained stopped question selects its own error projection. The premise
compares actual handler executions at each original question, without comparing
handler functions or discarding an earlier successful original reply. -/
theorem substituteCheckedProgress_compatible {InnerQuestion : Type x} {InnerReply : Type y}
    {Error : Question → Type} {OldError : Type} [DecidableEq Question] [DecidableEq InnerQuestion]
    (handlers : (question : Question) → Program InnerQuestion InnerReply (Except (Error question) Reply))
    (oldHandlers : Question → Program InnerQuestion InnerReply (Except OldError Reply))
    (erase : (question : Question) → Error question → OldError)
    (program : Program Question Reply Value) (oracle : InnerQuestion → InnerReply)
    (compatible : ∀ question,
      ((handlers question).protocol.run oracle).value.mapError (erase question) =
        ((oldHandlers question).protocol.run oracle).value ∧
      ((handlers question).protocol.run oracle).trace = ((oldHandlers question).protocol.run oracle).trace) :
    let progressed := (substituteCheckedProgress handlers program).protocol.run oracle
    let original := (program.substituteChecked oldHandlers).protocol.run oracle
    progressed.value.mapError (fun stopped => erase stopped.question stopped.reason) = original.value ∧
      progressed.trace = original.trace := by
  induction program with
  | pure value => exact ⟨rfl, rfl⟩
  | request question next induction =>
      rw [substituteCheckedProgress_request, substituteChecked_request]
      unfold checkedStep
      constructor
      · dsimp only
        conv_lhs => rw [Program.bind_execution, Protocol.bind_run_value]
        conv_rhs => rw [Program.bind_execution, Protocol.bind_run_value]
        have head := (compatible question).1
        cases returned : ((handlers question).protocol.run oracle).value with
        | error failure =>
            rw [returned] at head
            change Except.error (erase question failure) = ((oldHandlers question).protocol.run oracle).value at head
            rw [← head]
            rfl
        | ok reply =>
            rw [returned] at head
            change Except.ok reply = ((oldHandlers question).protocol.run oracle).value at head
            rw [← head]
            dsimp only
            conv_lhs => rw [Program.map_execution, Protocol.map_run_value]
            conv_rhs => rw [Program.map_execution, Protocol.map_run_value]
            have earlier := (induction reply).1
            cases nextResult : ((substituteCheckedProgress handlers (next reply)).protocol.run oracle).value with
            | error stopped =>
                rw [nextResult] at earlier
                rewrite [← earlier]
                rfl
            | ok completed =>
                rw [nextResult] at earlier
                rw [← earlier]
                rfl
      · dsimp only
        conv_lhs => rw [Program.bind_execution, Protocol.bind_run_trace]
        conv_rhs => rw [Program.bind_execution, Protocol.bind_run_trace]
        have headValue := (compatible question).1
        have headTrace := (compatible question).2
        cases returned : ((handlers question).protocol.run oracle).value with
        | error failure =>
            rw [returned] at headValue
            change Except.error (erase question failure) =
              ((oldHandlers question).protocol.run oracle).value at headValue
            rw [← headValue]
            exact congrArg (fun trace => trace ++ []) headTrace
        | ok reply =>
            rw [returned] at headValue
            change Except.ok reply = ((oldHandlers question).protocol.run oracle).value at headValue
            rw [← headValue]
            dsimp only
            conv_lhs => rw [Program.map_execution, Protocol.map_run_trace]
            conv_rhs => rw [Program.map_execution, Protocol.map_run_trace]
            exact congrArg₂ List.append headTrace (induction reply).2

/-- A checked request with a query-free continuation records only its actual handler trace. -/
theorem substituteChecked_request_trace
    {InnerQuestion : Type x} {InnerReply : Type y} {Error : Type} [DecidableEq InnerQuestion]
    (handlers : Question → Program InnerQuestion InnerReply (Except Error Reply))
    (question : Question) (next : Reply → Program Question Reply Value) (oracle : InnerQuestion → InnerReply)
    (empty : ∀ reply, (((next reply).substituteChecked handlers).protocol.run oracle).trace = []) :
    (((Program.request question next).substituteChecked handlers).protocol.run oracle).trace =
      ((handlers question).protocol.run oracle).trace := by
  rw [substituteChecked_request, bind_execution, Protocol.bind_run_trace]
  cases result : ((handlers question).protocol.run oracle).value with
  | error invalid =>
      change ((handlers question).protocol.run oracle).trace ++ [] = _
      rw [List.append_nil]
  | ok reply =>
      rw [map_execution, Protocol.map_run_trace, empty reply, List.append_nil]

/-- Recorded requests return the original ordered questions paired with their actual replies. -/
theorem record_value [DecidableEq Question] (oracle : Question → Reply) : ∀ questions : List Question,
    (((record questions).protocol).run oracle).value = questions.map (fun question => (question, oracle question))
  | [] => rfl
  | question :: remaining => by
      change ((((record remaining).map (fun tail => (question, oracle question) :: tail)).protocol).run
        oracle).value = _
      rw [map_execution]
      change (question, oracle question) :: (((record remaining).protocol).run oracle).value = _
      rw [record_value oracle remaining]
      rfl

/-- Recorded requests retain their exact original questions and replies in execution order. -/
theorem record_trace [DecidableEq Question] (oracle : Question → Reply) : ∀ questions : List Question,
    (((record questions).protocol).run oracle).trace = questions.map (fun question => ⟨question, oracle question⟩)
  | [] => rfl
  | question :: remaining => by
      change (⟨question, oracle question⟩ : Basic.Exchange Question Reply) ::
        ((((record remaining).map (fun tail => (question, oracle question) :: tail)).protocol).run oracle).trace = _
      rw [map_execution, Protocol.map_run_trace, record_trace oracle remaining]
      rfl

/-- Compiling substituted constructions agrees with checked expansion, including both complete ordered logs. -/
theorem substituteChecked_execution
    {InnerQuestion : Type x} {InnerReply : Type y} {Error : Type} [DecidableEq InnerQuestion]
    (handlers : Question → Program InnerQuestion InnerReply (Except Error Reply))
    (program : Program Question Reply Value) (oracle : InnerQuestion → InnerReply) :
    ((program.substituteChecked handlers).protocol).run oracle =
      (program.expandChecked (fun question => (handlers question).protocol)).run oracle := by
  induction program with
  | pure value => rfl
  | request question next induction =>
      rewrite [substituteChecked, checkedStep, bind_execution, expandChecked]
      apply Protocol.bind_execution_eq _ _ _ _ oracle rfl
      cases ((handlers question).protocol.run oracle).value with
      | error error => rfl
      | ok reply =>
          rewrite [map_execution]
          exact Protocol.map_execution_eq _ _ _ oracle (induction reply)

/-- Pointwise equal handler executions give equal complete checked substitutions.

The comparison follows the actual reply selected at each request and retains
the ordered inner trace, without requiring equality of handler functions.
-/
theorem substituteChecked_handlers_eq
    {InnerQuestion : Type x} {InnerReply : Type y} {Error : Type} [DecidableEq InnerQuestion]
    (first second : Question → Program InnerQuestion InnerReply (Except Error Reply))
    (program : Program Question Reply Value) (oracle : InnerQuestion → InnerReply)
    (same : ∀ question, ((first question).protocol.run oracle) = ((second question).protocol.run oracle)) :
    ((program.substituteChecked first).protocol.run oracle) =
      ((program.substituteChecked second).protocol.run oracle) := by
  rw [substituteChecked_execution, substituteChecked_execution]
  induction program with
  | pure value => rfl
  | request question next induction =>
      rewrite [expandChecked, expandChecked]
      apply Protocol.bind_execution_eq _ _ _ _ oracle (same question)
      cases ((second question).protocol.run oracle).value with
      | error error => rfl
      | ok reply => exact Protocol.map_execution_eq _ _ _ oracle (induction reply)

/-- Checked substitution distributes over a bind after projecting its returned outer execution.

The first handler error stops the computation. On success the continuation
uses the same returned value, and both sides retain the complete ordered inner trace.
-/
theorem substituteChecked_bind_execution
    {InnerQuestion : Type x} {InnerReply : Type y} {Error : Type} [DecidableEq InnerQuestion]
    (handlers : Question → Program InnerQuestion InnerReply (Except Error Reply))
    (first : Program Question Reply Value) (next : Value → Program Question Reply Result)
    (oracle : InnerQuestion → InnerReply) :
    ((((first.bind next).substituteChecked handlers).map
      (fun result => result.map (fun execution => execution.value))).protocol.run oracle) =
      (((first.substituteChecked handlers).bind fun result => match result with
        | .error error => .pure (.error error)
        | .ok before => ((next before.value).substituteChecked handlers).map
            (fun result => result.map (fun execution => execution.value))).protocol.run oracle) := by
  induction first with
  | pure value =>
      change ((((next value).substituteChecked handlers).map
        (fun result => result.map (fun execution => execution.value))).protocol.run oracle) = _
      rfl
  | request question remaining induction =>
      rw [bind, substituteChecked_request, map_execution, bind_execution,
        substituteChecked_request]
      apply Basic.Execution.ext
      · rw [Protocol.map_run_value, bind_execution, Protocol.bind_run_value,
          Protocol.bind_run_value, bind_execution, Protocol.bind_run_value]
        cases returned : ((handlers question).protocol.run oracle).value with
        | error error => rfl
        | ok reply =>
            have agree := congrArg Basic.Execution.value (induction reply)
            rw [map_execution, Protocol.map_run_value, bind_execution, Protocol.bind_run_value] at agree
            dsimp only
            rw [map_execution, Protocol.map_run_value, map_execution, Protocol.map_run_value]
            cases before : (((remaining reply).substituteChecked handlers).protocol.run oracle).value with
            | error failure =>
                rw [before] at agree
                dsimp only at agree ⊢
                cases after : ((((remaining reply).bind next).substituteChecked handlers).protocol.run
                    oracle).value with
                | error error => rw [after] at agree; exact agree
                | ok execution => rw [after] at agree; exact agree
            | ok execution =>
                rw [before] at agree
                dsimp only at agree ⊢
                cases after : ((((remaining reply).bind next).substituteChecked handlers).protocol.run
                    oracle).value with
                | error error => rw [after] at agree; exact agree
                | ok execution => rw [after] at agree; exact agree
      · rw [Protocol.map_run_trace, bind_execution, Protocol.bind_run_trace,
          Protocol.bind_run_trace, bind_execution, Protocol.bind_run_trace]
        cases returned : ((handlers question).protocol.run oracle).value with
        | error error =>
            rw [Protocol.bind_run_value, returned]
            change ((handlers question).protocol.run oracle).trace ++ [] =
              (((handlers question).protocol.run oracle).trace ++ []) ++ []
            rw [Append.append_nil, Append.append_nil]
        | ok reply =>
            rw [Protocol.bind_run_value, returned]
            dsimp only
            rw [map_execution, Protocol.map_run_trace, map_execution, Protocol.map_run_trace,
              Protocol.map_run_value]
            have agree := congrArg Basic.Execution.trace (induction reply)
            rw [map_execution, Protocol.map_run_trace, bind_execution, Protocol.bind_run_trace] at agree
            cases before : (((remaining reply).substituteChecked handlers).protocol.run oracle).value with
            | error failure =>
                rw [before] at agree
                dsimp only at agree ⊢
                rw [Append.append_assoc]
                exact congrArg (List.append ((handlers question).protocol.run oracle).trace) agree
            | ok execution =>
                rw [before] at agree
                dsimp only at agree ⊢
                rw [Append.append_assoc]
                exact congrArg (List.append ((handlers question).protocol.run oracle).trace) agree

/-- Checked substitution of a mapped program projects the same mapped original value and trace. -/
theorem substituteChecked_map_execution
    {InnerQuestion : Type x} {InnerReply : Type y} {Error : Type} [DecidableEq InnerQuestion]
    (handlers : Question → Program InnerQuestion InnerReply (Except Error Reply))
    (program : Program Question Reply Value) (function : Value → Result)
    (oracle : InnerQuestion → InnerReply) :
    ((((program.map function).substituteChecked handlers).map
      (fun result => result.map (fun execution => execution.value))).protocol.run oracle) =
      (((program.substituteChecked handlers).map
        (fun result => result.map (fun execution => function execution.value))).protocol.run oracle) := by
  change (((((program.bind fun value => .pure (function value)).substituteChecked handlers).map
    (fun result => result.map (fun execution => execution.value))).protocol.run oracle) = _)
  rw [substituteChecked_bind_execution]
  apply Basic.Execution.ext
  · rw [bind_execution, Protocol.bind_run_value, map_execution, Protocol.map_run_value]
    cases returned : ((program.substituteChecked handlers).protocol.run oracle).value with
    | error error => rfl
    | ok execution => rfl
  · rw [bind_execution, Protocol.bind_run_trace, map_execution, Protocol.map_run_trace]
    cases returned : ((program.substituteChecked handlers).protocol.run oracle).value with
    | error error =>
        change ((program.substituteChecked handlers).protocol.run oracle).trace ++ [] = _
        exact Append.append_nil _
    | ok execution =>
        change ((program.substituteChecked handlers).protocol.run oracle).trace ++ [] = _
        exact Append.append_nil _

/-- A scalar view of checked substitution distributes over the actual bound execution. -/
theorem substituteChecked_bind_map_execution
    {InnerQuestion : Type x} {InnerReply : Type y} {Error Output : Type} [DecidableEq InnerQuestion]
    (handlers : Question → Program InnerQuestion InnerReply (Except Error Reply))
    (first : Program Question Reply Value) (next : Value → Program Question Reply Result)
    (view : Except Error Result → Output) (oracle : InnerQuestion → InnerReply) :
    ((((first.bind next).substituteChecked handlers).map
      (fun result => view (result.map (fun execution => execution.value)))).protocol.run oracle) =
      ((((first.substituteChecked handlers).bind fun result => match result with
        | .error error => .pure (.error error)
        | .ok before => ((next before.value).substituteChecked handlers).map
            (fun result => result.map (fun execution => execution.value))).map view).protocol.run oracle) := by
  have same := substituteChecked_bind_execution handlers first next oracle
  apply Basic.Execution.ext
  · rw [map_execution, Protocol.map_run_value, map_execution, Protocol.map_run_value]
    have values := congrArg Basic.Execution.value same
    rw [map_execution, Protocol.map_run_value] at values
    exact congrArg view values
  · rw [map_execution, Protocol.map_run_trace, map_execution, Protocol.map_run_trace]
    have traces := congrArg Basic.Execution.trace same
    rw [map_execution, Protocol.map_run_trace] at traces
    exact traces

/-- A scalar view of checked substitution commutes with mapping the original program. -/
theorem substituteChecked_map_map_execution
    {InnerQuestion : Type x} {InnerReply : Type y} {Error Output : Type} [DecidableEq InnerQuestion]
    (handlers : Question → Program InnerQuestion InnerReply (Except Error Reply))
    (program : Program Question Reply Value) (function : Value → Result)
    (view : Except Error Result → Output) (oracle : InnerQuestion → InnerReply) :
    ((((program.map function).substituteChecked handlers).map
      (fun result => view (result.map (fun execution => execution.value)))).protocol.run oracle) =
      ((((program.substituteChecked handlers).map
        (fun result => result.map (fun execution => function execution.value))).map view).protocol.run oracle) := by
  have same := substituteChecked_map_execution handlers program function oracle
  apply Basic.Execution.ext
  · rw [map_execution, Protocol.map_run_value, map_execution, Protocol.map_run_value]
    have values := congrArg Basic.Execution.value same
    rw [map_execution, Protocol.map_run_value] at values
    exact congrArg view values
  · rw [map_execution, Protocol.map_run_trace, map_execution, Protocol.map_run_trace]
    have traces := congrArg Basic.Execution.trace same
    rw [map_execution, Protocol.map_run_trace] at traces
    exact traces

/-- Pointwise equal original value maps preserve any scalar view of their checked executions.

The value comparison uses only the actual returned value; the complete
ordered handler trace is the same for both original maps.
-/
theorem substituteChecked_map_pointwise_view_execution
    {InnerQuestion : Type x} {InnerReply : Type y} {Error Output : Type} [DecidableEq InnerQuestion]
    (handlers : Question → Program InnerQuestion InnerReply (Except Error Reply))
    (program : Program Question Reply Value) (first second : Value → Result)
    (same : ∀ value, first value = second value) (view : Except Error Result → Output)
    (oracle : InnerQuestion → InnerReply) :
    ((((program.map first).substituteChecked handlers).map
      (fun result => view (result.map (fun execution => execution.value)))).protocol.run oracle) =
    ((((program.map second).substituteChecked handlers).map
      (fun result => view (result.map (fun execution => execution.value)))).protocol.run oracle) := by
  rw [substituteChecked_map_map_execution, substituteChecked_map_map_execution]
  apply Basic.Execution.ext
  · rw [map_execution, Protocol.map_run_value, map_execution, Protocol.map_run_value,
      map_execution, Protocol.map_run_value, map_execution, Protocol.map_run_value]
    cases returned : ((program.substituteChecked handlers).protocol.run oracle).value with
    | error error => rfl
    | ok execution => exact congrArg view (congrArg Except.ok (same execution.value))
  · rw [map_execution, Protocol.map_run_trace, map_execution, Protocol.map_run_trace,
      map_execution, Protocol.map_run_trace, map_execution, Protocol.map_run_trace]

/-- Iterate the retained step construction from the same state for a displayed finite count. -/
@[expose] def iterate (step : Value → Program Question Reply Value) : Nat → Value → Program Question Reply Value
  | 0, state => .pure state
  | count + 1, state => (step state).bind (iterate step count)

/-- Iteration compilation retains every original step's ordered execution. -/
theorem iterate_execution [DecidableEq Question] (step : Value → Program Question Reply Value)
    (count : Nat) (state : Value) (oracle : Question → Reply) :
    ((iterate step count state).protocol).run oracle =
      (Protocol.iterate (fun value => (step value).protocol) count state).run oracle := by
  induction count generalizing state with
  | zero => rfl
  | succ count induction =>
      rewrite [iterate, bind_execution, Protocol.iterate]
      change (let before := (step state).protocol.run oracle
        ; let after := (iterate step count before.value).protocol.run oracle
        ; (⟨after.value, before.trace ++ after.trace⟩ : Basic.Execution Question Reply Value)) = _
      dsimp only
      rewrite [induction ((step state).protocol.run oracle).value]
      rfl

/-- Expansion agrees with the original complete outer execution, including adaptive questions and repeated replies. -/
theorem expand_value [DecidableEq Question] {InnerQuestion : Type x} {InnerReply : Type y}
    (handlers : Question → Protocol InnerQuestion InnerReply Reply)
    (program : Program Question Reply Value) (oracle : InnerQuestion → InnerReply) :
    ((program.expand handlers).run oracle).value =
      program.protocol.run (fun question => ((handlers question).run oracle).value) := by
  induction program with
  | pure value => rfl
  | request question next induction =>
      rewrite [expand, Protocol.bind_run_value, Protocol.map_run_value,
        induction ((handlers question).run oracle).value]
      rfl

/-- Successful actual checked handlers preserve the whole original outer execution and every repeated request. -/
theorem expandChecked_value [DecidableEq Question] {InnerQuestion : Type x} {InnerReply : Type y} {Error : Type}
    (handlers : Question → Protocol InnerQuestion InnerReply (Except Error Reply))
    (program : Program Question Reply Value) (oracle : InnerQuestion → InnerReply) (answer : Question → Reply)
    (success : ∀ question, ((handlers question).run oracle).value = .ok (answer question)) :
    ((program.expandChecked handlers).run oracle).value = .ok (program.protocol.run answer) := by
  induction program with
  | pure value => rfl
  | request question next induction =>
      rewrite [expandChecked, Protocol.bind_run_value, success question]
      dsimp only
      rewrite [Protocol.map_run_value, induction (answer question)]
      rfl

/-- Successful substituted handlers retain the complete original outer execution for every actual query. -/
theorem substituteChecked_value {InnerQuestion : Type x} {InnerReply : Type y} {Error : Type}
    [DecidableEq Question] [DecidableEq InnerQuestion]
    (handlers : Question → Program InnerQuestion InnerReply (Except Error Reply))
    (program : Program Question Reply Value) (oracle : InnerQuestion → InnerReply) (answer : Question → Reply)
    (success : ∀ question, ((handlers question).protocol.run oracle).value = .ok (answer question)) :
    ((program.substituteChecked handlers).protocol.run oracle).value = .ok (program.protocol.run answer) := by
  rewrite [substituteChecked_execution]
  exact expandChecked_value (fun question => (handlers question).protocol) program oracle answer success

/-- Replaying the expanded trace returns the same complete outer execution without consulting the inner oracle. -/
theorem expand_replay [DecidableEq Question] {InnerQuestion : Type x} {InnerReply : Type y}
    (handlers : Question → Protocol InnerQuestion InnerReply Reply)
    (program : Program Question Reply Value) (oracle : InnerQuestion → InnerReply) :
    (program.expand handlers).replayExact ((program.expand handlers).run oracle).trace =
      .ok (program.protocol.run (fun question => ((handlers question).run oracle).value)) :=
  ((program.expand handlers).replayExact_run oracle).trans (congrArg Except.ok (expand_value handlers program oracle))

/-- Payload changes outside the actual internal requests preserve the complete expanded execution and both logs. -/
theorem expand_payload_erasure {InnerQuestion : Type x} {InnerReply : Type y} [DecidableEq InnerQuestion]
    {Payload : Type} (handlers : Question → Protocol InnerQuestion InnerReply Reply)
    (program : Program Question Reply Value) (oracle : InnerQuestion → InnerReply)
    (payload : Payload) (outside : Payload → InnerQuestion → InnerReply) :
    let computation := program.expand handlers
    computation.run (Boundary.Trace.overlay (computation.run oracle).trace (outside payload)) =
      computation.run oracle :=
  Protocol.annotation_erasure (program.expand handlers) oracle payload outside

end Program

end Purelib.Computation.Query
