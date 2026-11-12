module

public import Purelib.Approximation.Gaussian.Observation.Observer.Expression
public import Purelib.Computation.Query.Path
public import Purelib.Computation.Query.Computation
import Purelib.Data.List.GetD
import Purelib.Data.List.Append

/-!
# Source-independent numerical query machines

Numerical syntax is interpreted through its finite command view. Reply
projections preserve the original register order and complete saved exchanges.
All observer backends share frame execution, fuel recursion and compilation.
-/

public section

namespace Purelib.Computation.Machine.Numerical

open Purelib.Approximation.Gaussian.Observation.Observer
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Computation.Query

universe u v w x

set_option genInjectivity false in
/-- A finite control frame retains its actual block or bounded iteration body.

Iteration keeps the supplied instruction body and its remaining natural count.
Executing a frame never expands that body into a copied instruction list.
-/
inductive Frame (Instruction : Type u) where
  /-- Continue the original finite instruction spine. -/ | block (instructions : List Instruction)
  /-- Retain the finite iteration count and original body. -/ | iteration (remaining : Nat) (body : List Instruction)
  /-- Execute the original finite program at its explicit instruction counter. -/ | counter
      (program : List Instruction) (index : Nat)
  /-- Retain the original caller registers and exact continuation until an explicit return. -/ | caller
      (registers : List Value) (continuation : List (Frame Instruction))
  /-- Recheck the numerical condition before each iteration of the same retained body. -/ | condition
      (expression : Expr) (body : List Instruction)

set_option genInjectivity false in
/-- Source-independent observer state retains finite registers, its actual mixed path and ordered saved exchanges.

The request path and exchange list preserve order and repetitions. Numerical
state carries no source identity; a source context supplies any relation to an
original recording.
-/
structure State (Request : Type v) (Reply : Type w) where
  /-- The finite numerical registers, newest first. -/ registers : List Value
  /-- The exact actual path of newly issued mixed requests. -/ path : List Request
  /-- The exact saved numerical exchanges, including repeated occurrences. -/ past :
    Basic.Trace (Path.Question Request) Reply

namespace State

variable {Request : Type v} {Reply : Type w}

/-- Start finite observer control with fixed numerical parameters and an empty path and trace. -/
@[expose] def initial (registers : List Value) : State Request Reply := ⟨registers, [], []⟩

/-- Push a numerical value while retaining the exact source path and saved exchanges. -/
@[expose] def push (state : State Request Reply) (value : Value) : State Request Reply :=
  { state with registers := value :: state.registers }

/-- Store a numerical register, extending absent preceding registers with natural zero. -/
@[expose] def put : List Value → Nat → Value → List Value
  | [], 0, value => [value]
  | [], index + 1, value => .natural 0 :: put [] index value
  | _ :: remaining, 0, value => value :: remaining
  | earlier :: remaining, index + 1, value => earlier :: put remaining index value

/-- Update the original numerical registers while retaining the exact path and saved exchanges. -/
@[expose] def store (state : State Request Reply) (index : Nat) (value : Value) : State Request Reply :=
  { state with registers := put state.registers index value }

/-- Replace local registers without changing the original numerical path or saved exchanges. -/
@[expose] def withRegisters (state : State Request Reply) (registers : List Value) : State Request Reply :=
  { state with registers := registers }

end State

namespace Frame

/-- Redirect the nearest original counter frame, preserving its program and caller boundary.

Temporary block and iteration frames are discarded. A jump cannot cross an
original caller frame; absence of a counter is a concrete numerical failure.
-/
@[expose] def redirect {Instruction : Type u} (target : Nat) :
    List (Frame Instruction) → Option (List (Frame Instruction))
  | [] => none
  | .counter program _ :: rest => some (.counter program target :: rest)
  | .caller _ _ :: _ => none
  | .block _ :: rest | .iteration _ _ :: rest | .condition _ _ :: rest => redirect target rest

/-- Read the nearest original caller's registers and exact retained continuation. -/
@[expose] def returnTo {Instruction : Type u} : List (Frame Instruction) →
    Option (List Value × List (Frame Instruction))
  | [] => none
  | .caller registers continuation :: _ => some (registers, continuation)
  | .block _ :: rest | .iteration _ _ :: rest | .counter _ _ :: rest | .condition _ _ :: rest => returnTo rest

end Frame

set_option genInjectivity false in
/-- A displayed mixed query is a new request or the same original saved path question.

A recall retains both its original coordinate and complete exchange. Legality
checks that coordinate against the same state's saved trace; a new request
extends that state's actual request path.
-/
inductive Query (Request : Type v) (Reply : Type w) where
  /-- Advance the actual current mixed request path. -/ | request (request : Request)
  /-- Repeat the actual exchange retained at its original finite coordinate. -/ | recall
      (index : Nat) (entry : Basic.Exchange (Path.Question Request) Reply)

namespace Query

variable {Request : Type v} {Reply : Type w}

/-- A recall identifies its exact original numerical occurrence in the saved trace. -/
@[expose] def Legal (query : Query Request Reply) (state : State Request Reply) : Prop :=
  match query with
  | .request _ => True
  | .recall index entry => Data.List.getElem? state.past index = some entry

/-- Read the actual path question denoted by this mixed observer query. -/
@[expose] def question (query : Query Request Reply) (state : State Request Reply) : Path.Question Request :=
  match query with
  | .request nextRequest => ⟨state.path, nextRequest⟩
  | .recall _ entry => entry.query

/-- Consume the original reply registers while retaining its complete numerical exchange.

The supplied projection prepends registers in their original order. New
requests extend the path, recalls leave it fixed, and both append the exact
question and complete received reply to the saved trace.
-/
@[expose] def receive (registers : Reply → List Value) (query : Query Request Reply)
    (state : State Request Reply) (reply : Reply) : State Request Reply :=
  let question := query.question state
  { registers := registers reply ++ state.registers
    path := match query with
      | .request _ => question.path
      | .recall _ _ => state.path
    past := state.past ++ [⟨question, reply⟩] }

end Query

set_option genInjectivity false in
/-- One pure numerical control step stops, continues or issues a certified displayed mixed query.

A pure continuation certifies that its request path and saved exchanges remain
unchanged. An asking continuation retains the displayed query's legality at
the exact preceding numerical state.
-/
inductive Action {Request : Type v} {Reply : Type w} (Instruction : Type u) (state : State Request Reply) where
  /-- Stop with the actual finite numerical outcome. -/ | stop (outcome : Outcome)
  /-- Continue while retaining the same original path and saved exchanges. -/ | next
      (control : List (Frame Instruction)) (nextState : State Request Reply)
      (pathEq : nextState.path = state.path) (pastEq : nextState.past = state.past)
  /-- Issue the legal displayed query and retain the finite continuation frames. -/ | ask
      (query : Query Request Reply) (control : List (Frame Instruction)) (legal : query.Legal state)

set_option genInjectivity false in
/-- The common finite control operations of an original numerical instruction.

A command view retains the original branch and iteration bodies. Backend
request operations remain explicit data; their interpreter is supplied to
control execution rather than stored as a callback in the command.
-/
inductive Command (Instruction : Type u) (Operation : Type x) where
  /-- Push one computed numerical value. -/ | assign (expression : Expr)
  /-- Execute the backend's finite numerical request operation. -/ | operation (operation : Operation)
  /-- Recall an actual saved numerical occurrence. -/ | recall (index : Expr)
  /-- Select one retained instruction block. -/ | branch
      (condition : Expr) (whenTrue whenFalse : List Instruction)
  /-- Repeat one retained instruction body a computed finite number of times. -/ | iterate
      (count : Expr) (body : List Instruction)
  /-- Return the computed numerical value from the complete observer execution. -/ | returnValue (expression : Expr)
  /-- Store a computed numerical value at its original register coordinate. -/ | store (index : Nat) (expression : Expr)
  /-- Set the nearest retained original instruction counter. -/ | jump (target : Nat)
  /-- Choose an explicit counter target from a numerical Boolean condition. -/ | jumpIf
      (condition : Expr) (whenTrue whenFalse : Nat)
  /-- Invoke the same finite numerical code with one explicit numerical argument. -/ | call
      (program : List Instruction) (argument : Expr)
  /-- Restore the original caller with the computed numerical result prepended to its registers. -/ | returnCall
      (expression : Expr)
  /-- Repeat a retained finite body while its actual numerical condition remains true. -/ | while
      (condition : Expr) (body : List Instruction)

variable {Instruction : Type u} {Operation : Type x} {Request : Type v} {Reply : Type w}

/-- Check a numerical request target and retain its exact strict-positivity proof.

Evaluation must return a rational value with a positive target. Success passes
that same value and positivity evidence to the supplied original constructor;
failure retains the expression error, wrong value kind or nonpositive target.
-/
@[expose] def target (make : (target : Fraction.Rational) → 0 < target → Request)
    (expression : Expr) (registers : List Value) : Except Error Request :=
  match expression.evaluate registers with
  | .error error => .error error
  | .ok (.rational target) =>
      if positive : 0 < target then .ok (make target positive)
      else .error (.nonpositiveTarget target positive)
  | .ok value => .error (.targetType value)

/-- Check an additional natural request count without changing its value.

A natural result, including zero, is passed unchanged to the original request
constructor. Expression failures and wrong numerical kinds retain their exact
error data.
-/
@[expose] def count (make : Nat → Request) (expression : Expr) (registers : List Value) : Except Error Request :=
  match expression.evaluate registers with
  | .error error => .error error
  | .ok (.natural count) => .ok (make count)
  | .ok value => .error (.countType value)

/-- Execute a displayed instruction with its exact retained continuation.

All numerical evaluation uses the original expression evaluator. Calls retain
finite program data, original caller registers and their exact continuation;
counter jumps and caller returns never capture a source or host callback.
-/
@[expose] def commandStep (view : Instruction → Command Instruction Operation)
    (request : Operation → List Value → Except Error Request) (instruction : Instruction)
    (next : List (Frame Instruction)) (state : State Request Reply) : Action Instruction state :=
  match view instruction with
  | .assign expression =>
      match expression.evaluate state.registers with
      | .error error => .stop (.failed error)
      | .ok value => .next next (state.push value) rfl rfl
  | .returnValue expression =>
      match expression.evaluate state.registers with
      | .error error => .stop (.failed error)
      | .ok value => .stop (.returned value)
  | .operation operation =>
      match request operation state.registers with
      | .error error => .stop (.failed error)
      | .ok requested => .ask (.request requested) next trivial
  | .recall expression =>
      match expression.evaluate state.registers with
      | .error error => .stop (.failed error)
      | .ok (.natural index) =>
          match found : Data.List.getElem? state.past index with
          | none => .stop (.failed (.missingRecall index))
          | some entry => .ask (.recall index entry) next found
      | .ok value => .stop (.failed (.recallType value))
  | .branch expression whenTrue whenFalse =>
      match expression.evaluate state.registers with
      | .error error => .stop (.failed error)
      | .ok (.bit decision) => .next (.block (if decision then whenTrue else whenFalse) :: next) state rfl rfl
      | .ok value => .stop (.failed (.branchType value))
  | .iterate expression body =>
      match expression.evaluate state.registers with
      | .error error => .stop (.failed error)
      | .ok (.natural count) => .next (.iteration count body :: next) state rfl rfl
      | .ok value => .stop (.failed (.countType value))

  | .store index expression =>
      match expression.evaluate state.registers with
      | .error error => .stop (.failed error)
      | .ok value => .next next (state.store index value) rfl rfl
  | .jump target =>
      match Frame.redirect target next with
      | none => .stop (.failed .missingCounter)
      | some control => .next control state rfl rfl
  | .jumpIf expression whenTrue whenFalse =>
      match expression.evaluate state.registers with
      | .error error => .stop (.failed error)
      | .ok (.bit decision) =>
          match Frame.redirect (if decision then whenTrue else whenFalse) next with
          | none => .stop (.failed .missingCounter)
          | some control => .next control state rfl rfl
      | .ok value => .stop (.failed (.branchType value))
  | .call program argument =>
      match argument.evaluate state.registers with
      | .error error => .stop (.failed error)
      | .ok value => .next [.counter program 0, .caller state.registers next]
          (state.withRegisters [value]) rfl rfl
  | .returnCall expression =>
      match expression.evaluate state.registers with
      | .error error => .stop (.failed error)
      | .ok value =>
          match Frame.returnTo next with
          | none => .stop (.failed .missingCaller)
          | some (registers, continuation) =>
              .next continuation (state.withRegisters (value :: registers)) rfl rfl
  | .while expression body => .next (.condition expression body :: next) state rfl rfl

/-- Execute one finite numerical transition on original block, counter or caller frames.

Original first-order block and bounded-iteration transitions keep their exact
fuel convention. A counter fetch, numerical branch, call, return or condition
check is one transition. Only displayed queries reach a source adapter.
-/
@[expose] def step (view : Instruction → Command Instruction Operation)
    (request : Operation → List Value → Except Error Request)
    (control : List (Frame Instruction)) (state : State Request Reply) : Action Instruction state :=
  match control with
  | [] => .stop (.failed .missingReturn)
  | .block [] :: rest => .next rest state rfl rfl
  | .iteration 0 _ :: rest => .next rest state rfl rfl
  | .iteration (remaining + 1) body :: rest =>
      .next (.block body :: .iteration remaining body :: rest) state rfl rfl
  | .block (instruction :: remaining) :: rest =>
      commandStep view request instruction (.block remaining :: rest) state
  | .counter program index :: rest =>
      match Data.List.getElem? program index with
      | none => .next rest state rfl rfl
      | some instruction => commandStep view request instruction (.counter program (index + 1) :: rest) state
  | .caller _ _ :: _ => .stop (.failed .missingReturn)
  | .condition expression body :: rest =>
      match expression.evaluate state.registers with
      | .error error => .stop (.failed error)
      | .ok (.bit decision) =>
          if decision then .next (.block body :: .condition expression body :: rest) state rfl rfl
          else .next rest state rfl rfl
      | .ok value => .stop (.failed (.branchType value))

/-- Run finite mixed numerical control against an oracle, retaining its complete ordered execution.

Every control transition consumes one fuel unit, including pure frame work.
Each asking transition reads one actual reply, receives its original numerical
registers and prepends that exchange to the remaining execution trace. Zero
fuel returns finite exhaustion without issuing a query.
-/
@[expose] def run (step : List (Frame Instruction) → (state : State Request Reply) → Action Instruction state)
    (registers : Reply → List Value) : Nat → List (Frame Instruction) → State Request Reply →
    (Path.Question Request → Reply) → Basic.Execution (Path.Question Request) Reply Outcome
  | 0, _, _, _ => ⟨.exhausted, []⟩
  | fuel + 1, control, state, oracle =>
      match step control state with
      | .stop outcome => ⟨outcome, []⟩
      | .next next nextState _pathEq _pastEq => run step registers fuel next nextState oracle
      | .ask query next _legal =>
          let question := query.question state
          let reply := oracle question
          let later := run step registers fuel next (query.receive registers state reply) oracle
          ⟨later.value, ⟨question, reply⟩ :: later.trace⟩

/-- Compile the same finite mixed control to the existing recording and replay protocol.

Compilation uses the same step function, reply projection and fuel transitions
as numerical execution. Request equality enables the protocol's exact replay
checks; returned, failed and exhausted outcomes keep their original boundaries.
-/
@[expose] def compile [DecidableEq Request]
    (step : List (Frame Instruction) → (state : State Request Reply) → Action Instruction state)
    (registers : Reply → List Value) : Nat → List (Frame Instruction) → State Request Reply →
    Protocol (Path.Question Request) Reply Outcome
  | 0, _, _ => Protocol.pure .exhausted
  | fuel + 1, control, state =>
      match step control state with
      | .stop outcome => Protocol.pure outcome
      | .next next nextState _pathEq _pastEq => compile step registers fuel next nextState
      | .ask query next _legal =>
          (Protocol.query (query.question state)).bind
            (fun reply => compile step registers fuel next (query.receive registers state reply))

/-- Protocol compilation preserves the entire mixed interpreter execution for every finite control and oracle.

The equality includes the complete outcome and ordered query/reply trace for
any numerical state, retained frames and finite fuel. Both interpreters use
the same supplied step function and original reply-register projection.
-/
theorem compile_run [DecidableEq Request]
    (step : List (Frame Instruction) → (state : State Request Reply) → Action Instruction state)
    (registers : Reply → List Value) (fuel : Nat) (control : List (Frame Instruction))
    (state : State Request Reply) (oracle : Path.Question Request → Reply) :
    (compile step registers fuel control state).run oracle = run step registers fuel control state oracle := by
  induction fuel generalizing control state with
  | zero => rfl
  | succ fuel induction =>
      rewrite [compile, run]
      cases action : step control state with
      | stop outcome => rfl
      | next next nextState _pathEq _pastEq => exact induction next nextState
      | ask query next _legal =>
          change (let later :=
                    (compile step registers fuel next
                      (query.receive registers state (oracle (query.question state)))).run oracle
                  (⟨later.value, ⟨query.question state, oracle (query.question state)⟩ :: later.trace⟩ :
                    Basic.Execution (Path.Question Request) Reply Outcome)) = _
          rewrite [induction next (query.receive registers state (oracle (query.question state)))]
          rfl

end Purelib.Computation.Machine.Numerical

end
