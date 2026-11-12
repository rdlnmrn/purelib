module

public import Purelib.Approximation.Gaussian.Observation.Prefix.Transcript
public import Purelib.Approximation.Gaussian.Observation.Cursor.Observer
import Purelib.Computation.Machine.Numerical
import Purelib.Computation.Query.Computation
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic

/-!
# Canonical first-order mixed numerical observers

The instruction and expression data are the original shared finite syntax.
Canonical replies expose their exact word, ambient squared radius and ball
as numerical registers. Complete original parser and inverse-chart caches
remain in the ordered trace. Explicit fuel bounds every control transition.
-/

public section

namespace Purelib.Approximation.Gaussian.Observation.Prefix.Observer

open Purelib
open Purelib.Computation.Machine
open Purelib.Approximation.Gaussian.Observation.Observer hiding Instruction Frame
open Purelib.Approximation.Gaussian.Observation.Cursor.Observer (Instruction Frame)
open Purelib.Computation.Query

/-- Read the original canonical word, ambient squared radius and ball registers in their original order. -/
@[expose] def replyRegisters (reply : Reply) : List Value :=
  [.word reply.word, .rational reply.ball.radiusSq, .ball reply.ball]

/-- Numerical state retains this backend's exact request path and complete saved exchanges. -/
abbrev State := Numerical.State Cursor.Request Reply

namespace State

/-- Start the original numerical registers with an empty path and saved trace. -/
@[expose] def initial (registers : List Value) : State := Numerical.State.initial registers

/-- Push the supplied register while preserving the exact path and saved trace. -/
@[expose] def push (state : State) (value : Value) : State := Numerical.State.push state value

end State

/-- A numerical query is a new request or an original retained exchange at its actual coordinate. -/
abbrev Query := Numerical.Query Cursor.Request Reply

namespace Query

/-- A recall is legal exactly at its original coordinate in the saved trace. -/
@[expose] def Legal (query : Query) (state : State) : Prop := Numerical.Query.Legal query state

/-- Read the complete original path question of this displayed query. -/
@[expose] def question (query : Query) (state : State) : Cursor.Question := Numerical.Query.question query state

/-- Consume the complete reply with this backend's original numerical register projection. -/
@[expose] def receive (query : Query) (state : State) (reply : Reply) : State :=
  Numerical.Query.receive replyRegisters query state reply

end Query

/-- The shared action retains legal queries and exact path/trace preservation through pure steps. -/
abbrev Action (state : State) := Numerical.Action Instruction state

/-- Execute one original finite instruction through the shared numerical control engine. -/
@[expose] def step (control : List Frame) (state : State) : Action state :=
  Numerical.step Cursor.Observer.Instruction.command Cursor.Observer.Operation.request control state

/-- Execute the original numerical control and retain its complete ordered execution. -/
@[expose] def run : Nat → List Frame → State → (Cursor.Question → Reply) →
    Basic.Execution Cursor.Question Reply Outcome := Numerical.run step replyRegisters

/-- Compile the same original control using the shared finite fuel recursion. -/
@[expose] def compile : Nat → List Frame → State → Protocol Cursor.Question Reply Outcome :=
  Numerical.compile step replyRegisters

/-- Compilation preserves the complete original execution for every finite fuel and oracle. -/
theorem compile_run (fuel : Nat) (control : List Frame) (state : State)
    (oracle : Cursor.Question → Reply) :
    (compile fuel control state).run oracle = run fuel control state oracle :=
  Numerical.compile_run step replyRegisters fuel control state oracle

/-- Run canonical numerical control from fixed finite frames, initial registers and transition fuel. -/
@[expose] def execute (control : List Frame) (registers : List Value) (fuel : Nat)
    (oracle : Cursor.Question → Reply) : Basic.Execution Cursor.Question Reply Outcome :=
  run fuel control (State.initial registers) oracle

/-- Compile the same fixed canonical control frames, initial registers and transition fuel. -/
@[expose] def protocol (control : List Frame) (registers : List Value) (fuel : Nat) :
    Protocol Cursor.Question Reply Outcome := compile fuel control (State.initial registers)

/-- The compiled public observer returns its actual result and complete ordered mixed trace. -/
theorem protocol_run (control : List Frame) (registers : List Value) (fuel : Nat)
    (oracle : Cursor.Question → Reply) :
    (protocol control registers fuel).run oracle = execute control registers fuel oracle :=
  compile_run fuel control (State.initial registers) oracle

end Purelib.Approximation.Gaussian.Observation.Prefix.Observer

end
