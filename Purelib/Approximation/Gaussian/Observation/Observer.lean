module

public import Purelib.Approximation.Gaussian.Observation.Continuation
public import Purelib.Computation.Machine.Numerical
import Purelib.Computation.Query.Computation
import Purelib.Data.Rat.Fraction.Arithmetic

/-!
# Finite first-order numerical observers

Control consists only of explicit numerical expressions and instructions.
No expression carries a source, a predicate, or a function-valued callback.
Finite control frames implement bounded iteration without expanding a loop
into copies of its body. Fuel bounds the complete interpreter, including
pure steps; exhaustion is a finite execution outcome.
-/

public section

namespace Purelib.Approximation.Gaussian.Observation.Observer

open Purelib
open Purelib.Computation.Machine
open Purelib.Approximation
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Computation.Query

set_option genInjectivity false in
/-- Finite first-order instructions with numerical branching and bounded iteration. -/
inductive Instruction where
  /-- Push one computed finite numerical register. -/ | assign (expression : Expr)
  /-- Refine the retained enclosure spine at the computed rational target. -/ | refine (target : Expr)
  /-- Issue the exact question of an earlier saved occurrence again. -/ | recall (index : Expr)
  /-- Select one finite instruction block by a numerical decision. -/ | branch
      (condition : Expr) (whenTrue whenFalse : List Instruction)
  /-- Execute the same finite body a computed finite number of times. -/ | iterate
      (count : Expr) (body : List Instruction)
  /-- Return the computed numerical value. -/ | returnValue (expression : Expr)
  /-- Store a computed value at an explicit numerical register coordinate. -/ | store (index : Nat) (expression : Expr)
  /-- Redirect the nearest retained original program counter. -/ | jump (target : Nat)
  /-- Branch to one explicit counter from a numerical Boolean. -/ | jumpIf (condition : Expr) (whenTrue whenFalse : Nat)
  /-- Invoke finite source-independent numerical code with one explicit argument. -/ | call
      (program : List Instruction) (argument : Expr)
  /-- Return a computed result to the original retained caller. -/ | returnCall (expression : Expr)
  /-- Repeat a finite body while its numerical condition remains true. -/ | while
      (condition : Expr) (body : List Instruction)

/-- View each original enclosure instruction as a shared finite control command. -/
@[expose] def Instruction.command : Instruction → Numerical.Command Instruction Expr
  | .assign expression => .assign expression
  | .refine expression => .operation expression
  | .recall expression => .recall expression
  | .branch condition whenTrue whenFalse => .branch condition whenTrue whenFalse
  | .iterate count body => .iterate count body
  | .returnValue expression => .returnValue expression
  | .store index expression => .store index expression
  | .jump target => .jump target
  | .jumpIf condition whenTrue whenFalse => .jumpIf condition whenTrue whenFalse
  | .call program argument => .call program argument
  | .returnCall expression => .returnCall expression
  | .while condition body => .while condition body

/-- Read the one original enclosure register from a complete numerical reply. -/
@[expose] def replyRegisters (reply : Enclosure.Ball) : List Value := [.ball reply]

/-- The shared finite control frame retains the original instruction body. -/
abbrev Frame := Numerical.Frame Instruction

/-- Numerical state retains this backend's exact request path and complete saved exchanges. -/
abbrev State := Numerical.State Request Enclosure.Ball

namespace State

/-- Start the original numerical registers with an empty path and saved trace. -/
@[expose] def initial (registers : List Value) : State := Numerical.State.initial registers

/-- Push the supplied register while preserving the exact path and saved trace. -/
@[expose] def push (state : State) (value : Value) : State := Numerical.State.push state value

end State

/-- A numerical query is a new request or an original retained exchange at its actual coordinate. -/
abbrev Query := Numerical.Query Request Enclosure.Ball

namespace Query

/-- A recall is legal exactly at its original coordinate in the saved trace. -/
@[expose] def Legal (query : Query) (state : State) : Prop := Numerical.Query.Legal query state

/-- Read the complete original path question of this displayed query. -/
@[expose] def question (query : Query) (state : State) : Question := Numerical.Query.question query state

/-- Consume the complete reply with this backend's original numerical register projection. -/
@[expose] def receive (query : Query) (state : State) (reply : Enclosure.Ball) : State :=
  Numerical.Query.receive replyRegisters query state reply

end Query

/-- The shared action retains legal queries and exact path/trace preservation through pure steps. -/
abbrev Action (state : State) := Numerical.Action Instruction state

/-- Execute one original finite instruction through the shared numerical control engine. -/
@[expose] def step (control : List Frame) (state : State) : Action state :=
  Numerical.step Instruction.command (Numerical.target Request.ofPositive) control state

/-- Execute the original numerical control and retain its complete ordered execution. -/
@[expose] def run : Nat → List Frame → State → (Question → Enclosure.Ball) →
    Basic.Execution Question Enclosure.Ball Outcome := Numerical.run step replyRegisters

/-- Compile the same original control using the shared finite fuel recursion. -/
@[expose] def compile : Nat → List Frame → State → Protocol Question Enclosure.Ball Outcome :=
  Numerical.compile step replyRegisters

/-- Compilation preserves the complete original execution for every finite fuel and oracle. -/
theorem compile_run (fuel : Nat) (control : List Frame) (state : State)
    (oracle : Question → Enclosure.Ball) :
    (compile fuel control state).run oracle = run fuel control state oracle :=
  Numerical.compile_run step replyRegisters fuel control state oracle

/-- Execute finite numerical control from fixed source-independent initial registers.

An original first-order program starts at `[.block instructions]`, preserving
its exact transition fuel. Explicit counter programs start at
`[.counter instructions 0]`; callers, conditions and registers remain finite
source-independent data.
-/
@[expose] def execute (control : List Frame) (registers : List Value) (fuel : Nat)
    (oracle : Question → Enclosure.Ball) : Basic.Execution Question Enclosure.Ball Outcome :=
  run fuel control (State.initial registers) oracle

/-- Compile finite numerical control using the same fixed initial registers and transition fuel. -/
@[expose] def protocol (control : List Frame) (registers : List Value) (fuel : Nat) :
    Protocol Question Enclosure.Ball Outcome :=
  compile fuel control (State.initial registers)

/-- The compiled public observer returns exactly its actual interpreted result and ordered trace. -/
theorem protocol_run (control : List Frame) (registers : List Value) (fuel : Nat)
    (oracle : Question → Enclosure.Ball) :
    (protocol control registers fuel).run oracle = execute control registers fuel oracle :=
  compile_run fuel control (State.initial registers) oracle

/-- Compare two actual enclosure replies, choosing the second target from the first observed squared radius.

A positive first radius selects half that radius as the next target. An
exact first observation instead retains the supplied positive target. The
returned numerical decision compares the actual observed radii; it asserts
no symbolic property of the source.
-/
@[expose] def adaptiveEnclosureComparison (initial : Request) : List Instruction :=
  [ .refine (.literal (.rational initial.targetSq))
  , .branch (.binary .less (.literal (.rational 0)) (.unary .radiusSq (.variable 0)))
      [ .refine (.binary .divide (.unary .radiusSq (.variable 0)) (.literal (.rational 2)))
      , .returnValue (.binary .less (.unary .radiusSq (.variable 0)) (.unary .radiusSq (.variable 1))) ]
      [ .refine (.literal (.rational initial.targetSq))
      , .returnValue (.binary .equal (.unary .radiusSq (.variable 0)) (.literal (.rational 0))) ] ]

end Purelib.Approximation.Gaussian.Observation.Observer

end
