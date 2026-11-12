module

public import Purelib.Approximation.Gaussian.Observation.Cursor.Transcript
public import Purelib.Approximation.Gaussian.Observation.Observer
import Purelib.Computation.Machine.Numerical
import Purelib.Computation.Query.Computation
import Purelib.Data.CCL.Transducer.Machine.Code

/-!
# First-order mixed prefix and enclosure observers

Control and initial registers are finite numerical data. A received cursor
reply exposes its word, squared allowance and local ball as three numerical
registers, while the trace retains the complete original charted reply.
The same explicit fuel bounds pure control, requests and bounded iterations.
-/

public section

namespace Purelib.Approximation.Gaussian.Observation.Cursor.Observer

open Purelib
open Purelib.Computation.Machine
open Purelib.Data.Rat
open Purelib.Approximation.Gaussian.Observation.Observer
open Purelib.Computation.Query

set_option genInjectivity false in
/-- Finite numerical instructions request productive bits and charted enclosures with explicit control. -/
inductive Instruction where
  /-- Push a computed numerical register. -/ | assign (expression : Expr)
  /-- Request this computed additional natural bit count. -/ | bits (count : Expr)
  /-- Refine the same retained chart at this computed positive squared allowance. -/ | refine (target : Expr)
  /-- Recall the actual saved occurrence at this finite coordinate. -/ | recall (index : Expr)
  /-- Select a finite instruction block using a numerical decision. -/ | branch
      (condition : Expr) (whenTrue whenFalse : List Instruction)
  /-- Repeat a finite block a computed finite number of times. -/ | iterate (count : Expr) (body : List Instruction)
  /-- Return a computed numerical value. -/ | returnValue (expression : Expr)
  /-- Store a computed value at an explicit numerical register coordinate. -/ | store (index : Nat) (expression : Expr)
  /-- Redirect the nearest retained original program counter. -/ | jump (target : Nat)
  /-- Branch to one explicit counter from a numerical Boolean. -/ | jumpIf (condition : Expr) (whenTrue whenFalse : Nat)
  /-- Invoke finite source-independent numerical code with one explicit argument. -/ | call
      (program : List Instruction) (argument : Expr)
  /-- Return a computed result to the original retained caller. -/ | returnCall (expression : Expr)
  /-- Repeat a finite body while its numerical condition remains true. -/ | while
      (condition : Expr) (body : List Instruction)

set_option genInjectivity false in
/-- A finite mixed request operation retains the original numerical count or target expression. -/
inductive Operation where
  /-- Request a computed additional natural bit count. -/ | bits (expression : Expr)
  /-- Request a computed positive rational enclosure target. -/ | refine (expression : Expr)

namespace Operation

/-- Evaluate the original numerical request expression with its exact failure behavior. -/
@[expose] def request : Operation → List Value → Except Error Request
  | .bits expression => Numerical.count Request.bits expression
  | .refine expression => Numerical.target Request.enclosure expression

end Operation

/-- View each original mixed instruction as a shared finite control command. -/
@[expose] def Instruction.command : Instruction → Numerical.Command Instruction Operation
  | .assign expression => .assign expression
  | .bits expression => .operation (.bits expression)
  | .refine expression => .operation (.refine expression)
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

/-- Read the original word, charted allowance and local ball registers in their original order. -/
@[expose] def replyRegisters (reply : Reply) : List Value :=
  [.word reply.cursor.emitted, .rational reply.allowanceSq, .ball reply.ball]

/-- The shared finite control frame retains the original instruction body. -/
abbrev Frame := Numerical.Frame Instruction

/-- Numerical state retains this backend's exact request path and complete saved exchanges. -/
abbrev State := Numerical.State Request Reply

namespace State

/-- Start the original numerical registers with an empty path and saved trace. -/
@[expose] def initial (registers : List Value) : State := Numerical.State.initial registers

/-- Push the supplied register while preserving the exact path and saved trace. -/
@[expose] def push (state : State) (value : Value) : State := Numerical.State.push state value

end State

/-- A numerical query is a new request or an original retained exchange at its actual coordinate. -/
abbrev Query := Numerical.Query Request Reply

namespace Query

/-- A recall is legal exactly at its original coordinate in the saved trace. -/
@[expose] def Legal (query : Query) (state : State) : Prop := Numerical.Query.Legal query state

/-- Read the complete original path question of this displayed query. -/
@[expose] def question (query : Query) (state : State) : Question := Numerical.Query.question query state

/-- Consume the complete reply with this backend's original numerical register projection. -/
@[expose] def receive (query : Query) (state : State) (reply : Reply) : State :=
  Numerical.Query.receive replyRegisters query state reply

end Query

/-- The shared action retains legal queries and exact path/trace preservation through pure steps. -/
abbrev Action (state : State) := Numerical.Action Instruction state

/-- Execute one original finite instruction through the shared numerical control engine. -/
@[expose] def step (control : List Frame) (state : State) : Action state :=
  Numerical.step Instruction.command Operation.request control state

/-- Execute the original numerical control and retain its complete ordered execution. -/
@[expose] def run : Nat → List Frame → State → (Question → Reply) →
    Basic.Execution Question Reply Outcome := Numerical.run step replyRegisters

/-- Compile the same original control using the shared finite fuel recursion. -/
@[expose] def compile : Nat → List Frame → State → Protocol Question Reply Outcome :=
  Numerical.compile step replyRegisters

/-- Compilation preserves the complete original execution for every finite fuel and oracle. -/
theorem compile_run (fuel : Nat) (control : List Frame) (state : State)
    (oracle : Question → Reply) :
    (compile fuel control state).run oracle = run fuel control state oracle :=
  Numerical.compile_run step replyRegisters fuel control state oracle

/-- Run mixed numerical control from fixed finite frames, initial registers and transition fuel. -/
@[expose] def execute (control : List Frame) (registers : List Value) (fuel : Nat)
    (oracle : Question → Reply) : Basic.Execution Question Reply Outcome :=
  run fuel control (State.initial registers) oracle

/-- Compile the same fixed mixed control frames, initial registers and transition fuel. -/
@[expose] def protocol (control : List Frame) (registers : List Value) (fuel : Nat) :
    Protocol Question Reply Outcome := compile fuel control (State.initial registers)

/-- The compiled public observer returns its actual result and complete ordered mixed trace. -/
theorem protocol_run (control : List Frame) (registers : List Value) (fuel : Nat)
    (oracle : Question → Reply) :
    (protocol control registers fuel).run oracle = execute control registers fuel oracle :=
  compile_run fuel control (State.initial registers) oracle

/-- Request a persistent prefix, choose an enclosure target from its observed length, and test the returned allowance.

The positive fallback handles an empty word. Both branches compare the
actual squared allowance with the numerical target they just requested.
-/
@[expose] def prefixEnclosureComparison (count : Nat) (fallback : Fraction.Rational) : List Instruction :=
  [ .bits (.literal (.natural count))
  , .branch (.binary .lessCount (.literal (.natural 0)) (.unary .length (.variable 0)))
      [ .assign (.binary .divide (.literal (.rational 1)) (.unary .toRational (.unary .length (.variable 0))))
      , .refine (.variable 0)
      , .returnValue (.binary .less (.variable 1) (.variable 3)) ]
      [ .refine (.literal (.rational fallback))
      , .returnValue (.binary .less (.variable 1) (.literal (.rational fallback))) ] ]

end Purelib.Approximation.Gaussian.Observation.Cursor.Observer

end
