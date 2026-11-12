module

import Purelib.Approximation.Gaussian.Observation.Cursor.Observer.Source
import Purelib.Data.Rat.Fraction.Cast
import TestPurelib.Approximation.Gaussian.Observation.Enclosure
import Purelib.Approximation.Gaussian.Observation.Cursor.Check

/-!
# Joint admission for actual mixed numerical observer executions

The regression retains complete ordered replies, including recalls, and
checks every cached earlier chart against the one computed rational reading.
Each saved candidate is then interpreted without its original source and
receives additional bits and a stricter enclosure request.
-/

namespace TestPurelib.Approximation.Gaussian.Observation.Cursor

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Observation
open Purelib.Approximation.Gaussian.Observation.Observer (Value)
open Purelib.Data.CCL.Transducer
open Purelib.Data.CCL.Progressive
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Projective
open Purelib.Computation.Query

/-- Every compiled mixed observer equals its complete actual cached execution, for arbitrary fixed control and fuel. -/
theorem complete_execution {initial : Machine.Snapshot} (origin : Cursor.Source.State initial)
    (instructions : List Cursor.Observer.Instruction) (registers : List Value) (fuel : Nat) :
    (Cursor.Observer.protocol [.block instructions] registers fuel).run (Cursor.Source.answer origin) =
      (Cursor.Observer.Source.execute origin [.block instructions] registers fuel).numerical :=
  (Cursor.Observer.protocol_run [.block instructions] registers fuel (Cursor.Source.answer origin)).trans
    (Cursor.Observer.Source.execute_correct origin [.block instructions] registers fuel).symm

/-- Every actual finite mixed execution agrees completely with its constructed source-free rational history. -/
theorem whole_replacement {initial : Machine.Snapshot} (origin : Cursor.Source.State initial)
    (instructions : List Cursor.Observer.Instruction) (registers : List Value) (fuel : Nat)
    {process : Process} {state : process.State}
    (initialCursor : Machine.Semantics.Basic.ExactCursor process state initial.machine) :
    let result := Cursor.Observer.Source.continueExecution origin [.block instructions] registers fuel initialCursor
    Cursor.Observer.execute [.block instructions] registers fuel
        (result.continuation.history.interpret result.continuation.valid) = result.execution.numerical :=
  (Cursor.Observer.Source.continueExecution origin [.block instructions] registers fuel initialCursor).same_execution

/-- Every arbitrary finite advance from a saved admitted candidate retains that same exact rational reading. -/
theorem saved_future {reply : Cursor.Reply} {point : Basic.Canonical}
    (candidate : Cursor.Reply.Candidate reply (Line.Proj.affine point)) (count : Nat) :
    Machine.Semantics.Basic.ExactCursor (Process.exact point) ()
      (Machine.Advance.advance ((reply.atTail candidate.tail).interpret candidate.valid) count) :=
  candidate.exactCursor.advance count

/-- A direct finite rational target used by the later source-free request. -/
private def target : Fraction.Rational := 1 / Fraction.Cast.fromInt 64

/-- Read the numerical equality of the complete word, ball and chart caches in two actual replies. -/
private def sameReply (left right : Cursor.Reply) : Bool :=
  decide (left = right)

/-- Compare every actual exchange in order, retaining repetitions and complete charted numerical replies. -/
private def sameTrace :
    Basic.Trace Cursor.Question Cursor.Reply → Basic.Trace Cursor.Question Cursor.Reply → Bool
  | [], [] => true
  | left :: rest, right :: later => decide (left.query = right.query) && sameReply left.reply right.reply &&
      sameTrace rest later
  | _, _ => false

/-- Check malformed numerical caches, an unpaid bit request and a retryable incompatible candidate directly. -/
private def checkInvalid (history : Cursor.Continuation.History) : IO Unit := do
  let initial := history.initial
  let wrongCoefficient := { initial.reply with coefficient := initial.reply.coefficient + 1 }
  match Cursor.Check.check { history with initial := { initial with reply := wrongCoefficient } } with
  | .invalid (.initial (.coefficient _)) => pure ()
  | _ => throw (IO.userError "mixed checker accepted a changed chart coefficient")
  let wrongAllowance := { initial.reply with allowanceSq := initial.reply.allowanceSq + 1 }
  match Cursor.Check.check { history with initial := { initial with reply := wrongAllowance } } with
  | .invalid (.initial (.allowance _)) => pure ()
  | _ => throw (IO.userError "mixed checker accepted a changed squared allowance")
  let outside := { initial.reply.ball with
    center := ⟨initial.tail.re + initial.reply.ball.radiusSq + 1, initial.tail.im⟩ }
  let incompatible := { initial with reply := { initial.reply with ball := outside } }
  match Cursor.Check.check { history with initial := incompatible } with
  | .inconclusive attempt =>
      unless attempt.unresolved.length == 1 do
        throw (IO.userError "mixed candidate failure lost its unresolved ball")
  | _ => throw (IO.userError "mixed checker confused candidate failure with invalidity")
  match history.steps with
  | step :: remaining =>
      match step.request with
      | .bits count =>
          let unpaid := { step with request := .bits (count + 1) }
          match Cursor.Check.check { history with steps := unpaid :: remaining } with
          | .invalid (.chain (.head _ (.length _ _ _))) => pure ()
          | _ => throw (IO.userError "mixed checker accepted an unpaid additional bit")
      | .enclosure _ _ => pure ()
  | [] => pure ()

/-- Run a finite mixed observer and verify its common reading and source-free continuation of every saved candidate. -/
private def checkSource (process : Process) (state : process.State) (point : Basic.Canonical) (seed : Nat)
    (instructions : List Cursor.Observer.Instruction)
    (fuel expectedLength : Nat) (expected : Option Nat) : IO Unit := do
  let machine := Machine.initial process state
  let initialCursor := Machine.Semantics.Basic.ExactCursor.initial process state
  let initial := Machine.Snapshot.ofFrame (Cursor.Image.Machine.Frame.ofMachine machine)
    (Machine.Grammar.initial_invariant _ _)
  let origin := Cursor.Source.State.ofHistory ((Machine.History.start initial).advance seed)
  let result := Cursor.Observer.Source.continueExecution origin [.block instructions] [] fuel initialCursor
  let execution := result.execution
  let admitted := result.continuation.admitted
  let interpreted := Cursor.Observer.execute [.block instructions] [] fuel
    (result.continuation.history.interpret result.continuation.valid)
  unless sameTrace execution.numerical.trace interpreted.trace && execution.numerical.trace.length == expectedLength do
    throw (IO.userError "mixed observer lost an actual question, chart or repeated reply")
  match expected, execution.outcome with
  | some length, .returned (.natural actual) =>
      unless actual == length do throw (IO.userError "mixed observer changed its exposed prefix length")
  | none, .returned (.bit true) => pure ()
  | _, _ => throw (IO.userError "mixed observer changed its expected numerical outcome")
  unless decide (admitted.point = point) && admitted.realizations.length == expectedLength &&
      sameReply admitted.current execution.context.recording.current.reply do
    throw (IO.userError "mixed admission changed the actual rational reading, final cache or occurrence count")
  let history := result.continuation.history
  let valid := result.continuation.valid
  match Cursor.Check.check history with
  | .valid certificate =>
      match Cursor.Check.validateTrace history certificate execution.numerical.trace with
      | .ok _ => pure ()
      | .error _ => throw (IO.userError "exact imported checker rejected an original complete numerical trace")
      match execution.numerical.trace with
      | entry :: remaining =>
          let changed := { entry with reply := { entry.reply with coefficient := entry.reply.coefficient + 1 } }
          match Cursor.Check.validateTrace history certificate (changed :: remaining) with
          | .error _ => pure ()
          | .ok _ => throw (IO.userError "mixed trace checker accepted a changed reply")
      | [] => pure ()
  | .invalid _ => throw (IO.userError "exact imported checker rejected valid source-generated history data")
  | .inconclusive _ => throw (IO.userError "exact imported checker lost the original compatible candidates")
  checkInvalid history
  let savedPath := history.steps.map (fun step => step.request)
  let afterSaved : Cursor.Question := ⟨savedPath, .bits 7⟩
  let grown := history.interpret valid afterSaved
  let refined := history.interpret valid ⟨savedPath ++ [.bits 7], .enclosure target (by decide)⟩
  unless grown.cursor.emitted.length == admitted.current.cursor.emitted.length + 7 &&
      decide (grown.cursor.emitted.take admitted.current.cursor.emitted.length = admitted.current.cursor.emitted) &&
      decide (refined.cursor.emitted = grown.cursor.emitted) && decide (refined.allowanceSq < target) do
    throw (IO.userError "whole-history continuation failed a later prefix or strict enclosure request")
  let diverged := history.interpret valid ⟨[], .bits 3⟩
  let continuedQuestion : Cursor.Question := ⟨[.bits 3], .bits 7⟩
  let continued := history.interpret valid continuedQuestion
  let common := result.continuation.candidate continuedQuestion
  let image := Line.Matrix.act continued.cursor.matrix (Line.Proj.affine common.tail)
  unless diverged.cursor.emitted.length == history.initial.reply.cursor.emitted.length + 3 &&
      continued.cursor.emitted.length == diverged.cursor.emitted.length + 7 &&
      decide (continued.cursor.emitted.take diverged.cursor.emitted.length = diverged.cursor.emitted) &&
      decide (image.p = admitted.point * image.q) do
    throw (IO.userError "a divergent request path changed its exposed prefix or common rational reading")
  for saved in admitted.realizations do
    let reply := saved.1.reply
    let candidate := saved.2.candidate
    let code := reply.atTail candidate.tail
    unless decide (reply.ball.Contains candidate.tail) &&
        decide (code.matrix = reply.cursor.matrix) && decide (code.adjugate = reply.cursor.adjugate) &&
        decide (code.emitted = reply.cursor.emitted) && decide (code.pending = reply.cursor.pending) do
      throw (IO.userError "mixed rational realization changed an original ball, word or chart cache")
    let image := Line.Matrix.act code.matrix (Line.Proj.affine candidate.tail)
    unless decide (image.p = admitted.point * image.q) do
      throw (IO.userError "saved mixed chart has a different affine rational reading")
    let snapshot := Machine.Snapshot.ofFrame (code.frame candidate.valid) (code.grammar candidate.valid)
    let restarted := Cursor.Source.State.ofHistory (Machine.History.start snapshot)
    let grown := (Cursor.Source.request restarted (.bits 11)).next
    let later := (Cursor.Source.request grown (.enclosure target (by decide))).next
    let reading := later.history.survive.read candidate.exactCursor
    unless later.reply.cursor.emitted.length == code.emitted.length + 11 &&
        decide (later.reply.cursor.emitted.take code.emitted.length = code.emitted) &&
        decide (later.reply.allowanceSq < target) && decide (reading.value = admitted.point) do
      throw (IO.userError "source-free saved candidate failed a later prefix or strict enclosure request")

/-- Run the same whole-history boundary from an exact rational source. -/
private def check (point : Basic.Canonical) (seed : Nat) (instructions : List Cursor.Observer.Instruction)
    (fuel expectedLength : Nat) (expected : Option Nat) : IO Unit :=
  checkSource (Process.exact point) () point seed instructions fuel expectedLength expected

/-- Fixed mixed control uses a prefix-dependent target, recalls an earlier question and performs bounded iteration. -/
private def mixed : List Cursor.Observer.Instruction :=
  [ .bits (.literal (.natural 2))
  , .refine (.binary .divide (.literal (.rational 1)) (.unary .toRational (.unary .length (.variable 0))))
  , .recall (.literal (.natural 0))
  , .bits (.literal (.natural 4))
  , .iterate (.literal (.natural 2)) [.bits (.literal (.natural 1))]
  , .returnValue (.unary .length (.variable 0)) ]

/-- Check literal source payments through original sector, pending, inverse and enclosure transitions.

The exact point `(1, 1/2)` selects north-east and leaves residual `(0, -1/2)`.
Its five-bit initial chunk pays three calls. Draining its queue pays none;
the next residual step prepares the inverse and its loop chunk for seven
calls. Refinement then pays three, and repeated recalls reuse the old cache.
-/
private def checkAccounting : IO Unit := do
  let point : Basic.Canonical := ⟨1, 1 / 2⟩
  let process := Process.exact point
  let machine := Machine.initial process ()
  let initialCursor := Machine.Semantics.Basic.ExactCursor.initial process ()
  let initial := Machine.Snapshot.ofFrame (Cursor.Image.Machine.Frame.ofMachine machine)
    (Machine.Grammar.initial_invariant _ _)
  let origin := Cursor.Source.State.ofHistory (Machine.History.start initial)
  unless origin.sourceCalls == 2 && origin.reply.cursor.pending.isEmpty do
    throw (IO.userError "productive setup changed its two original observation calls")
  let first := (Cursor.Source.request origin (.bits 1)).next
  unless first.sourceCalls == 5 && first.reply.cursor.pending.length == 4 &&
      decide (first.reply.cursor.emitted = [false]) do
    throw (IO.userError "initial productive emission did not pay three calls for its same five-bit chunk")
  let drained := (Cursor.Source.request first (.bits 4)).next
  unless drained.sourceCalls == 5 && drained.reply.cursor.pending.isEmpty &&
      decide (drained.reply.cursor.emitted = [false, false, false, false, true]) do
    throw (IO.userError "pending sector bits reread the source or changed the original chunk")
  let inverse := (Cursor.Source.request drained (.bits 1)).next
  unless inverse.sourceCalls == 12 && inverse.reply.cursor.pending.length == 3 &&
      decide (inverse.reply.cursor.emitted = [false, false, false, false, true, false]) do
    throw (IO.userError "residual inverse transition lost its seven actual source calls or loop chunk")
  let refined := (Cursor.Source.request inverse (.enclosure target (by decide))).next
  unless refined.sourceCalls == 15 && refined.reply.cursor.pending.length == 3 &&
      decide (refined.reply.cursor.emitted = inverse.reply.cursor.emitted) &&
      decide (refined.reply.allowanceSq < target) do
    throw (IO.userError "productive enclosure refinement changed its three calls or cached pending bits")
  let instructions : List Cursor.Observer.Instruction :=
    [.bits (.literal (.natural 1)), .bits (.literal (.natural 4)), .bits (.literal (.natural 1)),
      .refine (.literal (.rational target)), .recall (.literal (.natural 0)),
      .recall (.literal (.natural 0)), .returnValue (.unary .length (.variable 0))]
  let result := Cursor.Observer.Source.continueExecution origin [.block instructions] [] 40 initialCursor
  let execution := result.execution
  unless execution.requestCount == 4 && execution.numerical.trace.length == 6 &&
      execution.sourceCalls == 15 && execution.sourceCallsSinceStart == 13 &&
      execution.context.recording.current.reply.cursor.emitted.length == 6 do
    throw (IO.userError "productive execution changed fresh work, cumulative work or zero-cost repeated recalls")
  match execution.outcome with
  | .returned (.natural 1) => pure ()
  | _ => throw (IO.userError "repeated productive recall did not return the original one-bit reply")
  let replay := Cursor.Observer.execute [.block instructions] [] 40
    (result.continuation.history.interpret result.continuation.valid)
  unless sameTrace execution.numerical.trace replay.trace do
    throw (IO.userError "productive source payments changed the complete rational replacement trace")
  match replay.value with
  | .returned (.natural 1) => pure ()
  | _ => throw (IO.userError "productive rational replacement changed the recalled one-bit result")
  let later : List Cursor.Observer.Instruction :=
    [.bits (.literal (.natural 1)), .refine (.literal (.rational target)),
      .recall (.literal (.natural 0)), .recall (.literal (.natural 0)),
      .returnValue (.unary .length (.variable 0))]
  let continued := Cursor.Observer.Source.continueExecution drained [.block later] [] 40 initialCursor
  unless continued.execution.requestCount == 2 && continued.execution.numerical.trace.length == 4 &&
      continued.execution.sourceCalls == 15 && continued.execution.sourceCallsSinceStart == 10 do
    throw (IO.userError "a nonempty productive origin was recharged or lost its earlier paid work")
  match continued.execution.outcome with
  | .returned (.natural 6) => pure ()
  | _ => throw (IO.userError "nonempty productive recall lost its original six-bit reply")
  let continuedReplay := Cursor.Observer.execute [.block later] [] 40
    (continued.continuation.history.interpret continued.continuation.valid)
  unless sameTrace continued.execution.numerical.trace continuedReplay.trace do
    throw (IO.userError "nonempty productive origin changed its complete rational replacement trace")
  match continuedReplay.value with
  | .returned (.natural 6) => pure ()
  | _ => throw (IO.userError "nonempty-origin rational replacement changed the recalled six-bit result")
  let immediate : List Cursor.Observer.Instruction := [.returnValue (.literal (.natural 7))]
  let empty := Cursor.Observer.Source.execute drained [.block immediate] [] 40
  unless empty.requestCount == 0 && empty.numerical.trace.isEmpty &&
      empty.sourceCalls == 5 && empty.sourceCallsSinceStart == 0 do
    throw (IO.userError "a query-free execution changed its original cumulative productive payment")
  let restartedHistory := Machine.History.start drained.history.current
  unless restartedHistory.sourceCalls == 5 do
    throw (IO.userError "restarting a prepared productive snapshot recharged setup or lost its paid work")
  let restarted := Cursor.Source.State.ofHistory restartedHistory
  let restartedEmpty := Cursor.Observer.Source.execute restarted [.block immediate] [] 40
  unless restartedEmpty.requestCount == 0 && restartedEmpty.numerical.trace.isEmpty &&
      restartedEmpty.sourceCalls == 5 && restartedEmpty.sourceCallsSinceStart == 0 do
    throw (IO.userError "query-free prepared-snapshot restart changed cumulative or newly paid source work")
  match empty.outcome, restartedEmpty.outcome with
  | .returned (.natural 7), .returned (.natural 7) => pure ()
  | _, _ => throw (IO.userError "query-free productive execution or snapshot restart changed its return value")

/-- Check exact empty observations, partial prefixes, queued bits, repeated queries and reply-dependent requests. -/
public def run : IO Unit := do
  check 0 0 [.returnValue (.literal (.bit true))] 10 0 none
  check 0 0 mixed 100 6 (some 8)
  check 1 1 mixed 100 6 (some 9)
  check 2 2 mixed 100 6 (some 10)
  check 1 0 (Cursor.Observer.prefixEnclosureComparison 3 1) 30 2 none
  check 0 0 (Cursor.Observer.prefixEnclosureComparison 0 1) 30 2 none
  let loose := TestPurelib.Approximation.Gaussian.Observation.Enclosure.looseProcess
  checkSource loose (Request.ofPositive 1 (by decide)) 0 0 mixed 100 6 (some 8)
  checkSource loose (Request.ofPositive 1 (by decide)) 0 1
    (Cursor.Observer.prefixEnclosureComparison 3 1) 30 2 none
  checkAccounting
  IO.print "mixed cursors: eight whole-history replays and exact productive source payments passed\n"

end TestPurelib.Approximation.Gaussian.Observation.Cursor
