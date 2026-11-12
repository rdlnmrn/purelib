module
import Purelib.System.IO

import Purelib.Approximation.Gaussian.Observation.Prefix.Source
import Purelib.Approximation.Gaussian.Observation.Prefix.Observer.Source
import Purelib.Approximation.Gaussian.Observation.Prefix.Check
public import Purelib.Approximation.Gaussian.Observation.Cursor.Observer
public import Purelib.Approximation.Gaussian.Observation.Prefix.Transcript
import Purelib.Geometry.CCL.Prefix.Path
import Purelib.Data.CCL.Encoding.Prefix.Enclosure
import Purelib.Geometry.Rational.Box.Subdivision
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Polynomial.Dense.Rational.Nonzero.Search.List

/-!
# Canonical raw-prefix and proper-box observation boundaries

One actual final sample is checked against every original numerical ball
and raw prefix. Exact canonical continuation preserves those words and
reports affine terminals without appending productive residual padding.
-/

namespace TestPurelib.Approximation.Gaussian.Observation.Prefix

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Observation
open Purelib.Data
open Purelib.Data.CCL
open Purelib.Data.CCL.Encoding.Prefix (Enclosure)
open Purelib.Data.Rat
open Purelib.Geometry
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Rational.Nonzero

/-- Every canonical finite request preserves the exact original word and its original affine rational reading. -/
theorem exact_request (cursor : Encoding.Prefix.Cursor) (valid : cursor.Valid) (count : Nat) :
    let result := cursor.request valid count
    cursor.word.IsPrefix result.next.word ∧
      Encoding.Parser.Semantics.Prefix.Represented result.next.word cursor.point :=
  ⟨(cursor.request valid count).wordPrefix, (cursor.request valid count).represented⟩

/-- Fixed canonical control includes reply-dependent refinement and recall of an earlier prefix. -/
@[expose] public def program : List Cursor.Observer.Instruction :=
  [ .bits (.literal (.natural 1))
  , .refine (.binary .divide (.literal (.rational 1)) (.unary .toRational (.unary .length (.variable 0))))
  , .recall (.literal (.natural 0))
  , .bits (.literal (.natural 2))
  , .returnValue (.unary .length (.variable 0)) ]

/-- An exact small squared-accuracy target using a direct integer denominator. -/
private def target : Fraction.Rational := 1 / Fraction.Cast.fromInt 32

/-- A retained proper box whose rational samples avoid the zero input. -/
private def box : Rational.Box := ⟨1 / 4, 1 / 2, 1 / 8, 1 / 4, by decide, by decide⟩

/-- Check actual finite-search stopping and retained work, including a failed first candidate and exhaustion. -/
private def checkWork : IO Unit := do
  let polynomial : Dense.Rational.Basic.CoordinatePolynomial := ⟨[1, -1 / 3]⟩
  let search := Search.List.scan polynomial [1 / 3, 2 / 3, 3 / 4]
  unless decide (search.result = some (2 / 3)) && search.evaluations.length == 2 &&
      decide (search.evaluations = [(1 / 3, 0), (2 / 3, 1 / 3)]) do
    throw (IO.userError "retained polynomial scan lost its original early stop or exact ordered evaluations")
  let failed := Search.List.scan polynomial [1 / 3, 1 / 3]
  unless failed.result.isNone && failed.evaluations.length == 2 do
    throw (IO.userError "retained polynomial exhaustion lost repeated original candidates")
  let origin := Prefix.Source.Snapshot.ofEnclosure (Enclosure.ofBox box ⟨by decide, by decide⟩)
  let recording := (Prefix.Source.Recording.start origin).execute
    [.bits 0, .bits 3, .enclosure target (by decide), .bits 1]
  unless recording.requestCount == 4 && recording.bitSteps == 4 && recording.enclosureSteps == 1 &&
      recording.evaluationCount ≤ recording.evaluationBound && recording.evaluationCount ≥ recording.bitSteps do
    throw (IO.userError "canonical work conflated request calls, geometric steps or cached polynomial evaluations")
  match occurrences : recording.occurrences with
  | [] => throw (IO.userError "canonical work fixture lost its original occurrences")
  | occurrence :: remaining =>
      have member : occurrence ∈ recording.occurrences := occurrences.symm ▸ List.Mem.head remaining
      let recalled := recording.recall occurrence member
      unless recalled.requestCount == recording.requestCount && recalled.bitSteps == recording.bitSteps &&
          recalled.enclosureSteps == recording.enclosureSteps &&
          recalled.evaluationCount == recording.evaluationCount &&
          recalled.evaluationBound == recording.evaluationBound &&
          recalled.trace.length == recording.trace.length + 1 do
        throw (IO.userError "canonical recall recomputed geometric work or lost its original numerical occurrence")
  for occurrence in recording.spine do
    unless decide (occurrence.reply = occurrence.result.next.reply) do
      throw (IO.userError "canonical work receipt changed its original returned checkpoint")

/-- Check every cached original canonical occurrence against one final sample and its same exact continuation. -/
private def check (requests : List Cursor.Request) : IO Unit := do
  let origin := Prefix.Source.Snapshot.ofEnclosure (Enclosure.ofBox box ⟨by decide, by decide⟩)
  let recording := (Prefix.Source.Recording.start origin).execute requests
  let admitted := recording.admission
  let continuation := Prefix.Continuation.ofAdmitted admitted
  let terminal := continuation.terminal
  unless decide (terminal.completion.word = terminal.encoding.word) &&
      terminal.bound == terminal.encoding.word.length - admitted.endpoint.cursor.word.length &&
      decide (continuation.endpointState.code.reply = recording.current.reply) do
    throw (IO.userError "automatic history splicing changed its original endpoint, canonical word or computed bound")
  unless admitted.exchanges.length == requests.length &&
      decide (admitted.enclosure.box.Contains admitted.realization.point) do
    throw (IO.userError "canonical admission lost the actual final sample or an original occurrence")
  let exact := Encoding.Prefix.Cursor.ofRealization admitted.realization
  let later := exact.val.request exact.property 40
  unless decide (later.next.point = admitted.realization.point) &&
      decide (later.next.word.take exact.val.word.length = exact.val.word) do
    throw (IO.userError "exact canonical continuation changed the saved word or rational reading")
  for entry in admitted.exchanges do
    unless decide (entry.1.reply.ball.Contains admitted.realization.point) &&
        decide (entry.1.reply.word.take entry.2.previousWord.length = entry.2.previousWord) &&
        decide (terminal.completion.word.take entry.1.reply.word.length = entry.1.reply.word) do
      throw (IO.userError "canonical survivor violated an old numerical ball or exposed prefix")
    let cursor := Encoding.Prefix.Cursor.ofEnclosure admitted.enclosure admitted.realization.point
      admitted.realization.sample.inside
    unless decide (cursor.val.state = admitted.enclosure.state) &&
        decide (cursor.val.inverseMatrix = admitted.enclosure.inverseMatrix) do
      throw (IO.userError "canonical continuation rebuilt or changed the original parser or inverse chart")

/-- Test exact zero and one against the canonical affine terminal convention. -/
private def terminalCases : IO Unit := do
  let outer := Rational.Box.symmetric 2 (by decide)
  let enclosure := Enclosure.ofBox outer ⟨by decide, by decide⟩
  let zero := Encoding.Prefix.Cursor.ofEnclosure enclosure 0 ⟨by decide, by decide, by decide, by decide⟩
  let zeroLater := zero.val.request zero.property 12
  unless zeroLater.suffix.length == 12 do
    throw (IO.userError "canonical zero failed a finite unary request")
  let one := Encoding.Prefix.Cursor.ofEnclosure enclosure 1 ⟨by decide, by decide, by decide, by decide⟩
  let oneLater := one.val.request one.property 32
  unless oneLater.suffix.length < 32 do
    throw (IO.userError "canonical one did not stop at its affine terminal")
  match oneLater.next.nextBit oneLater.valid with
  | .terminal _ => pure ()
  | .advanced _ => throw (IO.userError "canonical terminal added an affine bit or productive padding")

/-- Every finite canonical first-order observer equals its same constructed complete rational execution. -/
theorem observer_replacement (origin : Prefix.Source.Snapshot)
    (instructions : List Cursor.Observer.Instruction) (registers : List Observation.Observer.Value) (fuel : Nat) :
    let result := Prefix.Observer.Source.continueExecution origin [.block instructions] registers fuel
    Prefix.Observer.execute [.block instructions] registers fuel
        (result.continuation.history.interpret result.continuation.valid) = result.execution.numerical :=
  (Prefix.Observer.Source.continueExecution origin [.block instructions] registers fuel).same_execution

/-- Compare complete original canonical exchanges in order, preserving all repeated occurrences. -/
public def sameTrace : Computation.Query.Basic.Trace Cursor.Question Prefix.Reply →
    Computation.Query.Basic.Trace Cursor.Question Prefix.Reply → Bool
  | [], [] => true
  | left :: remaining, right :: later => decide (left.query = right.query) && decide (left.reply = right.reply) &&
      sameTrace remaining later
  | _, _ => false

/-- Check mismatched prefix caches, an unpaid bit request and a retryable incompatible candidate directly. -/
private def checkInvalid (history : Prefix.Continuation.History) : IO Unit := do
  let initial := history.initial
  let wrongWord := { initial.reply with word := false :: initial.reply.word }
  match Prefix.Check.check { history with initial := { initial with reply := wrongWord } } with
  | .invalid (.initial (.word _)) => pure ()
  | _ => throw (IO.userError "canonical checker accepted a mismatched reply word")
  let wrongInverse := { initial.reply.inverseMatrix with a := initial.reply.inverseMatrix.a + 1 }
  let wrongReply := { initial.reply with inverseMatrix := wrongInverse }
  match Prefix.Check.check { history with initial := { initial with reply := wrongReply } } with
  | .invalid (.initial (.inverse _)) => pure ()
  | _ => throw (IO.userError "canonical checker accepted a mismatched inverse chart")
  let outside := { initial.reply.ball with
    center := ⟨initial.point.re + initial.reply.ball.radiusSq + 1, initial.point.im⟩ }
  let incompatible := { initial with reply := { initial.reply with ball := outside } }
  match Prefix.Check.check { history with initial := incompatible } with
  | .inconclusive attempt =>
      unless attempt.unresolved.length == 1 do
        throw (IO.userError "canonical candidate failure lost its unresolved ball")
  | _ => throw (IO.userError "canonical checker confused candidate failure with invalidity")
  match history.steps with
  | step :: remaining =>
      match step.request with
      | .bits count =>
          let unpaid := { step with request := .bits (count + 1) }
          match Prefix.Check.check { history with steps := unpaid :: remaining } with
          | .invalid (.chain (.head _ (.length _ _ _))) => pure ()
          | _ => throw (IO.userError "canonical checker accepted an unpaid additional bit")
      | .enclosure _ _ => pure ()
  | [] => pure ()

/-- Check a complete canonical first-order execution and legal later and divergent source-free requests. -/
private def checkObserver (instructions : List Cursor.Observer.Instruction)
    (expectedQueries expectedRequests : Nat) (seed : Nat := 0) : IO Unit := do
  let enclosure := Enclosure.ofBox box ⟨by decide, by decide⟩
  let origin := Prefix.Source.Snapshot.ofEnclosure (CCL.Prefix.Path.build enclosure seed).result
  let result := Prefix.Observer.Source.continueExecution origin [.block instructions] [] 100
  let execution := result.execution
  unless execution.simulation.usedFuel + execution.simulation.remainingFuel == 100 && execution.budget == 100 &&
      execution.requestCount == expectedRequests && execution.requestCount == execution.state.path.length &&
      execution.evaluationCount ≤ execution.evaluationBound do
    throw (IO.userError "canonical execution confused numerical fuel, actual handler calls or geometric search bounds")
  let history := result.continuation.history
  let valid := result.continuation.valid
  match Prefix.Check.check history with
  | .valid checked =>
      match Prefix.Check.validateTrace history checked result.execution.numerical.trace with
      | .ok _ => pure ()
      | .error _ => throw (IO.userError "canonical source-generated trace failed exact checking")
      match result.execution.numerical.trace with
      | entry :: remaining =>
          let changed := { entry with reply := { entry.reply with terminal := !entry.reply.terminal } }
          match Prefix.Check.validateTrace history checked (changed :: remaining) with
          | .error _ => pure ()
          | .ok _ => throw (IO.userError "canonical trace checker accepted a changed reply")
      | [] => pure ()
  | .invalid _ => throw (IO.userError "canonical source-generated history failed independent checking")
  | .inconclusive _ => throw (IO.userError "canonical source-generated candidate failed retained containment")
  checkInvalid history
  let terminal := result.continuation.terminal
  unless decide (terminal.completion.word = terminal.encoding.word) &&
      terminal.bound == terminal.encoding.word.length - result.continuation.admitted.endpoint.cursor.word.length do
    throw (IO.userError "canonical execution changed its terminal word or computed completion bound")
  let replay := Prefix.Observer.execute [.block instructions] [] 100 (history.interpret valid)
  unless sameTrace replay.trace result.execution.numerical.trace && replay.trace.length == expectedQueries do
    throw (IO.userError "canonical rational history changed the complete first-order execution trace")
  match replay.value with
  | .returned (.bit true) | .returned (.natural _) => pure ()
  | _ => throw (IO.userError "canonical observer changed its finite expected numerical outcome")
  let savedPath := history.steps.map (fun step => step.request)
  let before := ((history.state valid).execute savedPath).code.reply
  let continued := history.interpret valid ⟨savedPath, .bits 30⟩
  let finalQuestion : Cursor.Question := ⟨savedPath ++ [.bits 30], .enclosure target (by decide)⟩
  let refined := history.interpret valid finalQuestion
  let candidate := history.interpret_candidate valid finalQuestion
  unless decide (continued.word.take before.word.length = before.word) &&
      continued.word.length ≤ before.word.length + 30 && decide (refined.word = continued.word) &&
      decide (refined.ball.radiusSq < target) && decide (refined.ball.Contains history.initial.point) do
    throw (IO.userError "canonical saved-path continuation failed prefix, terminal or accuracy payment")
  unless decide (candidate.tail =
      Projective.Homography.Basic.homographic refined.inverseMatrix history.initial.point) do
    throw (IO.userError "canonical continuation lost its original affine inverse-chart tail")
  let diverged := history.interpret valid ⟨[], .bits 3⟩
  let after := history.interpret valid ⟨[.bits 3], .bits 12⟩
  unless decide (after.word.take diverged.word.length = diverged.word) &&
      after.word.length ≤ diverged.word.length + 12 do
    throw (IO.userError "canonical divergent path changed its actual exposed prefix or request bound")

/-- Extend an actual old recording before splicing, keeping its exact old replies and original returned source state. -/
private def checkExtension : IO Unit := do
  let origin := Prefix.Source.Snapshot.ofEnclosure (Enclosure.ofBox box ⟨by decide, by decide⟩)
  let earlier := (Prefix.Source.Recording.start origin).execute [.bits 1, .enclosure target (by decide)]
  let extended := earlier.continueRequests [.bits 2, .enclosure target (by decide), .bits 1]
  let longer := extended.fst
  let continuation := extended.snd
  unless decide (continuation.endpointState.code.reply = longer.current.reply) &&
      decide (continuation.terminal.completion.word = continuation.terminal.encoding.word) do
    throw (IO.userError "longer source recording lost its actual endpoint or automatic canonical completion")
  for entry in earlier.trace do
    let reply := continuation.history.interpret continuation.valid entry.query
    unless decide (reply = entry.reply) &&
        decide (continuation.terminal.completion.word.take entry.reply.word.length = entry.reply.word) do
      throw (IO.userError "longer recording splicing changed an old complete reply or exposed word")

/-- Run empty and mixed proper-box requests and the explicit zero and affine-terminal cases. -/
public def run : IO Unit := do
  checkWork
  check []
  check [.bits 1, .enclosure target (by decide), .bits 2, .enclosure target (by decide), .bits 1]
  terminalCases
  checkExtension
  checkObserver [.returnValue (.literal (.bit true))] 0 0
  checkObserver (Cursor.Observer.prefixEnclosureComparison 2 1) 2 2
  checkObserver program 4 3
  checkObserver program 4 3 8
  IO.print "canonical prefixes: exact observers, joint admission, later requests, zero and affine terminal passed\n"

end TestPurelib.Approximation.Gaussian.Observation.Prefix
