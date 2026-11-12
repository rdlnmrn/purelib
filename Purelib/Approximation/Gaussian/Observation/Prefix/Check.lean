module

public import Purelib.Approximation.Gaussian.Observation.Prefix.Continuation
import Purelib.Approximation.Gaussian.Observation.Cursor.Request
import Purelib.Computation.Query.History
public import Purelib.Data.CCL.Encoding.Prefix.Check
import Purelib.Data.List.All
import Purelib.Data.List.Filter
import Purelib.Data.List.Membership
import Purelib.Data.List.Map
import Purelib.Data.List.Prefix

/-!
# Exact checking of canonical mixed history code

The checker preserves every supplied affine cursor, numerical reply and
request-chain index. Invalidity identifies its actual failed condition;
a failed supplied containment assignment retains all unresolved old balls
and its finite budget without asserting global nonrealizability.
-/

public section

namespace Purelib.Approximation.Gaussian.Observation.Prefix.Check

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Data.CCL
open Purelib.Data.CCL.Encoding
open Purelib.Data.Rat
open Purelib.Data
open Purelib.Computation
open Purelib.Computation.Query
open Continuation (Code History)

set_option genInjectivity false in
/-- A supplied canonical code violates its exact cursor, reply cache or reported affine-terminal condition. -/
inductive CodeInvalid (code : Code) where
  /-- The exact supplied affine cursor has the identified intrinsic defect. -/ | cursor
      (reason : Encoding.Prefix.Cursor.Invalid code.cursor)
  /-- The supplied reply word differs from its exact retained cursor word. -/ | word
      (failed : code.reply.word ≠ code.cursor.word)
  /-- The supplied reply parser differs from its exact retained cursor parser. -/ | state
      (failed : code.reply.state ≠ code.cursor.state)
  /-- The supplied reply inverse chart differs from its same retained cursor chart. -/ | inverse
      (failed : code.reply.inverseMatrix ≠ code.cursor.inverseMatrix)
  /-- A reported affine terminal actually admits this specific next bit at the same input. -/ | terminal
      (flag : code.reply.terminal = true) (bit : Bool)
      (possible : Parser.Semantics.Prefix.CanStep code.cursor.state code.point bit)

set_option genInjectivity false in
/-- Supplied canonical cursor and reply data have passed every check except candidate ball containment. -/
structure PreparedCode (code : Code) : Prop where
  /-- The original exact affine cursor is valid. -/ cursor : code.cursor.Valid
  /-- The original reply exposes that same retained word. -/ wordEq : code.reply.word = code.cursor.word
  /-- The original reply retains that same parser cache. -/ stateEq : code.reply.state = code.cursor.state
  /-- The original reply retains that same inverse-chart cache. -/ inverseEq :
    code.reply.inverseMatrix = code.cursor.inverseMatrix
  /-- A reported terminal has no admissible affine next bit at the same input. -/ stopped :
    code.reply.terminal = true → ∀ bit, ¬Parser.Semantics.Prefix.CanStep code.cursor.state code.point bit

namespace PreparedCode

/-- Dropping only containment retains every independent original canonical-code check. -/
theorem ofValid {code : Code} (valid : code.Valid) : PreparedCode code :=
  ⟨valid.cursor, valid.wordEq, valid.stateEq, valid.inverseEq, valid.stopped⟩

/-- A successful containment check completes the same original canonical code's validity. -/
theorem valid {code : Code} (prepared : PreparedCode code) (inside : code.reply.ball.Contains code.point) :
    code.Valid :=
  ⟨prepared.cursor, prepared.wordEq, prepared.stateEq, prepared.inverseEq, inside, prepared.stopped⟩

end PreparedCode

namespace CodeInvalid

/-- Every reported canonical-code defect excludes that same exact supplied cursor or reply certificate. -/
theorem refutes {code : Code} (invalid : CodeInvalid code) : ¬ PreparedCode code := by
  intro prepared
  cases invalid with
  | cursor reason => exact reason.refutes prepared.cursor
  | word failed => exact failed prepared.wordEq
  | state failed => exact failed prepared.stateEq
  | inverse failed => exact failed prepared.inverseEq
  | terminal flag bit possible => exact prepared.stopped flag bit possible

end CodeInvalid

/-- Check supplied canonical cursor and reply caches and the exact reported terminal, without replacing any data. -/
def prepareCode (code : Code) : Except (CodeInvalid code) (PLift (PreparedCode code)) :=
  match Encoding.Prefix.Cursor.check code.cursor with
  | .error reason => .error (.cursor reason)
  | .ok cursor =>
      if wordEq : code.reply.word = code.cursor.word then
        if stateEq : code.reply.state = code.cursor.state then
          if inverseEq : code.reply.inverseMatrix = code.cursor.inverseMatrix then
            if flag : code.reply.terminal = true then
              if advance : Parser.Next.CanAdvanceAt code.cursor.state false code.cursor.tail then
                .error (.terminal flag false ((Parser.Next.canStep_iff_canAdvanceAt code.cursor.state code.point
                  code.cursor.tail cursor.down.determinant cursor.down.represents false).mpr advance))
              else if advanceTrue : Parser.Next.CanAdvanceAt code.cursor.state true code.cursor.tail then
                .error (.terminal flag true ((Parser.Next.canStep_iff_canAdvanceAt code.cursor.state code.point
                  code.cursor.tail cursor.down.determinant cursor.down.represents true).mpr advanceTrue))
              else .ok ⟨{ cursor := cursor.down
                          wordEq := wordEq
                          stateEq := stateEq
                          inverseEq := inverseEq
                          stopped := by
                            intro _ bit possible
                            cases bit with
                            | false => exact advance ((Parser.Next.canStep_iff_canAdvanceAt _ _ _
                                cursor.down.determinant cursor.down.represents false).mp possible)
                            | true => exact advanceTrue ((Parser.Next.canStep_iff_canAdvanceAt _ _ _
                                cursor.down.determinant cursor.down.represents true).mp possible) }⟩
            else .ok ⟨⟨cursor.down, wordEq, stateEq, inverseEq, fun flagged => (flag flagged).elim⟩⟩
          else .error (.inverse inverseEq)
        else .error (.state stateEq)
      else .error (.word wordEq)

/-- Retain the original independent next-code checks and complete numerical request payment. -/
abbrev PreparedStep := Cursor.Request.PreparedStep Code.point (fun code : Code => code.reply.word)
  (fun code : Code => code.reply.ball.radiusSq) PreparedCode

/-- Identify the same original next-code, reading, prefix or exact request-payment defect. -/
abbrev StepInvalid := Cursor.Request.StepInvalid Code.point (fun code : Code => code.reply.word)
  (fun code : Code => code.reply.ball.radiusSq) CodeInvalid

namespace StepInvalid

/-- An identified saved-transition defect refutes preparation of that exact original transition. -/
theorem refutes {earlier : Code} {step : Continuation.Step} (invalid : StepInvalid earlier step) :
    ¬ PreparedStep earlier step :=
  Cursor.Request.StepInvalid.refutes (fun _ reason => CodeInvalid.refutes reason) invalid

end StepInvalid

/-- Check the original tagged request against its exact preceding code after intrinsic next-code checking. -/
def prepareStep (earlier : Code) (step : Continuation.Step) :
    Except (StepInvalid earlier step) (PLift (PreparedStep earlier step)) :=
  Cursor.Request.prepareStep Code.point (fun code : Code => code.reply.word)
    (fun code : Code => code.reply.ball.radiusSq) prepareCode earlier step

/-- The entire original chronological chain passed independent code and exact request-payment checks. -/
abbrev PreparedChain := Query.History.Chain PreparedStep

/-- Retain the original first failing transition and its exact preceding-code indices. -/
abbrev ChainInvalid := Query.History.Chain.Invalid StepInvalid

namespace ChainInvalid

/-- A chronological defect refutes preparation of that exact supplied saved chain. -/
theorem refutes {earlier : Code} {steps : List Continuation.Step} (invalid : ChainInvalid earlier steps) :
    ¬ PreparedChain earlier steps :=
  Query.History.Chain.Invalid.refutes (fun _ _ reason => StepInvalid.refutes reason) invalid

end ChainInvalid

/-- Check original saved transitions once and retain the exact first failing suffix. -/
def prepareChain (earlier : Code) (steps : List Continuation.Step) :
    Except (ChainInvalid earlier steps) (PLift (PreparedChain earlier steps)) :=
  Query.History.Chain.check prepareStep earlier steps

/-- The original initial code and complete chronological chain passed their independent checks. -/
abbrev Prepared := Query.History.Valid PreparedCode PreparedStep

/-- Identify the original initial-code or chronological request-chain defect. -/
abbrev Invalid := Query.History.Invalid CodeInvalid StepInvalid

namespace Invalid

/-- Every identified history defect refutes preparation of that same supplied finite history. -/
theorem refutes {history : History} (invalid : Invalid history) : ¬ Prepared history :=
  Query.History.Invalid.refutes (fun _ reason => CodeInvalid.refutes reason)
    (fun _ _ reason => StepInvalid.refutes reason) invalid

end Invalid

/-- Check the same original initial code and complete numerical chain before candidate containment. -/
def prepare (history : History) : Except (Invalid history) (PLift (Prepared history)) :=
  Query.History.prepare prepareCode prepareStep history

/-- Each chronological original code retains its own certified candidate inside its exact saved ball. -/
private theorem chain_inside (earlier : Code) (valid : earlier.Valid)
    (steps : List Continuation.Step) (chain : Continuation.Chain earlier steps) :
    ∀ code ∈ earlier :: steps.map Query.History.Step.next, code.reply.ball.Contains code.point :=
  Query.History.Chain.all (valid := Continuation.Step.Valid) (fun code : Code => code.reply.ball.Contains code.point)
    (fun _ _ head => head.nextValid.inside) earlier valid.inside steps chain

/-- Removing only containment preserves the exact saved code and every original numerical payment. -/
private theorem prepare_of_chain {earlier : Code} {steps : List Continuation.Step}
    (chain : Continuation.Chain earlier steps) : PreparedChain earlier steps :=
  Query.History.Chain.map (valid := Continuation.Step.Valid) (other := PreparedStep)
    (fun _ _ head => { next := PreparedCode.ofValid head.nextValid, toPayment := head.toPayment }) chain

namespace Prepared

/-- Retain all independent checks of an already valid finite mixed history. -/
theorem ofValid {history : History} (valid : history.Valid) : Prepared history :=
  ⟨PreparedCode.ofValid valid.initial, prepare_of_chain valid.chain⟩

end Prepared

/-- Complete the same prepared saved chain from containment at each original cached next code. -/
private theorem completeChain {earlier : Code} {steps : List Continuation.Step}
    (prepared : PreparedChain earlier steps)
    (inside : ∀ code ∈ steps.map Query.History.Step.next, code.reply.ball.Contains code.point) :
    Continuation.Chain earlier steps :=
  Query.History.Chain.complete (valid := PreparedStep) (other := Continuation.Step.Valid)
    (fun code : Code => code.reply.ball.Contains code.point)
    (fun _ _ head inside => { nextValid := head.next.valid inside, toPayment := head.toPayment }) prepared inside

/-- Complete the original history after every same retained candidate passes its own saved ball. -/
private theorem complete (history : History) (prepared : Prepared history)
    (inside : ∀ code ∈ history.codes, code.reply.ball.Contains code.point) : history.Valid :=
  ⟨prepared.initial.valid (inside history.initial (List.Mem.head _)),
    completeChain prepared.chain (fun code member => inside code (List.Mem.tail history.initial member))⟩

/-- Retain every original unresolved containment occurrence and the exact finite checking budget. -/
abbrev Attempt := Query.History.Attempt Prepared (fun code : Code => code.reply.ball.Contains code.point)

namespace Attempt

/-- The unresolved cache contains exactly every original code whose same supplied candidate fails containment. -/
theorem unresolved_iff {history : History} (attempt : Attempt history) (code : Code) :
    code ∈ attempt.unresolved ↔ code ∈ history.codes ∧ ¬ code.reply.ball.Contains code.point :=
  Query.History.Attempt.unresolved_iff attempt code

end Attempt

/-- Checking returns the original history's validity, an identified defect or a complete finite containment attempt. -/
abbrev Result := Query.History.CheckResult History.Valid Invalid Attempt

/-- Check the same supplied code, words, balls and chart caches without replacing retained data. -/
def check (history : History) : Result history :=
  Query.History.check (fun code : Code => code.reply.ball.Contains code.point) prepare complete history

namespace Result

/-- Read whether the original supplied finite history has its complete checked validity. -/
@[expose] def succeeded {history : History} : Result history → Prop := Query.History.CheckResult.succeeded

/-- Every source-generated valid saved history passes exact checking with its original supplied candidates. -/
theorem of_valid {history : History} (valid : history.Valid) : (check history).succeeded :=
  Query.History.check_of_valid (fun code : Code => code.reply.ball.Contains code.point) prepare complete
    (fun _ valid => Prepared.ofValid valid) (fun _ reason => Invalid.refutes reason)
    (fun history valid => chain_inside history.initial valid.initial history.steps valid.chain) valid

end Result

/-- Retain the exact original trace occurrence whose complete reply differs from this same history interpreter. -/
abbrev TraceInvalid (history : History) (valid : history.Valid)
    (trace : Basic.Trace Cursor.Question Reply) :=
  Query.History.TraceInvalid (history.interpret valid) trace

namespace TraceInvalid

/-- The identified complete-reply disagreement refutes interpretation of the same original supplied trace. -/
theorem refutes {history : History} {valid : history.Valid} {trace : Basic.Trace Cursor.Question Reply}
    (invalid : TraceInvalid history valid trace) : ¬ Basic.Answers (history.interpret valid) trace :=
  Query.History.TraceInvalid.refutes invalid

end TraceInvalid

/-- Check all original complete replies, including repeated questions, against the same certified history. -/
def validateTrace (history : History) (valid : history.Valid) (trace : Basic.Trace Cursor.Question Reply) :
    Except (TraceInvalid history valid trace) (PLift (Basic.Answers (history.interpret valid) trace)) :=
  Query.History.validateTrace (history.interpret valid) trace

/-- A source-produced saved continuation passes checking for its complete original recording. -/
theorem validateTrace_of_continuation {trace : Basic.Trace Cursor.Question Reply}
    (result : Continuation.Result trace) :
    ∃ certificate, validateTrace result.history result.valid trace = .ok certificate :=
  Query.History.validateTrace_of_answers (result.history.interpret result.valid) trace result.answers

end Purelib.Approximation.Gaussian.Observation.Prefix.Check

end
