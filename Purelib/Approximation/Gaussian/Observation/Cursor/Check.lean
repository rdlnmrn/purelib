module

public import Purelib.Approximation.Gaussian.Observation.Cursor.Continuation
import Purelib.Approximation.Gaussian.Observation.Cursor.Request
import Purelib.Computation.Query.History
public import Purelib.Data.CCL.Transducer.Machine.Check
import Purelib.Data.List.All
import Purelib.Data.List.Filter
import Purelib.Data.List.Membership
import Purelib.Data.List.Map
import Purelib.Data.List.Prefix
import Purelib.Geometry.Projective.Line.Basic

/-!
# Exact checking of imported mixed continuation histories

The checker validates every supplied phase, chart cache and numerical request
payment. It then tests the supplied compatible rational tails against every
retained ball. A failed containment attempt preserves the complete unresolved
list and its finite budget, without claiming that no other realizer exists.
-/

public section

namespace Purelib.Approximation.Gaussian.Observation.Cursor.Check

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Data.CCL.Transducer
open Purelib.Data.Rat
open Purelib.Data
open Purelib.Geometry.Projective
open Purelib.Computation
open Purelib.Computation.Query
open Continuation (Code History)

set_option genInjectivity false in
/-- A supplied finite rational cursor code violates an identified phase, cache, numerical or chart condition. -/
inductive CodeInvalid (code : Code) where
  /-- The finite cursor certificate fails its identified intrinsic condition. -/ | cursor
      (reason : Machine.Code.Invalid (code.reply.atTail code.tail))
  /-- The supplied coefficient does not belong to its same retained matrix. -/ | coefficient
      (failed : code.reply.coefficient ≠ Chordal.Transport.transportCoefficient code.reply.cursor.matrix)
  /-- The supplied chart coefficient is not strictly positive. -/ | nonpositiveCoefficient
      (failed : ¬ 0 < code.reply.coefficient)
  /-- The allowance does not consume the same supplied coefficient and ball radius. -/ | allowance
      (failed : code.reply.allowanceSq ≠ 4 * code.reply.coefficient * code.reply.ball.radiusSq)
  /-- The supplied rational tail and chart do not represent the same supplied point. -/ | chart
      (failed : ¬ (Line.Proj.affine code.point).Equivalent
        (Line.Matrix.act code.reply.cursor.matrix (Line.Proj.affine code.tail)))

set_option genInjectivity false in
/-- A finite code has passed its exact phase, cache and chart checks before candidate ball containment. -/
structure PreparedCode (code : Code) : Prop where
  /-- The exact supplied intrinsic cursor data are valid at its supplied tail. -/ cursor :
    (code.reply.atTail code.tail).Valid
  /-- The same supplied chart represents its own rational point. -/ represented :
    (Line.Proj.affine code.point).Equivalent
      (Line.Matrix.act code.reply.cursor.matrix (Line.Proj.affine code.tail))
  /-- The complete numerical coefficient and allowance are valid. -/ numerical : Reply.Numerical code.reply

namespace PreparedCode

/-- Dropping only ball containment retains all independent finite-code checks. -/
theorem ofValid {code : Code} (valid : Continuation.Valid code) : PreparedCode code :=
  ⟨valid.cursor, valid.represented, valid.numerical⟩

/-- A successful containment check completes this same retained code's validity. -/
theorem valid {code : Code} (prepared : PreparedCode code) (inside : code.reply.ball.Contains code.tail) :
    Continuation.Valid code := ⟨prepared.cursor, inside, prepared.represented, prepared.numerical⟩

end PreparedCode

namespace CodeInvalid

/-- Every reported code condition excludes that exact supplied phase, cache or chart certificate. -/
theorem refutes {code : Code} (invalid : CodeInvalid code) : ¬ PreparedCode code := by
  intro prepared
  cases invalid with
  | cursor reason => exact reason.refutes prepared.cursor
  | coefficient failed => exact failed prepared.numerical.coefficientEq
  | nonpositiveCoefficient failed => exact failed prepared.numerical.coefficientPositive
  | allowance failed => exact failed prepared.numerical.allowanceEq
  | chart failed => exact failed prepared.represented

end CodeInvalid

/-- Check exact finite-code phase, cache and chart data without replacing any supplied cache. -/
def prepareCode (code : Code) : Except (CodeInvalid code) (PLift (PreparedCode code)) :=
  match Machine.Code.check (code.reply.atTail code.tail) with
  | .error reason => .error (.cursor reason)
  | .ok cursor =>
      if coefficient : code.reply.coefficient = Chordal.Transport.transportCoefficient code.reply.cursor.matrix then
        if positive : 0 < code.reply.coefficient then
          if allowance : code.reply.allowanceSq = 4 * code.reply.coefficient * code.reply.ball.radiusSq then
            if chart : (Line.Proj.affine code.point).Equivalent
                (Line.Matrix.act code.reply.cursor.matrix (Line.Proj.affine code.tail)) then
              .ok ⟨⟨cursor.down, chart, coefficient, positive, allowance⟩⟩
            else .error (.chart chart)
          else .error (.allowance allowance)
        else .error (.nonpositiveCoefficient positive)
      else .error (.coefficient coefficient)

/-- Retain the original independent next-code checks and complete numerical request payment. -/
abbrev PreparedStep := Cursor.Request.PreparedStep Code.point (fun code : Code => code.reply.cursor.emitted)
  (fun code : Code => code.reply.allowanceSq) PreparedCode

/-- Identify the same original next-code, reading, prefix or exact request-payment defect. -/
abbrev StepInvalid := Cursor.Request.StepInvalid Code.point (fun code : Code => code.reply.cursor.emitted)
  (fun code : Code => code.reply.allowanceSq) CodeInvalid

namespace StepInvalid

/-- An identified saved-transition defect refutes preparation of that exact original transition. -/
theorem refutes {earlier : Code} {step : Continuation.Step} (invalid : StepInvalid earlier step) :
    ¬ PreparedStep earlier step :=
  Cursor.Request.StepInvalid.refutes (fun _ reason => CodeInvalid.refutes reason) invalid

end StepInvalid

/-- Check the original tagged request against its exact preceding code after intrinsic next-code checking. -/
def prepareStep (earlier : Code) (step : Continuation.Step) :
    Except (StepInvalid earlier step) (PLift (PreparedStep earlier step)) :=
  Cursor.Request.prepareStep Code.point (fun code : Code => code.reply.cursor.emitted)
    (fun code : Code => code.reply.allowanceSq) prepareCode earlier step

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
private theorem chain_inside (earlier : Code) (valid : Continuation.Valid earlier)
    (steps : List Continuation.Step) (chain : Continuation.Chain earlier steps) :
    ∀ code ∈ earlier :: steps.map Query.History.Step.next, code.reply.ball.Contains code.tail :=
  Query.History.Chain.all (valid := Continuation.Step.Valid) (fun code : Code => code.reply.ball.Contains code.tail)
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
    (inside : ∀ code ∈ steps.map Query.History.Step.next, code.reply.ball.Contains code.tail) :
    Continuation.Chain earlier steps :=
  Query.History.Chain.complete (valid := PreparedStep) (other := Continuation.Step.Valid)
    (fun code : Code => code.reply.ball.Contains code.tail)
    (fun _ _ head inside => { nextValid := head.next.valid inside, toPayment := head.toPayment }) prepared inside

/-- Complete the original history after every same retained candidate passes its own saved ball. -/
private theorem complete (history : History) (prepared : Prepared history)
    (inside : ∀ code ∈ history.codes, code.reply.ball.Contains code.tail) : history.Valid :=
  ⟨prepared.initial.valid (inside history.initial (List.Mem.head _)),
    completeChain prepared.chain (fun code member => inside code (List.Mem.tail history.initial member))⟩

/-- Retain every original unresolved containment occurrence and the exact finite checking budget. -/
abbrev Attempt := Query.History.Attempt Prepared (fun code : Code => code.reply.ball.Contains code.tail)

namespace Attempt

/-- The unresolved cache contains exactly every original code whose same supplied candidate fails containment. -/
theorem unresolved_iff {history : History} (attempt : Attempt history) (code : Code) :
    code ∈ attempt.unresolved ↔ code ∈ history.codes ∧ ¬ code.reply.ball.Contains code.tail :=
  Query.History.Attempt.unresolved_iff attempt code

end Attempt

/-- Checking returns the original history's validity, an identified defect or a complete finite containment attempt. -/
abbrev Result := Query.History.CheckResult History.Valid Invalid Attempt

/-- Check the same supplied code, words, balls and chart caches without replacing retained data. -/
def check (history : History) : Result history :=
  Query.History.check (fun code : Code => code.reply.ball.Contains code.tail) prepare complete history

namespace Result

/-- Read whether the original supplied finite history has its complete checked validity. -/
@[expose] def succeeded {history : History} : Result history → Prop := Query.History.CheckResult.succeeded

/-- Every source-generated valid saved history passes exact checking with its original supplied candidates. -/
theorem of_valid {history : History} (valid : history.Valid) : (check history).succeeded :=
  Query.History.check_of_valid (fun code : Code => code.reply.ball.Contains code.tail) prepare complete
    (fun _ valid => Prepared.ofValid valid) (fun _ reason => Invalid.refutes reason)
    (fun history valid => chain_inside history.initial valid.initial history.steps valid.chain) valid

end Result

/-- Retain the exact original trace occurrence whose complete reply differs from this same history interpreter. -/
abbrev TraceInvalid (history : History) (valid : history.Valid)
    (trace : Basic.Trace Cursor.Question Cursor.Reply) :=
  Query.History.TraceInvalid (history.interpret valid) trace

namespace TraceInvalid

/-- The identified complete-reply disagreement refutes interpretation of the same original supplied trace. -/
theorem refutes {history : History} {valid : history.Valid} {trace : Basic.Trace Cursor.Question Cursor.Reply}
    (invalid : TraceInvalid history valid trace) : ¬ Basic.Answers (history.interpret valid) trace :=
  Query.History.TraceInvalid.refutes invalid

end TraceInvalid

/-- Check all original complete replies, including repeated questions, against the same certified history. -/
def validateTrace (history : History) (valid : history.Valid) (trace : Basic.Trace Cursor.Question Cursor.Reply) :
    Except (TraceInvalid history valid trace) (PLift (Basic.Answers (history.interpret valid) trace)) :=
  Query.History.validateTrace (history.interpret valid) trace

/-- A source-produced saved continuation passes checking for its complete original recording. -/
theorem validateTrace_of_continuation {trace : Basic.Trace Cursor.Question Cursor.Reply}
    (result : Continuation.Result trace) :
    ∃ certificate, validateTrace result.history result.valid trace = .ok certificate :=
  Query.History.validateTrace_of_answers (result.history.interpret result.valid) trace result.answers

end Purelib.Approximation.Gaussian.Observation.Cursor.Check

end
