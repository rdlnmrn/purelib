module

public import Purelib.Approximation.Gaussian.Observation.Continuation
import Purelib.Data.List.All
import Purelib.Data.List.Filter
import Purelib.Data.List.Membership

/-!
# Exact checking of imported enclosure transcripts

The input is typed finite numerical data: requests already retain checked
positive targets, and balls retain checked nonnegative squared radii.
Transcript accuracy and repeated replies are checked independently of the
supplied rational candidate. A failed candidate retains every unresolved
ball constraint and establishes no impossibility of another candidate.
-/

public section

namespace Purelib.Approximation.Gaussian.Observation.Imported

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Data
open Purelib.Computation.Query

set_option genInjectivity false in
/-- The numerical conditions independent of a proposed common rational reading. -/
structure Valid (trace : Basic.Trace Question Enclosure.Ball) : Type where
  /-- Every actual reply pays its original positive request. -/ accurate :
    ∀ entry ∈ trace, entry.reply.radiusSq < entry.query.request.targetSq
  /-- Repeated exact questions have identical complete numerical replies. -/ consistent :
    ∀ left ∈ trace, ∀ right ∈ trace, left.query = right.query → left.reply = right.reply

set_option genInjectivity false in
/-- Invalid numerical transcript evidence identifies the original violated condition and occurrences. -/
inductive Invalid (trace : Basic.Trace Question Enclosure.Ball) where
  /-- This actual reply fails its own strict squared-error request. -/ | inaccurate
      (entry : Basic.Exchange Question Enclosure.Ball) (member : entry ∈ trace)
      (failed : ¬ entry.reply.radiusSq < entry.query.request.targetSq)
  /-- These actual identical questions have different complete replies. -/ | repeated
      (left right : Basic.Exchange Question Enclosure.Ball)
      (leftMember : left ∈ trace) (rightMember : right ∈ trace)
      (sameQuestion : left.query = right.query) (differentReply : left.reply ≠ right.reply)

namespace Invalid

/-- An identified numerical transcript violation excludes the displayed validity certificate. -/
theorem refutes {trace : Basic.Trace Question Enclosure.Ball} (invalid : Invalid trace) : Valid trace → False := by
  intro valid
  cases invalid with
  | inaccurate entry member failed => exact failed (valid.accurate entry member)
  | repeated left right leftMember rightMember same different =>
      exact different (valid.consistent left leftMember right rightMember same)

end Invalid

/-- Decide one repeated-question condition by exact question and numerical ball equality. -/
private def pairDecision (left right : Basic.Exchange Question Enclosure.Ball) :
    Decidable (left.query = right.query → left.reply = right.reply) :=
  if same : left.query = right.query then
    match decEq left.reply right.reply with
    | .isTrue equal => .isTrue (fun _ => equal)
    | .isFalse different => .isFalse (fun agrees => different (agrees same))
  else .isTrue (fun equal => (same equal).elim)

/-- Check all repeated replies against one original occurrence, retaining the actual rejected pair. -/
private def checkReplies (trace : Basic.Trace Question Enclosure.Ball)
    (left : Basic.Exchange Question Enclosure.Ball) (member : left ∈ trace) :
    Except (Invalid trace) (PLift (∀ right ∈ trace, left.query = right.query → left.reply = right.reply)) :=
  match List.All.check _ (pairDecision left) trace with
  | .accepted all => .ok ⟨all⟩
  | .rejected right rightMember failed => .error (.repeated left right member rightMember
      (by
        by_cases same : left.query = right.query
        · exact same
        · exact (failed (fun equal => (same equal).elim)).elim)
      (fun equal => failed (fun _ => equal)))

/-- Check the original remaining occurrences against the unchanged complete transcript. -/
private def checkConsistency (trace : Basic.Trace Question Enclosure.Ball) :
    (remaining : Basic.Trace Question Enclosure.Ball) →
    (∀ entry ∈ remaining, entry ∈ trace) →
    Except (Invalid trace)
      (PLift (∀ left ∈ remaining, ∀ right ∈ trace, left.query = right.query → left.reply = right.reply))
  | [], _ => .ok ⟨fun _ impossible => by nomatch impossible⟩
  | head :: tail, retained =>
      match checkReplies trace head (retained head (List.Mem.head tail)) with
      | .error invalid => .error invalid
      | .ok headAgrees =>
          match checkConsistency trace tail (fun entry member => retained entry (List.Mem.tail head member)) with
          | .error invalid => .error invalid
          | .ok tailAgrees => .ok ⟨fun left member => by
              cases member with
              | head => exact headAgrees.down
              | tail _ tailMember => exact tailAgrees.down left tailMember⟩

/-- Validate numerical accuracy and complete repeated replies before testing any rational candidate. -/
def validate (trace : Basic.Trace Question Enclosure.Ball) : Except (Invalid trace) (Valid trace) :=
  match List.All.check
      (fun entry : Basic.Exchange Question Enclosure.Ball => entry.reply.radiusSq < entry.query.request.targetSq)
      (fun _ => inferInstance) trace with
  | .rejected entry member failed => .error (.inaccurate entry member failed)
  | .accepted accurate =>
      match checkConsistency trace trace (fun _ member => member) with
      | .error invalid => .error invalid
      | .ok consistent => .ok ⟨accurate, consistent.down⟩

set_option genInjectivity false in
/-- A finite failed rational candidate attempt retains the valid transcript and every unresolved ball constraint.

Exactly one supplied candidate is checked at every occurrence. The cached
unresolved list preserves their original order and repetitions. Its complete
membership law identifies all unsatisfied constraints; the retained rejection
is a stopping reason for this attempt, not a global realizability claim.
-/
structure Attempt (trace : Basic.Trace Question Enclosure.Ball) (candidate : Gaussian.Basic.Canonical) where
  /-- The transcript has already passed its candidate-independent numerical checks. -/ valid : Valid trace
  /-- All original occurrences failing membership for this exact supplied candidate. -/ unresolved :
    Basic.Trace Question Enclosure.Ball
  /-- The cache is the actual finite filter of the original trace. -/ unresolvedEq :
    unresolved = trace.filter (fun entry => decide (¬ entry.reply.Contains candidate))
  /-- The actual occurrence which caused this candidate attempt to stop. -/ rejected :
    Basic.Exchange Question Enclosure.Ball
  /-- That rejected occurrence is in the original transcript. -/ member : rejected ∈ trace
  /-- This particular candidate violates that retained ball constraint. -/ outside : ¬ rejected.reply.Contains candidate
  /-- The actual number of inspected ball constraints. -/ inspected : Nat
  /-- All original occurrences were inspected by the cached unresolved filter. -/ inspectedEq : inspected = trace.length
  /-- The actual finite candidate budget is exactly one supplied rational point. -/ candidateBudget : Nat
  /-- No additional candidate or grid search was attempted. -/ budgetEq : candidateBudget = 1

namespace Attempt

/-- The cached unresolved list contains exactly the original constraints violated by this candidate. -/
theorem unresolved_iff {trace : Basic.Trace Question Enclosure.Ball} {candidate : Gaussian.Basic.Canonical}
    (attempt : Attempt trace candidate) (entry : Basic.Exchange Question Enclosure.Ball) :
    entry ∈ attempt.unresolved ↔ entry ∈ trace ∧ ¬ entry.reply.Contains candidate := by
  rewrite [attempt.unresolvedEq]
  constructor
  · intro member
    have retained := List.Filter.mem_filter.mp member
    exact ⟨retained.1, of_decide_eq_true retained.2⟩
  · intro rejected
    exact List.Filter.mem_filter.mpr ⟨rejected.1, decide_eq_true rejected.2⟩

/-- A rejected candidate leaves an actual unsatisfied constraint in the cached unresolved list. -/
theorem rejected_unresolved {trace : Basic.Trace Question Enclosure.Ball} {candidate : Gaussian.Basic.Canonical}
    (attempt : Attempt trace candidate) : attempt.rejected ∈ attempt.unresolved :=
  (attempt.unresolved_iff attempt.rejected).mpr ⟨attempt.member, attempt.outside⟩

end Attempt

set_option genInjectivity false in
/-- Exact imported-transcript checking separates continuation, numerical invalidity and a failed candidate attempt. -/
inductive Check (trace : Basic.Trace Question Enclosure.Ball) (candidate : Gaussian.Basic.Canonical) where
  /-- The same supplied candidate yields a valid finite rational continuation. -/ | admitted
      (result : Continuation.Result trace) (pointEq : result.code.point = candidate)
  /-- An actual candidate-independent numerical condition is violated. -/ | invalid (reason : Invalid trace)
  /-- This finite candidate failed; all unresolved constraints and its budget are retained. -/ | inconclusive
      (attempt : Attempt trace candidate)

/-- Check one imported typed transcript and one supplied rational candidate by exact finite computations.

Typed requests and balls already certify target positivity and nonnegative
allowances. The procedure checks complete numerical consistency before
candidate containment. Success constructs the same finite continuation API
as source admission; failure never changes the original numerical trace.
-/
def check (trace : Basic.Trace Question Enclosure.Ball) (candidate : Gaussian.Basic.Canonical) :
    Check trace candidate :=
  match validate trace with
  | .error invalid => .invalid invalid
  | .ok valid =>
      match List.All.check (fun entry : Basic.Exchange Question Enclosure.Ball => entry.reply.Contains candidate)
          (fun _ => inferInstance) trace with
      | .accepted inside =>
          let admitted : Admitted trace := ⟨candidate, inside, valid.accurate, valid.consistent⟩
          let result := Continuation.ofAdmitted admitted
          .admitted result (Continuation.ofAdmitted_point admitted)
      | .rejected entry member outside => .inconclusive
          ⟨valid, trace.filter (fun entry => decide (¬ entry.reply.Contains candidate)), rfl,
            entry, member, outside, trace.length, rfl, 1, rfl⟩

namespace Check

/-- Read whether the typed checking result contains a certified rational continuation. -/
@[expose] def succeeded {trace : Basic.Trace Question Enclosure.Ball} {candidate : Gaussian.Basic.Canonical} :
    Check trace candidate → Prop
  | .admitted _ _ => True
  | .invalid _ => False
  | .inconclusive _ => False

/-- An already admitted source-generated reading succeeds in exact imported-transcript checking. -/
theorem of_admitted {trace : Basic.Trace Question Enclosure.Ball} (admitted : Admitted trace) :
    (check trace admitted.point).succeeded := by
  cases result : check trace admitted.point with
  | admitted continuation equal => exact True.intro
  | invalid reason => exact (reason.refutes ⟨admitted.accurate, admitted.consistent⟩).elim
  | inconclusive attempt => exact (attempt.outside (admitted.inside attempt.rejected attempt.member)).elim

end Check

set_option genInjectivity false in
/-- A saved continuation description fails a retained centre-bound or transcript condition. -/
inductive CodeInvalid (code : Continuation.Code) where
  /-- The saved uniform squared centre bound is negative. -/ | negativeBound (failed : ¬ 0 ≤ code.centerBound)
  /-- The exact saved rational reading exceeds that same bound. -/ | pointBound
      (failed : ¬ Gaussian.Norm.Basic.normSq code.point ≤ code.centerBound)
  /-- An actual historical centre exceeds the saved bound. -/ | centreBound
      (entry : Basic.Exchange Question Enclosure.Ball) (member : entry ∈ code.trace)
      (failed : ¬ Gaussian.Norm.Basic.normSq entry.reply.center ≤ code.centerBound)
  /-- The exact saved numerical transcript violates accuracy or complete repeated replies. -/ | transcript
      (reason : Invalid code.trace)

namespace CodeInvalid

/-- A saved-code violation excludes validity of that same finite code and bound cache. -/
theorem refutes {code : Continuation.Code} (invalid : CodeInvalid code) : ¬ Continuation.Valid code := by
  intro valid
  cases invalid with
  | negativeBound failed => exact failed valid.bound_nonnegative
  | pointBound failed => exact failed valid.point_bounded
  | centreBound entry member failed => exact failed (valid.centres_bounded entry member)
  | transcript reason => exact reason.refutes ⟨valid.accurate, valid.consistent⟩

end CodeInvalid

set_option genInjectivity false in
/-- Checking saved finite continuation code preserves its original numerical data and cached bound. -/
inductive CodeCheck (code : Continuation.Code) where
  /-- This exact saved code is valid for every historical and future request. -/ | valid
      (certificate : Continuation.Valid code)
  /-- The retained numerical code violates the identified condition. -/ | invalid (reason : CodeInvalid code)
  /-- The saved candidate failed its membership attempt, retaining all unresolved constraints. -/ | inconclusive
      (attempt : Attempt code.trace code.point)

/-- Check saved finite code without changing its point, trace or cached centre bound.

The same saved cache is validated and consumed by the continuation interpreter.
Neither original source states nor source callbacks are required. A candidate
failure has the same finite, explicitly inconclusive meaning as transcript checking.
-/
def checkCode (code : Continuation.Code) : CodeCheck code :=
  match validate code.trace with
  | .error reason => .invalid (.transcript reason)
  | .ok valid =>
      if nonnegative : 0 ≤ code.centerBound then
        if pointBound : Gaussian.Norm.Basic.normSq code.point ≤ code.centerBound then
          match List.All.check
              (fun entry : Basic.Exchange Question Enclosure.Ball =>
                Gaussian.Norm.Basic.normSq entry.reply.center ≤ code.centerBound)
              (fun _ => inferInstance) code.trace with
          | .rejected entry member failed => .invalid (.centreBound entry member failed)
          | .accepted centresBound =>
              match List.All.check
                  (fun entry : Basic.Exchange Question Enclosure.Ball => entry.reply.Contains code.point)
                  (fun _ => inferInstance) code.trace with
              | .accepted inside =>
                  .valid ⟨inside, valid.accurate, valid.consistent, nonnegative, pointBound, centresBound⟩
              | .rejected entry member outside => .inconclusive
                  ⟨valid, code.trace.filter (fun entry => decide (¬ entry.reply.Contains code.point)), rfl,
                    entry, member, outside, code.trace.length, rfl, 1, rfl⟩
        else .invalid (.pointBound pointBound)
      else .invalid (.negativeBound nonnegative)

namespace CodeCheck

/-- Read whether checking the saved numerical code established complete continuation validity. -/
@[expose] def succeeded {code : Continuation.Code} : CodeCheck code → Prop
  | .valid _ => True
  | .invalid _ => False
  | .inconclusive _ => False

/-- Every valid finite code passes the source-free saved-code checker. -/
theorem of_valid (code : Continuation.Code) (valid : Continuation.Valid code) :
    (checkCode code).succeeded := by
  cases result : checkCode code with
  | valid certificate => exact True.intro
  | invalid reason => exact (reason.refutes valid).elim
  | inconclusive attempt => exact (attempt.outside (valid.inside attempt.rejected attempt.member)).elim

end CodeCheck

end Purelib.Approximation.Gaussian.Observation.Imported

end
