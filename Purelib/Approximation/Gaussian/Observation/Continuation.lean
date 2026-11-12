module

public import Purelib.Approximation.Gaussian.Observation.Transcript
public import Purelib.Approximation.Gaussian.Process.Coherence.Basic
public import Purelib.Computation.Query.Boundary
public import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Data.List.Rat.Order
import Purelib.Data.List.Map
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

/-!
# Finite rational continuation of an admitted enclosure transcript

Continuation code consists of a rational reading, the exact saved numerical
trace and one cached centre bound. Its interpreter consults that finite trace
and returns the exact point ball outside it. The certified process has one
singleton reading at every historical and future request state; no original
source, source state type or callback is retained by the interpreter.
-/

public section

namespace Purelib.Approximation.Gaussian.Observation.Continuation

open Purelib.Approximation
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Computation.Query

set_option genInjectivity false in
/-- Finite numerical code for one rational continuation, including its exact cached historical replies. -/
structure Code where
  /-- The cached Gaussian rational reading of this continuation. -/ point : Gaussian.Basic.Canonical
  /-- The exact retained finite numerical trace. -/ trace : Basic.Trace Question Enclosure.Ball
  /-- A cached uniform bound on historical centres and the exact rational reading. -/ centerBound : Fraction.Rational

set_option genInjectivity false in
/-- Numerical validity of one finite continuation code under its own exact rational reading.

Every historical occurrence contains that same reading and pays its target.
Complete reply consistency and the retained centre bounds justify both saved
reply lookup and arbitrary future exact-point requests.
-/
structure Valid (code : Code) : Prop where
  /-- The cached reading belongs to every actual saved ball. -/ inside :
    ∀ entry ∈ code.trace, entry.reply.Contains code.point
  /-- Every saved reply pays its exact original request. -/ accurate :
    ∀ entry ∈ code.trace, entry.reply.radiusSq < entry.query.request.targetSq
  /-- Identical saved questions have identical complete replies. -/ consistent :
    ∀ left ∈ code.trace, ∀ right ∈ code.trace,
      left.query = right.query → left.reply = right.reply
  /-- The retained uniform centre bound is nonnegative. -/ bound_nonnegative : 0 ≤ code.centerBound
  /-- The cached exact rational reading meets the same bound. -/ point_bounded :
    Gaussian.Norm.Basic.normSq code.point ≤ code.centerBound
  /-- Every actual historical centre meets the same bound. -/ centres_bounded :
    ∀ entry ∈ code.trace, Gaussian.Norm.Basic.normSq entry.reply.center ≤ code.centerBound

namespace Code

/-- Interpret a finite path question using exact cached replies and the same rational reading as fallback. -/
@[expose] def interpret (code : Code) (question : Question) : Enclosure.Ball :=
  match Boundary.Trace.lookup code.trace question with
  | some ball => ball
  | none => Enclosure.Ball.point code.point

/-- A valid code returns exactly each original saved reply, including repeated occurrences. -/
theorem answers (code : Code) (valid : Valid code) : Basic.Answers code.interpret code.trace := by
  intro entry member
  unfold interpret
  rewrite [Boundary.Trace.lookup_of_consistent code.trace valid.consistent entry member]
  rfl

/-- Every interpreted reply contains the code's same exact rational reading. -/
theorem interpret_inside (code : Code) (valid : Valid code) (question : Question) :
    (code.interpret question).Contains code.point := by
  unfold interpret
  cases found : Boundary.Trace.lookup code.trace question with
  | none => exact Enclosure.Ball.contains_point code.point
  | some ball =>
      rcases Boundary.Trace.lookup_eq_some_member code.trace question ball found with
        ⟨entry, member, _queryEq, replyEq⟩
      exact replyEq ▸ valid.inside entry member

/-- Every positive future question receives a reply strictly within its own squared-error target. -/
theorem interpret_accurate (code : Code) (valid : Valid code) (question : Question) :
    (code.interpret question).radiusSq < question.request.targetSq := by
  unfold interpret
  cases found : Boundary.Trace.lookup code.trace question with
  | none => exact question.request.positive
  | some ball =>
      rcases Boundary.Trace.lookup_eq_some_member code.trace question ball found with
        ⟨entry, member, queryEq, replyEq⟩
      exact replyEq ▸ queryEq ▸ valid.accurate entry member

/-- The interpreter consumes the retained centre bound for every historical and future question. -/
theorem interpret_center_bounded (code : Code) (valid : Valid code) (question : Question) :
    Gaussian.Norm.Basic.normSq (code.interpret question).center ≤ code.centerBound := by
  unfold interpret
  cases found : Boundary.Trace.lookup code.trace question with
  | none => exact valid.point_bounded
  | some ball =>
      rcases Boundary.Trace.lookup_eq_some_member code.trace question ball found with
        ⟨entry, member, _queryEq, replyEq⟩
      exact replyEq ▸ valid.centres_bounded entry member

/-- Read the original finite path denoted by a retained continuation state. -/
@[expose] def statePath : Option Question → List Request
  | none => []
  | some question => question.path

/-- Construct the actual persistent rational process from the code and its numerical validity certificate.

Historical states retain their exact saved balls. A new request appends its
positive target to the actual state path and invokes the finite interpreter.
Every state has the same singleton possibility predicate; persistence and
accuracy therefore hold for paths leaving the saved history as well.
-/
@[expose] def process (code : Code) (valid : Valid code) : Gaussian.Process where
  State := Option Question
  ball
    | none => Enclosure.Ball.point code.point
    | some question => code.interpret question
  Possible _ value := value = code.point
  witness _ := ⟨code.point, rfl⟩
  possible_inside := by
    intro state value equal
    cases equal
    cases state with
    | none => exact Enclosure.Ball.contains_point code.point
    | some question => exact code.interpret_inside valid question
  refine state target positive := some ⟨statePath state, Request.ofPositive target positive⟩
  refine_persists := by
    intro _state _target _positive _value possible
    exact possible
  accurate state target positive :=
    code.interpret_accurate valid ⟨statePath state, Request.ofPositive target positive⟩
  centerBound := code.centerBound
  centerBound_nonneg := valid.bound_nonnegative
  center_bounded state := by
    cases state with
    | none => exact valid.point_bounded
    | some question => exact code.interpret_center_bounded valid question

/-- The actual singleton-reading continuation process is coherent at its historical ball allowances. -/
def coherent (code : Code) (valid : Valid code) :
    Process.Coherence.Basic.Coherent (code.process valid) where
  allowance state := ((code.process valid).ball state).radiusSq
  allowance_nonneg state := ((code.process valid).ball state).radiusSq_nonneg
  ball_radius_le state := Fraction.Order.Basic.le_refl _
  possible_close := by
    intro leftState rightState leftValue rightValue leftEqual rightEqual
    change leftValue = code.point at leftEqual
    change rightValue = code.point at rightEqual
    cases leftEqual
    cases rightEqual
    rewrite [Gaussian.Basic.sub_self, Gaussian.Norm.Basic.normSq_zero]
    exact Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (Fraction.Order.Arithmetic.add_le_add_direct
        ((code.process valid).ball leftState).radiusSq_nonneg
        ((code.process valid).ball rightState).radiusSq_nonneg)
  accuracyRequest target := target
  accuracyRequest_pos positive := positive
  refine_accurate := by
    intro state target _positive request requestPositive requestSmall
    have accurate := (code.process valid).accurate state request requestPositive
    change _ ≤ request ∧ ¬ request ≤ _ at accurate
    change request ≤ target ∧ ¬ target ≤ request at requestSmall
    change _ ≤ target ∧ ¬ target ≤ _
    constructor
    · exact Fraction.Order.Basic.le_trans _ _ _ accurate.1 requestSmall.1
    · intro reverse
      exact accurate.2 (Fraction.Order.Basic.le_trans _ _ _ requestSmall.1 reverse)

/-- Name the same certified finite continuation process at its exact initial state. -/
def named (code : Code) (valid : Valid code) : Gaussian.Name.Coherent.CoherentNamed :=
  ⟨⟨code.process valid, none⟩, code.coherent valid⟩

private theorem named_sample_specification (code : Code) (valid : Valid code) (index : Nat) :
    (Gaussian.Name.Sampling.approximation (code.named valid).name).sample index = code.point := rfl

/-- Every actual finite witness sample of the retained continuation name is its same exact rational reading. -/
theorem named_sample (code : Code) (valid : Valid code) (index : Nat) :
    (Gaussian.Name.Sampling.approximation (code.named valid).name).sample index = code.point :=
  named_sample_specification code valid index

end Code

set_option genInjectivity false in
/-- Retain both the original admitted trace and its own finite-code rational continuation.

The code uses that exact trace and cached rational survivor. Its validity
certificate justifies every saved reply and arbitrary future requests; the
new process is interpreted solely from these finite numerical data.
-/
structure Result (trace : Basic.Trace Question Enclosure.Ball) where
  /-- The original admitted numerical trace and its cached common reading. -/ admitted : Admitted trace
  /-- The actual finite executable continuation description. -/ code : Code
  /-- The code retains the exact original trace. -/ traceEq : code.trace = trace
  /-- The code consumes the exact original admitted rational reading. -/ pointEq : code.point = admitted.point
  /-- Complete numerical validity of that same interpreted code. -/ valid : Valid code

/-- Construct finite-code rational continuation from the actual admitted reading and cached trace.

The largest retained centre quadrance, together with the exact reading's
quadrance, is computed once and cached. The answering interpreter and
process consume that exact cache for every subsequent request.
-/
def ofAdmitted {trace : Basic.Trace Question Enclosure.Ball} (admitted : Admitted trace) : Result trace := by
  let values := trace.map
    (fun (entry : Basic.Exchange Question Enclosure.Ball) => Gaussian.Norm.Basic.normSq entry.reply.center)
  let pointNorm := Gaussian.Norm.Basic.normSq admitted.point
  let bound := List.Rat.maximum pointNorm values
  let code : Code := ⟨admitted.point, trace, bound⟩
  have valid : Valid code :=
    { inside := admitted.inside
      accurate := admitted.accurate
      consistent := admitted.consistent
      bound_nonnegative := List.Rat.maximum_nonneg (Gaussian.Norm.Basic.normSq_nonneg admitted.point) values
      point_bounded := by
        change pointNorm ≤ List.Rat.maximum pointNorm values
        exact List.Rat.floor_le_maximum pointNorm values
      centres_bounded := by
        intro entry member
        change Gaussian.Norm.Basic.normSq entry.reply.center ≤ List.Rat.maximum pointNorm values
        have included : Gaussian.Norm.Basic.normSq entry.reply.center ∈ values :=
          List.Map.mem_map_of_mem
            (f := fun (saved : Basic.Exchange Question Enclosure.Ball) =>
              Gaussian.Norm.Basic.normSq saved.reply.center) member
        exact @List.Rat.le_maximum_of_mem pointNorm values
          (Gaussian.Norm.Basic.normSq entry.reply.center) included }
  exact ⟨admitted, code, rfl, rfl, valid⟩

/-- The retained admission and rational reading are the builder's exact original inputs. -/
private theorem ofAdmitted_specification {trace : Basic.Trace Question Enclosure.Ball} (admitted : Admitted trace) :
    (ofAdmitted admitted).admitted = admitted ∧ (ofAdmitted admitted).code.point = admitted.point :=
  ⟨rfl, rfl⟩

/-- The continuation builder retains the exact original admission certificate. -/
theorem ofAdmitted_admitted {trace : Basic.Trace Question Enclosure.Ball} (admitted : Admitted trace) :
    (ofAdmitted admitted).admitted = admitted := (ofAdmitted_specification admitted).1

/-- The continuation builder reads the same supplied rational survivor. -/
theorem ofAdmitted_point {trace : Basic.Trace Question Enclosure.Ball} (admitted : Admitted trace) :
    (ofAdmitted admitted).code.point = admitted.point := (ofAdmitted_specification admitted).2

namespace Result

/-- The finite continuation interpreter returns every original recorded reply exactly. -/
theorem answers {trace : Basic.Trace Question Enclosure.Ball} (continuation : Result trace) :
    Basic.Answers continuation.code.interpret trace := by
  intro entry member
  have retained : entry ∈ continuation.code.trace := continuation.traceEq.symm ▸ member
  exact continuation.code.answers continuation.valid entry retained

/-- Agreement on the admitted replies preserves the entire finite adaptive execution.

The original source oracle and finite continuation code remain separate.
The admission hypothesis is indexed by the exact executed trace, including
ordered repetitions, rather than an arbitrary compatible set of observations.
-/
theorem same_execution {Value : Type} (observer : Protocol Question Enclosure.Ball Value)
    (source : Question → Enclosure.Ball) (continuation : Result (observer.run source).trace) :
    observer.run continuation.code.interpret = observer.run source :=
  observer.run_of_answers source continuation.code.interpret continuation.answers

end Result

end Purelib.Approximation.Gaussian.Observation.Continuation

end
