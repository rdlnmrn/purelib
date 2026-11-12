module

public import Purelib.Data.CCL.Transducer.Machine.History
import Purelib.Computation.Query.Basic
import Purelib.Computation.Query.Path
public import Purelib.Approximation.Gaussian.Observation.Cursor.Request
public import Purelib.Geometry.Projective.Chordal.Transport
import Purelib.Computation.Query.History
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.List.Append

/-!
# Numerical productive cursor transcripts

Replies contain finite numerical words, phase descriptions, retained chart
caches and a rational tail ball. A candidate certificate interprets those
same finite data at a supplied rational tail and relates its chart image
to one common projective reading. Productive residual-zero padding retains
its homogeneous infinity convention through the finite mode interpreter.
-/

public section

namespace Purelib.Approximation.Gaussian.Observation.Cursor

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Data.CCL.Transducer
open Purelib.Data.CCL.Progressive
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Computation
open Purelib.Computation.Query
open Purelib.Geometry.Projective

/-- A numerical cursor question retains its original finite request path and next request. -/
abbrev Question := Path.Question Request

namespace Question

/-- Read the exact request path after consuming this question. -/
@[expose] def path (question : Question) : List Request :=
  Path.Question.path question

end Question

set_option genInjectivity false in
/-- One finite numerical cursor reply retains exact words, chart caches and a tail enclosure. -/
structure Reply where
  /-- The finite phase description and exact word/chart caches, at the observed ball centre. -/ cursor : Machine.Code
  /-- The actual numerical enclosure in that same local tail coordinate. -/ ball : Enclosure.Ball
  /-- The cached transport coefficient of the retained image matrix. -/ coefficient : Fraction.Rational
  /-- The displayed squared-chordal allowance paid by the numerical tail ball. -/ allowanceSq : Fraction.Rational
deriving @[expose] DecidableEq

namespace Reply

/-- Interpret the retained finite phase description at a supplied candidate, preserving every other data field. -/
@[expose] def atTail (reply : Reply) (tail : Basic.Canonical) : Machine.Code :=
  { reply.cursor with mode := reply.cursor.mode.replaceValue tail }

set_option genInjectivity false in
/-- A candidate-independent numerical reply certificate validates its chart coefficient and squared allowance. -/
structure Numerical (reply : Reply) : Prop where
  /-- The cached coefficient belongs to the exact retained image matrix. -/ coefficientEq :
    reply.coefficient = Chordal.Transport.transportCoefficient reply.cursor.matrix
  /-- The actual retained chart has a positive transport coefficient. -/ coefficientPositive : 0 < reply.coefficient
  /-- The displayed allowance consumes the same coefficient and cached tail radius. -/ allowanceEq :
    reply.allowanceSq = 4 * reply.coefficient * reply.ball.radiusSq

set_option genInjectivity false in
/-- An explicit rational tail realizes a numerical productive cursor reply at one common projective reading. -/
structure Candidate (reply : Reply) (image : Line.GaussianLine) where
  /-- The actual rational tail proposed in this reply's original local chart. -/ tail : Basic.Canonical
  /-- The finite code at that same tail satisfies all retained mode, parser and chart conditions. -/ valid :
    (reply.atTail tail).Valid
  /-- The same tail belongs to the exact retained numerical enclosure. -/ inside : reply.ball.Contains tail
  /-- The original chart and proposed tail represent the same common projective reading. -/ represented :
    image.Equivalent (Line.Matrix.act reply.cursor.matrix (Line.Proj.affine tail))

namespace Candidate

/-- The cached finite reply code has the same exact singleton affine origin as its certified rational reading. -/
theorem exactCursor {reply : Reply} {point : Basic.Canonical}
    (candidate : Candidate reply (Line.Proj.affine point)) :
    Machine.Semantics.Basic.ExactCursor (Process.exact point) ()
      ((reply.atTail candidate.tail).interpret candidate.valid) := by
  apply Machine.Code.exactCursor
  change (Line.Matrix.act reply.cursor.matrix
    (Line.Proj.affine (reply.cursor.mode.replaceValue candidate.tail).value)).Equivalent (Line.Proj.affine point)
  rewrite [Mode.Code.replaceValue_value]
  exact Line.Proj.Equivalent.symm candidate.represented

end Candidate

/-- Construct a numerical reply from an original cached snapshot and an already retained chart coefficient. -/
@[expose] def withCoefficient (snapshot : Machine.Snapshot) (coefficient : Fraction.Rational) : Reply :=
  let cursor : Machine.Code :=
    ⟨Mode.Code.data snapshot.machine.mode snapshot.ball.center, snapshot.machine.emitted, snapshot.machine.pending,
      snapshot.frame.parser, snapshot.frame.normalization, snapshot.frame.matrix, snapshot.frame.adjugate⟩
  ⟨cursor, snapshot.ball, coefficient, 4 * coefficient * snapshot.ball.radiusSq⟩

/-- Construct a numerical reply from a cached snapshot, computing its chart coefficient once. -/
@[expose] def ofSnapshot (snapshot : Machine.Snapshot) : Reply :=
  withCoefficient snapshot (Chordal.Transport.transportCoefficient snapshot.frame.matrix)

/-- Reusing a retained correct coefficient gives exactly the same complete numerical snapshot reply. -/
theorem withCoefficient_eq (snapshot : Machine.Snapshot) (coefficient : Fraction.Rational)
    (coefficientEq : coefficient = Chordal.Transport.transportCoefficient snapshot.frame.matrix) :
    withCoefficient snapshot coefficient = ofSnapshot snapshot :=
  congrArg (withCoefficient snapshot) coefficientEq

/-- The actual snapshot reply retains the correct positive chart coefficient and its own squared allowance. -/
theorem ofSnapshot_numerical (snapshot : Machine.Snapshot) : Numerical (ofSnapshot snapshot) :=
  ⟨rfl, Chordal.Transport.transportCoefficient_pos snapshot.frame.matrix snapshot.frame.determinantNonzero, rfl⟩

/-- An original history realization certifies the exact saved numerical reply at its shared projective reading. -/
def ofRealization {snapshot : Machine.Snapshot} {image : Line.GaussianLine}
    (realization : Machine.History.Realization snapshot image) : Candidate (ofSnapshot snapshot) image := by
  let mode := Mode.Exact.ofPossible snapshot.machine.mode realization.value realization.possible
  let description := Machine.Code.ofRealization snapshot.frame mode snapshot.grammar
  have modeEq : ((ofSnapshot snapshot).atTail realization.value).mode = description.code.mode :=
    (Mode.Code.data_replaceValue snapshot.machine.mode snapshot.ball.center realization.value).trans
      ((Mode.Exact.ofPossible_code snapshot.machine.mode realization.value realization.possible).symm.trans
        description.modeEq.symm)
  have codeEq : (ofSnapshot snapshot).atTail realization.value = description.code :=
    Machine.Code.ext modeEq description.emittedEq.symm description.pendingEq.symm description.parserEq.symm
      description.normalizationEq.symm description.matrixEq.symm description.adjugateEq.symm
  exact ⟨realization.value, codeEq.symm ▸ description.valid, realization.inside, realization.represented⟩

/-- The reply constructor retains the same explicitly computed old-chart rational tail. -/
private theorem ofRealization_tail_specification {snapshot : Machine.Snapshot} {image : Line.GaussianLine}
    (realization : Machine.History.Realization snapshot image) :
    (ofRealization realization).tail = realization.value := rfl

/-- The public reply realization reuses the exact earlier tail computed by the retained history. -/
theorem ofRealization_tail {snapshot : Machine.Snapshot} {image : Line.GaussianLine}
    (realization : Machine.History.Realization snapshot image) :
    (ofRealization realization).tail = realization.value := ofRealization_tail_specification realization

end Reply

namespace Continuation

set_option genInjectivity false in
/-- Finite cursor continuation code retains its rational reading, exact numerical reply and local rational tail. -/
structure Code where
  /-- The fixed Gaussian-rational reading of this continuation. -/ point : Basic.Canonical
  /-- The complete saved numerical reply with original words, ball and chart caches. -/ reply : Reply
  /-- The actual local tail realizing that same saved reply. -/ tail : Basic.Canonical

set_option genInjectivity false in
/-- Finite code has valid phase data, ball containment and its own fixed affine rational reading. -/
structure Valid (code : Code) : Prop where
  /-- The exact retained words, phase bounds and chart caches are valid at the supplied local tail. -/ cursor :
    (code.reply.atTail code.tail).Valid
  /-- The supplied local tail satisfies the same saved numerical ball. -/ inside : code.reply.ball.Contains code.tail
  /-- The same local chart represents the code's fixed rational reading. -/ represented :
    (Line.Proj.affine code.point).Equivalent
      (Line.Matrix.act code.reply.cursor.matrix (Line.Proj.affine code.tail))
  /-- The saved numerical coefficient and squared allowance are valid. -/ numerical : Reply.Numerical code.reply

namespace Valid

/-- Project the same cached local tail and proofs as the original reply's rational candidate. -/
@[expose] def candidate {code : Code} (valid : Valid code) : Reply.Candidate code.reply (Line.Proj.affine code.point) :=
  ⟨code.tail, valid.cursor, valid.inside, valid.represented⟩

end Valid

namespace Code

/-- Construct finite code from one saved candidate without rebuilding its words, ball or chart caches. -/
@[expose] def ofCandidate (point : Basic.Canonical) (reply : Reply)
    (candidate : Reply.Candidate reply (Line.Proj.affine point)) (numerical : Reply.Numerical reply) :
    {code : Code // Valid code} :=
  ⟨⟨point, reply, candidate.tail⟩, candidate.valid, candidate.inside, candidate.represented, numerical⟩

end Code

/-- One saved numerical request and its complete original next code. -/
abbrev Step := Query.History.Step Request Code

namespace Step

/-- A saved transition preserves its exact reading and prefix and pays the complete original request. -/
abbrev Valid (earlier : Code) (step : Step) : Prop :=
  Cursor.Request.ValidStep Code.point (fun code : Code => code.reply.cursor.emitted)
  (fun code : Code => code.reply.allowanceSq) Continuation.Valid earlier step

end Step

/-- An ordered saved chain binds each transition to its exact preceding code. -/
abbrev Chain := Query.History.Chain Step.Valid

namespace Chain

/-- Construct one certified saved transition followed by its original suffix. -/
abbrev cons := @Query.History.Chain.cons Request Code Step.Valid

/-- Project the first saved transition's exact original preceding-code certificate. -/
theorem head {earlier : Code} {step : Step} {remaining : List Step} (chain : Chain earlier (step :: remaining)) :
    step.Valid earlier := Query.History.Chain.head chain

/-- Project the same original suffix beginning at its exact cached next code. -/
theorem tail {earlier : Code} {step : Step} {remaining : List Step} (chain : Chain earlier (step :: remaining)) :
    Chain step.next remaining := Query.History.Chain.tail chain

end Chain

/-- A finite saved history retains its original initial code and complete ordered requests. -/
abbrev History := Query.History Request Code

namespace History

/-- The same saved history starts valid and certifies every request from its exact preceding code. -/
abbrev Valid (history : History) : Prop := Query.History.Valid Continuation.Valid Step.Valid history

/-- Read all exact saved codes, including the original initial code, in chronological order. -/
@[expose] def codes (history : History) : List Code := Query.History.codes history

/-- Read the exact numerical trace from its original path and complete cached replies. -/
@[expose] def traceFrom : List Request → List Step → Basic.Trace Question Reply :=
  Query.History.traceFrom Code.reply

/-- Read every original saved request occurrence in chronological order. -/
@[expose] def trace (history : History) : Basic.Trace Question Reply := traceFrom [] history.steps

end History

end Continuation

set_option genInjectivity false in
/-- One retained mixed exchange has a cached rational realization, strict accuracy and exact prefix payment. -/
structure Realization (entry : Basic.Exchange Question Reply) (point : Basic.Canonical) where
  /-- The cached rational tail realizes this same reply at the shared affine reading. -/ candidate :
    Reply.Candidate entry.reply (Line.Proj.affine point)
  /-- The reply's actual chart coefficient and allowance are valid. -/ numerical : Reply.Numerical entry.reply
  /-- The exact word exposed before this original request. -/ previousWord : List Bool
  /-- The reply extends that exact previously exposed word. -/ wordPrefix :
    previousWord.IsPrefix entry.reply.cursor.emitted
  /-- A bit request pays its actual additional length. -/ length :
    ∀ count, entry.query.request = .bits count → entry.reply.cursor.emitted.length = previousWord.length + count
  /-- An enclosure request pays its actual strict squared-chordal target. -/ accurate :
    ∀ target positive, entry.query.request = .enclosure target positive → entry.reply.allowanceSq < target

set_option genInjectivity false in
/-- A source-produced mixed transcript retains one rational reading and every original numerical realization.

The ordered realization table caches the actual old-chart candidates and
complete prefix and accuracy payments, including repeated occurrences.
The final reply has its own certified finite cursor for later requests.
-/
structure Admitted (trace : Basic.Trace Question Reply) where
  /-- The shared explicitly computed Gaussian-rational reading. -/ point : Basic.Canonical
  /-- The ordered cached certificates for these exact numerical exchanges. -/ realizations :
    List ((entry : Basic.Exchange Question Reply) × Realization entry point)
  /-- The cached certificates retain the complete trace in its original order. -/ traceEq :
    realizations.map Sigma.fst = trace
  /-- The exact cached numerical reply at the final retained state. -/ current : Reply
  /-- The final finite cursor realizes the same rational reading. -/ currentCandidate :
    Reply.Candidate current (Line.Proj.affine point)
  /-- The final numerical chart and allowance are valid. -/ currentNumerical : Reply.Numerical current
  /-- The complete finite rational history starts at the same actual original reply. -/ history : Continuation.History
  /-- Every saved transition consumes its exact preceding code and preserves the same reading and prefix. -/
  historyValid :
    history.Valid
  /-- The finite history retains this same explicitly computed rational reading. -/ historyPoint :
    history.initial.point = point
  /-- Every recorded or recalled exchange belongs to that same chronological saved chain. -/ covered :
    ∀ entry ∈ trace, entry ∈ history.trace
  /-- Identical path questions have identical complete numerical replies. -/ consistent :
    ∀ left ∈ trace, ∀ right ∈ trace, left.query = right.query → left.reply = right.reply

end Purelib.Approximation.Gaussian.Observation.Cursor

end
