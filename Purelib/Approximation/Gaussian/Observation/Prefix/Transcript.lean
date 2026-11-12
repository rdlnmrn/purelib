module

public import Purelib.Approximation.Gaussian.Observation.Cursor.Transcript
public import Purelib.Data.CCL.Encoding.Prefix.Cursor
public import Purelib.Geometry.Rational.Box.Enclosure
import Purelib.Computation.Query.History
import Purelib.Data.List.Append
import Purelib.Data.List.Membership
import Purelib.Approximation.Gaussian.Observation.Cursor.Request
import Purelib.LinearAlgebra.Coordinates2.Matrix

/-!
# Canonical affine raw-prefix observations

These replies retain the original exact raw word, affine parser and inverse
chart together with an ambient Gaussian ball. The payment flag records an
explicit affine terminal when a finite rational continuation cannot provide
the whole additional-bit count; productive residual padding is separate.
-/

public section

namespace Purelib.Approximation.Gaussian.Observation.Prefix

open Purelib
open Purelib.Data.CCL.Encoding
open Purelib.Data.CCL
open Purelib.Data.Gaussian
open Purelib.Computation
open Purelib.Computation.Query
open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2

set_option genInjectivity false in
/-- A canonical numerical reply retains its exact word, original parser and inverse chart, and ambient enclosure. -/
structure Reply where
  /-- The exact original affine raw prefix. -/ word : List Bool
  /-- The same original parser-state cache. -/ state : Parser.State
  /-- The same original inverse-chart cache. -/ inverseMatrix : Matrix2.GaussianMatrix
  /-- The observed enclosure of the input in its fixed ambient affine chart. -/ ball : Enclosure.Ball
  /-- This request reported an affine terminal instead of paying the entire additional count. -/ terminal : Bool
deriving @[expose] DecidableEq

namespace Reply

set_option genInjectivity false in
/-- One exact Gaussian candidate realizes the original canonical reply at its retained affine parser tail. -/
structure Candidate (reply : Reply) (point : Basic.Canonical) where
  /-- The supplied exact affine tail in this same original chart. -/ tail : Basic.Canonical
  /-- The retained parser belongs to the exact original word. -/ stateSpec : reply.state = Parser.State.parse reply.word
  /-- The retained parser chart is nonsingular. -/ determinant : Matrix2.Matrix2.determinant reply.state.matrix ≠ 0
  /-- The retained inverse chart belongs to that same parser matrix. -/ inverseSpec :
    reply.inverseMatrix = Matrix2.BoundaryAdjugate.adjugate reply.state.matrix
  /-- The cached affine tail uses that same original inverse chart. -/ tailSpec :
    tail = Purelib.Geometry.Projective.Homography.Basic.homographic reply.inverseMatrix point
  /-- The same affine tail represents the supplied input under all original parser constraints. -/ represented :
    Parser.Semantics.State.Represents reply.state point tail
  /-- The same candidate belongs to the exact supplied ambient numerical ball. -/ inside : reply.ball.Contains point
  /-- A reported terminal proves that no further affine bit is admissible for this same input and parser. -/ stopped :
    reply.terminal = true → ∀ bit, ¬Parser.Semantics.Prefix.CanStep reply.state point bit

/-- Read the exact canonical word representation from the same retained affine-tail certificate. -/
theorem wordRepresented {reply : Reply} {point : Basic.Canonical} (candidate : Candidate reply point) :
    Parser.Semantics.Prefix.Represented reply.word point :=
  ⟨candidate.tail, candidate.stateSpec ▸ candidate.represented⟩

end Reply

namespace Continuation

set_option genInjectivity false in
/-- Finite canonical continuation code retains an exact affine cursor and its same complete numerical reply. -/
structure Code where
  /-- The exact retained affine cursor, including its original parser and inverse chart. -/ cursor :
    Encoding.Prefix.Cursor
  /-- The original complete numerical reply, including its ball and terminal flag. -/ reply : Reply

namespace Code

/-- Read the same fixed Gaussian-rational input from the exact retained cursor. -/
@[expose] def point (code : Code) : Basic.Canonical := code.cursor.point

set_option genInjectivity false in
/-- A canonical code binds its numerical reply to the same exact cursor, input and terminal convention. -/
structure Valid (code : Code) : Prop where
  /-- The exact retained cursor has its complete affine representation. -/ cursor : code.cursor.Valid
  /-- The numerical reply exposes that exact retained word. -/ wordEq : code.reply.word = code.cursor.word
  /-- The numerical reply consumes that same original parser cache. -/ stateEq : code.reply.state = code.cursor.state
  /-- The numerical reply consumes that same original inverse-chart cache. -/ inverseEq :
    code.reply.inverseMatrix = code.cursor.inverseMatrix
  /-- The same rational input belongs to the exact retained numerical ball. -/ inside :
    code.reply.ball.Contains code.point
  /-- A reported terminal proves no further affine bit at this same exact cursor. -/ stopped :
    code.reply.terminal = true → ∀ bit, ¬Parser.Semantics.Prefix.CanStep code.cursor.state code.point bit

/-- Restore finite code from the same cached candidate, preserving every original word, chart and tail. -/
@[expose] def ofCandidate (reply : Reply) (point : Basic.Canonical) (candidate : reply.Candidate point) :
    {code : Code // code.Valid} :=
  let cursor : Encoding.Prefix.Cursor := ⟨point, reply.word, reply.state, reply.inverseMatrix, candidate.tail⟩
  ⟨⟨cursor, reply⟩,
    ⟨candidate.stateSpec, candidate.determinant, candidate.inverseSpec, candidate.tailSpec, candidate.represented⟩,
    rfl, rfl, rfl, candidate.inside, candidate.stopped⟩

end Code

/-- One saved numerical request and its complete original next code. -/
abbrev Step := Query.History.Step Cursor.Request Code

namespace Step

/-- A saved transition preserves its exact reading and prefix and pays the complete original request. -/
abbrev Valid (earlier : Code) (step : Step) : Prop :=
  Cursor.Request.ValidStep Code.point (fun code : Code => code.reply.word)
  (fun code : Code => code.reply.ball.radiusSq) Code.Valid earlier step

end Step

/-- An ordered saved chain binds each transition to its exact preceding code. -/
abbrev Chain := Query.History.Chain Step.Valid

namespace Chain

/-- Construct one certified saved transition followed by its original suffix. -/
abbrev cons := @Query.History.Chain.cons Cursor.Request Code Step.Valid

/-- Project the first saved transition's exact original preceding-code certificate. -/
theorem head {earlier : Code} {step : Step} {remaining : List Step} (chain : Chain earlier (step :: remaining)) :
    step.Valid earlier := Query.History.Chain.head chain

/-- Project the same original suffix beginning at its exact cached next code. -/
theorem tail {earlier : Code} {step : Step} {remaining : List Step} (chain : Chain earlier (step :: remaining)) :
    Chain step.next remaining := Query.History.Chain.tail chain

end Chain

/-- A finite saved history retains its original initial code and complete ordered requests. -/
abbrev History := Query.History Cursor.Request Code

namespace History

/-- The same saved history starts valid and certifies every request from its exact preceding code. -/
abbrev Valid (history : History) : Prop := Query.History.Valid Code.Valid Step.Valid history

/-- Read all exact saved codes, including the original initial code, in chronological order. -/
@[expose] def codes (history : History) : List Code := Query.History.codes history

/-- Read the exact last stored code by following only the original chronological list spine.

The empty saved suffix returns its supplied current code. A nonempty suffix
uses the actual next-code cache; it invokes no numerical request procedure.
-/
@[expose] def endpointFrom : Code → List Step → Code
  | code, [] => code
  | _, step :: remaining => endpointFrom step.next remaining

/-- Read the last original cached code without replaying or rebuilding any request. -/
@[expose] def endpoint (history : History) : Code := endpointFrom history.initial history.steps

/-- The final saved cache has the intrinsic validity carried by its exact chronological chain. -/
theorem endpointFrom_valid (code : Code) (valid : code.Valid) (steps : List Step)
    (chain : Chain code steps) : (endpointFrom code steps).Valid := by
  induction chain with
  | nil code => exact valid
  | cons step head tail induction => exact induction head.nextValid

/-- A valid saved history certifies the same exact final stored code. -/
theorem endpoint_valid (history : History) (valid : history.Valid) : history.endpoint.Valid :=
  endpointFrom_valid history.initial valid.initial history.steps valid.chain

/-- Each final saved code keeps the rational reading of the same original initial code. -/
theorem endpointFrom_point (code : Code) (steps : List Step) (chain : Chain code steps) :
    (endpointFrom code steps).point = code.point := by
  induction chain with
  | nil code => rfl
  | cons step head tail induction => exact induction.trans head.pointEq

/-- The actual saved endpoint reads the same rational point as its original initial code. -/
theorem endpoint_point (history : History) (valid : history.Valid) :
    history.endpoint.point = history.initial.point :=
  endpointFrom_point history.initial history.steps valid.chain

/-- The last saved numerical word extends its original starting word through the same actual request chain. -/
theorem endpointFrom_prefix (code : Code) (steps : List Step) (chain : Chain code steps) :
    code.reply.word.IsPrefix (endpointFrom code steps).reply.word := by
  induction chain with
  | nil code => exact ⟨[], Data.List.Append.append_nil _⟩
  | cons step head tail induction =>
      rcases head.wordPrefix with ⟨first, firstEq⟩
      rcases induction with ⟨second, secondEq⟩
      exact ⟨first ++ second, (Data.List.Append.append_assoc _ first second).symm.trans
        ((congrArg (fun earlier => earlier ++ second) firstEq).trans secondEq)⟩

/-- Read the exact numerical trace from its original path and complete cached replies. -/
@[expose] def traceFrom : List Cursor.Request → List Step → Basic.Trace Cursor.Question Reply :=
  Query.History.traceFrom Code.reply

/-- Read every original saved request occurrence in chronological order. -/
@[expose] def trace (history : History) : Basic.Trace Cursor.Question Reply := traceFrom [] history.steps

/-- Every original saved numerical exchange exposes a prefix of the same final cached word. -/
theorem traceFrom_prefix (code : Code) (steps : List Step) (chain : Chain code steps)
    (path : List Cursor.Request) : ∀ entry ∈ traceFrom path steps,
    entry.reply.word.IsPrefix (endpointFrom code steps).reply.word := by
  induction steps generalizing code path with
  | nil => intro entry member; nomatch member
  | cons step remaining induction =>
      intro entry member
      cases Data.List.Membership.mem_cons.mp member with
      | inl same =>
          cases same
          exact endpointFrom_prefix step.next remaining chain.tail
      | inr later => exact induction step.next chain.tail (path ++ [step.request]) entry later

/-- Every saved numerical word remains in the actual final endpoint's word. -/
theorem trace_prefix (history : History) (valid : history.Valid) : ∀ entry ∈ history.trace,
    entry.reply.word.IsPrefix history.endpoint.reply.word :=
  traceFrom_prefix history.initial history.steps valid.chain []

end History

end Continuation

set_option genInjectivity false in
/-- One original canonical exchange has its exact affine reading, prefix payment and strict enclosure accuracy. -/
structure Realization (entry : Basic.Exchange Cursor.Question Reply) (point : Basic.Canonical) where
  /-- The exact old-chart candidate and complete original representation. -/ candidate : entry.reply.Candidate point
  /-- The exact word exposed before the original request. -/ previousWord : List Bool
  /-- The original previously exposed word persists. -/ wordPrefix : previousWord.IsPrefix entry.reply.word
  /-- An original source prefix request pays the exact additional count. -/ length :
    ∀ count, entry.query.request = .bits count → entry.reply.word.length = previousWord.length + count
  /-- An original enclosure request pays its same strict positive squared target. -/ accurate :
    ∀ target positive, entry.query.request = .enclosure target positive → entry.reply.ball.radiusSq < target

set_option genInjectivity false in
/-- One canonical transcript retains a proper uniform realization box and its actual rational survivor. -/
structure Admitted (trace : Basic.Trace Cursor.Question Reply) where
  /-- The exact final proper prefix enclosure, retaining its original parser and inverse chart. -/ enclosure :
    Encoding.Prefix.Enclosure
  /-- The one explicit rational survivor of that same original proper enclosure. -/ realization : enclosure.Realization
  /-- Every original recorded exchange has its same cached candidate at the shared survivor. -/ exchanges :
    List ((entry : Basic.Exchange Cursor.Question Reply) × Realization entry realization.point)
  /-- All original exchanges and repeated occurrences are retained in order. -/ traceEq :
    exchanges.map Sigma.fst = trace
  /-- Every point in the final proper box satisfies every original numerical ball and canonical prefix. -/ uniform :
    ∀ point, enclosure.box.Contains point → ∀ entry ∈ trace,
      entry.reply.ball.Contains point ∧ Parser.Semantics.Prefix.Represented entry.reply.word point
  /-- Every original positive enclosure request pays its own strict target. -/ accurate :
    ∀ entry ∈ trace, ∀ target positive, entry.query.request = .enclosure target positive →
      entry.reply.ball.radiusSq < target
  /-- Every repeated full path question has an identical complete original numerical reply. -/ consistent :
    ∀ left ∈ trace, ∀ right ∈ trace, left.query = right.query → left.reply = right.reply
  /-- The exact original starting code and chronological saved canonical request chain. -/ history :
    Continuation.History
  /-- The same complete finite canonical history has its affine and numerical validity. -/ historyValid : history.Valid
  /-- The finite history retains this same actual proper-box rational survivor. -/ historyPoint :
    history.initial.point = realization.point
  /-- The exact final finite code retained from the original chronological saved chain. -/ endpoint :
    Continuation.Code
  /-- The endpoint consumes the original final saved cache. -/ endpointEq : endpoint = history.endpoint
  /-- The final cached cursor keeps the same original realization's word, parser, inverse chart and tail. -/
  endpointCursor : endpoint.cursor = (Encoding.Prefix.Cursor.ofRealization realization).val
  /-- Every recorded or recalled exchange belongs to that same chronological saved request chain. -/ covered :
    ∀ entry ∈ trace, entry ∈ history.trace

namespace Admitted

/-- The retained final code has the exact intrinsic validity of its original saved chain. -/
theorem endpointValid {trace : Basic.Trace Cursor.Question Reply} (admitted : Admitted trace) :
    admitted.endpoint.Valid :=
  admitted.endpointEq.symm ▸ admitted.history.endpoint_valid admitted.historyValid

/-- The retained endpoint keeps the same cached nonzero proper-box rational sample. -/
theorem endpointPoint {trace : Basic.Trace Cursor.Question Reply} (admitted : Admitted trace) :
    admitted.endpoint.point = admitted.realization.point :=
  congrArg Encoding.Prefix.Cursor.point admitted.endpointCursor

/-- Every original recorded word remains in the same retained endpoint's exact word. -/
theorem endpointPrefix {trace : Basic.Trace Cursor.Question Reply} (admitted : Admitted trace) :
    ∀ entry ∈ trace, entry.reply.word.IsPrefix admitted.endpoint.reply.word := by
  intro entry member
  exact admitted.endpointEq.symm ▸ admitted.history.trace_prefix admitted.historyValid entry
    (admitted.covered entry member)

end Admitted

end Purelib.Approximation.Gaussian.Observation.Prefix

end
