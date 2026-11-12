module

public import Purelib.Integration.Algebraic.SquareFactor.OwnedCells.Observation
import Purelib.Data.List.Append

/-!
# Ordered cell compilation with displayed original source requests

Every request retains its position in the original prepared edge list.
Compilation consumes each original cell handler and its certified model
once, then uses the named cached-cell constructor. A wrong-position or
invalid cell reply stops before any later edge is evaluated.
-/

public section

namespace Purelib.Integration.Algebraic.SquareFactor.OwnedCells

open Purelib
open Purelib.Curves.Hyperelliptic.Differentials
open Purelib.Computation.Query

namespace Compilation

variable {polynomial : SquareFactor.GaussianPolynomial} {request : SquareFactor.Request}
  {prepared : SquareFactor.Prepared polynomial request} {segment : PathInput.Segment}
  {data : PathInput.Data prepared segment} {safe : data.Safe}

set_option genInjectivity false in
/-- A source request at an exact retained position in the original prepared edge list. -/
inductive Question : List (Edge safe) → Type where
  /-- Request the current original edge's root or polynomial value. -/ | first {edge remaining}
      (question : Edge.Observation.Question) : Question (edge :: remaining)
  /-- Request an original later edge without changing its retained list owner. -/ | later {edge remaining}
      (question : Question remaining) : Question (edge :: remaining)

/-- Compare retained positions and operations without comparing prepared owners or callbacks. -/
@[expose] def decideQuestion {edges : List (Edge safe)} (left right : Question edges) : Decidable (left = right) :=
  match left, right with
  | .first question, .first other =>
      if same : question = other then .isTrue (congrArg Question.first same)
      else .isFalse (fun equal => by cases equal; exact same rfl)
  | .later question, .later other =>
      match decideQuestion question other with
      | .isTrue same => .isTrue (congrArg Question.later same)
      | .isFalse different => .isFalse (fun equal => by cases equal; exact different rfl)
  | .first _, .later _ => .isFalse (fun equal => by cases equal)
  | .later _, .first _ => .isFalse (fun equal => by cases equal)

/-- Retained cell questions have executable position and operation equality. -/
instance {edges : List (Edge safe)} : DecidableEq (Question edges) := decideQuestion

set_option genInjectivity false in
/-- A certified original cell reply at its exact retained edge-list position. -/
inductive Reply : List (Edge safe) → Type 1 where
  /-- Retain the current original edge's complete root or polynomial reading. -/ | first {edge remaining}
      (reply : Edge.Observation.Reply edge) : Reply (edge :: remaining)
  /-- Retain a later edge's same nominal reply and ownership. -/ | later {edge remaining}
      (reply : Reply remaining) : Reply (edge :: remaining)

set_option genInjectivity false in
/-- A reply has the wrong retained position or violates an original cell request. -/
inductive Invalidity where
  /-- A current-edge request received a later-edge reply. -/ | expectedFirst
  /-- A later-edge request received a current-edge reply. -/ | expectedLater
  /-- The current cell's original checking boundary rejected its reply. -/ | cell
      (invalid : Edge.Observation.Invalidity)
  /-- Retain the actual invalidity in the original list's later part. -/ | later (invalid : Invalidity)

/-- Ordered cached cells with identity to compilation of their exact original retained edges. -/
abbrev Realization (edges : List (Edge safe)) :=
  {cells : List (Cell safe) // cells = compileEdges edges}

namespace Realization

/-- Split the actual cached cells at the original first edge-list length, preserving both compilation identities.

The operation takes and drops the same retained cell list. Every cell model
and prepared owner is reused; neither original edge compilation is executed
to construct the returned caches or determine the split position.
-/
@[expose] def split {first second : List (Edge safe)} (actual : Realization (first ++ second)) :
    Realization first × Realization second :=
  let head := actual.val.take first.length
  let tail := actual.val.drop first.length
  have headEq : head = compileEdges first := by
    dsimp only [head]
    rewrite [actual.property, compileEdges_append, ← compileEdges_length first,
      Data.List.Append.take_length_append]
    rfl
  have tailEq : tail = compileEdges second := by
    dsimp only [tail]
    rewrite [actual.property, compileEdges_append, ← compileEdges_length first,
      Data.List.Append.drop_length_append]
    rfl
  (⟨head, headEq⟩, ⟨tail, tailEq⟩)

end Realization

/-- Execute the original cell callback at the exact displayed retained position. -/
@[expose] def answer : {edges : List (Edge safe)} → Question edges → Reply edges
  | _ :: _, .first question => .first (Edge.Observation.answer _ question)
  | _ :: _, .later question => .later (answer question)

/-- Forward the current original cell's request and reject an actual wrong-position reply. -/
private def firstHandler (edge : Edge safe) (remaining : List (Edge safe)) (question : Edge.Observation.Question) :
    Program (Question (edge :: remaining)) (Reply (edge :: remaining))
      (Except Invalidity (Edge.Observation.Reply edge)) :=
  (Program.query (.first question)).map fun reply =>
    match reply with
    | .first cached => .ok cached
    | .later _ => .error .expectedFirst

/-- Forward a later original request without changing its owner or reconstructing its cached edge. -/
private def laterHandler (edge : Edge safe) (remaining : List (Edge safe)) (question : Question remaining) :
    Program (Question (edge :: remaining)) (Reply (edge :: remaining)) (Except Invalidity (Reply remaining)) :=
  (Program.query (.later question)).map fun reply =>
    match reply with
    | .first _ => .error .expectedLater
    | .later cached => .ok cached

/-- Compile the current original cell from its same retained root and coefficient caches. -/
private def firstCell (edge : Edge safe) (remaining : List (Edge safe)) :
    Program (Question (edge :: remaining)) (Reply (edge :: remaining))
      (Except Invalidity (Edge.Observation.Realization edge)) :=
  ((Edge.Observation.program edge).substituteChecked (firstHandler edge remaining)).map fun result =>
    match result with
    | .error invalid => .error invalid
    | .ok executed => executed.value.mapError Invalidity.cell

/-- Assemble the cached current cell and already compiled tail with their original defining identities. -/
private def prepend (edge : Edge safe) (remaining : List (Edge safe))
    (head : Edge.Observation.Realization edge) (tail : Realization remaining) : Realization (edge :: remaining) :=
  ⟨Cell.ofModel edge head.val head.property :: tail.val,
    congrArg₂ List.cons (Cell.ofModel_eq_compileEdge edge head.val head.property) tail.property⟩

/-- Compile every original retained edge in order, stopping on the first actual invalid reply.

The returned cells use the original cached-model constructor. Substitution
retains each intermediate query construction, so later composition exposes
all source calls without rerunning an edge to obtain its log or certificate.
-/
def program : (edges : List (Edge safe)) →
    Program (Question edges) (Reply edges) (Except Invalidity (Realization edges))
  | [] => .pure (.ok ⟨[], rfl⟩)
  | edge :: remaining => (firstCell edge remaining).bind fun result =>
      match result with
      | .error invalid => .pure (.error invalid)
      | .ok head => ((program remaining).substituteChecked (laterHandler edge remaining)).map fun result =>
          match result with
          | .error invalid => .error invalid
          | .ok executed =>
              match executed.value with
              | .error invalid => .error (.later invalid)
              | .ok tail => .ok (prepend edge remaining head tail)

/-- Transport an already built compilation along equality of its original retained edge-list owner. -/
@[expose] def castEdges {edges other : List (Edge safe)} (same : edges = other)
    (construction : Program (Question edges) (Reply edges) (Except Invalidity (Realization edges))) :
    Program (Question other) (Reply other) (Except Invalidity (Realization other)) := by
  cases same
  exact construction

/-- Compile the original ordered cells with every root and polynomial reading recorded. -/
def compile (edges : List (Edge safe)) :
    Protocol (Question edges) (Reply edges) (Except Invalidity (Realization edges)) := (program edges).protocol

/-- The current original handler retains precisely its original model under the original displayed replies. -/
private theorem firstCell_value (edge : Edge safe) (remaining : List (Edge safe)) :
    ((firstCell edge remaining).protocol.run answer).value = .ok ⟨edge.model, rfl⟩ := by
  rewrite [firstCell, Program.map_execution, Protocol.map_run_value,
    Program.substituteChecked_value _ _ _ (Edge.Observation.answer edge) (fun _ => rfl)]
  dsimp only
  rewrite [Edge.Observation.program_value]
  rfl

/-- A successful realization retains exactly the original cached ordered cell list. -/
private theorem realization_eq {edges : List (Edge safe)} (actual : Realization edges) :
    actual = ⟨compileEdges edges, rfl⟩ := by
  cases actual with
  | mk cells same =>
      cases same
      rfl

/-- Every retained edge list compiles to its exact original cached cells under the original actual source replies. -/
private theorem program_value_spec (edges : List (Edge safe)) :
    ((program edges).protocol.run answer).value = .ok ⟨compileEdges edges, rfl⟩ := by
  induction edges with
  | nil => rfl
  | cons edge remaining induction =>
      rewrite [program, Program.bind_execution, Protocol.bind_run_value, firstCell_value]
      dsimp only
      rewrite [Program.map_execution, Protocol.map_run_value,
        Program.substituteChecked_value _ _ _ answer (fun _ => rfl)]
      dsimp only
      rewrite [induction]
      exact congrArg Except.ok (realization_eq _)

/-- Original callback replies preserve the complete original ordered compiled-cell result. -/
theorem compile_value (edges : List (Edge safe)) :
    ((compile edges).run answer).value = .ok ⟨compileEdges edges, rfl⟩ := program_value_spec edges

/-- The expandable original construction retains its exact ordered compiled cells and cache identity. -/
theorem program_value (edges : List (Edge safe)) :
    ((program edges).protocol.run answer).value = .ok ⟨compileEdges edges, rfl⟩ := program_value_spec edges

/-- The whole compilation retains the original cells and every actual ordered callback receipt. -/
theorem compile_execution (edges : List (Edge safe)) :
    (compile edges).run answer = ⟨.ok ⟨compileEdges edges, rfl⟩, ((compile edges).run answer).trace⟩ :=
  Basic.Execution.ext (compile_value edges) rfl

/-- Replay returns the same cached original cells without requesting any root or polynomial value. -/
theorem compile_replay (edges : List (Edge safe)) :
    (compile edges).replayExact ((compile edges).run answer).trace = .ok (.ok ⟨compileEdges edges, rfl⟩) :=
  ((compile edges).replayExact_run answer).trans (congrArg Except.ok (compile_value edges))

/-- Changes outside the reached original edge requests preserve the complete compiled cells and ordered trace. -/
theorem payload_erasure {Payload : Type} (edges : List (Edge safe)) (payload : Payload)
    (outside : Payload → Question edges → Reply edges) :
    let computation := compile edges
    computation.run (Boundary.Trace.overlay (computation.run answer).trace (outside payload)) =
      computation.run answer :=
  Protocol.annotation_erasure (compile edges) answer payload outside

end Compilation

end Purelib.Integration.Algebraic.SquareFactor.OwnedCells
