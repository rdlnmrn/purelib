module

public import Purelib.Integration.Algebraic.SquareFactor.OwnedCells.Compilation
public import Purelib.Integration.Algebraic.SquareFactor.PathContinuation.Observation

/-!
# Original prepared runs from recorded mesh and cell construction

The mesh receipt carries the actual original isolated owner and prepared
subdivision. Subsequent cell requests carry that same cached mesh; the
source reads its retained edges instead of selecting another mesh. The
returned compiled run consumes the exact certified cell models and preserves
all original path, sheet, resolution and subdivision identities.
-/

public section

namespace Purelib.Integration.Algebraic.SquareFactor.OwnedCells

open Purelib
open Purelib.Curves.Hyperelliptic.Differentials
open Purelib.Computation.Query

namespace Preparation

variable {polynomial : SquareFactor.GaussianPolynomial} {request : SquareFactor.Request}
  {prepared : SquareFactor.Prepared polynomial request} {segment : PathInput.Segment}
  {data : PathInput.Data prepared segment}

/-- The exact original selected mesh and its retained construction identity. -/
abbrev Mesh (safe : data.Safe) (sheet : Fin 2) (diameter : Coordinate) (positive : 0 < diameter) (minimum : Nat) :=
  PathContinuation.Observation.RetainedMesh safe sheet diameter positive minimum

set_option genInjectivity false in
/-- An original isolation/preparation request or a cell request on the actual retained prepared mesh. -/
inductive Question (safe : data.Safe) (sheet : Fin 2) (diameter : Coordinate)
    (positive : 0 < diameter) (minimum : Nat) where
  /-- Request the original sheet isolation or same-owner mesh preparation. -/ | prepare
      (question : PathContinuation.Observation.Question safe sheet)
  /-- Request one actual original edge value from this retained prepared mesh. -/ | cell
      (mesh : Mesh safe sheet diameter positive minimum) (question : Compilation.Question (edges mesh.val.run))

/-- Compare stages and original cell positions using retained mesh identity instead of comparing source callbacks. -/
instance {safe : data.Safe} {sheet : Fin 2} {diameter : Coordinate} {positive : 0 < diameter} {minimum : Nat} :
    DecidableEq (Question safe sheet diameter positive minimum) := fun left right =>
  match left, right with
  | .prepare question, .prepare other =>
      if same : question = other then .isTrue (congrArg Question.prepare same)
      else .isFalse (fun equal => by cases equal; exact same rfl)
  | .cell ⟨mesh, meshEq⟩ question, .cell ⟨other, otherEq⟩ otherQuestion => by
      cases meshEq
      cases otherEq
      exact if same : question = otherQuestion then
        .isTrue (congrArg (Question.cell ⟨_, rfl⟩) same)
      else .isFalse (fun equal => by cases equal; exact same rfl)
  | .prepare _, .cell _ _ => .isFalse (fun equal => by cases equal)
  | .cell _ _, .prepare _ => .isFalse (fun equal => by cases equal)

set_option genInjectivity false in
/-- The complete original preparation reply or an owned cell reply from its exact cached mesh. -/
inductive Reply (safe : data.Safe) (sheet : Fin 2) (diameter : Coordinate)
    (positive : 0 < diameter) (minimum : Nat) where
  /-- Retain the actual initial owner or original selected mesh. -/ | prepare
      (reply : PathContinuation.Observation.Reply safe sheet diameter positive minimum)
  /-- Retain the actual cached mesh with the cell reply at its original position. -/ | cell
      (mesh : Mesh safe sheet diameter positive minimum) (reply : Compilation.Reply (edges mesh.val.run))

set_option genInjectivity false in
/-- A reply has the wrong construction stage or violates an actual original preparation or cell request. -/
inductive Invalidity where
  /-- Preparation received a cell reply instead of its original owner or mesh. -/ | expectedPreparation
  /-- Cell compilation received an owner or mesh reply. -/ | expectedCell
  /-- Retain the original preparation boundary's exact invalidity. -/ | preparation
      (invalid : PathContinuation.Observation.Invalidity)
  /-- Retain the original ordered cell boundary's exact invalidity and position. -/ | cell
      (invalid : Compilation.Invalidity)

/-- The actual original compiled run with identity to its complete sheet and resolution request. -/
abbrev Realization (safe : data.Safe) (sheet : Fin 2) (diameter : Coordinate)
    (positive : 0 < diameter) (minimum : Nat) :=
  {run : CompiledRun safe sheet diameter positive minimum // run = OwnedCells.compile sheet diameter positive minimum}

/-- Execute preparation or evaluate the actual retained mesh's edge, without selecting another mesh for a cell call. -/
def answer (safe : data.Safe) (sheet : Fin 2) (diameter : Coordinate) (positive : 0 < diameter) (minimum : Nat) :
    Question safe sheet diameter positive minimum → Reply safe sheet diameter positive minimum
  | .prepare question => .prepare (PathContinuation.Observation.answer safe sheet diameter positive minimum question)
  | .cell mesh question => .cell mesh (Compilation.answer question)

/-- Two retained meshes have the same original nominal owner and complete cached data. -/
private theorem mesh_eq {safe : data.Safe} {sheet : Fin 2} {diameter : Coordinate}
    {positive : 0 < diameter} {minimum : Nat} (first second : Mesh safe sheet diameter positive minimum) :
    first = second := by
  cases first with
  | mk first firstEq =>
      cases second with
      | mk second secondEq =>
          cases firstEq
          cases secondEq
          rfl

/-- Forward the actual preparation request and reject a reply from the cell-construction stage. -/
private def preparationHandler (safe : data.Safe) (sheet : Fin 2) (diameter : Coordinate)
    (positive : 0 < diameter) (minimum : Nat) (question : PathContinuation.Observation.Question safe sheet) :
    Program (Question safe sheet diameter positive minimum) (Reply safe sheet diameter positive minimum)
      (Except Invalidity (PathContinuation.Observation.Reply safe sheet diameter positive minimum)) :=
  (Program.query (.prepare question)).map fun reply =>
    match reply with
    | .prepare actual => .ok actual
    | .cell _ _ => .error .expectedPreparation

/-- Forward a cell request on the exact returned mesh and transport only the original mesh ownership index. -/
private def cellHandler (safe : data.Safe) (sheet : Fin 2) (diameter : Coordinate)
    (positive : 0 < diameter) (minimum : Nat) (mesh : Mesh safe sheet diameter positive minimum)
    (question : Compilation.Question (edges mesh.val.run)) :
    Program (Question safe sheet diameter positive minimum) (Reply safe sheet diameter positive minimum)
      (Except Invalidity (Compilation.Reply (edges mesh.val.run))) :=
  (Program.query (.cell mesh question)).map fun reply =>
    match reply with
    | .prepare _ => .error .expectedCell
    | .cell retained actual => .ok (mesh_eq retained mesh ▸ actual)

/-- Retain the original isolated owner and selected mesh through the same displayed preparation requests. -/
private def meshProgram (safe : data.Safe) (sheet : Fin 2) (diameter : Coordinate)
    (positive : 0 < diameter) (minimum : Nat) :
    Program (Question safe sheet diameter positive minimum) (Reply safe sheet diameter positive minimum)
      (Except Invalidity (Mesh safe sheet diameter positive minimum)) :=
  ((PathContinuation.Observation.retainedProgram safe sheet diameter positive minimum).substituteChecked
    (preparationHandler safe sheet diameter positive minimum)).map fun result =>
      match result with
      | .error invalid => .error invalid
      | .ok executed => executed.value.mapError Invalidity.preparation

/-- Assemble the original compiled run from its exact retained mesh and already compiled cells. -/
private def assemble {safe : data.Safe} {sheet : Fin 2} {diameter : Coordinate}
    {positive : 0 < diameter} {minimum : Nat} (mesh : Mesh safe sheet diameter positive minimum)
    (cells : Compilation.Realization (edges mesh.val.run)) : Realization safe sheet diameter positive minimum :=
  let cellsEq := cells.property.trans (compileEdges_edges mesh.val.run)
  ⟨CompiledRun.ofMeshCells mesh.val mesh.property cells.val cellsEq,
    CompiledRun.ofMeshCells_eq_compile mesh.val mesh.property cells.val cellsEq⟩

/-- Compile the actual returned mesh's cells with each original root and polynomial request displayed. -/
private def cellsProgram (safe : data.Safe) (sheet : Fin 2) (diameter : Coordinate)
    (positive : 0 < diameter) (minimum : Nat) (mesh : Mesh safe sheet diameter positive minimum) :
    Program (Question safe sheet diameter positive minimum) (Reply safe sheet diameter positive minimum)
      (Except Invalidity (Realization safe sheet diameter positive minimum)) :=
  ((Compilation.program (edges mesh.val.run)).substituteChecked
    (cellHandler safe sheet diameter positive minimum mesh)).map fun result =>
      match result with
      | .error invalid => .error invalid
      | .ok executed =>
          match executed.value with
          | .error invalid => .error (.cell invalid)
          | .ok cells => .ok (assemble mesh cells)

/-- Construct the original whole prepared run, consuming its mesh and cell caches through their named constructors. -/
def program (safe : data.Safe) (sheet : Fin 2) (diameter : Coordinate) (positive : 0 < diameter) (minimum : Nat) :
    Program (Question safe sheet diameter positive minimum) (Reply safe sheet diameter positive minimum)
      (Except Invalidity (Realization safe sheet diameter positive minimum)) :=
  (meshProgram safe sheet diameter positive minimum).bind fun result =>
    match result with
    | .error invalid => .pure (.error invalid)
    | .ok mesh => cellsProgram safe sheet diameter positive minimum mesh

/-- Record the original whole preparation and compilation with one chronological source-request trace. -/
def compile (safe : data.Safe) (sheet : Fin 2) (diameter : Coordinate) (positive : 0 < diameter) (minimum : Nat) :
    Protocol (Question safe sheet diameter positive minimum) (Reply safe sheet diameter positive minimum)
      (Except Invalidity (Realization safe sheet diameter positive minimum)) :=
  (program safe sheet diameter positive minimum).protocol

/-- The same original source retains exactly its original selected mesh and construction certificate. -/
private theorem meshProgram_value (safe : data.Safe) (sheet : Fin 2) (diameter : Coordinate)
    (positive : 0 < diameter) (minimum : Nat) :
    ((meshProgram safe sheet diameter positive minimum).protocol.run
      (answer safe sheet diameter positive minimum)).value =
      .ok ⟨PathContinuation.selectMesh safe sheet diameter positive minimum, rfl⟩ := by
  rewrite [meshProgram, Program.map_execution, Protocol.map_run_value,
    Program.substituteChecked_value _ _ _
      (PathContinuation.Observation.answer safe sheet diameter positive minimum) (fun _ => rfl)]
  dsimp only
  rewrite [PathContinuation.Observation.retainedProgram_value]
  rfl

/-- Original actual replies to a cached-mesh cell request retain that same reply without recomputing the mesh. -/
private theorem cellHandler_value (safe : data.Safe) (sheet : Fin 2) (diameter : Coordinate)
    (positive : 0 < diameter) (minimum : Nat) (mesh : Mesh safe sheet diameter positive minimum)
    (question : Compilation.Question (edges mesh.val.run)) :
    ((cellHandler safe sheet diameter positive minimum mesh question).protocol.run
      (answer safe sheet diameter positive minimum)).value = .ok (Compilation.answer question) := rfl

/-- A successful whole-run realization is exactly the same original compiled run and complete ownership certificate. -/
private theorem realization_eq {safe : data.Safe} {sheet : Fin 2} {diameter : Coordinate}
    {positive : 0 < diameter} {minimum : Nat} (actual : Realization safe sheet diameter positive minimum) :
    actual = ⟨OwnedCells.compile sheet diameter positive minimum, rfl⟩ := by
  cases actual with
  | mk run same =>
      cases same
      rfl

/-- Compiling the exact returned mesh's cell replies assembles the same original whole compiled run. -/
private theorem cellsProgram_value (safe : data.Safe) (sheet : Fin 2) (diameter : Coordinate)
    (positive : 0 < diameter) (minimum : Nat) (mesh : Mesh safe sheet diameter positive minimum) :
    ((cellsProgram safe sheet diameter positive minimum mesh).protocol.run
      (answer safe sheet diameter positive minimum)).value =
      .ok ⟨OwnedCells.compile sheet diameter positive minimum, rfl⟩ := by
  rewrite [cellsProgram, Program.map_execution, Protocol.map_run_value,
    Program.substituteChecked_value _ _ _ Compilation.answer
      (cellHandler_value safe sheet diameter positive minimum mesh)]
  dsimp only
  rewrite [Compilation.program_value]
  exact congrArg Except.ok (realization_eq _)

/-- The whole displayed construction preserves the original compiled run for every safe path and sheet request. -/
private theorem program_value_spec (safe : data.Safe) (sheet : Fin 2) (diameter : Coordinate)
    (positive : 0 < diameter) (minimum : Nat) :
    ((program safe sheet diameter positive minimum).protocol.run
      (answer safe sheet diameter positive minimum)).value =
      .ok ⟨OwnedCells.compile sheet diameter positive minimum, rfl⟩ := by
  rewrite [program, Program.bind_execution, Protocol.bind_run_value, meshProgram_value]
  dsimp only
  exact cellsProgram_value safe sheet diameter positive minimum _

/-- The retained whole-run construction returns its exact original compiled run with its defining identity. -/
theorem program_value (safe : data.Safe) (sheet : Fin 2) (diameter : Coordinate)
    (positive : 0 < diameter) (minimum : Nat) :
    ((program safe sheet diameter positive minimum).protocol.run
      (answer safe sheet diameter positive minimum)).value =
      .ok ⟨OwnedCells.compile sheet diameter positive minimum, rfl⟩ :=
  program_value_spec safe sheet diameter positive minimum

/-- Whole-run compilation retains the exact original result and every reached preparation and cell callback. -/
theorem compile_execution (safe : data.Safe) (sheet : Fin 2) (diameter : Coordinate)
    (positive : 0 < diameter) (minimum : Nat) :
    let computation := compile safe sheet diameter positive minimum
    let oracle := answer safe sheet diameter positive minimum
    computation.run oracle =
      ⟨.ok ⟨OwnedCells.compile sheet diameter positive minimum, rfl⟩, (computation.run oracle).trace⟩ :=
  Basic.Execution.ext (program_value safe sheet diameter positive minimum) rfl

/-- Replay consumes the same cached mesh and cell replies without calling their original source operations. -/
theorem compile_replay (safe : data.Safe) (sheet : Fin 2) (diameter : Coordinate)
    (positive : 0 < diameter) (minimum : Nat) :
    let computation := compile safe sheet diameter positive minimum
    let oracle := answer safe sheet diameter positive minimum
    computation.replayExact (computation.run oracle).trace =
      .ok (.ok ⟨OwnedCells.compile sheet diameter positive minimum, rfl⟩) :=
  ((compile safe sheet diameter positive minimum).replayExact_run _).trans
    (congrArg Except.ok (program_value safe sheet diameter positive minimum))

/-- Outside-request changes preserve the entire original prepared run and its ordered mesh and cell trace. -/
theorem payload_erasure {Payload : Type} (safe : data.Safe) (sheet : Fin 2) (diameter : Coordinate)
    (positive : 0 < diameter) (minimum : Nat) (payload : Payload)
    (outside : Payload → Question safe sheet diameter positive minimum → Reply safe sheet diameter positive minimum) :
    let computation := compile safe sheet diameter positive minimum
    let oracle := answer safe sheet diameter positive minimum
    computation.run (Boundary.Trace.overlay (computation.run oracle).trace (outside payload)) =
      computation.run oracle :=
  Protocol.annotation_erasure (compile safe sheet diameter positive minimum)
    (answer safe sheet diameter positive minimum) payload outside

end Preparation

end Purelib.Integration.Algebraic.SquareFactor.OwnedCells
