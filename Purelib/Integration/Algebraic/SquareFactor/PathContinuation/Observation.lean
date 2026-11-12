module

public import Purelib.Integration.Algebraic.SquareFactor.PathContinuation
public import Purelib.Computation.Query.Program
import Purelib.Computation.Query.Boundary
import Purelib.Polynomial.Dense.Evaluation

/-!
# Root isolation and mesh preparation on the original retained path

The initial isolation reply carries the actual original sheet owner.
The next query passes that same owner to preparation. Its ownership
certificate makes query equality executable without comparing functions.
The returned mesh retains all original prepared sources and subdivisions.
-/

public section

namespace Purelib.Integration.Algebraic.SquareFactor.PathContinuation

open Purelib
open Purelib.Computation.Query
open Purelib.Curves.Hyperelliptic.Differentials

namespace Observation

variable {polynomial : SquareFactor.GaussianPolynomial} {request : SquareFactor.Request}
  {prepared : SquareFactor.Prepared polynomial request} {segment : PathInput.Segment}
  {data : PathInput.Data prepared segment}

/-- The actual starting owner carrier of the original safe path. -/
abbrev StartingOwner (safe : data.Safe) := Owner (data.radicand.parameterPolynomial.eval
  ((clearSegment safe).pointAt first.parameter))

/-- Retain the exact original sheet owner with its defining identity. -/
abbrev RetainedOwner (safe : data.Safe) (sheet : Fin 2) :=
  {owner : StartingOwner safe // owner = initialOwner safe sheet}

/-- The selected mesh retains the same original sheet owner and complete diameter and minimum-depth request. -/
abbrev Mesh (safe : data.Safe) (sheet : Fin 2) (diameter : Coordinate) (positive : 0 < diameter) (minimum : Nat) :=
  SelectedMesh safe (initialOwner safe sheet) diameter positive minimum

/-- The actual selected mesh with identity to its original path, sheet and complete resolution request. -/
abbrev RetainedMesh (safe : data.Safe) (sheet : Fin 2) (diameter : Coordinate)
    (positive : 0 < diameter) (minimum : Nat) :=
  {mesh : Mesh safe sheet diameter positive minimum // mesh = selectMesh safe sheet diameter positive minimum}

set_option genInjectivity false in
/-- Isolate the original initial sheet or prepare the supplied exact retained owner on that same path. -/
inductive Question (safe : data.Safe) (sheet : Fin 2) where
  /-- Compute the original independent starting sheet owner. -/ | isolate
  /-- Prepare this same retained starting owner without isolating a second root. -/ | prepare
      (owner : RetainedOwner safe sheet)

/-- Compare operation tags and use the retained original-owner identities for preparation queries. -/
instance {safe : data.Safe} {sheet : Fin 2} : DecidableEq (Question safe sheet) := fun left right =>
  match left, right with
  | .isolate, .isolate => .isTrue rfl
  | .prepare ⟨first, firstEq⟩, .prepare ⟨second, secondEq⟩ => by
      cases firstEq
      cases secondEq
      exact .isTrue rfl
  | .isolate, .prepare _ => .isFalse (fun equal => by cases equal)
  | .prepare _, .isolate => .isFalse (fun equal => by cases equal)

set_option genInjectivity false in
/-- An actual starting owner or prepared mesh, with identity to its original canonical construction. -/
inductive Reply (safe : data.Safe) (sheet : Fin 2) (diameter : Coordinate)
    (positive : 0 < diameter) (minimum : Nat) where
  /-- Retain the actual original independently isolated owner. -/ | owner (cached : RetainedOwner safe sheet)
  /-- Retain the same owner's actual mesh and its full original construction identity. -/ | mesh
      (cached : Mesh safe sheet diameter positive minimum)
      (cachedEq : cached = selectMesh safe sheet diameter positive minimum)

set_option genInjectivity false in
/-- A supplied reply has the wrong original root/preparation operation tag. -/
inductive Invalidity where
  /-- Initial isolation received a prepared mesh instead of its root owner. -/ | expectedOwner
  /-- Mesh preparation received a root owner instead of its prepared mesh. -/ | expectedMesh

/-- Execute the original isolation or prepare the actual owner carried by the displayed query. -/
def answer (safe : data.Safe) (sheet : Fin 2) (diameter : Coordinate) (positive : 0 < diameter) (minimum : Nat) :
    Question safe sheet → Reply safe sheet diameter positive minimum
  | .isolate => .owner ⟨initialOwner safe sheet, rfl⟩
  | .prepare ⟨owner, ownerEq⟩ =>
      let selected := selectMeshFromOwner safe owner diameter positive minimum
      let cached := selected.castOwner ownerEq
      have cachedEq : cached = selectMesh safe sheet diameter positive minimum := by
        cases ownerEq
        rfl
      .mesh cached cachedEq

/-- Retain isolation and same-owner preparation together with the returned mesh's original construction identity. -/
def retainedProgram (safe : data.Safe) (sheet : Fin 2) (diameter : Coordinate)
    (positive : 0 < diameter) (minimum : Nat) :
    Computation.Query.Program (Question safe sheet) (Reply safe sheet diameter positive minimum)
      (Except Invalidity (RetainedMesh safe sheet diameter positive minimum)) :=
  (Computation.Query.Program.query .isolate).bind fun result =>
    match result with
    | .mesh _ _ => .pure (.error .expectedOwner)
    | .owner cached => (Computation.Query.Program.query (.prepare cached)).map fun result =>
        match result with
        | .owner _ => .error .expectedMesh
        | .mesh selected same => .ok ⟨selected, same⟩

/-- Retain isolation and same-owner preparation as an expandable original query construction. -/
def program (safe : data.Safe) (sheet : Fin 2) (diameter : Coordinate) (positive : 0 < diameter) (minimum : Nat) :
    Computation.Query.Program (Question safe sheet) (Reply safe sheet diameter positive minimum)
      (Except Invalidity (Mesh safe sheet diameter positive minimum)) :=
  (retainedProgram safe sheet diameter positive minimum).map (Except.map Subtype.val)

/-- Original source replies retain the selected mesh and its exact original construction certificate. -/
private theorem retainedProgram_value_spec (safe : data.Safe) (sheet : Fin 2) (diameter : Coordinate)
    (positive : 0 < diameter) (minimum : Nat) :
    ((retainedProgram safe sheet diameter positive minimum).protocol.run
      (answer safe sheet diameter positive minimum)).value =
      .ok ⟨selectMesh safe sheet diameter positive minimum, rfl⟩ := rfl

/-- The retained preparation construction returns the same original mesh with its cache identity. -/
theorem retainedProgram_value (safe : data.Safe) (sheet : Fin 2) (diameter : Coordinate)
    (positive : 0 < diameter) (minimum : Nat) :
    ((retainedProgram safe sheet diameter positive minimum).protocol.run
      (answer safe sheet diameter positive minimum)).value =
      .ok ⟨selectMesh safe sheet diameter positive minimum, rfl⟩ :=
  retainedProgram_value_spec safe sheet diameter positive minimum

/-- Request the initial root and prepare that exact returned owner, retaining the original selected mesh. -/
def prepare (safe : data.Safe) (sheet : Fin 2) (diameter : Coordinate) (positive : 0 < diameter) (minimum : Nat) :
    Protocol (Question safe sheet) (Reply safe sheet diameter positive minimum)
      (Except Invalidity (Mesh safe sheet diameter positive minimum)) :=
  (program safe sheet diameter positive minimum).protocol

/-- Expansion retains the complete original mesh result and both actual isolation/preparation requests. -/
theorem expand_value {Question Reply : Type} (safe : data.Safe) (sheet : Fin 2) (diameter : Coordinate)
    (positive : 0 < diameter) (minimum : Nat)
    (handlers : Observation.Question safe sheet → Protocol Question Reply
      (Observation.Reply safe sheet diameter positive minimum)) (oracle : Question → Reply) :
    (((program safe sheet diameter positive minimum).expand handlers).run oracle).value =
      (prepare safe sheet diameter positive minimum).run (fun question => ((handlers question).run oracle).value) :=
  Computation.Query.Program.expand_value handlers (program safe sheet diameter positive minimum) oracle

/-- The displayed isolation and preparation return the same original selected mesh for every safe path and sheet. -/
private theorem prepare_value_spec (safe : data.Safe) (sheet : Fin 2) (diameter : Coordinate)
    (positive : 0 < diameter) (minimum : Nat) :
    ((prepare safe sheet diameter positive minimum).run (answer safe sheet diameter positive minimum)).value =
      .ok (selectMesh safe sheet diameter positive minimum) := rfl

/-- Isolation and preparation retain the exact original selected mesh without exposing the callback implementations. -/
theorem prepare_value (safe : data.Safe) (sheet : Fin 2) (diameter : Coordinate)
    (positive : 0 < diameter) (minimum : Nat) :
    ((prepare safe sheet diameter positive minimum).run (answer safe sheet diameter positive minimum)).value =
      .ok (selectMesh safe sheet diameter positive minimum) := prepare_value_spec safe sheet diameter positive minimum

/-- The whole preparation records initial isolation and the same actual owner passed to its preparation callback. -/
private theorem prepare_execution_spec (safe : data.Safe) (sheet : Fin 2) (diameter : Coordinate)
    (positive : 0 < diameter) (minimum : Nat) :
    (prepare safe sheet diameter positive minimum).run (answer safe sheet diameter positive minimum) =
      ⟨.ok (selectMesh safe sheet diameter positive minimum),
        [⟨.isolate, answer safe sheet diameter positive minimum .isolate⟩,
          ⟨.prepare ⟨initialOwner safe sheet, rfl⟩,
            answer safe sheet diameter positive minimum (.prepare ⟨initialOwner safe sheet, rfl⟩)⟩]⟩ := rfl

/-- The complete preparation retains its original mesh and actual ordered isolation and owner-preparation replies. -/
theorem prepare_execution (safe : data.Safe) (sheet : Fin 2) (diameter : Coordinate)
    (positive : 0 < diameter) (minimum : Nat) :
    (prepare safe sheet diameter positive minimum).run (answer safe sheet diameter positive minimum) =
      ⟨.ok (selectMesh safe sheet diameter positive minimum),
        [⟨.isolate, answer safe sheet diameter positive minimum .isolate⟩,
          ⟨.prepare ⟨initialOwner safe sheet, rfl⟩,
            answer safe sheet diameter positive minimum (.prepare ⟨initialOwner safe sheet, rfl⟩)⟩]⟩ :=
  prepare_execution_spec safe sheet diameter positive minimum

/-- Replaying the two retained replies returns the original selected mesh without isolation or preparation callbacks. -/
theorem prepare_replay (safe : data.Safe) (sheet : Fin 2) (diameter : Coordinate)
    (positive : 0 < diameter) (minimum : Nat) :
    (prepare safe sheet diameter positive minimum).replayExact
      ((prepare safe sheet diameter positive minimum).run (answer safe sheet diameter positive minimum)).trace =
      .ok (.ok (selectMesh safe sheet diameter positive minimum)) :=
  ((prepare safe sheet diameter positive minimum).replayExact_run _).trans
    (congrArg Except.ok (prepare_value safe sheet diameter positive minimum))

/-- Outside-query changes preserve the complete original mesh and both actual isolation/preparation exchanges. -/
theorem payload_erasure {Payload : Type} (safe : data.Safe) (sheet : Fin 2) (diameter : Coordinate)
    (positive : 0 < diameter) (minimum : Nat) (payload : Payload)
    (outside : Payload → Question safe sheet → Reply safe sheet diameter positive minimum) :
    let computation := prepare safe sheet diameter positive minimum
    let oracle := answer safe sheet diameter positive minimum
    computation.run (Boundary.Trace.overlay (computation.run oracle).trace (outside payload)) =
      computation.run oracle :=
  Protocol.annotation_erasure (prepare safe sheet diameter positive minimum)
    (answer safe sheet diameter positive minimum) payload outside

end Observation

end Purelib.Integration.Algebraic.SquareFactor.PathContinuation
