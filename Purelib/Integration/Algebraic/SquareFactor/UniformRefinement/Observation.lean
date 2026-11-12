module

public import Purelib.Integration.Algebraic.SquareFactor.UniformRefinement.Compilation
import Purelib.Approximation.Rational.Geometric.Basic

open Purelib.Approximation.Rational.Geometric

/-!
# Synchronized refinement from recorded original mesh selection and cells

Selection returns the actual original prepared mesh bank and its complete
request identity. Subsequent cell queries carry that same selection and
consume its cached prepared edges. Assembly uses the original synchronization
and refinement constructors with their retained identities, so replay performs
neither mesh selection nor root and polynomial evaluations.
-/

public section

namespace Purelib.Integration.Algebraic.SquareFactor.UniformRefinement

open Purelib
open Purelib.Curves.Hyperelliptic.Differentials
open Purelib.Computation.Query

namespace Observation

variable {polynomial : SquareFactor.GaussianPolynomial} {request : SquareFactor.Request}
  {prepared : SquareFactor.Prepared polynomial request} {segment : PathInput.Segment}
  {data : PathInput.Data prepared segment} {safe : data.Safe}

/-- The actual original selected mesh bank with its exact parents, diameter and minimum-depth construction identity. -/
abbrev Selection (parents : List (OwnedCells.Cell safe)) (diameter : Coordinate)
    (positive : 0 < diameter) (minimum : Nat) :=
  {selected : SelectedMeshes parents diameter minimum // selected = selectMeshes parents diameter positive minimum}

set_option genInjectivity false in
/-- Original mesh selection or a cell request on the actual returned selected mesh bank. -/
inductive Question (parents : List (OwnedCells.Cell safe)) (diameter : Coordinate)
    (positive : 0 < diameter) (minimum : Nat) where
  /-- Prepare and select the original parents' common mesh bank. -/ | select
  /-- Request the actual retained bank's cell root or polynomial reading at its original ordered position. -/ | cell
      (selected : Selection parents diameter positive minimum)
      (question : OwnedCells.Compilation.Question selected.val.meshes.edges)

/-- Compare stages and cell positions using the original selected-bank identity instead of comparing functions. -/
instance {parents : List (OwnedCells.Cell safe)} {diameter : Coordinate} {positive : 0 < diameter} {minimum : Nat} :
    DecidableEq (Question parents diameter positive minimum) := fun left right =>
  match left, right with
  | .select, .select => .isTrue rfl
  | .cell ⟨selected, selectedEq⟩ question, .cell ⟨other, otherEq⟩ otherQuestion => by
      cases selectedEq
      cases otherEq
      exact if same : question = otherQuestion then
        .isTrue (congrArg (Question.cell ⟨_, rfl⟩) same)
      else .isFalse (fun equal => by cases equal; exact same rfl)
  | .select, .cell _ _ => .isFalse (fun equal => by cases equal)
  | .cell _ _, .select => .isFalse (fun equal => by cases equal)

set_option genInjectivity false in
/-- The original selected bank or a complete owned cell reply from that same actual retained selection. -/
inductive Reply (parents : List (OwnedCells.Cell safe)) (diameter : Coordinate)
    (positive : 0 < diameter) (minimum : Nat) where
  /-- Retain the actual original selected mesh bank with its construction identity. -/ | selected
      (cached : Selection parents diameter positive minimum)
  /-- Retain the same selected bank and its exact owned cell reply. -/ | cell
      (selected : Selection parents diameter positive minimum)
      (reply : OwnedCells.Compilation.Reply selected.val.meshes.edges)

set_option genInjectivity false in
/-- A reply has the wrong selection/cell stage or violates the original ordered cell checking boundary. -/
inductive Invalidity where
  /-- Original mesh selection received a cell reading. -/ | expectedSelection
  /-- Cell construction received a selected mesh instead of its cell reading. -/ | expectedCell
  /-- Retain the original cell invalidity and exact retained list position. -/ | cell
      (invalid : OwnedCells.Compilation.Invalidity)

/-- The actual synchronized expansion with identity to its same original parents and full resolution request. -/
abbrev Realization (parents : List (OwnedCells.Cell safe)) (diameter : Coordinate)
    (positive : 0 < diameter) (minimum : Nat) :=
  {result : Synchronized parents diameter minimum // result = synchronize parents diameter positive minimum}

/-- Execute original mesh selection or the actual returned bank's source request, without selecting a second bank. -/
def answer (parents : List (OwnedCells.Cell safe)) (diameter : Coordinate)
    (positive : 0 < diameter) (minimum : Nat) :
    Question parents diameter positive minimum → Reply parents diameter positive minimum
  | .select => .selected ⟨selectMeshes parents diameter positive minimum, rfl⟩
  | .cell selected question => .cell selected (MeshBank.Compilation.answer selected.val.meshes question)

/-- Retained selections belong to the same original parents and exact full mesh-selection request. -/
private theorem selection_eq {parents : List (OwnedCells.Cell safe)} {diameter : Coordinate}
    {positive : 0 < diameter} {minimum : Nat} (first second : Selection parents diameter positive minimum) :
    first = second := by
  cases first with
  | mk first firstEq =>
      cases second with
      | mk second secondEq =>
          cases firstEq
          cases secondEq
          rfl

/-- Request the original selected mesh bank and retain an actual wrong-stage failure. -/
private def selectionProgram (parents : List (OwnedCells.Cell safe)) (diameter : Coordinate)
    (positive : 0 < diameter) (minimum : Nat) :
    Program (Question parents diameter positive minimum) (Reply parents diameter positive minimum)
      (Except Invalidity (Selection parents diameter positive minimum)) :=
  (Program.query .select).map fun reply =>
    match reply with
    | .selected actual => .ok actual
    | .cell _ _ => .error .expectedSelection

/-- Forward a cell request on the actual selected bank and transport only its original selection index. -/
private def cellHandler (parents : List (OwnedCells.Cell safe)) (diameter : Coordinate)
    (positive : 0 < diameter) (minimum : Nat) (selected : Selection parents diameter positive minimum)
    (question : OwnedCells.Compilation.Question selected.val.meshes.edges) :
    Program (Question parents diameter positive minimum) (Reply parents diameter positive minimum)
      (Except Invalidity (OwnedCells.Compilation.Reply selected.val.meshes.edges)) :=
  (Program.query (.cell selected question)).map fun reply =>
    match reply with
    | .selected _ => .error .expectedCell
    | .cell retained actual => .ok (selection_eq retained selected ▸ actual)

/-- Assemble the original synchronization from the actual selected bank and its returned compiled expansion cache. -/
private def assemble {parents : List (OwnedCells.Cell safe)} {diameter : Coordinate}
    {positive : 0 < diameter} {minimum : Nat} (selected : Selection parents diameter positive minimum)
    (cached : MeshBank.Compilation.Realization selected.val.meshes) : Realization parents diameter positive minimum :=
  ⟨Synchronized.ofMeshes selected.val cached.val cached.property,
    Synchronized.ofMeshes_eq_synchronize selected.val selected.property cached.val cached.property⟩

/-- Compile the actual selected bank's cells, retaining every original request and cached block. -/
private def cellsProgram (parents : List (OwnedCells.Cell safe)) (diameter : Coordinate)
    (positive : 0 < diameter) (minimum : Nat) (selected : Selection parents diameter positive minimum) :
    Program (Question parents diameter positive minimum) (Reply parents diameter positive minimum)
      (Except Invalidity (Realization parents diameter positive minimum)) :=
  ((MeshBank.Compilation.program selected.val.meshes).substituteChecked
    (cellHandler parents diameter positive minimum selected)).map fun result =>
      match result with
      | .error invalid => .error invalid
      | .ok executed =>
          match executed.value with
          | .error invalid => .error (.cell invalid)
          | .ok cached => .ok (assemble selected cached)

/-- Construct the original synchronized refinement from its actual selected mesh bank and displayed cell requests. -/
def program (parents : List (OwnedCells.Cell safe)) (diameter : Coordinate)
    (positive : 0 < diameter) (minimum : Nat) :
    Program (Question parents diameter positive minimum) (Reply parents diameter positive minimum)
      (Except Invalidity (Realization parents diameter positive minimum)) :=
  (selectionProgram parents diameter positive minimum).bind fun result =>
    match result with
    | .error invalid => .pure (.error invalid)
    | .ok selected => cellsProgram parents diameter positive minimum selected

/-- Record original mesh selection and every reached cell callback with the complete synchronized result. -/
def synchronize (parents : List (OwnedCells.Cell safe)) (diameter : Coordinate)
    (positive : 0 < diameter) (minimum : Nat) :
    Protocol (Question parents diameter positive minimum) (Reply parents diameter positive minimum)
      (Except Invalidity (Realization parents diameter positive minimum)) :=
  (program parents diameter positive minimum).protocol

/-- Actual original replies to selected-bank cell requests preserve their same complete retained cell receipt. -/
private theorem cellHandler_value (parents : List (OwnedCells.Cell safe)) (diameter : Coordinate)
    (positive : 0 < diameter) (minimum : Nat) (selected : Selection parents diameter positive minimum)
    (question : OwnedCells.Compilation.Question selected.val.meshes.edges) :
    ((cellHandler parents diameter positive minimum selected question).protocol.run
      (answer parents diameter positive minimum)).value =
      .ok (MeshBank.Compilation.answer selected.val.meshes question) := rfl

/-- Successful synchronization retains exactly the original complete synchronized result. -/
private theorem realization_eq {parents : List (OwnedCells.Cell safe)} {diameter : Coordinate}
    {positive : 0 < diameter} {minimum : Nat} (actual : Realization parents diameter positive minimum) :
    actual = ⟨UniformRefinement.synchronize parents diameter positive minimum, rfl⟩ := by
  cases actual with
  | mk result same =>
      cases same
      rfl

/-- The actual selected bank and original cell replies assemble the original synchronized refinement. -/
private theorem cellsProgram_value (parents : List (OwnedCells.Cell safe)) (diameter : Coordinate)
    (positive : 0 < diameter) (minimum : Nat) (selected : Selection parents diameter positive minimum) :
    ((cellsProgram parents diameter positive minimum selected).protocol.run
      (answer parents diameter positive minimum)).value =
      .ok ⟨UniformRefinement.synchronize parents diameter positive minimum, rfl⟩ := by
  rewrite [cellsProgram, Program.map_execution, Protocol.map_run_value,
    Program.substituteChecked_value _ _ _ (MeshBank.Compilation.answer selected.val.meshes)
      (cellHandler_value parents diameter positive minimum selected)]
  dsimp only
  rewrite [MeshBank.Compilation.program_value]
  exact congrArg Except.ok (realization_eq _)

/-- The displayed original selection and cell callbacks retain the same original synchronization for every request. -/
private theorem program_value_spec (parents : List (OwnedCells.Cell safe)) (diameter : Coordinate)
    (positive : 0 < diameter) (minimum : Nat) :
    ((program parents diameter positive minimum).protocol.run (answer parents diameter positive minimum)).value =
      .ok ⟨UniformRefinement.synchronize parents diameter positive minimum, rfl⟩ := by
  rewrite [program, Program.bind_execution, Protocol.bind_run_value]
  change ((cellsProgram parents diameter positive minimum
    ⟨selectMeshes parents diameter positive minimum, rfl⟩).protocol.run
      (answer parents diameter positive minimum)).value = _
  exact cellsProgram_value parents diameter positive minimum _

/-- The expandable synchronization construction returns its original result with the complete retained identity. -/
theorem program_value (parents : List (OwnedCells.Cell safe)) (diameter : Coordinate)
    (positive : 0 < diameter) (minimum : Nat) :
    ((program parents diameter positive minimum).protocol.run (answer parents diameter positive minimum)).value =
      .ok ⟨UniformRefinement.synchronize parents diameter positive minimum, rfl⟩ :=
  program_value_spec parents diameter positive minimum

/-- Complete synchronization preserves the original result and every reached selection and cell request in order. -/
theorem synchronize_execution (parents : List (OwnedCells.Cell safe)) (diameter : Coordinate)
    (positive : 0 < diameter) (minimum : Nat) :
    let computation := synchronize parents diameter positive minimum
    let oracle := answer parents diameter positive minimum
    computation.run oracle =
      ⟨.ok ⟨UniformRefinement.synchronize parents diameter positive minimum, rfl⟩, (computation.run oracle).trace⟩ :=
  Basic.Execution.ext (program_value parents diameter positive minimum) rfl

/-- Replay reconstructs the same synchronized refinement from saved mesh selection and cell caches only. -/
theorem synchronize_replay (parents : List (OwnedCells.Cell safe)) (diameter : Coordinate)
    (positive : 0 < diameter) (minimum : Nat) :
    let computation := synchronize parents diameter positive minimum
    let oracle := answer parents diameter positive minimum
    computation.replayExact (computation.run oracle).trace =
      .ok (.ok ⟨UniformRefinement.synchronize parents diameter positive minimum, rfl⟩) :=
  ((synchronize parents diameter positive minimum).replayExact_run _).trans
    (congrArg Except.ok (program_value parents diameter positive minimum))

/-- Outside-request changes preserve the whole original synchronization and chronological source trace. -/
theorem payload_erasure {Payload : Type} (parents : List (OwnedCells.Cell safe)) (diameter : Coordinate)
    (positive : 0 < diameter) (minimum : Nat) (payload : Payload)
    (outside : Payload → Question parents diameter positive minimum → Reply parents diameter positive minimum) :
    let computation := synchronize parents diameter positive minimum
    let oracle := answer parents diameter positive minimum
    computation.run (Boundary.Trace.overlay (computation.run oracle).trace (outside payload)) =
      computation.run oracle :=
  Protocol.annotation_erasure (synchronize parents diameter positive minimum)
    (answer parents diameter positive minimum) payload outside

/-- The target refinement with identity to its original parent widths, request and complete cached construction. -/
abbrev RefinementRealization (parentDepth : Nat) (parents : List (OwnedCells.Cell safe))
    (parentWidths : ∀ parent ∈ parents,
      parent.edge.span.width ^ 2 = Basic.quarterRadius 1 parentDepth)
    (target : Coordinate) (positive : 0 < target) :=
  {result : Refined parentDepth parents target //
    result = refine parentDepth parents parentWidths target positive}

/-- Source questions at the exact supplied target resolution and original additional minimum depth. -/
abbrev RefinementQuestion (parentDepth : Nat) (parents : List (OwnedCells.Cell safe))
    {target : Coordinate} (resolution : Accuracy.Resolution data 1 target) :=
  Question parents resolution.rootDiameter resolution.rootDiameterPositive (resolution.minimumDepth - parentDepth)

/-- Original selection and cell receipts at the same retained target resolution. -/
abbrev RefinementReply (parentDepth : Nat) (parents : List (OwnedCells.Cell safe))
    {target : Coordinate} (resolution : Accuracy.Resolution data 1 target) :=
  Reply parents resolution.rootDiameter resolution.rootDiameterPositive (resolution.minimumDepth - parentDepth)

/-- Execute a target-refinement source request using the supplied original resolution instead of recomputing it. -/
def refineAnswer (parentDepth : Nat) (parents : List (OwnedCells.Cell safe))
    {target : Coordinate} (resolution : Accuracy.Resolution data 1 target) :
    RefinementQuestion parentDepth parents resolution → RefinementReply parentDepth parents resolution :=
  answer parents resolution.rootDiameter resolution.rootDiameterPositive (resolution.minimumDepth - parentDepth)

/-- Assemble the original target refinement from its exact returned synchronization and retained resolution identity. -/
private def assembleRefinement (parentDepth : Nat) (parents : List (OwnedCells.Cell safe))
    (parentWidths : ∀ parent ∈ parents,
      parent.edge.span.width ^ 2 = Basic.quarterRadius 1 parentDepth)
    (target : Coordinate) (positive : 0 < target) (resolution : Accuracy.Resolution data 1 target)
    (resolutionEq : resolution = Accuracy.resolve safe 1 (by decide) target positive)
    (cached : Realization parents resolution.rootDiameter resolution.rootDiameterPositive
      (resolution.minimumDepth - parentDepth)) :
    RefinementRealization parentDepth parents parentWidths target positive :=
  ⟨Refined.ofSynchronized parentDepth parents parentWidths target resolution cached.val,
    Refined.ofSynchronized_eq_refine parentDepth parents parentWidths target positive
      resolution resolutionEq cached.val cached.property⟩

/-- Construct the original target refinement with its retained request and displayed selection and cell callbacks. -/
def refineProgram (parentDepth : Nat) (parents : List (OwnedCells.Cell safe))
    (parentWidths : ∀ parent ∈ parents,
      parent.edge.span.width ^ 2 = Basic.quarterRadius 1 parentDepth)
    (target : Coordinate) (positive : 0 < target) (resolution : Accuracy.Resolution data 1 target)
    (resolutionEq : resolution = Accuracy.resolve safe 1 (by decide) target positive) :
    Program (RefinementQuestion parentDepth parents resolution) (RefinementReply parentDepth parents resolution)
      (Except Invalidity (RefinementRealization parentDepth parents parentWidths target positive)) :=
  (program parents resolution.rootDiameter resolution.rootDiameterPositive (resolution.minimumDepth - parentDepth)).map
    (Except.map (assembleRefinement parentDepth parents parentWidths target positive resolution resolutionEq))

/-- Record the original target refinement with every mesh-selection and ordered cell source request. -/
def refine (parentDepth : Nat) (parents : List (OwnedCells.Cell safe))
    (parentWidths : ∀ parent ∈ parents,
      parent.edge.span.width ^ 2 = Basic.quarterRadius 1 parentDepth)
    (target : Coordinate) (positive : 0 < target) (resolution : Accuracy.Resolution data 1 target)
    (resolutionEq : resolution = Accuracy.resolve safe 1 (by decide) target positive) :
    Protocol (RefinementQuestion parentDepth parents resolution) (RefinementReply parentDepth parents resolution)
      (Except Invalidity (RefinementRealization parentDepth parents parentWidths target positive)) :=
  (refineProgram parentDepth parents parentWidths target positive resolution resolutionEq).protocol

/-- A successful refinement realization retains the original complete target-refinement result. -/
private theorem refinementRealization_eq {parentDepth : Nat} {parents : List (OwnedCells.Cell safe)}
    {parentWidths : ∀ parent ∈ parents,
      parent.edge.span.width ^ 2 = Basic.quarterRadius 1 parentDepth}
    {target : Coordinate} {positive : 0 < target}
    (actual : RefinementRealization parentDepth parents parentWidths target positive) :
    actual = ⟨UniformRefinement.refine parentDepth parents parentWidths target positive, rfl⟩ := by
  cases actual with
  | mk result same =>
      cases same
      rfl

/-- Original target-resolution replies retain the same original target refinement and complete executable caches. -/
private theorem refineProgram_value_spec (parentDepth : Nat) (parents : List (OwnedCells.Cell safe))
    (parentWidths : ∀ parent ∈ parents,
      parent.edge.span.width ^ 2 = Basic.quarterRadius 1 parentDepth)
    (target : Coordinate) (positive : 0 < target) (resolution : Accuracy.Resolution data 1 target)
    (resolutionEq : resolution = Accuracy.resolve safe 1 (by decide) target positive) :
    ((refineProgram parentDepth parents parentWidths target positive resolution resolutionEq).protocol.run
      (refineAnswer parentDepth parents resolution)).value =
      .ok ⟨UniformRefinement.refine parentDepth parents parentWidths target positive, rfl⟩ := by
  rewrite [refineProgram, Program.map_execution, Protocol.map_run_value]
  change Except.map (assembleRefinement parentDepth parents parentWidths target positive resolution resolutionEq)
    ((program parents resolution.rootDiameter resolution.rootDiameterPositive
      (resolution.minimumDepth - parentDepth)).protocol.run (answer parents resolution.rootDiameter
        resolution.rootDiameterPositive (resolution.minimumDepth - parentDepth))).value = _
  rewrite [program_value]
  exact congrArg Except.ok (refinementRealization_eq _)

/-- The expandable target construction returns the original refinement with its exact original identity certificate. -/
theorem refineProgram_value (parentDepth : Nat) (parents : List (OwnedCells.Cell safe))
    (parentWidths : ∀ parent ∈ parents,
      parent.edge.span.width ^ 2 = Basic.quarterRadius 1 parentDepth)
    (target : Coordinate) (positive : 0 < target) (resolution : Accuracy.Resolution data 1 target)
    (resolutionEq : resolution = Accuracy.resolve safe 1 (by decide) target positive) :
    ((refineProgram parentDepth parents parentWidths target positive resolution resolutionEq).protocol.run
      (refineAnswer parentDepth parents resolution)).value =
      .ok ⟨UniformRefinement.refine parentDepth parents parentWidths target positive, rfl⟩ :=
  refineProgram_value_spec parentDepth parents parentWidths target positive resolution resolutionEq

/-- Complete target-refinement execution preserves its original result and chronological selection and cell trace. -/
theorem refine_execution (parentDepth : Nat) (parents : List (OwnedCells.Cell safe))
    (parentWidths : ∀ parent ∈ parents,
      parent.edge.span.width ^ 2 = Basic.quarterRadius 1 parentDepth)
    (target : Coordinate) (positive : 0 < target) (resolution : Accuracy.Resolution data 1 target)
    (resolutionEq : resolution = Accuracy.resolve safe 1 (by decide) target positive) :
    let computation := refine parentDepth parents parentWidths target positive resolution resolutionEq
    let oracle := refineAnswer parentDepth parents resolution
    computation.run oracle =
      ⟨.ok ⟨UniformRefinement.refine parentDepth parents parentWidths target positive, rfl⟩,
        (computation.run oracle).trace⟩ :=
  Basic.Execution.ext (refineProgram_value parentDepth parents parentWidths target positive resolution resolutionEq) rfl

/-- Replay of saved target-refinement replies reconstructs the same original caches without any source callback. -/
theorem refine_replay (parentDepth : Nat) (parents : List (OwnedCells.Cell safe))
    (parentWidths : ∀ parent ∈ parents,
      parent.edge.span.width ^ 2 = Basic.quarterRadius 1 parentDepth)
    (target : Coordinate) (positive : 0 < target) (resolution : Accuracy.Resolution data 1 target)
    (resolutionEq : resolution = Accuracy.resolve safe 1 (by decide) target positive) :
    let computation := refine parentDepth parents parentWidths target positive resolution resolutionEq
    let oracle := refineAnswer parentDepth parents resolution
    computation.replayExact (computation.run oracle).trace =
      .ok (.ok ⟨UniformRefinement.refine parentDepth parents parentWidths target positive, rfl⟩) :=
  ((refine parentDepth parents parentWidths target positive resolution resolutionEq).replayExact_run _).trans
    (congrArg Except.ok
      (refineProgram_value parentDepth parents parentWidths target positive resolution resolutionEq))

/-- Changes outside reached target-refinement requests preserve the whole original result and ordered callback log. -/
theorem refine_payload_erasure {Payload : Type} (parentDepth : Nat) (parents : List (OwnedCells.Cell safe))
    (parentWidths : ∀ parent ∈ parents,
      parent.edge.span.width ^ 2 = Basic.quarterRadius 1 parentDepth)
    (target : Coordinate) (positive : 0 < target) (resolution : Accuracy.Resolution data 1 target)
    (resolutionEq : resolution = Accuracy.resolve safe 1 (by decide) target positive) (payload : Payload)
    (outside : Payload → RefinementQuestion parentDepth parents resolution →
      RefinementReply parentDepth parents resolution) :
    let computation := refine parentDepth parents parentWidths target positive resolution resolutionEq
    let oracle := refineAnswer parentDepth parents resolution
    computation.run (Boundary.Trace.overlay (computation.run oracle).trace (outside payload)) =
      computation.run oracle :=
  Protocol.annotation_erasure (refine parentDepth parents parentWidths target positive resolution resolutionEq)
    (refineAnswer parentDepth parents resolution) payload outside

end Observation

end Purelib.Integration.Algebraic.SquareFactor.UniformRefinement
