module

public import Purelib.Integration.Algebraic.SquareFactor.UniformRefinement
public import Purelib.Integration.Algebraic.SquareFactor.OwnedCells.Compilation

/-!
# Original mesh-bank compilation from recorded cell caches

The retained mesh bank supplies its original prepared leaf edges in parent
order. Their cell construction records every root and coefficient request.
Assembly splits the actual returned cache at the original mesh boundaries
and retains each original parent, mesh and block without requesting models
again. Its identity law preserves the original parallel compiler's result.
-/

public section

namespace Purelib.Integration.Algebraic.SquareFactor.UniformRefinement.MeshBank

open Purelib
open Purelib.Curves.Hyperelliptic.Differentials
open Purelib.Computation.Query

namespace Compilation

variable {polynomial : SquareFactor.GaussianPolynomial} {request : SquareFactor.Request}
  {prepared : SquareFactor.Prepared polynomial request} {segment : PathInput.Segment}
  {data : PathInput.Data prepared segment} {safe : data.Safe}
  {diameter : Coordinate} {depth : Nat}

/-- The actual original mesh-bank expansion with identity to its original compiler and complete parent list. -/
abbrev Realization {parents : List (OwnedCells.Cell safe)} (bank : MeshBank diameter depth parents) :=
  {expansion : Expansion diameter depth parents // expansion = bank.compile}

/-- Assemble the same original child blocks from the actual returned ordered cell cache.

Each split consumes the original first mesh's edge count and the retained
remaining cache. The original mesh and parent indices survive in the named
block constructor, and all root, coefficient and comparison data are reused.
-/
def ofCells : {parents : List (OwnedCells.Cell safe)} → (bank : MeshBank diameter depth parents) →
    OwnedCells.Compilation.Realization bank.edges → Realization bank
  | _, .nil, _ => ⟨.nil, rfl⟩
  | _, .cons head tail, cached =>
      let parts := OwnedCells.Compilation.Realization.split cached
      let headEq := parts.1.property.trans head.compileEdges_edges
      let block := ChildMeshes.Block.ofCells head parts.1.val headEq
      let remaining := ofCells tail parts.2
      have same : Expansion.cons block remaining.val = (MeshBank.cons head tail).compile :=
        (congrArg₂ Expansion.cons (ChildMeshes.Block.ofCells_eq_compile head parts.1.val headEq)
          (remaining.property.trans tail.compile_eq_sequential)).trans
            (MeshBank.compile_eq_sequential (MeshBank.cons head tail)).symm
      ⟨.cons block remaining.val, same⟩

/-- Construct the original mesh-bank expansion with every ordered root and polynomial cell reading displayed. -/
def program {parents : List (OwnedCells.Cell safe)} (bank : MeshBank diameter depth parents) :
    Program (OwnedCells.Compilation.Question bank.edges) (OwnedCells.Compilation.Reply bank.edges)
      (Except OwnedCells.Compilation.Invalidity (Realization bank)) :=
  (OwnedCells.Compilation.program bank.edges).map (Except.map (ofCells bank))

/-- Record the original retained mesh bank's cell construction and complete expansion result. -/
def compile {parents : List (OwnedCells.Cell safe)} (bank : MeshBank diameter depth parents) :
    Protocol (OwnedCells.Compilation.Question bank.edges) (OwnedCells.Compilation.Reply bank.edges)
      (Except OwnedCells.Compilation.Invalidity (Realization bank)) := (program bank).protocol

/-- The original source reads the actual retained mesh bank's edge list at each displayed cell position. -/
def answer {parents : List (OwnedCells.Cell safe)} (bank : MeshBank diameter depth parents) :
    OwnedCells.Compilation.Question bank.edges → OwnedCells.Compilation.Reply bank.edges :=
  OwnedCells.Compilation.answer

/-- A successful realization retains exactly the original complete compiled expansion. -/
private theorem realization_eq {parents : List (OwnedCells.Cell safe)} {bank : MeshBank diameter depth parents}
    (actual : Realization bank) : actual = ⟨bank.compile, rfl⟩ := by
  cases actual with
  | mk expansion same =>
      cases same
      rfl

/-- The original displayed cell replies preserve the same original complete compiled mesh-bank expansion. -/
private theorem program_value_spec {parents : List (OwnedCells.Cell safe)} (bank : MeshBank diameter depth parents) :
    ((program bank).protocol.run (answer bank)).value = .ok ⟨bank.compile, rfl⟩ := by
  rewrite [program, Program.map_execution, Protocol.map_run_value]
  change Except.map (ofCells bank)
    ((OwnedCells.Compilation.program bank.edges).protocol.run OwnedCells.Compilation.answer).value = _
  rewrite [OwnedCells.Compilation.program_value]
  exact congrArg Except.ok (realization_eq _)

/-- The expandable bank construction returns the original compiled expansion with its exact defining identity. -/
theorem program_value {parents : List (OwnedCells.Cell safe)} (bank : MeshBank diameter depth parents) :
    ((program bank).protocol.run (answer bank)).value = .ok ⟨bank.compile, rfl⟩ := program_value_spec bank

/-- Whole bank compilation preserves the original expansion and each reached cell callback in parent order. -/
theorem compile_execution {parents : List (OwnedCells.Cell safe)} (bank : MeshBank diameter depth parents) :
    (compile bank).run (answer bank) = ⟨.ok ⟨bank.compile, rfl⟩, ((compile bank).run (answer bank)).trace⟩ :=
  Basic.Execution.ext (program_value bank) rfl

/-- Replay consumes the same saved cell caches and reconstructs the original bank without source callbacks. -/
theorem compile_replay {parents : List (OwnedCells.Cell safe)} (bank : MeshBank diameter depth parents) :
    (compile bank).replayExact ((compile bank).run (answer bank)).trace = .ok (.ok ⟨bank.compile, rfl⟩) :=
  ((compile bank).replayExact_run _).trans (congrArg Except.ok (program_value bank))

/-- Changes outside reached bank requests preserve the whole original expansion and ordered source trace. -/
theorem payload_erasure {Payload : Type} {parents : List (OwnedCells.Cell safe)}
    (bank : MeshBank diameter depth parents) (payload : Payload)
    (outside : Payload → OwnedCells.Compilation.Question bank.edges → OwnedCells.Compilation.Reply bank.edges) :
    (compile bank).run (Boundary.Trace.overlay ((compile bank).run (answer bank)).trace (outside payload)) =
      (compile bank).run (answer bank) :=
  Protocol.annotation_erasure (compile bank) (answer bank) payload outside

end Compilation

end Purelib.Integration.Algebraic.SquareFactor.UniformRefinement.MeshBank
