module
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Polynomial.Geometry.Grid.RowCircuitOrder
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CircuitAreas
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank

open Purelib.Polynomial.Geometry.Grid

open Purelib.Polynomial.Geometry.Grid.RowCircuitOrder

@[expose] public section

/-! The enlarged-grid compiler preserves the original cell accounting,
including multiplicity, independently of its arriving root sheets. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Curves.Hyperelliptic.Branches.Cuts (Ambient)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid
open _root_.Purelib.Polynomial.Geometry.Grid.ClearGrid (Cell)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank (CircuitPartition)
open Purelib.Polynomial.Geometry.Grid.CellBoundary (sumValues sumValues_append)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {faces : PuncturedFaces bank} {grid :
    Polynomial.Geometry.Grid.ClearGrid curve.polynomial (Ambient
    curve)}
  (included : Purelib.Polynomial.Geometry.Grid.Extension.CoordinateInclusion bank.grid grid)
  {frames : RootIsolation.SquareRoot.Grid.RootFrames grid} (edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames) (vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank grid)
  (reference : ∀ point, Polynomial.Geometry.Grid.FromStates.ContainsVertex grid point →
    Purelib.Riemann.Paths.OwnerLoopMonodromy.WindingOneLoop curve.polynomial point)
  {start : Purelib.Data.Gaussian.Basic.Canonical} (member :
    Polynomial.Geometry.Grid.FromStates.ContainsVertex bank.grid start)

/-- The retained kept circuit cells have exactly the same arbitrary signed contribution sum as their original branch
labels, including multiplicity. -/
theorem kept_cell_sum {tree : RowCircuitOrder.CellCircuits bank.grid start} (partition : BranchCellBank.CircuitPartition
  faces tree)
    (value : ClearGrid.Cell curve.polynomial (Cuts.Ambient curve) → Data.Gaussian.Basic.Canonical) :
    CellBoundary.sumValues value partition.kept.cells = CellBoundary.sumValues (fun index => value (bank.cell index))
      partition.labels := by
  induction partition with
  | nil => rfl
  | regular => rfl
  | hole location =>
      change value _ + 0 = value (bank.cell location.hole.index) + 0
      exact congrArg (fun cell => value cell + 0) (location.cell_eq.symm.trans location.hole.cell_eq)
  | append first last ihFirst ihLast =>
      change CellBoundary.sumValues value (first.kept.cells ++ last.kept.cells) =
        CellBoundary.sumValues (fun index => value (bank.cell index)) (first.labels ++ last.labels)
      rw [CellBoundary.sumValues_append, CellBoundary.sumValues_append, ihFirst, ihLast]

/-- Arbitrary signed cell contributions split into exactly the retained regular occurrences and the original branch-cell
tree. -/
theorem compileResplit_cell_sum {tree : RowCircuitOrder.CellCircuits bank.grid start} (partition :
  BranchCellBank.CircuitPartition faces tree)
    (sheet : Fin 2) (value : ClearGrid.Cell curve.polynomial (Cuts.Ambient curve) → Data.Gaussian.Basic.Canonical) :
    CellBoundary.sumValues (fun occurrence => value occurrence.cell)
        (CircuitPartition.compileResplit included edges vertices reference member partition sheet).regulars +
      CellBoundary.sumValues value partition.kept.cells = CellBoundary.sumValues value tree.cells := by
  induction partition generalizing sheet with
  | nil => exact add_zero _
  | @regular cell present stem location =>
      rcases location with ⟨index, face, indexed, equal⟩
      cases equal
      change (value face.cell + 0) + 0 = value face.cell + 0
      exact add_zero _
  | hole => exact zero_add _
  | append first last ihFirst ihLast =>
      let initial := CircuitPartition.compileResplit included edges vertices reference member first sheet
      let final := CircuitPartition.compileResplit included edges vertices reference member last initial.finish
      change CellBoundary.sumValues _ (initial.regulars ++ final.regulars) +
        CellBoundary.sumValues value (first.kept.cells ++ last.kept.cells) = _
      rw [CellBoundary.sumValues_append, CellBoundary.sumValues_append, CellCircuits.cells,
        CellBoundary.sumValues_append]
      calc
        _ = (CellBoundary.sumValues (fun occurrence => value occurrence.cell) initial.regulars + CellBoundary.sumValues
          value first.kept.cells) +
            (CellBoundary.sumValues (fun occurrence => value occurrence.cell) final.regulars + CellBoundary.sumValues
              value last.kept.cells) := by ring1
        _ = _ := congrArg₂ (· + ·) (ihFirst sheet) (ihLast initial.finish)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition
