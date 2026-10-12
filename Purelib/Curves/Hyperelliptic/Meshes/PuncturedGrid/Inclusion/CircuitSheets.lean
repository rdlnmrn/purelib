module
import Purelib.Data.Fin
import Purelib.RootIsolation.SquareRoot.Grid.Walk
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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WindowRootTransport
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedFaceLookup
import Purelib.Tactic.Ring

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank

open Purelib.Polynomial.Geometry.Grid

open Purelib.RootIsolation.SquareRoot.Grid.EdgeBank

public section

/-! The two initial sheets enumerate both arriving sheets at every regular
occurrence of the literal resplit compiler, including after branch excursions. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition

open Purelib.Data

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Curves.Hyperelliptic.Branches.Cuts (Ambient)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank (CircuitPartition)
open Purelib.Polynomial.Geometry.Grid.CellBoundary (sumValues sumValues_append)

section

/-- Two sheets have a positive literal finite bound. -/
local instance : NeZero (2 : Nat) := ⟨by decide +kernel⟩

/-- Two distinct retained sheets account for both original sheet contributions. -/
private theorem two_sheets (value : Fin 2 → Data.Gaussian.Basic.Canonical) (first last : Fin 2) (different : first ≠
  last) :
    value first + value last = value 0 + value 1 := by
  revert different last
  refine Fin.cases_induction ?_ (fun next => ?_) first
  · change ∀ last : Fin 2, (0 : Fin 2) ≠ last → value 0 + value last = value 0 + value 1
    intro last
    refine Fin.cases_induction ?_ (fun next => ?_) last
    · intro different
      exact (different rfl).elim
    · refine Fin.cases_induction ?_ (fun empty => Fin.elim0 empty) next
      intro _
      rfl
  · refine Fin.cases_induction ?_ (fun empty => Fin.elim0 empty) next
    change ∀ last : Fin 2, (1 : Fin 2) ≠ last → value 1 + value last = value 0 + value 1
    intro last
    refine Fin.cases_induction ?_ (fun next => ?_) last
    · intro _
      change value 1 + value 0 = value 0 + value 1
      exact Data.Gaussian.Basic.add_comm _ _
    · refine Fin.cases_induction ?_ (fun empty => Fin.elim0 empty) next
      intro different
      exact (different rfl).elim

end

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

/-- Sum over the actual arriving sheets, without assuming that either initial sheet stays fixed on the stems or the
preceding branch circuits. -/
theorem compileResplit_two_sheets {tree : RowCircuitOrder.CellCircuits bank.grid start}
    (partition : BranchCellBank.CircuitPartition faces tree) (value : Fin faces.regulars.length → Fin 2 →
      Data.Gaussian.Basic.Canonical)
    (first last : Fin 2) (different : first ≠ last) :
    CellBoundary.sumValues (fun occurrence => value occurrence.location.index occurrence.sheet)
        (CircuitPartition.compileResplit included edges vertices reference member partition first).regulars +
      CellBoundary.sumValues (fun occurrence => value occurrence.location.index occurrence.sheet)
        (CircuitPartition.compileResplit included edges vertices reference member partition last).regulars =
      CellBoundary.sumValues (fun occurrence => value occurrence.location.index 0 + value occurrence.location.index 1)
        (CircuitPartition.compileResplit included edges vertices reference member partition first).regulars := by
  induction partition generalizing first last with
  | nil => exact add_zero _
  | @regular cell present stem location =>
      rcases location with ⟨position, face, indexed, equal⟩
      cases equal
      change (value position (RootEdgeBank.target edges (included.resplit stem (face.cell.anchor_mem face.member))
        first) + 0) +
        (value position (RootEdgeBank.target edges (included.resplit stem (face.cell.anchor_mem face.member)) last) + 0)
          =
        (value position 0 + value position 1) + 0
      rw [add_zero, add_zero, add_zero]
      exact two_sheets
        (value position) _ _ (fun equal => different
        (edges.target_injective reference _ equal))
  | hole => exact add_zero _
  | @append firstTree lastTree initial final ihInitial ihFinal =>
      let firstInitial := CircuitPartition.compileResplit included edges vertices reference member initial first
      let lastInitial := CircuitPartition.compileResplit included edges vertices reference member initial last
      let firstFinal := CircuitPartition.compileResplit included edges vertices reference member final
        firstInitial.finish
      let lastFinal := CircuitPartition.compileResplit included edges vertices reference member final lastInitial.finish
      have distinct : firstInitial.finish ≠ lastInitial.finish := by
        intro equal
        exact different (edges.target_injective reference (included.resplit firstTree.product member)
          (firstInitial.target_eq.trans (equal.trans lastInitial.target_eq.symm)))
      change CellBoundary.sumValues _ (firstInitial.regulars ++ firstFinal.regulars) +
        CellBoundary.sumValues _ (lastInitial.regulars ++ lastFinal.regulars) =
        CellBoundary.sumValues _ (firstInitial.regulars ++ firstFinal.regulars)
      rw [CellBoundary.sumValues_append, CellBoundary.sumValues_append, CellBoundary.sumValues_append]
      have initialEq := ihInitial first last different
      have finalEq := ihFinal firstInitial.finish lastInitial.finish distinct
      calc
        _ = (CellBoundary.sumValues (fun occurrence => value occurrence.location.index occurrence.sheet)
          firstInitial.regulars +
            CellBoundary.sumValues (fun occurrence => value occurrence.location.index occurrence.sheet)
              lastInitial.regulars) +
          (CellBoundary.sumValues (fun occurrence => value occurrence.location.index occurrence.sheet)
            firstFinal.regulars +
            CellBoundary.sumValues (fun occurrence => value occurrence.location.index occurrence.sheet)
              lastFinal.regulars) := by ring1
        _ = _ := congrArg₂ (· + ·) initialEq finalEq

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition
