module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.List.Append
import Purelib.Data.List.Membership
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.FromStates
import Purelib.Polynomial.Geometry.Grid.RowCircuitOrder
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Meshes.PuncturedFaceLookup
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.RootIsolation.SquareRoot.Grid.Walk
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.Walk.ChainComparison

/-! # The actual connector retained by a single-hole circuit partition

Removing literal empty circuit nodes preserves the complete grid walk.
The extracted connector is the existing hole leaf's connector, transported
only along its original cell/label readbacks. No root or edge is acquired.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Branches.BranchIsolation (Data)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Geometry.Grid
open Purelib.Polynomial.Geometry.Grid.RowCircuitOrder (CellCircuits)
open Purelib.Polynomial.Geometry.Grid.Walks (Walk)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.RootIsolation.SquareRoot.Grid

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches : Data curve}
    {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches higher}
    {faces : PuncturedFaces bank} {base : Canonical}

/-- An empty append has two actually empty original lists. -/
private theorem append_empty {Alpha : Type} (first last : List Alpha) (same : first ++ last = []) :
    first = [] ∧ last = [] := by
  cases first with
  | nil => exact ⟨rfl, same⟩
  | cons head tail => nomatch same

/-- A partition with no hole labels has the literal empty kept walk at its SAME original base.

The proof follows the original finite partition. Nil nodes have an actual
empty walk; regular leaves were already replaced by that same empty walk
by the original compiler. No zero-valued chain is treated as a root path.
-/
theorem empty_product : {tree : CellCircuits bank.grid base} →
    (partition : CircuitPartition faces tree) → partition.labels = [] →
    partition.kept.product = Walk.nil base
  | _, .nil, _ => rfl
  | _, .regular _, _ => rfl
  | _, .hole _, empty => nomatch empty
  | _, .append first last, empty => by
      have parts := append_empty first.labels last.labels empty
      have left := empty_product first parts.1
      have right := empty_product last parts.2
      change first.kept.product.append last.kept.product = _
      exact (congrArg₂ Walk.append left right)

/-- An actually empty kept subtree leaves the SAME retained sheet unchanged. -/
theorem empty_target {tree : CellCircuits bank.grid base}
    (partition : CircuitPartition faces tree) (empty : partition.labels = [])
    {frames : RootFrames bank.grid} (edges : RootEdgeBank frames) (sheet : Fin 2) :
    EdgeBank.RootEdgeBank.target edges partition.kept.product sheet = sheet :=
  congrArg (fun walk => EdgeBank.RootEdgeBank.target edges walk sheet) (partition.empty_product empty)

/-- An actually empty kept subtree has the genuine nil owner trace on its SAME given frame and sheet.

This heterogeneous readback retains both dependent endpoint Owners. It uses
the literal empty-walk factory, independently of a valuation or chain word.
-/
theorem empty_trace {tree : CellCircuits bank.grid base}
    (partition : CircuitPartition faces tree) (empty : partition.labels = [])
    {frames : RootFrames bank.grid} (edges : RootEdgeBank frames)
    (member : FromStates.ContainsVertex bank.grid base) (sheet : Fin 2) :
    HEq (EdgeBank.RootEdgeBank.trace edges partition.kept.product member member sheet)
      (OwnerPath.nil base ((frames.frameAt base member).owners sheet)) := by
  have traced : ∀ (walk : Walk bank.grid base base), walk = .nil base →
      HEq (EdgeBank.RootEdgeBank.trace edges walk member member sheet)
        (OwnerPath.nil base ((frames.frameAt base member).owners sheet)) := by
    intro walk same
    cases same
    rfl
  exact traced partition.kept.product (partition.empty_product empty)

/-- One retained connector and its literal kept-walk factory for an original branch occurrence. -/
@[expose] def SingleHole {tree : CellCircuits bank.grid base}
    (partition : CircuitPartition faces tree) (index : Data.Index branches) : Type _ :=
  {stem : Walk bank.grid base (bank.cell index).box.anchor //
    partition.kept.product = stem.based (CellBoundary.Cell.boundaryWalk (bank.cell index) (bank.cell_mem index))}

/-- Whole cell equality transports the actual connector and its boundary together. -/
private def transportCell (first last : ClearGrid.Cell curve.polynomial (Cuts.Ambient curve))
    (same : first = last) (firstMember : first ∈ bank.grid.cells) (lastMember : last ∈ bank.grid.cells)
    (stem : Walk bank.grid base first.box.anchor) :
    {moved : Walk bank.grid base last.box.anchor //
      stem.based (CellBoundary.Cell.boundaryWalk first firstMember) =
        moved.based (CellBoundary.Cell.boundaryWalk last lastMember)} := by
  cases same
  exact ⟨stem, rfl⟩

/-- Extract the actual hole connector from a proved singleton partition, removing only literal empty nodes.

The executable branch reads the original left label list, then recurses into
that same finite subtree. The retained leaf's cell and branch-label laws
transport its complete connector. Every removed subtree has empty_product,
so its trace is genuinely nil at the same retained frame and sheet.
-/
def singleHole : {tree : CellCircuits bank.grid base} →
    (partition : CircuitPartition faces tree) → (index : Data.Index branches) →
    partition.labels = [index] → partition.SingleHole index
  | _, .nil, _, same => nomatch same
  | _, .regular _, _, same => nomatch same
  | .cell cell member stem, .hole location, index, same => by
      have indexEq := (List.cons.inj same).1
      cases indexEq
      have cellEq : cell = bank.cell location.hole.index :=
        location.cell_eq.symm.trans location.hole.cell_eq
      exact transportCell cell (bank.cell location.hole.index) cellEq member
        (bank.cell_mem location.hole.index) stem
  | _, .append first last, index, same => by
      cases leftLabels : first.labels with
      | nil =>
          have rightLabels : last.labels = [index] :=
            (congrArg (fun values => values ++ last.labels) leftLabels).symm.trans same
          let selected := singleHole last index rightLabels
          have empty := empty_product first leftLabels
          refine ⟨selected.val, ?_⟩
          change first.kept.product.append last.kept.product = _
          exact (congrArg (fun walk => walk.append last.kept.product) empty).trans selected.property
      | cons head tail =>
          have expanded : head :: (tail ++ last.labels) = [index] :=
            (congrArg (fun values => values ++ last.labels) leftLabels).symm.trans same
          have heads := (List.cons.inj expanded).1
          have parts := append_empty tail last.labels (List.cons.inj expanded).2
          have firstLabels : first.labels = [index] :=
            leftLabels.trans (congrArg₂ List.cons heads parts.1)
          let selected := singleHole first index firstLabels
          have empty := empty_product last parts.2
          refine ⟨selected.val, ?_⟩
          change first.kept.product.append last.kept.product = _
          exact (congrArg (fun walk => first.kept.product.append walk) empty).trans
            ((first.kept.product.append_nil).trans selected.property)
termination_by structural _ partition _ _ => partition

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition

end
