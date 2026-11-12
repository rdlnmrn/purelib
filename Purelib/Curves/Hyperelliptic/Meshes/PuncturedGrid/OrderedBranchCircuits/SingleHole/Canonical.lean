module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.SingleHole
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
public import Purelib.Polynomial.Geometry.Grid.CircuitStemGeometry
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.RowCircuitOrder
import Purelib.Polynomial.Geometry.Grid.FromStates
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Meshes.PuncturedGridFaces

/-! # Canonicalizing a retained singleton hole circuit

The actual partition and label readbacks determine the original selected
cell. Only the existing canonicalization operation changes its connector;
no new root owner, sheet match or period is admitted.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Curves.Hyperelliptic.Branches.BranchIsolation (Data)
open Purelib.Curves.Hyperelliptic.Branches.Cuts (Ambient)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy.Grid (connect)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Geometry.Grid
open Purelib.Polynomial.Geometry.Grid.RowCircuitOrder (CellCircuits)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches : Data curve}
    {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches higher}
    {faces : PuncturedFaces bank} {base : Canonical}

/-- Canonicalization of a genuinely empty kept subtree still has the literal empty walk. -/
private theorem canonicalize_empty (first : FromStates.ContainsVertex bank.grid base) :
    {tree : CellCircuits bank.grid base} → (partition : CircuitPartition faces tree) →
    partition.labels = [] → (partition.kept.canonicalize first).product = Walks.Walk.nil base
  | _, .nil, _ => rfl
  | _, .regular _, _ => rfl
  | _, .hole _, empty => nomatch empty
  | _, .append initial final, empty => by
      cases initialLabels : initial.labels with
      | nil =>
          have finalLabels : final.labels = [] :=
            (congrArg (fun labels => labels ++ final.labels) initialLabels).symm.trans empty
          exact congrArg₂ Walks.Walk.append (canonicalize_empty first initial initialLabels)
            (canonicalize_empty first final finalLabels)
      | cons head tail =>
          have impossible : head :: (tail ++ final.labels) = [] :=
            (congrArg (fun labels => labels ++ final.labels) initialLabels).symm.trans empty
          nomatch impossible

/-- Transport the entire original canonical cell circuit along its actual cell equality. -/
private theorem canonical_cell (first : FromStates.ContainsVertex bank.grid base)
    (cell other : ClearGrid.Cell curve.polynomial (Ambient curve))
    (member : cell ∈ bank.grid.cells) (otherMember : other ∈ bank.grid.cells) (same : cell = other) :
    ((connect bank.grid cell.box.anchor base (cell.anchor_mem member) first).reverse.based
      (CellBoundary.Cell.boundaryWalk cell member)) =
    ((connect bank.grid other.box.anchor base (other.anchor_mem otherMember) first).reverse.based
      (CellBoundary.Cell.boundaryWalk other otherMember)) := by
  cases same
  rfl

/-- The canonicalized singleton kept product is the actual canonical connector around its SAME selected hole.

The original partition is traversed structurally. Actual empty subtrees
remain empty; the hole case transports the complete cell circuit jointly
along its original location and label readbacks.
-/
theorem canonicalize_single (first : FromStates.ContainsVertex bank.grid base) :
    {tree : CellCircuits bank.grid base} → (partition : CircuitPartition faces tree) →
    (index : Data.Index branches) → partition.labels = [index] →
    (partition.kept.canonicalize first).product =
      ((connect bank.grid (bank.cell index).box.anchor base ((bank.cell index).anchor_mem (bank.cell_mem index))
        first).reverse.based (CellBoundary.Cell.boundaryWalk (bank.cell index) (bank.cell_mem index)))
  | _, .nil, _, same => nomatch same
  | _, .regular _, _, same => nomatch same
  | .cell cell member _, .hole location, index, same => by
      have label := (List.cons.inj same).1
      have cells := (location.cell_eq.symm.trans location.hole.cell_eq).trans (congrArg bank.cell label)
      exact canonical_cell first cell (bank.cell index) member (bank.cell_mem index) cells
  | _, .append initial final, index, same => by
      cases initialLabels : initial.labels with
      | nil =>
          have finalLabels : final.labels = [index] :=
            (congrArg (fun labels => labels ++ final.labels) initialLabels).symm.trans same
          exact (congrArg (fun walk => walk.append (final.kept.canonicalize first).product)
            (canonicalize_empty first initial initialLabels)).trans
            (canonicalize_single first final index finalLabels)
      | cons head tail =>
          have expanded : head :: (tail ++ final.labels) = [index] :=
            (congrArg (fun labels => labels ++ final.labels) initialLabels).symm.trans same
          have label := (List.cons.inj expanded).1
          cases tail with
          | nil =>
              have finalLabels : final.labels = [] := (List.cons.inj expanded).2
              have singleton : initial.labels = [index] := initialLabels.trans (congrArg (fun value => [value]) label)
              exact (congrArg (fun walk => (initial.kept.canonicalize first).product.append walk)
                (canonicalize_empty first final finalLabels)).trans
                (((initial.kept.canonicalize first).product.append_nil).trans
                  (canonicalize_single first initial index singleton))
          | cons next rest => nomatch (List.cons.inj expanded).2

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition

end
