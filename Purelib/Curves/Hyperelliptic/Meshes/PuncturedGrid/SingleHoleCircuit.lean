module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.RowCircuitOrder
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.Walk.ChainComparison
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Init.Core
import Init.Data.List.Basic
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.PuncturedFaceLookup

open Purelib

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits

open Purelib.Polynomial.Geometry.Grid

open Purelib.Polynomial.Geometry.Grid.Walks

open Purelib.Riemann.Meshes

@[expose] public section

/-! A partition with one retained label supplies its actual hole and stem,
with an exact readback of the kept product. No replacement stem is chosen. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SingleHoleCircuit

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces BranchHole)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank (CircuitPartition)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve branches
    higher}
  {faces : Purelib.Riemann.Meshes.PuncturedGridFaces.PuncturedFaces bank} {start :
    Purelib.Data.Gaussian.Basic.Canonical}

/-- If a finite-list concatenation is empty, both original lists are empty. -/
public theorem append_empty {Item : Type} (first last : List Item) (empty : first ++ last = []) :
    first = [] ∧ last = [] := by
  cases first with
  | nil => exact ⟨rfl, empty⟩
  | cons head tail => cases empty

/-- A partition with no retained branch labels has the empty retained branch walk. -/
public theorem kept_nil_of_labels_nil {tree : RowCircuitOrder.CellCircuits bank.grid start}
    (partition : BranchCellBank.CircuitPartition faces tree) (empty : partition.labels = []) :
    partition.kept.product = Walk.nil start := by
  induction partition with
  | nil => rfl
  | regular => rfl
  | hole location =>
      change [location.hole.index] = [] at empty
      cases empty
  | append first last ihFirst ihLast =>
      have parts := Curves.Hyperelliptic.Meshes.PuncturedGrid.SingleHoleCircuit.append_empty first.labels last.labels
        empty
      change first.kept.product.append last.kept.product = _
      rw [ihFirst parts.1, ihLast parts.2]
      rfl

set_option genInjectivity false in
/-- The original hole and connector retained by a circuit partition with one specified branch label.

The exact product equality identifies the retained branch walk with that original connector's based hole boundary. -/
structure SingleHole {tree : RowCircuitOrder.CellCircuits bank.grid start}
    (partition : BranchCellBank.CircuitPartition faces tree) (index : BranchIsolation.Data.Index branches) where
  /-- The original branch-hole payload retained in the unique hole leaf. -/ hole : PuncturedGridFaces.BranchHole bank
  /-- The retained original hole has exactly the specified branch index. -/ hole_index : hole.index = index
  /-- The original connector from the circuit base to the retained hole anchor. -/ stem : Walks.Walk bank.grid start
    hole.cell.box.anchor
  /-- The retained partition product is exactly this original connector's based hole boundary. -/ product_eq :
    partition.kept.product = stem.based
    (CellBoundary.Cell.boundaryWalk hole.cell hole.member)

constructive_injectivity SingleHole

/-- Read the sole retained hole from the literal partition. The connector and hole payload are those already present in
its unique hole leaf. -/
def singleHole (index : BranchIsolation.Data.Index branches) :
    {tree : RowCircuitOrder.CellCircuits bank.grid start} → (partition : BranchCellBank.CircuitPartition faces tree) →
      partition.labels = [index] → Curves.Hyperelliptic.Meshes.PuncturedGrid.SingleHoleCircuit.SingleHole partition
        index
  | _, .nil, equal => by
      change [] = [index] at equal
      cases equal
  | _, .regular _, equal => by
      change [] = [index] at equal
      cases equal
  | _, .hole location, equal => by
      rcases location with ⟨position, hole, indexed, cellEq⟩
      cases cellEq
      exact ⟨hole, (List.cons.inj equal).1, _, rfl⟩
  | _, .append first last, equal => by
      cases firstEq : first.labels with
      | nil =>
          have lastEq : last.labels = [index] := by
            change first.labels ++ last.labels = [index] at equal
            rw [firstEq, List.nil_append] at equal
            exact equal
          let found := Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SingleHoleCircuit.singleHole index last lastEq
          refine ⟨found.hole, found.hole_index, found.stem, ?_⟩
          change first.kept.product.append last.kept.product = _
          rw [Curves.Hyperelliptic.Meshes.PuncturedGrid.SingleHoleCircuit.kept_nil_of_labels_nil first firstEq]
          exact found.product_eq
      | cons head tail =>
          have parts : head = index ∧ tail ++ last.labels = [] := by
            change first.labels ++ last.labels = [index] at equal
            rw [firstEq, List.cons_append] at equal
            exact List.cons.inj equal
          have empty := Curves.Hyperelliptic.Meshes.PuncturedGrid.SingleHoleCircuit.append_empty tail last.labels
            parts.2
          have firstOnly : first.labels = [index] := by rw [firstEq, parts.1, empty.1]
          let found := Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SingleHoleCircuit.singleHole index first
            firstOnly
          refine ⟨found.hole, found.hole_index, found.stem, ?_⟩
          change first.kept.product.append last.kept.product = _
          rw [Curves.Hyperelliptic.Meshes.PuncturedGrid.SingleHoleCircuit.kept_nil_of_labels_nil last empty.2,
            Walk.append_nil]
          exact found.product_eq
termination_by structural _ partition => partition

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SingleHoleCircuit
