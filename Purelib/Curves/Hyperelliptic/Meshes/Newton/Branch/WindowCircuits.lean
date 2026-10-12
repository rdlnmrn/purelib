module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CircuitAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Topology.Mesh.RetracingWords
import Purelib.Topology.Polygon.Stokes
public import Purelib.Riemann.RootContinuation.NewtonOriginalAnnularFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Purelib.RootIsolation.SquareRoot.Grid.Inclusion.CellPolygon
import Purelib.RootIsolation.SquareRoot.Grid.Subdivision.Self
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CircuitCells
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.FromStates
import Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.Walk.ChainComparison

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Polynomial

open Purelib.Riemann

open Purelib

public section

/-! The original branch-cell window retains precisely its own shrunken
hole circuit. Its polygon remains explicit in the fine compiler identity. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Branch.WindowCircuits

open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank
  (NewtonPreparation NewtonGrid)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation original} {target radius :
    Fraction.Rational}
  {grid : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid preparation target radius} {index :
    Hyperelliptic.Branches.BranchIsolation.Data.Index branches}
  {current : Meshes.LiftedPuncturedGrid grid.punctured}

/-- Prepare the retained hole ordering inside the original branch-cell window on the chosen sheet. -/
@[expose] def fineOrder (region : RootContinuation.NewtonOriginalAnnularFaces.OriginalAnnularFaces grid index) (sheet :
  Fin 2) :=
  Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.Window.prepareBranches
    grid.faces region.window current.edges current.vertices sheet

/-- Compile the original window partition into its retained resplit boundary word and complete area terms. -/
@[expose] def fineCompiler (region : RootContinuation.NewtonOriginalAnnularFaces.OriginalAnnularFaces grid index) (sheet
  : Fin 2) :
    Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.ResplitCompiled
      (Geometry.Grid.Extension.CoordinateInclusion.refl grid.punctured.bank.grid) current.edges current.vertices
      (grid.shrunk.included.vertex (Geometry.Grid.ClearGrid.Cell.anchor_mem (original.cell index) (original.cell_mem
        index)))
      (Hyperelliptic.Meshes.Newton.Branch.WindowCircuits.fineOrder (current := current) region sheet).partition sheet :=
  Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.compileResplit _
    current.edges current.vertices
    (fun point member => (Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy.BranchCellBank.referenceAt
      grid.punctured.bank.toBranchCellBank point member).toLoop) _
    (Hyperelliptic.Meshes.Newton.Branch.WindowCircuits.fineOrder (current := current) region sheet).partition sheet

/-- A duplicate-free list containing one designated element and no other value is exactly its singleton. -/
private theorem singleton_of_unique {Item : Type} (entries : List Item) (index : Item)
    (unique : entries.Nodup) (present : index ∈ entries)
    (only : ∀ entry ∈ entries, entry = index) : entries = [index] := by
  cases entries with
  | nil => exact (List.not_mem_nil present).elim
  | cons head tail =>
      have headEq := only head List.mem_cons_self
      have empty : tail = [] := by
        cases tail with
        | nil => rfl
        | cons next rest =>
            have nextEq := only next (List.mem_cons_of_mem _ List.mem_cons_self)
            exact ((List.pairwise_cons.mp unique).1 next List.mem_cons_self (headEq.trans nextEq.symm)).elim
      rw [headEq, empty]

/-- There is exactly one retained hole label. This is about the compiler
partition, including its multiplicity, rather than just geometric membership. -/
theorem fine_kept_labels (region : RootContinuation.NewtonOriginalAnnularFaces.OriginalAnnularFaces grid index) (sheet :
  Fin 2) :
    (Hyperelliptic.Meshes.Newton.Branch.WindowCircuits.fineOrder (current := current) region sheet).partition.labels =
      [index] := open Purelib.Geometry in by
  let order := Hyperelliptic.Meshes.Newton.Branch.WindowCircuits.fineOrder (current := current) region sheet
  have present : index ∈ order.labels := order.selected index |>.mpr
      (Geometry.Rational.Box.Refinement.StrictInterior.refines
    (grid.shrunk.cell_strict index))
  have only : ∀ entry ∈ order.labels, entry = index := by
    intro entry member
    have inside := (order.selected entry).mp member
    have retained := (Geometry.Rational.Box.Refinement.StrictInterior.refines (grid.shrunk.cell_strict entry))
    by_cases same : entry = index
    · exact same
    · exact ((original.cells_separated entry index same).points_ne
        (retained.contains (grid.punctured.bank.cell entry).box.contains_anchor)
        (inside.contains (grid.punctured.bank.cell entry).box.contains_anchor) rfl).elim
  exact order.labels_eq.symm.trans (Hyperelliptic.Meshes.Newton.Branch.WindowCircuits.singleton_of_unique order.labels
    index order.unique present only)

/-- The hole polygon and every connector and regular polygon are retained
in the comparison with the literal resplit original branch-cell boundary. -/
theorem fineCompiler_area (region : RootContinuation.NewtonOriginalAnnularFaces.OriginalAnnularFaces grid index) (sheet
  : Fin 2)
    (value : Topology.Polygon.Stokes.OrientedEdge current.vertices.count → Gaussian.Basic.Canonical)
    (anti : ∀ edge, value edge.reverse = -value edge) :
    current.edges.chainArea current.vertices value
      (grid.shrunk.included.resplit (Geometry.Grid.CellBoundary.Cell.boundaryWalk (original.cell index)
        (original.cell_mem index))
        (Geometry.Grid.ClearGrid.Cell.anchor_mem (original.cell index) (original.cell_mem index))) sheet =
      Topology.Mesh.RetracingWords.wordArea value (Hyperelliptic.Meshes.Newton.Branch.WindowCircuits.fineCompiler
        (current := current) region sheet).word +
        Topology.Mesh.RetracingWords.AreaTerm.total value
          (Hyperelliptic.Meshes.Newton.Branch.WindowCircuits.fineCompiler (current := current) region sheet).areaTerms
          := by
  let order := Hyperelliptic.Meshes.Newton.Branch.WindowCircuits.fineOrder (current := current) region sheet
  let compiled := Hyperelliptic.Meshes.Newton.Branch.WindowCircuits.fineCompiler (current := current) region sheet
  let reference := fun point member => (Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy.BranchCellBank.referenceAt
    grid.punctured.bank.toBranchCellBank point member).toLoop
  have boundary := grid.shrunk.included.cell_boundary_comparison (original.cell index) (original.cell_mem index)
    region.window current.edges current.vertices reference
  have ordered := order.ordered.comparison.areas value anti sheet
  rw [order.ordered.product_eq] at ordered
  have self := Polynomial.Geometry.Grid.ClearGrid.self_resplit_comparison current.edges current.vertices reference
    order.ordered.tree.product
    (grid.shrunk.included.vertex (Geometry.Grid.ClearGrid.Cell.anchor_mem (original.cell index) (original.cell_mem
      index)))
  exact (boundary.areas value anti sheet).trans
    (ordered.symm.trans ((self.areas value anti sheet).symm.trans (compiled.areas value anti)))

end Purelib.Curves.Hyperelliptic.Meshes.Newton.Branch.WindowCircuits
