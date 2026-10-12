module
import Purelib.Data.List.Search
import Purelib.Data.List.Filter
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CircuitAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Integration.Surface.Sewn.Selection.Basic
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.CellSeparation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.ClearGridCoverage
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
import Purelib.Polynomial.Geometry.Grid.Inclusion.CellParents
public import Purelib.Riemann.Topology.NewtonSewnExcision
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CircuitCells

public section

/-! Complete, disjoint original-cell accounting on the actual Newton cut
surface. Signed areas and both sheet occurrences are preserved exactly. -/

namespace Purelib.Riemann.RootContinuation.NewtonOriginalRegionPartition.NewtonGrid

open Purelib.Data

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Surface.Sewing.PrimitiveSewing (PrimitiveValues)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Integration.Surface.Sewn.Selection.Basic.SewnPrimitiveFaces.CachedSample (FaceSelection)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Polynomial.Geometry.Grid.ClearGrid (Cell)
open Purelib.Polynomial.Geometry.Grid.CellBoundary (sumValues)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.Topology.NewtonSewnExcision.AllHoleExcision (sourceFace)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {preparation : NewtonPreparation base.bank.toBranchCellBank} {target radius : Purelib.Data.Rat.Fraction.Rational}
  {grid : NewtonGrid preparation target radius} {lifted : LiftedPuncturedGrid grid.punctured}
  {localValues : Fin lifted.mesh.triangles.length → Purelib.Topology.Surface.Sewing.PrimitiveSewing.PrimitiveValues 3}

section
open Purelib.Curves
open Purelib.Polynomial
/-- Select a source triangle by refinement of its original face into the specified cell. -/
@[expose] def originalCellMask (lifted : LiftedPuncturedGrid grid.punctured) (cell : Geometry.Grid.ClearGrid.Cell
  curve.polynomial (Hyperelliptic.Branches.Cuts.Ambient curve))
    (source : Fin lifted.mesh.triangles.length) : Bool :=
  decide ((sourceFace lifted source).cell.box.Refines cell.box)

/-- Every retained Newton source triangle belongs to some original grid cell. -/
theorem originalCellMask_complete (lifted : LiftedPuncturedGrid grid.punctured)
    (source : Fin lifted.mesh.triangles.length) :
    base.bank.grid.cells.any (fun cell => originalCellMask lifted cell source) = true := by
  let small := (sourceFace lifted source).cell
  have smallMember := (sourceFace lifted source).member
  have proper : (Hyperelliptic.Branches.Cuts.Ambient curve).Proper :=
    ⟨small.box_refines.1.trans_lt (small.box_proper.1.trans_le small.box_refines.2.1),
      small.box_refines.2.2.1.trans_lt (small.box_proper.2.trans_le small.box_refines.2.2.2)⟩
  let owner := Geometry.Grid.Inclusion.CellParents.parent grid.shrunk.included base.bank.frame proper small smallMember
  apply (Data.List.Search.any_iff _ _).mpr
  exact ⟨owner.cell, owner.member, decide_eq_true owner.refines⟩

end

open Purelib.Polynomial in
/-- Distinct original grid cells select disjoint retained source triangles. -/
theorem originalCellMask_disjoint (lifted : LiftedPuncturedGrid grid.punctured) :
    base.bank.grid.cells.Pairwise (fun first last => ∀ source,
      originalCellMask lifted first source = true → originalCellMask lifted last source = true → False) := by
  apply (Geometry.Grid.ClearGridCoverage.cells_pairwise base.bank.grid).imp
  intro first last separated source left right
  exact Geometry.Grid.Inclusion.CellParents.refinements_disjoint separated (of_decide_eq_true left) (of_decide_eq_true
    right)

section
open Purelib.Curves
open Purelib.Integration
open Purelib.Topology
open Purelib.Polynomial
/-- Sum the supplied complete disjoint cell selections to recover the signed surface area.

The proof consumes the retained masks and cached areas and preserves every source occurrence. -/
private theorem cells_area_partition (surface : Surface.Sewing.SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch
  localValues)
    (cells : List (Geometry.Grid.ClearGrid.Cell curve.polynomial (Hyperelliptic.Branches.Cuts.Ambient curve)))
    (complete : ∀ source, cells.any (fun cell => originalCellMask lifted cell source) = true)
    (disjoint : cells.Pairwise (fun first last => ∀ source,
      originalCellMask lifted first source = true → originalCellMask lifted last source = true → False))
    (selected : (cell : Geometry.Grid.ClearGrid.Cell curve.polynomial (Hyperelliptic.Branches.Cuts.Ambient curve)) →
      Surface.Sewn.Selection.Basic.SewnPrimitiveFaces.CachedSample.FaceSelection surface (originalCellMask lifted cell))
      :
    Geometry.Grid.CellBoundary.sumValues (fun cell => (selected cell).area) cells = surface.boundaryArea := by
  let remaining := Surface.Sewn.Selection.Basic.SewnPrimitiveFaces.CachedSample.FaceSelection.build surface
    (fun source => !(cells.any (fun cell => originalCellMask lifted cell source)))
  have empty : surface.faces.entries.filter
      (fun trace => !(cells.any (fun cell => originalCellMask lifted cell trace.source))) = [] := by
    induction surface.faces.entries with
    | nil => rfl
    | cons trace tail ih =>
        have excluded := congrArg Bool.not (complete trace.source)
        rw [List.Filter.filter_cons_of_neg (by
          intro accepted
          exact Bool.noConfusion (excluded.symm.trans accepted))]
        exact ih
  have zero : remaining.area = 0 := by
    rw [remaining.area_readback, empty]
    rfl
  have partition := Surface.Sewn.Selection.Basic.SewnPrimitiveFaces.CachedSample.FaceSelection.family_partition cells
    (originalCellMask lifted)
    disjoint selected remaining
  rw [zero, add_zero] at partition
  exact partition

/-- The original grid-cell selections partition the full cached surface boundary area. -/
theorem original_cells_area_partition (surface : Surface.Sewing.SewnPrimitiveSamples.CachedSample
  lifted.cutPolygon.patch localValues)
    (selected : (cell : Geometry.Grid.ClearGrid.Cell curve.polynomial (Hyperelliptic.Branches.Cuts.Ambient curve)) →
      Surface.Sewn.Selection.Basic.SewnPrimitiveFaces.CachedSample.FaceSelection surface (originalCellMask lifted cell))
      :
    Geometry.Grid.CellBoundary.sumValues (fun cell => (selected cell).area) base.bank.grid.cells = surface.boundaryArea
      :=
  cells_area_partition surface base.bank.grid.cells (originalCellMask_complete lifted) (originalCellMask_disjoint
    lifted) selected

/-- The original regular and branch regions partition the full signed surface area.

The original cached classification accounts for every source triangle with no remaining-region term. -/
theorem original_regions_area_partition (surface : Surface.Sewing.SewnPrimitiveSamples.CachedSample
  lifted.cutPolygon.patch localValues)
    (selected : (cell : Geometry.Grid.ClearGrid.Cell curve.polynomial (Hyperelliptic.Branches.Cuts.Ambient curve)) →
      Surface.Sewn.Selection.Basic.SewnPrimitiveFaces.CachedSample.FaceSelection surface (originalCellMask lifted cell))
      :
    Geometry.Grid.CellBoundary.sumValues (fun face => (selected face.cell).area) base.faces.regulars +
      Geometry.Grid.CellBoundary.sumValues (fun hole => (selected hole.cell).area) base.faces.holes =
        surface.boundaryArea := by
  rw [base.faces.regulars_eq, base.faces.holes_eq, base.faces.split.sum_eq (fun cell => (selected cell).area)]
  exact original_cells_area_partition surface selected

end

end Purelib.Riemann.RootContinuation.NewtonOriginalRegionPartition.NewtonGrid

namespace Purelib.Riemann.RootContinuation.NewtonOriginalRegionPartition.Ordered

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonOriginalRegionPartition.NewtonGrid (originalCellMask)
open Purelib.Topology.Surface.Sewing.PrimitiveSewing (PrimitiveValues)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Integration.Surface.Sewn.Selection.Basic.SewnPrimitiveFaces.CachedSample (FaceSelection)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Polynomial.Geometry.Grid.ClearGrid (Cell)
open Purelib.Polynomial.Geometry.Grid.CellBoundary (sumValues)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank (Ordered)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank (CircuitPartition)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {originalLifted : LiftedPuncturedGrid base} {bank :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank
    originalLifted} {sheet : Fin 2}
  {preparation : NewtonPreparation base.bank.toBranchCellBank} {target radius : Purelib.Data.Rat.Fraction.Rational}
  {grid : NewtonGrid preparation target radius} {current : LiftedPuncturedGrid grid.punctured}
  {localValues : Fin current.mesh.triangles.length → Purelib.Topology.Surface.Sewing.PrimitiveSewing.PrimitiveValues 3}

open Purelib.Curves in
open Purelib.Integration in
open Purelib.Topology in
open Purelib.Polynomial in
/-- Recover the signed cut area from the compiler's regular occurrences and original ordered branch labels.

The identity retains the original period ordering, actual compiled occurrences and supplied face-selection caches. -/
theorem original_regions_area_partition (ordered :
  Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank sheet) (newSheet
  : Fin 2)
    (surface : Surface.Sewing.SewnPrimitiveSamples.CachedSample current.cutPolygon.patch localValues)
    (selected : (cell : Geometry.Grid.ClearGrid.Cell curve.polynomial (Hyperelliptic.Branches.Cuts.Ambient curve)) →
      Surface.Sewn.Selection.Basic.SewnPrimitiveFaces.CachedSample.FaceSelection surface (originalCellMask current
      cell)) :
    let reference := fun point member => (Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy.BranchCellBank.referenceAt
      grid.punctured.bank.toBranchCellBank point member).toLoop
    let compiled :=
      Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.compileResplit
      grid.shrunk.included current.edges current.vertices
      reference (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank)
        ordered.prepared.partition newSheet
    Geometry.Grid.CellBoundary.sumValues (fun occurrence => (selected occurrence.cell).area) compiled.regulars +
      Geometry.Grid.CellBoundary.sumValues (fun index => (selected (base.bank.cell index)).area) ordered.prepared.labels
        = surface.boundaryArea := by
  intro reference compiled
  have members (cell : Geometry.Grid.ClearGrid.Cell curve.polynomial (Hyperelliptic.Branches.Cuts.Ambient curve)) :
      cell ∈ ordered.prepared.ordered.tree.cells ↔ cell ∈ base.bank.grid.cells := by
    rewrite [ordered.prepared.ordered.tree_eq]
    exact ordered.window.circuits_member.trans ⟨And.left, fun present => ⟨present, cell.box_refines⟩⟩
  have unique : ordered.prepared.ordered.tree.cells.Nodup := by
    rw [ordered.prepared.ordered.tree_eq]
    exact ordered.window.circuits_unique
  have complete (source : Fin current.mesh.triangles.length) :
      ordered.prepared.ordered.tree.cells.any (fun cell => originalCellMask current cell source) = true := by
    obtain ⟨cell, present, kept⟩ := (Data.List.Search.any_iff _ _).mp (NewtonGrid.originalCellMask_complete current
      source)
    exact (Data.List.Search.any_iff _ _).mpr ⟨cell, (members cell).mpr present, kept⟩
  have disjoint : ordered.prepared.ordered.tree.cells.Pairwise (fun first last => ∀ source,
      originalCellMask current first source = true → originalCellMask current last source = true → False) := by
    apply unique.imp_of_mem
    intro first last firstMember lastMember different source left right
    exact Geometry.Grid.Inclusion.CellParents.refinements_disjoint
      (Geometry.Grid.CellSeparation.cells_interiorSeparated base.bank.grid ((members first).mp firstMember) ((members
        last).mp lastMember) different)
      (of_decide_eq_true left) (of_decide_eq_true right)
  have total := NewtonGrid.cells_area_partition surface ordered.prepared.ordered.tree.cells complete disjoint selected
  have split :=
    Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.compileResplit_cell_sum
    grid.shrunk.included current.edges current.vertices
    reference (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank)
      ordered.prepared.partition newSheet (fun cell => (selected cell).area)
  rw [Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.kept_cell_sum] at split
  have labels := congrArg (Geometry.Grid.CellBoundary.sumValues (fun index => (selected (base.bank.cell index)).area))
    ordered.prepared.labels_eq
  exact (congrArg (fun area => Geometry.Grid.CellBoundary.sumValues (fun occurrence => (selected occurrence.cell).area)
    compiled.regulars + area) labels).trans
    (split.trans total)

end Purelib.Riemann.RootContinuation.NewtonOriginalRegionPartition.Ordered
