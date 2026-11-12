module
import Purelib.Data.List.Search
import Purelib.Data.List.Filter
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CircuitAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CircuitCells
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Integration.Surface.Sewn.Selection.Basic
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.CellSeparation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Inclusion.CellParents
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
public import Purelib.Riemann.RootContinuation.NewtonOriginalRegionPartition
import Purelib.Integration.Surface.Sewn.Selection.Paired

public section

/-! The retained original-cell selections partition arbitrary paired values
on the same cut surface and the same ordered compiler. -/
namespace Purelib.Riemann.RootContinuation.NewtonOriginalPairedPartition

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
open Purelib.Riemann.RootContinuation.NewtonOriginalRegionPartition.NewtonGrid (originalCellMask)

open Purelib.Topology.Polygon.Stokes (OrientedTriangle PrimitivePoint edgeListArea)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {preparation : NewtonPreparation base.bank.toBranchCellBank} {target radius : Data.Rat.Fraction.Rational}
  {grid : NewtonGrid preparation target radius} {lifted : LiftedPuncturedGrid grid.punctured}
  {localValues : Fin lifted.mesh.triangles.length → PrimitiveValues 3}

open Purelib.Curves in
open Purelib.Integration in
open Purelib.Topology in
open Purelib.Polynomial in
/-- Complete disjoint original-cell selections account for the entire paired cut-boundary area.

Each selected triangle list comes from the supplied cached surface, and completeness makes the remaining face selection
empty. -/
private theorem paired_cells_area_partition (surface : CachedSample
  lifted.cutPolygon.patch localValues)
    (cells : List (Cell curve.polynomial (Hyperelliptic.Branches.Cuts.Ambient curve)))
    (complete : ∀ source, cells.any (fun cell => originalCellMask lifted cell source) = true)
    (disjoint : cells.Pairwise (fun first last => ∀ source,
      originalCellMask lifted first source = true → originalCellMask lifted last source = true → False))
    (primitive : Fin lifted.cutPolygon.patch.cut.count → PrimitivePoint)
    (selected : (cell : Cell curve.polynomial (Hyperelliptic.Branches.Cuts.Ambient curve)) →
      FaceSelection surface (originalCellMask lifted cell))
      :
    sumValues (fun cell => edgeListArea primitive ((selected cell).triangles.flatMap
      OrientedTriangle.boundary)) cells = edgeListArea primitive lifted.cutPolygon.patch.cut.boundary := by
  let remaining := FaceSelection.build surface
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
  have zero : edgeListArea primitive (remaining.triangles.flatMap OrientedTriangle.boundary) = 0 := by
    rw [Surface.Sewn.Selection.Paired.paired_area_readback remaining primitive, empty]
    rfl
  have partition := Surface.Sewn.Selection.Paired.paired_family_partition cells (originalCellMask lifted)
    disjoint selected remaining primitive
  rw [zero, add_zero] at partition
  exact partition

end Purelib.Riemann.RootContinuation.NewtonOriginalPairedPartition

namespace Purelib.Riemann.RootContinuation.NewtonOriginalPairedPartition.Ordered

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

open Purelib.Topology.Polygon.Stokes (OrientedTriangle PrimitivePoint edgeListArea)
variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {originalLifted : LiftedPuncturedGrid base} {bank :
    BasedBranchBank
    originalLifted} {sheet : Fin 2}
  {preparation : NewtonPreparation base.bank.toBranchCellBank} {target radius : Data.Rat.Fraction.Rational}
  {grid : NewtonGrid preparation target radius} {current : LiftedPuncturedGrid grid.punctured}
  {localValues : Fin current.mesh.triangles.length → PrimitiveValues 3}

open Purelib.Riemann in
open Purelib.Curves in
open Purelib.Integration in
open Purelib.Topology in
open Purelib.Polynomial in
/-- Partition the signed cut area by the original ordered compiler's actual cell occurrences.

The regular occurrence list and ordered branch labels retain their literal selections on the same cut surface;
completeness and disjointness follow from the original cell partition. -/
theorem original_paired_regions_area_partition (ordered :
  Ordered bank sheet) (newSheet
  : Fin 2)
    (surface : CachedSample current.cutPolygon.patch localValues)
    (primitive : Fin current.cutPolygon.patch.cut.count → PrimitivePoint)
    (selected : (cell : Cell curve.polynomial (Hyperelliptic.Branches.Cuts.Ambient curve)) →
      FaceSelection surface (originalCellMask current
      cell)) :
    let reference := fun point member => (Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy.BranchCellBank.referenceAt
      grid.punctured.bank.toBranchCellBank point member).toLoop
    let compiled :=
      CircuitPartition.compileResplit
      grid.shrunk.included current.edges current.vertices
      reference (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank)
        ordered.prepared.partition newSheet
    sumValues (fun occurrence => edgeListArea primitive ((selected
      occurrence.cell).triangles.flatMap OrientedTriangle.boundary)) compiled.regulars +
      sumValues (fun index => edgeListArea primitive ((selected (base.bank.cell
        index)).triangles.flatMap OrientedTriangle.boundary)) ordered.prepared.labels = edgeListArea primitive
        current.cutPolygon.patch.cut.boundary := by
  intro reference compiled
  have members (cell : Cell curve.polynomial (Hyperelliptic.Branches.Cuts.Ambient curve)) :
      cell ∈ ordered.prepared.ordered.tree.cells ↔ cell ∈ base.bank.grid.cells := by
    rewrite [ordered.prepared.ordered.tree_eq]
    exact ordered.window.circuits_member.trans ⟨And.left, fun present => ⟨present, cell.box_refines⟩⟩
  have unique : ordered.prepared.ordered.tree.cells.Nodup := by
    rw [ordered.prepared.ordered.tree_eq]
    exact ordered.window.circuits_unique
  have complete (source : Fin current.mesh.triangles.length) :
      ordered.prepared.ordered.tree.cells.any (fun cell => originalCellMask current cell source) = true := by
    obtain ⟨cell, present, kept⟩ := (Data.List.Search.any_iff _ _).mp
      (NewtonOriginalRegionPartition.NewtonGrid.originalCellMask_complete current source)
    exact (Data.List.Search.any_iff _ _).mpr ⟨cell, (members cell).mpr present, kept⟩
  have disjoint : ordered.prepared.ordered.tree.cells.Pairwise (fun first last => ∀ source,
      originalCellMask current first source = true → originalCellMask current last source = true → False) := by
    apply unique.imp_of_mem
    intro first last firstMember lastMember different source left right
    exact Geometry.Grid.Inclusion.CellParents.refinements_disjoint
      (Geometry.Grid.CellSeparation.cells_interiorSeparated base.bank.grid ((members first).mp firstMember) ((members
        last).mp lastMember) different)
      (of_decide_eq_true left) (of_decide_eq_true right)
  have total := paired_cells_area_partition surface
    ordered.prepared.ordered.tree.cells complete disjoint primitive selected
  have split :=
    CircuitPartition.compileResplit_cell_sum
    grid.shrunk.included current.edges current.vertices
    reference (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank)
      ordered.prepared.partition newSheet (fun cell => edgeListArea primitive ((selected cell).triangles.flatMap
      OrientedTriangle.boundary))
  rw [CircuitPartition.kept_cell_sum] at split
  have labels := congrArg (sumValues (fun index => edgeListArea primitive ((selected
    (base.bank.cell index)).triangles.flatMap OrientedTriangle.boundary))) ordered.prepared.labels_eq
  exact (congrArg (fun area => sumValues (fun occurrence => edgeListArea primitive ((selected
    occurrence.cell).triangles.flatMap OrientedTriangle.boundary)) compiled.regulars + area) labels).trans
    (split.trans total)

end Purelib.Riemann.RootContinuation.NewtonOriginalPairedPartition.Ordered
