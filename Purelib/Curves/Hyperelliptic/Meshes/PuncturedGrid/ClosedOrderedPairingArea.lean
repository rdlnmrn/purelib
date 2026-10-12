module
import Purelib.Data.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Vector.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.GeneratorValuation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedClosedSurfaceArea
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Topology.Mesh.RetracingWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ClosedPairedEnding
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryWord
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.Walk.Vertex
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Tactic.Ring
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedSheetReplay
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ClosedPairedSheets

open Purelib.Curves

open Purelib.Data

open Purelib

open Purelib.Riemann

public section

/-! Exact area identity between the corrected ordered pairing and the actual full cut. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ClosedOrderedPairingArea

open Purelib.Topology.Polygon.Stokes

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {bank :
    Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted} {sheet : Fin 2}
  {values : Data.Vector Gaussian.Basic.Canonical lifted.cutBoundaryWord.alphabet.count}
  (data : Cut.GeneratorValuation lifted values)

/-- The original paired opposite-sheet correction areas sum to the complete retained cut-word area. -/
private theorem opposite_correction_area (ordered :
  Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank sheet)
    (first : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.Compiled
      ordered.prepared.partition lifted.edges lifted.vertices sheet)
    (second : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.Compiled
      ordered.prepared.partition lifted.edges lifted.vertices
      (Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts.otherSheet sheet)) :
    Topology.Mesh.RetracingWords.AreaTerm.total data.value first.areaTerms + Topology.Mesh.RetracingWords.AreaTerm.total
      data.value second.areaTerms =
      Topology.Mesh.RetracingWords.wordArea data.value lifted.cutPolygon.patch.boundary := by
  have both (selected : Fin 2) :
      ∀ (first : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.Compiled
        ordered.prepared.partition lifted.edges lifted.vertices selected)
        (second : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.Compiled
          ordered.prepared.partition lifted.edges lifted.vertices (Hyperelliptic.Branches.BranchCutLifts.otherSheet
          selected)),
      Topology.Mesh.RetracingWords.AreaTerm.total data.value first.areaTerms +
        Topology.Mesh.RetracingWords.AreaTerm.total data.value second.areaTerms =
        Topology.Mesh.RetracingWords.wordArea data.value lifted.cutPolygon.patch.boundary := by
    refine Purelib.Data.Fin.cases_induction ?_ (Purelib.Data.Fin.cases_induction ?_ (fun impossible => Fin.elim0
      impossible)) selected
    · intro first second
      exact
        OrderedClosedSurfaceArea.LiftedPuncturedGrid.BasedBranchBank.Ordered.twoSheet_correction_area
        ordered data first second
    · intro first second
      exact (add_comm _ _).trans
        (OrderedClosedSurfaceArea.LiftedPuncturedGrid.BasedBranchBank.Ordered.twoSheet_correction_area
        ordered data second first)
  exact both sheet first second

namespace Paired
variable {ordered : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank
  sheet} (paired : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered)

/-- The opposite-sheet internal polygons cancel, while the corrected A/B pairing is unchanged. -/
theorem twice_correctedArea_eq_cut_area : 2 * paired.rows.correctedArea data.value =
    Topology.Mesh.RetracingWords.wordArea data.value lifted.cutPolygon.patch.boundary := by
  let other := paired.atSheet (Hyperelliptic.Branches.BranchCutLifts.otherSheet sheet)
  have first := paired.area_closed data
  have second := other.area_closed data
  have same := paired.rows.correctedArea_other data other.rows (by exact neg_zero.symm)
  have internal := paired.rows.internalArea_other data other.rows
  have ending := paired.ending.internalArea_other data other.ending
  have corrections := Hyperelliptic.Meshes.PuncturedGrid.ClosedOrderedPairingArea.opposite_correction_area data ordered
    ordered.prepared.compiled
    (ordered.atSheet (Hyperelliptic.Branches.BranchCutLifts.otherSheet sheet)).prepared.compiled
  have secondReadback : paired.rows.correctedArea data.value =
      -paired.rows.internalArea data.value + -paired.ending.internalArea data.value +
        Topology.Mesh.RetracingWords.AreaTerm.total data.value (ordered.atSheet
          (Hyperelliptic.Branches.BranchCutLifts.otherSheet sheet)).prepared.compiled.areaTerms :=
    same.symm.trans (second.trans (congrArg (· + Topology.Mesh.RetracingWords.AreaTerm.total data.value
      (ordered.atSheet (Hyperelliptic.Branches.BranchCutLifts.otherSheet sheet)).prepared.compiled.areaTerms) (congrArg₂
        (· + ·) internal ending)))
  calc
    _ = paired.rows.correctedArea data.value + paired.rows.correctedArea data.value := by ring1
    _ = (paired.rows.internalArea data.value + paired.ending.internalArea data.value +
          Topology.Mesh.RetracingWords.AreaTerm.total data.value ordered.prepared.compiled.areaTerms) +
        (-paired.rows.internalArea data.value + -paired.ending.internalArea data.value +
          Topology.Mesh.RetracingWords.AreaTerm.total data.value (ordered.atSheet
            (Hyperelliptic.Branches.BranchCutLifts.otherSheet sheet)).prepared.compiled.areaTerms) := by
      exact congrArg₂ (· + ·) first secondReadback
    _ = Topology.Mesh.RetracingWords.AreaTerm.total data.value ordered.prepared.compiled.areaTerms +
        Topology.Mesh.RetracingWords.AreaTerm.total data.value (ordered.atSheet
          (Hyperelliptic.Branches.BranchCutLifts.otherSheet sheet)).prepared.compiled.areaTerms := by ring1
    _ = _ := corrections

namespace Prepared
variable (prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired)

/-- This reads the exact program-owning corrected A/B family, not an abstract handle model. -/
theorem twice_pairing_eq_cut_area : 2 * prepared.pairing data.value =
    Topology.Mesh.RetracingWords.wordArea data.value lifted.cutPolygon.patch.boundary := by
  rw [prepared.pairing_eq]
  exact Hyperelliptic.Meshes.PuncturedGrid.ClosedOrderedPairingArea.Paired.twice_correctedArea_eq_cut_area data paired

end Prepared
end Paired
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ClosedOrderedPairingArea
