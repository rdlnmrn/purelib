module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
public import Purelib.Riemann.RootContinuation.NewtonBandWindowCircuits

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Polynomial.Geometry.Grid.VertexStar
import Purelib.Curves.Hyperelliptic.Meshes.Newton.BandWindowConnectors
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CircuitCells
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularNeighborUniqueness
import Purelib.Tactic.Ring

public section

/-! Complete cell accounting for the compiler inside an Newton-band
window. Its traversal order does not change the selected finite sum. -/
section

open Purelib
open Purelib.Data.Rat

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches.Cuts (Ambient)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank
  (NewtonPreparation NewtonGrid)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces (AnnularFaces)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Polynomial.Geometry.Grid.ClearGrid (Cell)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition
open Purelib.Polynomial.Geometry.Grid.CellBoundary
  (sumValues sumValues_append sumValues_flatMap sumValues_congr sumValues_map sumValues_swap sumValues_reverse
   sumValues_filter_eq_sumFin)
open Purelib.Riemann.RootContinuation.NewtonBandWindowCircuits
  (fineOrder fineCompiler fine_kept_labels)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve branches
    higher}
  {preparation : NewtonPreparation original} {target radius : Rational}
  {grid : NewtonGrid preparation target radius} {index : Curves.Hyperelliptic.Branches.BranchIsolation.Data.Index
    branches}
  {current : LiftedPuncturedGrid grid.punctured}

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces.AnnularFaces

open Purelib.Riemann in
open Purelib.Curves in
open Purelib.Data in
open Purelib.Polynomial in
/-- The fine compiler retains the complete regular-cell value sum of the Newton annulus.

After the unique hole contribution cancels, traversal order, arriving sheets and connector paths leave every actual
regular-cell occurrence accounted for. -/
theorem fineCompiler_cell_sum (region :
  AnnularFaces grid index) (sheet : Fin 2)
    (value : Cell curve.polynomial (Ambient curve) →
      Gaussian.Basic.Canonical) :
    sumValues (fun occurrence => value occurrence.cell)
        (fineCompiler (current := current) region sheet).regulars =
      sumValues (fun entry => value entry.cell) region.faces := by
  let order := fineOrder (current := current) region sheet
  have kept := kept_cell_sum
    order.partition value
  have labels := congrArg (sumValues (fun entry => value (grid.shrunk.prepared.cell entry)))
    (fine_kept_labels (current := current) region sheet)
  have hole : sumValues value order.partition.kept.cells = value (grid.shrunk.prepared.cell
    index) :=
    kept.trans (labels.trans (add_zero _))
  have compiled :=
    compileResplit_cell_sum
    (Geometry.Grid.Extension.CoordinateInclusion.refl grid.punctured.bank.grid) current.edges current.vertices
    (fun point member => (PuncturedGrid.LoopMonodromy.BranchCellBank.referenceAt
      grid.punctured.bank.toBranchCellBank point member).toLoop)
    (LiftedBoundary.anchor_onGrid region)
    order.partition sheet value
  have orderedCells : sumValues value order.ordered.tree.cells =
      sumValues value region.window.circuits.cells :=
    congrArg (fun tree => sumValues value tree.cells) order.ordered.tree_eq
  have accounted := (congrArg
    (fun rest => sumValues (fun occurrence => value occurrence.cell)
      (fineCompiler (current := current) region sheet).regulars + rest) hole).symm.trans compiled
  have windowSum : sumValues value region.window.circuits.cells =
    sumValues value region.window.cells := by
    rw [region.window.circuits_cells, sumValues_flatMap, region.window.sum_cells]
    have readback := sumValues_congr _
      (fun band => sumValues (fun interval => value (Cell.mk interval
        band)) region.window.x.edges)
      region.window.y.edges (fun band _ => (sumValues_map value _ _).trans
        (sumValues_reverse _ _))
    exact readback.trans (sumValues_swap _ _ _)
  exact add_right_cancel ((accounted.trans orderedCells).trans (windowSum.trans (region.sum_balance value).symm))

end Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces.AnnularFaces

open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_ite_eq)
attribute [local congr] sumFin_congr

namespace Purelib.Riemann.RootContinuation.NewtonBandWindowCells

open Purelib.Algebra in
open Purelib.Curves in
open Purelib.Data in
open Purelib.Polynomial in
/-- Read an indexed regular-face value through finite equality of its actual cell anchor. -/
private def cellValue (value : Fin grid.faces.regulars.length → Gaussian.Basic.Canonical)
    (cell : Cell curve.polynomial (Ambient curve)) : Gaussian :=
  sumFin (fun position =>
    if (grid.faces.regulars[position.val]'position.isLt).cell.box.anchor = cell.box.anchor
    then value position else 0)

open Purelib.Algebra in
open Purelib.Data in
open Purelib.Polynomial in
/-- The cell-anchor readback recovers the exact value at its original regular-face position. -/
private theorem cellValue_index (value : Fin grid.faces.regulars.length → Gaussian.Basic.Canonical)
    (position : Fin grid.faces.regulars.length) :
    cellValue value (grid.faces.regulars[position.val]'position.isLt).cell = value position := by
  apply Eq.trans ?_ (sumFin_ite_eq position value)
  apply sumFin_congr
  intro index
  by_cases equal : index = position
  · cases equal
    rw [if_pos rfl, if_pos rfl]
  · have different : (grid.faces.regulars[index.val]'index.isLt).cell.box.anchor ≠
        (grid.faces.regulars[position.val]'position.isLt).cell.box.anchor := by
      intro same
      exact equal (grid.faces.position_eq_of_cell index position
        (Geometry.Grid.ClearGrid.cell_eq_of_anchor (grid.faces.regulars[index.val]'index.isLt).member
          (grid.faces.regulars[position.val]'position.isLt).member same))
    rw [if_neg different, if_neg equal]

end Purelib.Riemann.RootContinuation.NewtonBandWindowCells

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces.AnnularFaces

open Purelib.Algebra in
open Purelib.Curves in
open Purelib.Data in
open Purelib.Polynomial in
/-- The compiler's retained regular occurrences sum to the original position-selected region sum.

Each occurrence's location certificate preserves its cached face index, and the selection keeps precisely the cells
refining the retained Newton band. -/
theorem fineCompiler_position_sum (region :
  AnnularFaces grid index) (sheet : Fin 2)
    (value : Fin grid.faces.regulars.length → Gaussian.Basic.Canonical) :
    sumValues (fun occurrence => value occurrence.location.index)
        (fineCompiler (current := current) region sheet).regulars =
      sumFin (fun position : Fin grid.faces.regulars.length =>
        if (grid.faces.regulars[position.val]'position.isLt).cell.box.Refines (grid.bands.box index)
        then value position else 0) := by
  have readback := sumValues_congr _ (fun occurrence =>
    Riemann.RootContinuation.NewtonBandWindowCells.cellValue value occurrence.cell)
    (fineCompiler (current := current) region sheet).regulars (by
      intro occurrence _
      have indexed : (grid.faces.regulars[occurrence.location.index.val]'occurrence.location.index.isLt).cell =
          occurrence.cell :=
        (congrArg RegularFace.cell occurrence.location.indexed).trans occurrence.location.cell_eq
      exact (Riemann.RootContinuation.NewtonBandWindowCells.cellValue_index value occurrence.location.index).symm.trans
        (congrArg (Riemann.RootContinuation.NewtonBandWindowCells.cellValue value) indexed))
  refine readback.trans ((region.fineCompiler_cell_sum sheet (Riemann.RootContinuation.NewtonBandWindowCells.cellValue
    value)).trans ?_)
  rw [region.faces_eq, sumValues_filter_eq_sumFin]
  apply sumFin_congr
  intro position
  by_cases inside : (grid.faces.regulars[position.val]'position.isLt).cell.box.Refines (grid.bands.box index)
  · rw [if_pos inside, if_pos (decide_eq_true inside), Riemann.RootContinuation.NewtonBandWindowCells.cellValue_index]
  · rw [if_neg inside, if_neg (fun kept => inside (of_decide_eq_true kept))]

end Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces.AnnularFaces

end
