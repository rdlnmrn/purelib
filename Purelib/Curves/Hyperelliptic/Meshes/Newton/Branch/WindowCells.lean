module
import Purelib.Data.List.Reverse
import Purelib.Data.List.Filter
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Riemann.Meshes.PuncturedGridFaces

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Branch.WindowCircuits
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Polynomial.Geometry.Grid.VertexStar
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonOriginalAnnularFaces
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Branch.WindowConnectors
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CircuitCells
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularNeighborUniqueness
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CircuitAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.WindowBoundary
import Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedFaceLookup
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Tactic.Ring

open Purelib.Polynomial.Geometry.Grid

open Purelib.Algebra

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Polynomial

open Purelib.Riemann

public section

/-! Complete cell accounting for the compiler inside an original branch
window. Its traversal order does not change the selected finite sum. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Branch.WindowCells

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition

/-- Reversing a finite list preserves its Gaussian value sum. -/
private theorem sum_reverse {Item : Type} (value : Item → Gaussian.Basic.Canonical) (items : List Item) :
    CellBoundary.sumValues value items.reverse = CellBoundary.sumValues value items := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
      rw [List.Reverse.reverse_cons, CellBoundary.sumValues_append, ih]
      change CellBoundary.sumValues value tail + (value head + 0) = value head +
        CellBoundary.sumValues value tail
      ring1

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Branches.BranchCellBank curve branches higher}
  {preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation original} {target radius :
    Fraction.Rational}
  {grid : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid preparation target radius} {index :
    Branches.BranchIsolation.Data.Index branches}
  {current : Meshes.LiftedPuncturedGrid grid.punctured}

/-- After the unique hole contributions cancel, every regular cell occurs
with its full multiplicity, independently
of the compiler's arriving sheets and connector paths. -/
theorem fineCompiler_cell_sum (region : RootContinuation.NewtonOriginalAnnularFaces.OriginalAnnularFaces grid index)
  (sheet : Fin 2)
    (value : ClearGrid.Cell curve.polynomial (Branches.Cuts.Ambient curve) →
      Gaussian.Basic.Canonical) :
    CellBoundary.sumValues (fun occurrence => value occurrence.cell)
        (WindowCircuits.fineCompiler (current := current) region sheet).regulars =
      CellBoundary.sumValues (fun entry => value entry.cell) region.faces := by
  let order := WindowCircuits.fineOrder (current := current) region sheet
  have kept := PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.kept_cell_sum
    order.partition value
  have labels := congrArg (CellBoundary.sumValues (fun entry => value (grid.punctured.bank.cell entry)))
    (WindowCircuits.fine_kept_labels (current := current) region sheet)
  have hole : CellBoundary.sumValues value order.partition.kept.cells = value (grid.punctured.bank.cell
    index) :=
    kept.trans (labels.trans (add_zero _))
  have compiled :=
    PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.compileResplit_cell_sum
    (Extension.CoordinateInclusion.refl grid.punctured.bank.grid) current.edges current.vertices
    (fun point member => (PuncturedGrid.LoopMonodromy.BranchCellBank.referenceAt
      grid.punctured.bank.toBranchCellBank point member).toLoop)
    (grid.shrunk.included.vertex ((original.cell index).anchor_mem (original.cell_mem index)))
    order.partition sheet value
  have orderedCells : CellBoundary.sumValues value order.ordered.tree.cells =
      CellBoundary.sumValues value region.window.circuits.cells :=
    congrArg (fun tree => CellBoundary.sumValues value tree.cells) order.ordered.tree_eq
  have accounted := (congrArg
    (fun rest => CellBoundary.sumValues (fun occurrence => value occurrence.cell)
      (WindowCircuits.fineCompiler (current := current) region sheet).regulars +
        rest) hole).symm.trans compiled
  have windowSum : CellBoundary.sumValues value region.window.circuits.cells =
    CellBoundary.sumValues value region.window.cells := by
    rw [region.window.circuits_cells, CellBoundary.sumValues_flatMap, region.window.sum_cells]
    have readback := CellBoundary.sumValues_congr _
      (fun band => CellBoundary.sumValues (fun interval => value (ClearGrid.Cell.mk interval
        band)) region.window.x.edges)
      region.window.y.edges (fun band _ => (CellBoundary.sumValues_map value _ _).trans
        (WindowCells.sum_reverse _ _))
    exact readback.trans (CellBoundary.sumValues_swap _ _ _)
  exact add_right_cancel ((accounted.trans orderedCells).trans (windowSum.trans (region.sum_balance value).symm))

attribute [local congr] FiniteSum.Fin.sumFin_congr

/-- Read an indexed regular-face value by matching its original cell anchor.

The finite sum keeps the actual regular-face indices and returns zero for nonmatching anchors. -/
private def cellValue (value : Fin grid.faces.regulars.length → Gaussian.Basic.Canonical)
    (cell : ClearGrid.Cell curve.polynomial (Branches.Cuts.Ambient curve)) : Gaussian :=
  FiniteSum.Fin.sumFin (fun position =>
    if (grid.faces.regulars[position.val]'position.isLt).cell.box.anchor = cell.box.anchor
    then value position else 0)

/-- The anchor-based value readback returns the value at the original regular-face index. -/
private theorem cellValue_index (value : Fin grid.faces.regulars.length → Gaussian.Basic.Canonical)
    (position : Fin grid.faces.regulars.length) :
    WindowCells.cellValue value
      (grid.faces.regulars[position.val]'position.isLt).cell = value position := by
  apply Eq.trans ?_ (FiniteSum.Fin.sumFin_ite_eq position value)
  apply FiniteSum.Fin.sumFin_congr
  intro index
  by_cases equal : index = position
  · cases equal
    rw [if_pos rfl, if_pos rfl]
  · have different : (grid.faces.regulars[index.val]'index.isLt).cell.box.anchor ≠
        (grid.faces.regulars[position.val]'position.isLt).cell.box.anchor := by
      intro same
      exact equal (grid.faces.position_eq_of_cell index position
        (ClearGrid.cell_eq_of_anchor (grid.faces.regulars[index.val]'index.isLt).member
          (grid.faces.regulars[position.val]'position.isLt).member same))
    rw [if_neg different, if_neg equal]

/-- A filtered list value sum equals the finite indexed sum with the same Boolean membership test. -/
private theorem filtered_sum {Item : Type} (items : List Item) (keep : Item → Bool)
    (value : Item → Gaussian.Basic.Canonical) :
    CellBoundary.sumValues value (items.filter keep) = FiniteSum.Fin.sumFin (fun position : Fin
      items.length =>
      if keep (items[position.val]'position.isLt) then value (items[position.val]'position.isLt) else 0) := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
      rw [FiniteSum.Fin.sumFin_succ]
      change CellBoundary.sumValues value ((head :: tail).filter keep) =
        (if keep head then value head else 0) + FiniteSum.Fin.sumFin (fun position : Fin tail.length =>
          if keep (tail[position.val]'position.isLt) then value (tail[position.val]'position.isLt) else 0)
      rewrite [← ih]
      cases equal : keep head <;>
        simp only [-eq_self, -iff_self, List.Filter.filter_cons, equal,
          if_neg (show (false : Bool) ≠ true by decide +kernel), if_pos (rfl : (true : Bool) = true),
          CellBoundary.sumValues, Gaussian.Basic.zero_add] <;> rfl

/-- Position-dependent triangle data can be summed over the entire
selected region, without replacing a cached face by an unindexed copy. -/
theorem fineCompiler_position_sum (region : RootContinuation.NewtonOriginalAnnularFaces.OriginalAnnularFaces grid index)
  (sheet : Fin 2)
    (value : Fin grid.faces.regulars.length → Gaussian.Basic.Canonical) :
    CellBoundary.sumValues (fun occurrence => value occurrence.location.index)
        (WindowCircuits.fineCompiler (current := current) region sheet).regulars =
      FiniteSum.Fin.sumFin (fun position : Fin grid.faces.regulars.length =>
        if (grid.faces.regulars[position.val]'position.isLt).cell.box.Refines (original.cell index).box
        then value position else 0) := by
  have readback := CellBoundary.sumValues_congr _ (fun occurrence =>
    WindowCells.cellValue value occurrence.cell)
    (WindowCircuits.fineCompiler (current := current) region sheet).regulars (by
      intro occurrence _
      have indexed : (grid.faces.regulars[occurrence.location.index.val]'occurrence.location.index.isLt).cell =
          occurrence.cell :=
        (congrArg Meshes.PuncturedGridFaces.RegularFace.cell occurrence.location.indexed).trans
          occurrence.location.cell_eq
      exact (WindowCells.cellValue_index value occurrence.location.index).symm.trans
        (congrArg (WindowCells.cellValue value) indexed))
  refine readback.trans ((WindowCells.fineCompiler_cell_sum region sheet
    (WindowCells.cellValue value)).trans ?_)
  rw [region.faces_eq, WindowCells.filtered_sum]
  apply FiniteSum.Fin.sumFin_congr
  intro position
  by_cases accepted : (grid.faces.regulars[position.val]'position.isLt).cell.box.Refines (original.cell index).box
  · rw [if_pos (decide_eq_true accepted), if_pos accepted]
    exact cellValue_index value position
  · rw [if_neg (fun found => accepted (of_decide_eq_true found)), if_neg accepted]

end Purelib.Curves.Hyperelliptic.Meshes.Newton.Branch.WindowCells
