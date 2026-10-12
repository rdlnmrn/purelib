module
import Purelib.Data.List.Reverse
import Purelib.Data.List.Filter
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.WindowCircuits
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Polynomial.Geometry.Grid.RowCircuitOrder
import Purelib.Polynomial.Geometry.Grid.VertexStar
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.RootContinuation.NewtonOriginalRegularFaces
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.WindowConnectors
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CircuitCells
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularNeighborUniqueness
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CircuitAreas
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

open Purelib.Algebra

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Polynomial

open Purelib.Riemann

public section

/-! Complete cell accounting for the compiler inside an original regular
window. Its traversal order does not change the selected finite sum. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.WindowCells

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition

/-- Reversing a finite list preserves its Gaussian value sum. -/
private theorem sum_reverse {Item : Type} (value : Item → Gaussian.Basic.Canonical) (items : List Item) :
    Geometry.Grid.CellBoundary.sumValues value items.reverse = Geometry.Grid.CellBoundary.sumValues value items := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
      rw [List.Reverse.reverse_cons, Geometry.Grid.CellBoundary.sumValues_append, ih]
      change Geometry.Grid.CellBoundary.sumValues value tail + (value head + 0) = value head +
        Geometry.Grid.CellBoundary.sumValues value tail
      ring1

/-- A circuit partition whose traversal contains no branch-hole cell retains no hole cells. -/
private theorem kept_cells_empty {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {branches : Hyperelliptic.Branches.BranchIsolation.Data curve} {higher : 1 < curve.polynomial.natDegree}
    {bank : Hyperelliptic.Branches.BranchCellBank curve branches higher} {faces :
      Meshes.PuncturedGridFaces.PuncturedFaces bank}
    {start : Gaussian.Basic.Canonical} {tree : Purelib.Polynomial.Geometry.Grid.RowCircuitOrder.CellCircuits bank.grid
      start}
    (partition : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition faces tree)
    (absent : ∀ hole : Meshes.PuncturedGridFaces.BranchHole bank, hole.cell ∉ tree.cells) :
    partition.kept.cells = [] := by
  induction partition with
  | nil => rfl
  | regular => rfl
  | hole location =>
      exact (absent location.hole (location.cell_eq.symm ▸ List.mem_cons_self)).elim
  | append first last ihFirst ihLast =>
      change first.kept.cells ++ last.kept.cells = []
      rw [ihFirst (fun hole member => absent hole (List.mem_append_left _ member)),
        ihLast (fun hole member => absent hole (List.mem_append_right _ member))]
      rfl

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation original} {target radius :
    Fraction.Rational}
  {grid : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid preparation target radius} {face :
    Meshes.PuncturedGridFaces.RegularFace original}
  {current : Meshes.LiftedPuncturedGrid grid.punctured}

/-- Every selected cell occurs with its full multiplicity, independently
of the compiler's arriving sheets and connector paths. -/
theorem fineCompiler_cell_sum (region : RootContinuation.NewtonOriginalRegularFaces.OriginalRegularFaces grid face)
  (sheet : Fin 2)
    (value : Geometry.Grid.ClearGrid.Cell curve.polynomial (Hyperelliptic.Branches.Cuts.Ambient curve) →
      Gaussian.Basic.Canonical) :
    Geometry.Grid.CellBoundary.sumValues (fun occurrence => value occurrence.cell)
        (Hyperelliptic.Meshes.Newton.Regular.WindowConnectors.fineCompiler (current := current) region sheet).regulars =
      Geometry.Grid.CellBoundary.sumValues (fun entry => value entry.cell) region.faces := by
  let order := Hyperelliptic.Meshes.Newton.Regular.WindowConnectors.fineOrder (current := current) region sheet
  have empty : order.partition.kept.cells = [] := by
    apply Hyperelliptic.Meshes.Newton.Regular.WindowCells.kept_cells_empty
    intro hole member
    exact Hyperelliptic.Meshes.Newton.Regular.WindowCircuits.window_hole_absent region hole (order.ordered.tree_eq ▸
      member)
  have compiled :=
    Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.compileResplit_cell_sum
    (Geometry.Grid.Extension.CoordinateInclusion.refl grid.punctured.bank.grid) current.edges current.vertices
    (fun point member => (Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy.BranchCellBank.referenceAt
      grid.punctured.bank.toBranchCellBank point member).toLoop)
    (grid.shrunk.included.vertex (face.cell.anchor_mem face.member)) order.partition sheet value
  have removed : Geometry.Grid.CellBoundary.sumValues value order.partition.kept.cells = 0 :=
    congrArg (Geometry.Grid.CellBoundary.sumValues value) empty
  have orderedCells : Geometry.Grid.CellBoundary.sumValues value order.ordered.tree.cells =
      Geometry.Grid.CellBoundary.sumValues value region.window.circuits.cells :=
    congrArg (fun tree => Geometry.Grid.CellBoundary.sumValues value tree.cells) order.ordered.tree_eq
  have accounted := (congrArg
    (fun rest => Geometry.Grid.CellBoundary.sumValues (fun occurrence => value occurrence.cell)
      (Hyperelliptic.Meshes.Newton.Regular.WindowConnectors.fineCompiler (current := current) region sheet).regulars +
        rest) removed).symm.trans compiled
  rw [add_zero] at accounted
  refine (accounted.trans orderedCells).trans (Eq.trans ?_ (region.sum_balance value).symm)
  rw [region.window.circuits_cells, Geometry.Grid.CellBoundary.sumValues_flatMap, region.window.sum_cells]
  have readback := Geometry.Grid.CellBoundary.sumValues_congr _
    (fun band => Geometry.Grid.CellBoundary.sumValues (fun interval => value (Geometry.Grid.ClearGrid.Cell.mk interval
      band)) region.window.x.edges)
    region.window.y.edges (fun band _ => (Geometry.Grid.CellBoundary.sumValues_map value _ _).trans
      (Hyperelliptic.Meshes.Newton.Regular.WindowCells.sum_reverse _ _))
  exact readback.trans (Geometry.Grid.CellBoundary.sumValues_swap _ _ _)

attribute [local congr] FiniteSum.Fin.sumFin_congr

/-- Read an indexed regular-face value by matching its original cell anchor.

The finite sum preserves the actual regular-face indices and contributes zero for other anchors. -/
private def cellValue (value : Fin grid.faces.regulars.length → Gaussian.Basic.Canonical)
    (cell : Geometry.Grid.ClearGrid.Cell curve.polynomial (Hyperelliptic.Branches.Cuts.Ambient curve)) : Gaussian :=
  FiniteSum.Fin.sumFin (fun position =>
    if (grid.faces.regulars[position.val]'position.isLt).cell.box.anchor = cell.box.anchor
    then value position else 0)

/-- The anchor-based readback returns the value at the original regular-face index. -/
private theorem cellValue_index (value : Fin grid.faces.regulars.length → Gaussian.Basic.Canonical)
    (position : Fin grid.faces.regulars.length) :
    Hyperelliptic.Meshes.Newton.Regular.WindowCells.cellValue value
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
        (Polynomial.Geometry.Grid.ClearGrid.cell_eq_of_anchor (grid.faces.regulars[index.val]'index.isLt).member
          (grid.faces.regulars[position.val]'position.isLt).member same))
    rw [if_neg different, if_neg equal]

/-- A filtered list sum equals the finite indexed sum using the same Boolean test. -/
private theorem filtered_sum {Item : Type} (items : List Item) (keep : Item → Bool)
    (value : Item → Gaussian.Basic.Canonical) :
    Geometry.Grid.CellBoundary.sumValues value (items.filter keep) = FiniteSum.Fin.sumFin (fun position : Fin
      items.length =>
      if keep (items[position.val]'position.isLt) then value (items[position.val]'position.isLt) else 0) := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
      rw [FiniteSum.Fin.sumFin_succ]
      change Geometry.Grid.CellBoundary.sumValues value ((head :: tail).filter keep) =
        (if keep head then value head else 0) + FiniteSum.Fin.sumFin (fun position : Fin tail.length =>
          if keep (tail[position.val]'position.isLt) then value (tail[position.val]'position.isLt) else 0)
      rewrite [← ih]
      cases equal : keep head <;>
        simp only [-eq_self, -iff_self, List.Filter.filter_cons, equal,
          if_neg (show (false : Bool) ≠ true by decide +kernel), if_pos (rfl : (true : Bool) = true),
          Geometry.Grid.CellBoundary.sumValues, Data.Gaussian.Basic.zero_add] <;> rfl

/-- Position-dependent triangle data can be summed over the entire
selected region, without replacing a cached face by an unindexed copy. -/
theorem fineCompiler_position_sum (region : RootContinuation.NewtonOriginalRegularFaces.OriginalRegularFaces grid face)
  (sheet : Fin 2)
    (value : Fin grid.faces.regulars.length → Gaussian.Basic.Canonical) :
    Geometry.Grid.CellBoundary.sumValues (fun occurrence => value occurrence.location.index)
        (Hyperelliptic.Meshes.Newton.Regular.WindowConnectors.fineCompiler (current := current) region sheet).regulars =
      FiniteSum.Fin.sumFin (fun position : Fin grid.faces.regulars.length =>
        if (grid.faces.regulars[position.val]'position.isLt).cell.box.Refines face.cell.box
        then value position else 0) := by
  have readback := Geometry.Grid.CellBoundary.sumValues_congr _ (fun occurrence =>
    Hyperelliptic.Meshes.Newton.Regular.WindowCells.cellValue value occurrence.cell)
    (Hyperelliptic.Meshes.Newton.Regular.WindowConnectors.fineCompiler (current := current) region sheet).regulars (by
      intro occurrence _
      have indexed : (grid.faces.regulars[occurrence.location.index.val]'occurrence.location.index.isLt).cell =
          occurrence.cell :=
        (congrArg Meshes.PuncturedGridFaces.RegularFace.cell occurrence.location.indexed).trans
          occurrence.location.cell_eq
      exact (Hyperelliptic.Meshes.Newton.Regular.WindowCells.cellValue_index value occurrence.location.index).symm.trans
        (congrArg (Hyperelliptic.Meshes.Newton.Regular.WindowCells.cellValue value) indexed))
  refine readback.trans ((Hyperelliptic.Meshes.Newton.Regular.WindowCells.fineCompiler_cell_sum region sheet
    (Hyperelliptic.Meshes.Newton.Regular.WindowCells.cellValue value)).trans ?_)
  rw [region.faces_eq, Hyperelliptic.Meshes.Newton.Regular.WindowCells.filtered_sum]
  apply FiniteSum.Fin.sumFin_congr
  intro position
  by_cases accepted : (grid.faces.regulars[position.val]'position.isLt).cell.box.Refines face.cell.box
  · rw [if_pos (decide_eq_true accepted), if_pos accepted]
    exact cellValue_index value position
  · rw [if_neg (fun found => accepted (of_decide_eq_true found)), if_neg accepted]

end Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.WindowCells
