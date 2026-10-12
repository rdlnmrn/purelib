module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.List.Map

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Polynomial.Geometry.Grid.WindowBoundary
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Tactic.Ring

public section

/-! The original branch cell, subdivided by the Newton grid, contains
exactly its retained smaller hole. The intervening regular faces are read
from the existing classification, not reclassified or assumed absent. -/

namespace Purelib.Riemann.RootContinuation.NewtonOriginalAnnularFaces

open Purelib.Data.List

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace BranchHole)
open Purelib.Polynomial.Geometry.Grid.ClearGrid (Cell Interval)
open Purelib.Polynomial.Geometry.Grid.CellBoundary (sumValues sumValues_congr sumValues_zero sumValues_add EdgeValues)
open Purelib.Polynomial.Geometry.Grid.CellBoundary.EdgeValues
open Purelib.Polynomial.Geometry.Grid.WindowBoundary (sumValues_filter)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces (AnnularFaces)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {target radius : Purelib.Data.Rat.Fraction.Rational}

open Purelib.Curves in
open Purelib.Geometry in
/-- A retained Newton hole inside an original branch cell has that cell's branch index. -/
private theorem original_hole_index (grid : NewtonGrid preparation target radius)
    (hole : BranchHole grid.punctured.bank.toBranchCellBank) (index : Hyperelliptic.Branches.BranchIsolation.Data.Index
      branches)
    (inside : hole.cell.box.Refines (original.cell index).box) : hole.index = index := by
  by_cases same : hole.index = index
  · exact same
  · have retained : hole.cell.box.Refines (original.cell hole.index).box := by
      rw [hole.cell_eq]
      exact (Geometry.Rational.Box.Refinement.StrictInterior.refines (grid.shrunk.cell_strict hole.index))
    exact ((original.cells_separated hole.index index same).points_ne
      (retained.contains hole.cell.box.contains_anchor) (inside.contains hole.cell.box.contains_anchor) rfl).elim

open Purelib.Curves in
open Purelib.Polynomial in
set_option genInjectivity false in
/-- The original branch cell's retained regular faces on the Newton grid.

The list is the existing classification filtered by the original box, together with the exact coordinate window. -/
structure OriginalAnnularFaces (grid : NewtonGrid preparation target radius) (index :
  Hyperelliptic.Branches.BranchIsolation.Data.Index branches) where
  /-- The retained regular faces between the original cell and its smaller hole. -/ faces : List (RegularFace
    grid.shrunk.prepared.toBranchCellBank)
  /-- The retained list is exactly the original-box filter of the Newton regular faces. -/ faces_eq : faces =
    grid.faces.regulars.filter (fun face => decide (face.cell.box.Refines (original.cell index).box))
  /-- The original cell's window in the refined Newton grid. -/ window : Polynomial.Geometry.Grid.WindowBoundary.Window
    grid.shrunk.prepared.grid (original.cell index).box

constructive_injectivity OriginalAnnularFaces

namespace OriginalAnnularFaces

variable {grid : NewtonGrid preparation target radius} {index :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data.Index branches}

open Purelib.Curves in
open Purelib.Data in
open Purelib.Polynomial in
/-- Select the original annular faces and construct their coordinate window.

Reuse the Newton grid's existing classification and coordinate inclusion without recomputing any face clearance. -/
@[expose] def build (grid : NewtonGrid preparation target radius) (index :
  Hyperelliptic.Branches.BranchIsolation.Data.Index branches) :
    OriginalAnnularFaces grid index := by
  let cell := original.cell index
  have intervals := Geometry.Grid.CellBoundary.Cell.intervals_mem cell (original.cell_mem index)
  have x := Geometry.Grid.ClearGrid.Interval.endpoints_mem _ original.grid.vertical_ordered intervals.1
  have y := Geometry.Grid.ClearGrid.Interval.endpoints_mem _ original.grid.horizontal_ordered intervals.2
  let included := grid.shrunk.included
  exact ⟨grid.faces.regulars.filter (fun face => decide (face.cell.box.Refines cell.box)), rfl,
    Polynomial.Geometry.Grid.WindowBoundary.Window.build _ cell.box
      (included.vertical _ (List.Map.mem_map_of_mem x.1))
      (included.vertical _ (List.Map.mem_map_of_mem x.2))
      (included.horizontal _ (List.Map.mem_map_of_mem y.1))
      (included.horizontal _ (List.Map.mem_map_of_mem y.2))⟩

open Purelib.Data in
open Purelib.Polynomial in
/-- A finite list with unique keys contributes exactly the value at its retained matching key. -/
private theorem sum_unique {Alpha : Type} {count : Nat} (key : Alpha → Fin count) (index : Fin count) (value :
  Gaussian.Basic.Canonical) :
    ∀ (entries : List Alpha), entries.Pairwise (fun first second => key first ≠ key second) →
      (∃ entry ∈ entries, key entry = index) →
      Geometry.Grid.CellBoundary.sumValues (fun entry => if key entry = index then value else 0) entries = value
  | [], _, found => by obtain ⟨_, member, _⟩ := found; cases member
  | head :: tail, unique, found => by
      by_cases same : key head = index
      · rw [Geometry.Grid.CellBoundary.sumValues, if_pos same]
        have zero : Geometry.Grid.CellBoundary.sumValues (fun entry => if key entry = index then value else 0) tail = 0
          := by
          rw [Geometry.Grid.CellBoundary.sumValues_congr _ (fun _ => 0) tail (by
            intro entry member
            have different : key entry ≠ index := fun equal =>
              (List.pairwise_cons.mp unique).1 entry member (same.trans equal.symm)
            rw [if_neg different]), Geometry.Grid.CellBoundary.sumValues_zero]
        rw [zero, add_zero]
      · rw [Geometry.Grid.CellBoundary.sumValues, if_neg same, zero_add]
        apply sum_unique key index value tail (List.pairwise_cons.mp unique).2
        obtain ⟨entry, member, equal⟩ := found
        rcases Membership.mem_cons.mp member with rfl | member
        · exact (same equal).elim
        · exact ⟨entry, member, equal⟩

open Purelib.Curves in
open Purelib.Data in
open Purelib.Polynomial in
open Purelib.Geometry in
/-- The hole contribution inside an original branch cell is exactly its retained smaller hole. -/
private theorem hole_sum (grid : NewtonGrid preparation target radius) (index :
  Hyperelliptic.Branches.BranchIsolation.Data.Index branches)
    (value : Geometry.Grid.ClearGrid.Cell curve.polynomial (Hyperelliptic.Branches.Cuts.Ambient curve) →
      Gaussian.Basic.Canonical) :
    Geometry.Grid.CellBoundary.sumValues (fun hole => if hole.cell.box.Refines (original.cell index).box then value
      hole.cell else 0) grid.faces.holes =
      value (grid.punctured.bank.toBranchCellBank.cell index) := by
  rw [Geometry.Grid.CellBoundary.sumValues_congr _ (fun hole => if hole.index = index then value
    (grid.punctured.bank.toBranchCellBank.cell index) else 0)
    grid.faces.holes (by
      intro hole _
      by_cases same : hole.index = index
      · have inside : hole.cell.box.Refines (original.cell index).box := by
          rw [hole.cell_eq, same]
          exact (Geometry.Rational.Box.Refinement.StrictInterior.refines (grid.shrunk.cell_strict index))
        rw [if_pos inside, if_pos same, hole.cell_eq, same]
        rfl
      · have outside : ¬hole.cell.box.Refines (original.cell index).box := fun inside => same (original_hole_index grid
          hole index inside)
        rw [if_neg outside, if_neg same])]
  exact sum_unique (fun hole => hole.index) index _ grid.faces.holes grid.faces.holes_pairwise (grid.faces.hole_complete
    index)

open Purelib.Curves in
open Purelib.Data in
open Purelib.Polynomial in
/-- The selected regular faces and retained hole sum to the original cell window. -/
theorem sum_balance (annulus : OriginalAnnularFaces grid index) (value : Geometry.Grid.ClearGrid.Cell curve.polynomial
  (Hyperelliptic.Branches.Cuts.Ambient curve) → Gaussian.Basic.Canonical) :
    Geometry.Grid.CellBoundary.sumValues (fun face => value face.cell) annulus.faces + value
      (grid.punctured.bank.toBranchCellBank.cell index) =
      Geometry.Grid.CellBoundary.sumValues value annulus.window.cells := by
  rw [annulus.faces_eq, annulus.window.cells_eq, Geometry.Grid.WindowBoundary.sumValues_filter,
    Geometry.Grid.WindowBoundary.sumValues_filter]
  have balance := grid.faces.split.sum_eq (fun cell => if cell.box.Refines (original.cell index).box then value cell
    else 0)
  rw [← grid.faces.regulars_eq, ← grid.faces.holes_eq, hole_sum] at balance
  exact balance

open Purelib.Polynomial in
/-- The regular face boundaries plus the retained hole boundary equal the original window boundary. -/
theorem boundary_balance (annulus : OriginalAnnularFaces grid index) (values : Geometry.Grid.CellBoundary.EdgeValues) :
    Geometry.Grid.CellBoundary.sumValues (fun face => values.walk face.boundary) annulus.faces +
      values.cellBoundary (grid.shrunk.prepared.toBranchCellBank.cell index) = values.walk annulus.window.boundary := by
  have regular := Geometry.Grid.CellBoundary.sumValues_congr
    (fun face : RegularFace grid.shrunk.prepared.toBranchCellBank => values.walk face.boundary)
    (fun face => values.cellBoundary face.cell) annulus.faces
    (fun face _ => Geometry.Grid.CellBoundary.Cell.boundaryWalk_value face.cell face.member values)
  exact (congrArg (fun total => total + values.cellBoundary (grid.shrunk.prepared.toBranchCellBank.cell index))
    regular).trans
    ((annulus.sum_balance values.cellBoundary).trans
      (Polynomial.Geometry.Grid.WindowBoundary.Window.sum_cells_eq_boundary annulus.window values))

open Purelib.Curves in
open Purelib.Polynomial in
/-- Subtract the original-cell and Newton-band balances by cancelling their common hole.

The difference retains the complete correction between the actual outer and inner boundary walks. -/
theorem boundary_difference (outer : OriginalAnnularFaces grid index) (inner :
  Hyperelliptic.Meshes.Newton.Annulus.Faces.AnnularFaces grid index) (values : Geometry.Grid.CellBoundary.EdgeValues) :
    Geometry.Grid.CellBoundary.sumValues (fun face => values.walk face.boundary) outer.faces -
      Geometry.Grid.CellBoundary.sumValues (fun face => values.walk face.boundary) inner.faces =
        values.walk outer.window.boundary - values.walk inner.boundary := by
  rw [← outer.boundary_balance values, ← inner.boundary_balance values]
  ring1

/-- Select the retained regular faces inside the original cell and outside the closed Newton band. -/
@[expose] def between (outer : OriginalAnnularFaces grid index) : List (RegularFace
  grid.shrunk.prepared.toBranchCellBank) :=
  outer.faces.filter (fun face => decide (¬face.cell.box.Refines (grid.bands.box index)))

open Purelib.Curves in
open Purelib.Data in
open Purelib.Polynomial in
open Purelib.Geometry in
/-- The intervening faces and band faces partition the original annular sum. -/
theorem between_partition (outer : OriginalAnnularFaces grid index) (inner :
  Hyperelliptic.Meshes.Newton.Annulus.Faces.AnnularFaces grid index)
    (value : RegularFace grid.shrunk.prepared.toBranchCellBank → Gaussian.Basic.Canonical) :
    Geometry.Grid.CellBoundary.sumValues value outer.between + Geometry.Grid.CellBoundary.sumValues value inner.faces =
      Geometry.Grid.CellBoundary.sumValues value outer.faces := by
  rw [between, Geometry.Grid.WindowBoundary.sumValues_filter, outer.faces_eq, inner.faces_eq]
  rw [Geometry.Grid.WindowBoundary.sumValues_filter, Geometry.Grid.WindowBoundary.sumValues_filter,
    Geometry.Grid.WindowBoundary.sumValues_filter, ← Geometry.Grid.CellBoundary.sumValues_add]
  apply Geometry.Grid.CellBoundary.sumValues_congr
  intro face _
  by_cases band : face.cell.box.Refines (grid.bands.box index)
  · have original : face.cell.box.Refines (original.cell index).box := band.trans
      (Geometry.Rational.Box.Refinement.StrictInterior.refines (grid.bands.strict_original index))
    rw [if_pos original, if_neg (not_not_intro band), if_pos band, if_pos original]
    exact Gaussian.Basic.zero_add _
  · by_cases original : face.cell.box.Refines (original.cell index).box
    · rw [if_pos original, if_pos band, if_neg band, if_pos original]
      exact Gaussian.Basic.add_zero _
    · rw [if_neg original, if_neg band, if_neg original]
      exact Gaussian.Basic.add_zero _

open Purelib.Curves in
open Purelib.Polynomial in
/-- The intervening face-boundary sum equals the outer boundary minus the Newton-band boundary.

Every intermediate cut in the actual refined grid remains part of this finite incidence identity. -/
theorem between_boundary (outer : OriginalAnnularFaces grid index) (inner :
  Hyperelliptic.Meshes.Newton.Annulus.Faces.AnnularFaces grid index) (values : Geometry.Grid.CellBoundary.EdgeValues) :
    Geometry.Grid.CellBoundary.sumValues (fun face => values.walk face.boundary) outer.between =
      values.walk outer.window.boundary - values.walk inner.boundary := by
  have partition := outer.between_partition inner (fun face => values.walk face.boundary)
  rw [← outer.boundary_difference inner values, ← partition]
  ring1

end OriginalAnnularFaces
end Purelib.Riemann.RootContinuation.NewtonOriginalAnnularFaces

end
