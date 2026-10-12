module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Algebra.NatCast
import Purelib.Data.List.Filter
public import Purelib.RootIsolation.SquareRoot.Grid.Walk
import Purelib.Data.Rat.Fraction
public import Purelib.Algebra.Ring.IntCast
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Cast
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Path.Box.Sides
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchCellWinding
import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Walks
public import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathClosure
import Purelib.Riemann.Paths.PreparedPathWinding
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Polynomial.Geometry.Grid.WindowBoundary
import Init.Data.Int.Basic
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Field
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Path
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Algebra

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts

open Purelib.Curves.Hyperelliptic.Branches.BranchIsolation

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy

open Purelib.Data.Gaussian

open Purelib.Data.List

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Polynomial

open Purelib.Polynomial.Dense.Gaussian.Path.Box

open Purelib.Polynomial.Dense.Rational

open Purelib.Polynomial.Geometry

open Purelib.Polynomial.Geometry.Grid

open Purelib.Polynomial.Geometry.Grid.CellBoundary

open Purelib.Polynomial.Geometry.Grid.FromStates

open Purelib.Polynomial.Geometry.Grid.WindowBoundary

open Purelib.Riemann.Meshes

open Purelib.Riemann.Paths.PreparedPathClosure

open Purelib.Riemann.Paths.PreparedPathWinding

open Purelib.RootIsolation.SquareRoot.Grid

open Purelib.RootIsolation.SquareRoot.Grid.EdgeBank

public section

/-!
# A retained rectangular window counts its actual branch winding

The cached punctured-face partition determines the selected holes. Finite
cell cancellation proves that their count is the winding of the actual
subdivided boundary. Only the hole list, count and parity are executed;
the Cauchy-index calculation is used solely in the erased correctness proof.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WindowBranchWinding

open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Polynomial.Winding.Box.Basic (quadrupledBoxWinding)
open Purelib.Polynomial.Dense.Gaussian.Path.Box.Sides (horizontalEdge verticalEdge)
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid
open _root_.Purelib.Polynomial.Geometry.Grid.ClearGrid (Cell)
open Purelib.Polynomial.Geometry.Grid.CellBoundary (EdgeValues sumValues)
open Purelib.Polynomial.Geometry.Grid.WindowBoundary (sumValues_filter)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces FaceSplit)
open Purelib.Riemann.Paths.PreparedPathWinding.ClearSegment (rawWinding rawWinding_eq_coordinateWinding)
open Purelib.Riemann.Paths.PreparedPathWinding.ClearPath (rawWinding)

/-- Assign each original rational grid edge its exact doubled winding embedded as a Gaussian rational.

Each directional field keeps its displayed endpoints and orientation. The
integer embedding reads the same original rational coordinate-side winding. -/
@[expose] def windingValues (polynomial : ClearPath.GaussianPolynomial) : CellBoundary.EdgeValues where
  horizontal := fun first last y => ((Sides.horizontalEdge polynomial y first last).doubledWinding :
    Data.Gaussian.Basic.Canonical)
  vertical := fun x first last => ((Sides.verticalEdge polynomial x first last).doubledWinding :
    Data.Gaussian.Basic.Canonical)

/-- The assigned edge value equals the exact raw winding of the original oriented edge segment.

Horizontal and vertical edges use their original coordinate winding. Reversed
edges negate that same retained winding and its exact Gaussian embedding. -/
theorem windingValues_edge {polynomial : ClearPath.GaussianPolynomial} {ambient : Rational.Box} {grid :
  Polynomial.Geometry.Grid.ClearGrid polynomial ambient} :
    {start finish : Data.Gaussian.Basic.Canonical} → (edge : Walks.Edge grid start finish) →
      (windingValues polynomial).edge edge =
        (ClearSegment.rawWinding edge.segment : Data.Gaussian.Basic.Canonical)
  | _, _, .horizontal .. => by rw [ClearSegment.rawWinding_eq_coordinateWinding]; rfl
  | _, _, .vertical .. => by rw [ClearSegment.rawWinding_eq_coordinateWinding]; rfl
  | _, _, .reverse edge => by
      change -(windingValues polynomial).edge edge =
        (ClearSegment.rawWinding
          (ClearSegment.reverse edge.segment) : Data.Gaussian.Basic.Canonical)
      rw [windingValues_edge edge,
        ClearSegment.rawWinding_reverse]
      exact (show ((-ClearSegment.rawWinding edge.segment : Int) : Data.Gaussian.Basic.Canonical) =
        -(ClearSegment.rawWinding edge.segment : Data.Gaussian.Basic.Canonical) from
        Ring.IntCast.neg (ClearSegment.rawWinding edge.segment)).symm

/-- The retained edge-value sum equals the exact raw winding of the original grid walk.

Structural recursion keeps the displayed edge occurrences and their order.
Each head contributes its original raw winding before the retained tail sum. -/
theorem windingValues_walk {polynomial : ClearPath.GaussianPolynomial} {ambient : Rational.Box} {grid :
  Polynomial.Geometry.Grid.ClearGrid polynomial ambient} :
    {start finish : Data.Gaussian.Basic.Canonical} → (walk : Walks.Walk grid start finish) →
      (windingValues polynomial).walk walk =
        (ClearPath.rawWinding walk.path : Data.Gaussian.Basic.Canonical)
  | _, _, .nil _ => rfl
  | _, _, .cons edge tail => by
      change (windingValues polynomial).edge edge +
        (windingValues polynomial).walk tail =
        ((ClearSegment.rawWinding edge.segment +
          ClearPath.rawWinding tail.path : Int) : Data.Gaussian.Basic.Canonical)
      rw [windingValues_edge edge,
        windingValues_walk tail, Ring.IntCast.add]

/-- The original cell-boundary value equals its exact quadrupled box winding.

The four displayed sides retain their original coordinate directions. The
reverse top and left readings supply the same signed boundary sum. -/
theorem windingValues_cell {polynomial : ClearPath.GaussianPolynomial} {ambient : Rational.Box} (cell :
  ClearGrid.Cell polynomial ambient) :
    (windingValues polynomial).cellBoundary cell =
      (quadrupledBoxWinding polynomial cell.box : Data.Gaussian.Basic.Canonical) := by
  rw [Winding.Box.Basic.quadrupledBoxWinding_eq]
  have top : (Sides.horizontalEdge polynomial cell.box.yUpper cell.box.xUpper cell.box.xLower).doubledWinding =
      -(Sides.horizontalEdge polynomial cell.box.yUpper cell.box.xLower cell.box.xUpper).doubledWinding :=
    CauchyIndex.Basic.cauchyIndex2_reverse _ _ _ _
  have left : (Sides.verticalEdge polynomial cell.box.xLower cell.box.yUpper cell.box.yLower).doubledWinding =
      -(Sides.verticalEdge polynomial cell.box.xLower cell.box.yLower cell.box.yUpper).doubledWinding :=
    CauchyIndex.Basic.cauchyIndex2_reverse _ _ _ _
  rw [top, left]
  simp only [Ring.IntCast.add, EdgeValues.cellBoundary,
    windingValues,
    Data.Gaussian.Basic.Canonical.sub_eq_add_neg, -eq_self, -iff_self]
  have topCast : ((-(Sides.horizontalEdge polynomial cell.box.yUpper cell.box.xLower cell.box.xUpper).doubledWinding :
    Int) : Data.Gaussian.Basic.Canonical) =
      -((Sides.horizontalEdge polynomial cell.box.yUpper cell.box.xLower cell.box.xUpper).doubledWinding :
        Data.Gaussian.Basic.Canonical) :=
    Ring.IntCast.neg _
  have leftCast : ((-(Sides.verticalEdge polynomial cell.box.xLower cell.box.yLower cell.box.yUpper).doubledWinding :
    Int) : Data.Gaussian.Basic.Canonical) =
      -((Sides.verticalEdge polynomial cell.box.xLower cell.box.yLower cell.box.yUpper).doubledWinding :
        Data.Gaussian.Basic.Canonical) :=
    Ring.IntCast.neg _
  rw [topCast, leftCast]

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WindowBranchWinding

end

public section

namespace Purelib.Riemann.Meshes.PuncturedGridFaces.FaceSplit

open Purelib.Geometry.Rational (Box)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches.Cuts (Ambient)
open Purelib.Polynomial.Geometry.Grid.ClearGrid (Cell)
open Purelib.Polynomial.Geometry.Grid.CellBoundary (sumValues)
open Purelib.Polynomial.Winding.Box.Basic (quadrupledBoxWinding)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}

/-- The original selected-cell winding sum equals four times the number of retained branch holes inside the window.

Regular cells contribute zero. A retained branch-hole cell contributes four
exactly when its original containment decision accepts it. -/
theorem selected_winding (box : Rational.Box) :
    {cells : List (ClearGrid.Cell curve.polynomial (Cuts.Ambient curve))} → (split : FaceSplit bank cells) →
      CellBoundary.sumValues (fun cell => if cell.box.Refines box then (quadrupledBoxWinding curve.polynomial cell.box :
        Data.Gaussian.Basic.Canonical) else 0) cells =
        4 * ((split.holes.filter (fun hole => decide (hole.cell.box.Refines box))).length :
          Data.Gaussian.Basic.Canonical)
  | _, .nil => by change (0 : Data.Gaussian.Basic.Canonical) = 4 * 0; exact (mul_zero _).symm
  | _, .regular face tail => by
      change (if face.cell.box.Refines box then (quadrupledBoxWinding curve.polynomial face.cell.box :
        Data.Gaussian.Basic.Canonical) else 0) +
        CellBoundary.sumValues _ _ = _
      rw [face.winding_zero, Ring.IntCast.cast_zero]
      by_cases kept : face.cell.box.Refines box
      · rw [if_pos kept, zero_add]
        exact selected_winding box tail
      · rw [if_neg kept, zero_add]
        exact selected_winding box tail
  | _, .hole face tail => by
      change (if face.cell.box.Refines box then (quadrupledBoxWinding curve.polynomial face.cell.box :
        Data.Gaussian.Basic.Canonical) else 0) +
        CellBoundary.sumValues _ _ = _
      have winding : quadrupledBoxWinding curve.polynomial face.cell.box = 4 := by
        rw [face.cell_eq, BranchCellWinding.selected_winding_four bank]
      rw [winding, selected_winding box tail]
      by_cases kept : face.cell.box.Refines box
      · rw [if_pos kept]
        change (4 : Data.Gaussian.Basic.Canonical) + _ =
          4 * ((List.filter (fun hole => decide (hole.cell.box.Refines box)) (face :: tail.holes)).length :
            Data.Gaussian.Basic.Canonical)
        rw [Data.List.Filter.filter_cons_of_pos
          (predicate := fun hole : PuncturedGridFaces.BranchHole bank => decide (hole.cell.box.Refines box))
          (head := face) (tail := tail.holes) (decide_eq_true kept)]
        simp only [List.length_cons, Algebra.NatCast.add, Nat.cast_one, -eq_self, -iff_self]
        ring1
      · rw [if_neg kept, zero_add]
        change _ = 4 * ((List.filter (fun hole => decide (hole.cell.box.Refines box)) (face :: tail.holes)).length :
          Data.Gaussian.Basic.Canonical)
        rw [Data.List.Filter.filter_cons_of_neg
          (predicate := fun hole : PuncturedGridFaces.BranchHole bank => decide (hole.cell.box.Refines box))
          (head := face) (tail := tail.holes) (fun accepted => kept (of_decide_eq_true accepted))]

end Purelib.Riemann.Meshes.PuncturedGridFaces.FaceSplit

end

public section

namespace Purelib.Polynomial.Geometry.Grid.WindowBoundary.Window

open _root_.Purelib.Polynomial.Geometry.Grid.WindowBoundary (Window)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Geometry.Rational (Box)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Gaussian.Components.Basic (point)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Polynomial.Geometry.Grid.CellBoundary (sumValues sumValues_congr)
open Purelib.Riemann.Paths.PreparedPathWinding.ClearPath (rawWinding)
open Purelib.Polynomial.Winding.Box.Basic (quadrupledBoxWinding)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher} {box : Purelib.Geometry.Rational.Box}

set_option genInjectivity false in
/-- The exact holes, count and parity of one retained rectangular window.

The hole list is the original face-bank list filtered by containment. Its
retained length and oddness bit determine the same two-sheet boundary action. -/
structure BranchCount (faces : PuncturedGridFaces.PuncturedFaces bank) (window : Window bank.grid box) where
  /-- The cached original branch holes geometrically contained in the retained window. -/ holes : List
    (PuncturedGridFaces.BranchHole bank)
  /-- The cached holes are exactly the original face-bank holes filtered by window containment. -/ holes_eq : holes =
    faces.holes.filter (fun hole => decide (hole.cell.box.Refines box))
  /-- The cached finite number of original branch holes in this window. -/ count : Nat
  /-- The cached count equals the exact retained hole-list length. -/ count_eq : count = holes.length
  /-- The cached parity action of the original window boundary. -/ flip : Bool
  /-- The retained action bit equals the oddness test of the original hole count. -/ flip_eq : flip = decide (count % 2
    = 1)
  /-- The original subdivided window boundary has raw winding four times its retained hole count. -/ winding :
    ClearPath.rawWinding window.boundary.path = 4 * count

constructive_injectivity BranchCount

namespace BranchCount

variable {faces : PuncturedFaces bank} {window :
  Window bank.grid box}

open Purelib.Polynomial.Geometry.Grid.WindowBoundary.Window in
/-- Filter and cache the actual original window holes, their count and parity, and certify the exact original boundary
winding. -/
@[expose] def build (faces : PuncturedGridFaces.PuncturedFaces bank) (window : Window bank.grid box) :
  BranchCount faces window := by
  let holes := faces.holes.filter (fun hole => decide (hole.cell.box.Refines box))
  refine ⟨holes, rfl, holes.length, rfl, decide (holes.length % 2 = 1), rfl, ?_⟩
  have sum : CellBoundary.sumValues (fun cell => (quadrupledBoxWinding curve.polynomial cell.box :
    Data.Gaussian.Basic.Canonical)) window.cells =
      4 * (holes.length : Data.Gaussian.Basic.Canonical) := by
    rw [window.cells_eq, WindowBoundary.sumValues_filter]
    have selected := Riemann.Meshes.PuncturedGridFaces.FaceSplit.selected_winding box faces.split
    rw [← faces.holes_eq] at selected
    exact selected
  have boundary : (ClearPath.rawWinding window.boundary.path : Data.Gaussian.Basic.Canonical) =
      4 * (holes.length : Data.Gaussian.Basic.Canonical) := by
    rw [← Curves.Hyperelliptic.Meshes.PuncturedGrid.WindowBranchWinding.windingValues_walk,
      ← window.sum_cells_eq_boundary]
    exact (CellBoundary.sumValues_congr _ _ window.cells (fun cell _ =>
      Curves.Hyperelliptic.Meshes.PuncturedGrid.WindowBranchWinding.windingValues_cell cell)).trans sum
  have cast : (ClearPath.rawWinding window.boundary.path : Data.Gaussian.Basic.Canonical) =
      ((4 * (holes.length : Int) : Int) : Data.Gaussian.Basic.Canonical) := by
    rw [Ring.IntCast.intCast_mul, Int.cast_natCast]
    exact boundary
  have parts := congrArg (fun value : Data.Gaussian.Basic.Canonical => value.re) cast
  rw [Data.Gaussian.Cast.gaussian_int_re,
    Data.Gaussian.Cast.gaussian_int_re] at parts
  exact Fraction.Cast.Compatibility.intCast_injective_direct parts

/-- A retained selected hole is exactly an original face-bank hole contained in the same window. -/
theorem holes_member (count : BranchCount faces window) (hole :
  PuncturedGridFaces.BranchHole bank) :
    hole ∈ count.holes ↔ hole ∈ faces.holes ∧ hole.cell.box.Refines box := by
  constructor
  · intro member
    rw [count.holes_eq] at member
    have retained := Data.List.Filter.mem_filter.mp member
    exact ⟨retained.1, of_decide_eq_true retained.2⟩
  · intro retained
    rw [count.holes_eq]
    exact Data.List.Filter.mem_filter.mpr ⟨retained.1, decide_eq_true retained.2⟩

/-- The report identifies every selected original branch label, including the reverse direction from geometric
containment to the retained hole. -/
theorem selected_iff (count : BranchCount faces window) (index :
  Data.Index branches) :
    (∃ hole ∈ count.holes, hole.index = index) ↔ (bank.cell index).box.Refines box := by
  constructor
  · rintro ⟨hole, member, equal⟩
    have inside := ((count.holes_member hole).mp member).2
    rw [hole.cell_eq, equal] at inside
    exact inside
  · intro inside
    obtain ⟨hole, member, equal⟩ := faces.hole_complete index
    refine ⟨hole, (count.holes_member hole).mpr ⟨member, ?_⟩, equal⟩
    rw [hole.cell_eq, equal]
    exact inside

/-- Apply the retained original window's cached parity action to its starting sheet. -/
@[expose] def action (count : BranchCount faces window) (sheet : Fin
  2) : Fin 2 :=
  if count.flip then BranchCutLifts.otherSheet sheet else sheet

/-- The cached parity acts on the original shared root frames. No separate owner matching, winding evaluation or
successful scan is needed. -/
theorem target {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} (count :
  BranchCount faces window)
    (edges : RootEdgeBank frames) (sheet : Fin 2) :
    RootEdgeBank.target edges window.boundary sheet = count.action sheet := by
  have member : FromStates.ContainsVertex bank.grid (Components.Basic.point box.xLower box.yLower) :=
    ⟨window.left.coordinate_eq ▸ Map.mem_map_of_mem window.left.member,
      window.bottom.coordinate_eq ▸ Map.mem_map_of_mem window.bottom.member⟩
  by_cases odd : count.count % 2 = 1
  · have raw : ClearPath.rawWinding window.boundary.path =
        4 * (2 * (count.count / 2 : Nat) + 1 : Int) := by
      have winding := count.winding
      omega
    rw [RootEdgeBank.target_odd edges window.boundary member ((count.count / 2 : Nat) : Int) raw,
      action, count.flip_eq, decide_eq_true odd]
    rfl
  · have raw : ClearPath.rawWinding window.boundary.path =
        8 * (count.count / 2 : Nat) := by
      have winding := count.winding
      omega
    rw [RootEdgeBank.target_even edges (BranchCellBank.referenceAt bank _ member).toLoop
      window.boundary member ((count.count / 2 : Nat) : Int) raw,
      action, count.flip_eq, decide_eq_false odd]
    rfl

end BranchCount
end Purelib.Polynomial.Geometry.Grid.WindowBoundary.Window

end
