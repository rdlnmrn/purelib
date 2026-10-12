module
import Purelib.Data.List.Append
import Purelib.Data.List.Map
import Purelib.Data.List.Filter
import Purelib.Data.Nat.Multiplication
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Polynomial.Geometry.Grid.AxisWalks
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Polynomial.Geometry.Grid.WindowAxes
public import Purelib.Polynomial.Geometry.Grid.WindowBoundary
public import Purelib.Polynomial.Geometry.Grid.FramedClearGrid
import Purelib.Data.List.Sort.RationalKey.Size
import Mathlib.Algebra.Group.Nat.Defs
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.QuotientFreeOmega

/-!
# Request-independent counts for retained window tours

A frame adds two lines per axis, and each branch box adds two more. Sorting
can only decrease those counts. Actual window walks use subsets of the
retained adjacent intervals, including when a window degenerates.
-/

namespace Purelib.Polynomial.Geometry.Grid.WindowSize

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

public section

universe u

namespace Interval

/-- The adjacent-interval list is no longer than its original ordered entry list. -/
theorem adjacent_length_le {Alpha : Type u} {key : Alpha → Fraction.Rational}
    (entries : List Alpha) (ordered : entries.Pairwise (fun first last => key first < key last)) :
    (Geometry.Grid.ClearGrid.Interval.adjacent entries ordered).length ≤ entries.length := by
  induction entries with
  | nil => exact Nat.le_refl _
  | cons first tail ih =>
      cases tail with
      | nil => exact Nat.zero_le _
      | cons next tail => exact Nat.succ_le_succ (ih (List.pairwise_cons.mp ordered).2)

end Interval

section Grid

variable {polynomial : Geometry.ClearPath.GaussianPolynomial} {ambient box : Box} {grid :
  ClearGrid polynomial ambient}

/-- The grid cell count is the product of its two adjacent-interval counts.

The original cell enumeration visits each horizontal interval for every retained vertical interval, preserving the
Cartesian-product list order. -/
theorem cells_length (grid : ClearGrid polynomial ambient) :
    grid.cells.length = grid.xIntervals.length * grid.yIntervals.length := by
  change (grid.xIntervals.flatMap (fun x => grid.yIntervals.map (fun y => (⟨x, y⟩ : Geometry.Grid.ClearGrid.Cell
    polynomial ambient)))).length = _
  induction grid.xIntervals with
  | nil => exact (Nat.zero_mul _).symm
  | cons head tail ih =>
      change ((grid.yIntervals.map (fun y => (⟨head, y⟩ : Geometry.Grid.ClearGrid.Cell polynomial ambient))) ++
        tail.flatMap (fun x => grid.yIntervals.map (fun y => (⟨x, y⟩ : Geometry.Grid.ClearGrid.Cell polynomial
          ambient)))).length = _
      rw [Data.List.Append.length_append, Data.List.Map.length_map, ih, List.length_cons]
      rw [Data.Nat.Multiplication.right_distrib, Nat.one_mul, Nat.add_comm]

/-- This also bounds the classified hole list without a cardinality oracle
or any assumption about how the grid cells were classified.

Each adjacent-interval count is bounded by the corresponding retained line count. Their product is therefore bounded by
the square of the total line count. -/
theorem cells_length_le (grid : ClearGrid polynomial ambient) :
    grid.cells.length ≤ (grid.vertical.length + grid.horizontal.length) ^ 2 := by
  rw [cells_length grid, Data.Nat.Multiplication.pow_two]
  exact Nat.mul_le_mul
    ((Geometry.Grid.WindowSize.Interval.adjacent_length_le _ grid.vertical_ordered).trans (Nat.le_add_right _ _))
    ((Geometry.Grid.WindowSize.Interval.adjacent_length_le _ grid.horizontal_ordered).trans (Nat.le_add_left _ _))

namespace Walk

/-- Appending walks adds their edge counts. -/
theorem append_edgeCount : {start middle finish : Gaussian.Basic.Canonical} →
    (first : Geometry.Grid.Walks.Walk grid start middle) → (last : Geometry.Grid.Walks.Walk grid middle finish) →
    (first.append last).edgeCount = first.edgeCount + last.edgeCount
  | _, _, _, .nil _, _ => (Nat.zero_add _).symm
  | _, _, _, .cons _ tail, last => by
      change (tail.append last).edgeCount + 1 = tail.edgeCount + 1 + last.edgeCount
      rw [append_edgeCount tail last]
      omega

/-- Reversing a walk onto a suffix adds their edge counts. -/
theorem reverseOnto_edgeCount : {start middle finish : Gaussian.Basic.Canonical} →
    (walk : Geometry.Grid.Walks.Walk grid start middle) → (suffix : Geometry.Grid.Walks.Walk grid start finish) →
    (walk.reverseOnto suffix).edgeCount = walk.edgeCount + suffix.edgeCount
  | _, _, _, .nil _, _ => (Nat.zero_add _).symm
  | _, _, _, .cons edge tail, suffix => by
      rw [Geometry.Grid.Walks.Walk.reverseOnto,
        reverseOnto_edgeCount tail
          (.cons (.reverse edge) suffix)]
      change tail.edgeCount + (suffix.edgeCount + 1) = tail.edgeCount + 1 + suffix.edgeCount
      omega

/-- Reversing a walk preserves its edge count. -/
theorem reverse_edgeCount {start finish : Gaussian.Basic.Canonical} (walk : Geometry.Grid.Walks.Walk grid start finish)
  :
    walk.reverse.edgeCount = walk.edgeCount :=
  (reverseOnto_edgeCount walk (.nil start)).trans (Nat.add_zero _)

/-- Transporting endpoint indices preserves the edge count. -/
theorem castEndpoints_edgeCount {start finish first last : Gaussian.Basic.Canonical} (walk : Geometry.Grid.Walks.Walk
  grid start finish)
    (firstEq : start = first) (lastEq : finish = last) :
    (walk.castEndpoints firstEq lastEq).edgeCount = walk.edgeCount := by
  cases firstEq
  cases lastEq
  rfl

/-- A lifted horizontal walk has one edge for each retained axis interval. -/
theorem horizontalIncreasing_edgeCount (line : Geometry.Grid.ClearGrid.HorizontalLine polynomial ambient) (member : line
  ∈ grid.horizontal) :
    {start finish : Fraction.Rational} → (walk : Geometry.Grid.AxisWalks.IncreasingWalk grid.xIntervals start finish) →
    (Geometry.Grid.Walks.Walk.horizontalIncreasing line member walk).edgeCount = walk.edges.length
  | _, _, .nil _ => rfl
  | _, _, .cons _ _ tail => congrArg Nat.succ
    (horizontalIncreasing_edgeCount line member tail)

/-- A lifted vertical walk has one edge for each retained axis interval. -/
theorem verticalIncreasing_edgeCount (line : Geometry.Grid.ClearGrid.VerticalLine polynomial ambient) (member : line ∈
  grid.vertical) :
    {start finish : Fraction.Rational} → (walk : Geometry.Grid.AxisWalks.IncreasingWalk grid.yIntervals start finish) →
    (Geometry.Grid.Walks.Walk.verticalIncreasing line member walk).edgeCount = walk.edges.length
  | _, _, .nil _ => rfl
  | _, _, .cons _ _ tail => congrArg Nat.succ
    (verticalIncreasing_edgeCount line member tail)

end Walk

namespace Window

/-- The boundary contains twice the sum of the two cached axis-interval counts. -/
theorem boundary_edgeCount (window : WindowBoundary.Window grid box) :
    window.boundary.edgeCount = 2 * (window.x.edges.length + window.y.edges.length) := by
  simp only [WindowBoundary.Window.boundary,
    Walk.append_edgeCount,
    Walk.reverse_edgeCount,
    WindowBoundary.Window.horizontal,
    WindowBoundary.Window.vertical,
    Walk.castEndpoints_edgeCount,
    Walk.horizontalIncreasing_edgeCount,
    Walk.verticalIncreasing_edgeCount]
  omega

/-- Twice the total grid-line count bounds the window's subdivided boundary length.

Both retained axis walks select intervals from their original adjacent-interval lists. Filtering and adjacency do not
increase either line count. -/
theorem boundary_edgeCount_le (window : WindowBoundary.Window grid box) :
    window.boundary.edgeCount ≤ 2 * (grid.vertical.length + grid.horizontal.length) := by
  have xCount : window.x.edges.length ≤ grid.vertical.length := by
    have count := congrArg List.length (Geometry.Grid.WindowAxes.IncreasingWalk.edges_eq_filter
      (Geometry.Grid.ClearGrid.Interval.adjacent_pairwise _ grid.vertical_ordered) window.x)
    exact count.le.trans ((Data.List.Filter.length_filter_le _ _).trans
      (Geometry.Grid.WindowSize.Interval.adjacent_length_le _ grid.vertical_ordered))
  have yCount : window.y.edges.length ≤ grid.horizontal.length := by
    have count := congrArg List.length (Geometry.Grid.WindowAxes.IncreasingWalk.edges_eq_filter
      (Geometry.Grid.ClearGrid.Interval.adjacent_pairwise _ grid.horizontal_ordered) window.y)
    exact count.le.trans ((Data.List.Filter.length_filter_le _ _).trans
      (Geometry.Grid.WindowSize.Interval.adjacent_length_le _ grid.horizontal_ordered))
  rw [boundary_edgeCount window]
  omega

end Window

/-- The retained branch states contribute exactly two vertical sides per state.

Each original state supplies its two displayed vertical sides, and structural concatenation preserves their order and
multiplicity. -/
private theorem verticalSides_length (states : List (Geometry.Grid.FromStates.BranchState polynomial ambient)) :
    (states.flatMap Geometry.Grid.FromStates.verticalSides).length = 2 * states.length := by
  induction states with
  | nil => rfl
  | cons state tail ih =>
      change ([_ , _] ++ tail.flatMap _).length = _
      rw [Data.List.Append.length_append, ih]
      change 2 + 2 * tail.length = 2 * (tail.length + 1)
      omega

/-- The retained branch states contribute exactly two horizontal sides per state.

Each original state supplies its two displayed horizontal sides, and structural concatenation preserves their order and
multiplicity. -/
private theorem horizontalSides_length (states : List (Geometry.Grid.FromStates.BranchState polynomial ambient)) :
    (states.flatMap Geometry.Grid.FromStates.horizontalSides).length = 2 * states.length := by
  induction states with
  | nil => rfl
  | cons state tail ih =>
      change ([_ , _] ++ tail.flatMap _).length = _
      rw [Data.List.Append.length_append, ih]
      change 2 + 2 * tail.length = 2 * (tail.length + 1)
      omega

/-- The right side is fixed before the new branch coordinates are chosen.

The original grid contributes its retained lines, the frame contributes four lines, and every state contributes two
lines per axis. Sorting can only decrease the total. -/
theorem withFrame_lineCount (original : ClearGrid polynomial ambient)
    (clearance : Clearance.Box.Boundary.Basic.BoundaryClearance polynomial ambient)
    (states : List (Geometry.Grid.FromStates.BranchState polynomial ambient)) :
    (FramedClearGrid.withFrame original clearance states).vertical.length +
      (FramedClearGrid.withFrame original clearance states).horizontal.length ≤
      original.vertical.length + original.horizontal.length + 4 + 4 * states.length := open Purelib in by
  have xCount := Data.List.Sort.RationalKey.Size.sort_length_le Geometry.Grid.ClearGrid.VerticalLine.coordinate
    (original.vertical ++ (Geometry.Grid.FramedClearGrid.frameVertical clearance ++ states.flatMap
      Geometry.Grid.FromStates.verticalSides))
  have yCount := Data.List.Sort.RationalKey.Size.sort_length_le Geometry.Grid.ClearGrid.HorizontalLine.coordinate
    (original.horizontal ++ (Geometry.Grid.FramedClearGrid.frameHorizontal clearance ++ states.flatMap
      Geometry.Grid.FromStates.horizontalSides))
  have frameV : (Geometry.Grid.FramedClearGrid.frameVertical clearance).length = 2 := rfl
  have frameH : (Geometry.Grid.FramedClearGrid.frameHorizontal clearance).length = 2 := rfl
  simp only [Data.List.Append.length_append, frameV, verticalSides_length] at xCount
  simp only [Data.List.Append.length_append, frameH, horizontalSides_length] at yCount
  change _ ≤ original.vertical.length + (2 + 2 * states.length) at xCount
  change _ ≤ original.horizontal.length + (2 + 2 * states.length) at yCount
  exact (Nat.add_le_add xCount yCount).trans_eq (by omega)

end Grid
end
end Purelib.Polynomial.Geometry.Grid.WindowSize
