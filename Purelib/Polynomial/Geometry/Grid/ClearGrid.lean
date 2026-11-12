module
public import Purelib.Data.List.Membership

public import Purelib.Polynomial.Clearance.Box.Line.Restriction
import Purelib.Data.Rat.Fraction
public import Purelib.Data.List.Sort.RationalKey.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
public import Purelib.Polynomial.Clearance.Box.Boundary.Lines
import Purelib.Polynomial.Clearance.Box.Line.Basic
public import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Data.List.Sort.Key
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Refinement
public import Purelib.Geometry.Rational.Box.Separation
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# A shared finite grid of certified polynomial-clear lines

Sort the retained line certificates by their rational coordinates and remove
duplicate coordinates.  Adjacent coordinates define proper rectangles, with
quantitative clearance on every boundary.  The grid does not assert that a
rectangle's interior is branch-free: isolating branch faces is a separate
step, and boundary clearance alone must never be used for that conclusion.
-/

namespace Purelib.Polynomial.Geometry.Grid

open Purelib.Data.List

open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Polynomial

universe u

namespace ClearGrid

set_option genInjectivity false in
/-- A vertical line with an ambient coordinate bound and retained polynomial clearance.

The original polynomial and ambient box index the line certificate. Its stored coordinate and clearance are reused by
every adjacent cell that meets the line. -/
public structure VerticalLine (polynomial : ClearPath.GaussianPolynomial) (ambient : Box) where
  /-- The retained horizontal coordinate of the vertical line. -/ coordinate : Fraction.Rational
  /-- The coordinate lies between the ambient horizontal endpoints. -/ inside : ambient.xLower ≤ coordinate ∧ coordinate
    ≤ ambient.xUpper
  /-- Quantitative polynomial clearance along this exact vertical line. -/ clearance :
    Clearance.Box.Line.Basic.VerticalLineClearance polynomial ambient coordinate

constructive_injectivity VerticalLine

end ClearGrid

namespace ClearGrid.VerticalLine.mk

end ClearGrid.VerticalLine.mk

namespace ClearGrid.VerticalLine.mk

end ClearGrid.VerticalLine.mk

namespace ClearGrid

set_option genInjectivity false in
/-- A horizontal line with an ambient coordinate bound and retained polynomial clearance.

The original polynomial and ambient box index the line certificate. Its stored coordinate and clearance are reused by
every adjacent cell that meets the line. -/
public structure HorizontalLine (polynomial : ClearPath.GaussianPolynomial) (ambient : Box)
  where
  /-- The retained vertical coordinate of the horizontal line. -/ coordinate : Fraction.Rational
  /-- The coordinate lies between the ambient vertical endpoints. -/ inside : ambient.yLower ≤ coordinate ∧ coordinate ≤
    ambient.yUpper
  /-- Quantitative polynomial clearance along this exact horizontal line. -/ clearance :
    Clearance.Box.Line.Basic.HorizontalLineClearance polynomial ambient coordinate

constructive_injectivity HorizontalLine

end ClearGrid

namespace ClearGrid.HorizontalLine.mk

end ClearGrid.HorizontalLine.mk

namespace ClearGrid.HorizontalLine.mk

end ClearGrid.HorizontalLine.mk

namespace ClearGrid

set_option genInjectivity false in
/-- Two retained endpoint payloads in strict order under a rational key.

The interval preserves the original payloads rather than only their numerical coordinates. -/
public structure Interval {Alpha : Type u} (key : Alpha → Fraction.Rational) where
  /-- The retained lower endpoint payload. -/ lower : Alpha
  /-- The retained upper endpoint payload. -/ upper : Alpha
  /-- The lower key is strictly less than the upper key. -/ ordered : key lower < key upper

constructive_injectivity Interval

end ClearGrid

namespace ClearGrid.Interval.mk

end ClearGrid.Interval.mk

namespace ClearGrid.Interval.mk

end ClearGrid.Interval.mk

namespace ClearGrid.Interval

variable {Alpha : Type u} {key : Alpha → Fraction.Rational}

/-- The first interval's upper key is at most the second interval's lower key. -/
@[expose] public def Before (first second : Interval key) : Prop := key first.upper ≤ key
  second.lower

/-- Actual adjacent entries, retaining their endpoint payloads. -/
@[expose] public def adjacent : (entries : List Alpha) → entries.Pairwise (fun left right => key left < key right) →
  List (Interval key)
  | [], _ => []
  | [_], _ => []
  | lower :: upper :: remaining, ordered =>
      ⟨lower, upper, (List.pairwise_cons.mp ordered).1 upper List.mem_cons_self⟩ ::
        Interval.adjacent (upper :: remaining) (List.pairwise_cons.mp
          ordered).2

/-- Read an actual interval's two rational keys while preserving its direction and strict order. -/
public def coordinates (interval : Interval key) : Interval (id : Fraction.Rational → Fraction.Rational) :=
  ⟨key interval.lower, key interval.upper, interval.ordered⟩

/-- The coordinate interval retains the original lower key. -/
public theorem coordinates_lower (interval : Interval key) : interval.coordinates.lower = key interval.lower := by
  rfl

/-- The coordinate interval retains the original upper key. -/
public theorem coordinates_upper (interval : Interval key) : interval.coordinates.upper = key interval.upper := by
  rfl

/-- Mapping the SAME retained adjacent payloads to their keys preserves the complete ordered interval list.

Both supplied order proofs concern the displayed source and mapped banks.
The proof follows the original adjacent construction; no sorting, lookup
or coordinate-based reconstruction replaces the retained intervals.
-/
public theorem coordinates_adjacent : (entries : List Alpha) →
    (ordered : entries.Pairwise (fun first last => key first < key last)) →
    (mapped : (entries.map key).Pairwise (fun first last => first < last)) →
    (Interval.adjacent entries ordered).map coordinates = Interval.adjacent (entries.map key) mapped
  | [], _, _ => rfl
  | [_], _, _ => rfl
  | first :: second :: rest, ordered, mapped =>
      congrArg (List.cons (coordinates ⟨first, second, (List.pairwise_cons.mp ordered).1 second List.mem_cons_self⟩))
        (coordinates_adjacent (second :: rest) (List.pairwise_cons.mp ordered).2 (List.pairwise_cons.mp mapped).2)

/-- Each adjacent interval retains two entries from the original sorted list.

The head interval retains the first two entries; every later interval retains the corresponding tail occurrences. Both
endpoint membership witnesses refer to the original list. -/
public theorem endpoints_mem (entries : List Alpha) (ordered : entries.Pairwise (fun left right => key left < key
  right))
    {interval : Interval key} (member : interval ∈ adjacent
      entries ordered) :
    interval.lower ∈ entries ∧ interval.upper ∈ entries := by
  induction entries with
  | nil => exact (List.not_mem_nil member).elim
  | cons lower remaining ih =>
      cases remaining with
      | nil => exact (List.not_mem_nil member).elim
      | cons upper rest =>
          rcases Membership.mem_cons.mp member with equal | member
          · subst interval
            exact ⟨List.mem_cons_self, List.mem_cons_of_mem _ List.mem_cons_self⟩
          · have tail := ih _ member
            exact ⟨List.mem_cons_of_mem _ tail.1, List.mem_cons_of_mem _ tail.2⟩

/-- Adjacent intervals in a strictly sorted list are ordered without overlapping interiors.

The first upper endpoint is weakly bounded by every later lower endpoint. Strict ordering of the retained axis supplies
this bound, including equality at a shared endpoint. -/
public theorem adjacent_pairwise (entries : List Alpha) (ordered : entries.Pairwise (fun left right => key left < key
  right)) :
    (adjacent entries ordered).Pairwise Before := by
  induction entries with
  | nil => exact List.Pairwise.nil
  | cons lower remaining ih =>
      cases remaining with
      | nil => exact List.Pairwise.nil
      | cons upper rest =>
          have tailOrdered := (List.pairwise_cons.mp ordered).2
          apply List.Pairwise.cons _ (ih tailOrdered)
          intro interval member
          have starts := (endpoints_mem (upper :: rest) tailOrdered member).1
          rcases Membership.mem_cons.mp starts with equal | member
          · change key upper ≤ key interval.lower
            rewrite [equal]
            exact Fraction.Order.Basic.le_refl _
          · exact ((List.pairwise_cons.mp tailOrdered).1 interval.lower member).le

end ClearGrid.Interval

set_option genInjectivity false in
/-- Retained sorted axes.  Lookup is into finite data; no line certificate
is recomputed when constructing a grid edge or face.

Both axes retain their original polynomial and ambient box. Their strict coordinate ordering determines adjacent
intervals while the stored line certificates are reused. -/
public structure ClearGrid (polynomial : ClearPath.GaussianPolynomial) (ambient : Box) where
  /-- The retained list of vertical line certificates. -/ vertical : List (ClearGrid.VerticalLine
    polynomial ambient)
  /-- The retained list of horizontal line certificates. -/ horizontal : List (ClearGrid.HorizontalLine
    polynomial ambient)
  /-- Vertical coordinates are pairwise strictly increasing. -/ vertical_ordered : vertical.Pairwise (fun left right =>
    left.coordinate < right.coordinate)
  /-- Horizontal coordinates are pairwise strictly increasing. -/ horizontal_ordered : horizontal.Pairwise (fun left
    right => left.coordinate < right.coordinate)

constructive_injectivity ClearGrid

namespace ClearGrid.mk

end ClearGrid.mk

namespace ClearGrid.mk

end ClearGrid.mk

namespace ClearGrid

variable {polynomial : ClearPath.GaussianPolynomial} {ambient : Box}

/-- Sort and deduplicate both coordinate lists while retaining line certificates.

The returned axes have strictly increasing rational coordinates and use the original polynomial and ambient box. -/
@[expose] public def build (vertical : List (VerticalLine polynomial ambient)) (horizontal :
  List (HorizontalLine polynomial ambient)) :
    ClearGrid polynomial ambient :=
  ⟨Sort.RationalKey.Basic.sort VerticalLine.coordinate vertical,
    Sort.RationalKey.Basic.sort HorizontalLine.coordinate horizontal,
    Sort.RationalKey.Basic.pairwise_sort _ _, Sort.RationalKey.Basic.pairwise_sort _ _⟩

/-- Grid construction preserves exactly the supplied vertical coordinate values. -/
public theorem build_vertical_coordinates (vertical : List (VerticalLine polynomial ambient))
    (horizontal : List (HorizontalLine polynomial ambient)) (coordinate : Fraction.Rational) :
    coordinate ∈ (build vertical horizontal).vertical.map
      VerticalLine.coordinate ↔
      coordinate ∈ vertical.map VerticalLine.coordinate := Sort.RationalKey.Basic.keys_sort _ _ _

/-- Grid construction preserves exactly the supplied horizontal coordinate values. -/
public theorem build_horizontal_coordinates (vertical : List (VerticalLine polynomial ambient))
    (horizontal : List (HorizontalLine polynomial ambient)) (coordinate : Fraction.Rational) :
    coordinate ∈ (build vertical horizontal).horizontal.map
      HorizontalLine.coordinate ↔
      coordinate ∈ horizontal.map HorizontalLine.coordinate := Sort.RationalKey.Basic.keys_sort _ _ _

/-- Retain consecutive vertical lines as the grid's horizontal intervals. -/
@[expose] public def xIntervals (grid : ClearGrid polynomial ambient) : List
  (Interval (VerticalLine.coordinate (polynomial := polynomial) (ambient
  := ambient))) :=
  Interval.adjacent grid.vertical grid.vertical_ordered

/-- Retain consecutive horizontal lines as the grid's vertical intervals. -/
@[expose] public def yIntervals (grid : ClearGrid polynomial ambient) : List
  (Interval (HorizontalLine.coordinate (polynomial := polynomial)
  (ambient := ambient))) :=
  Interval.adjacent grid.horizontal grid.horizontal_ordered

end ClearGrid

namespace ClearGrid

set_option genInjectivity false in
/-- One proper face of the grid, with its four cached line certificates.

The horizontal and vertical intervals retain the actual two pairs of line payloads. Their strict key ordering defines a
proper rectangle without replacing any clearance certificate. -/
public structure Cell (polynomial : ClearPath.GaussianPolynomial) (ambient : Box) where
  /-- The horizontal interval retaining the left and right vertical lines. -/ horizontal :
    Interval (VerticalLine.coordinate (polynomial := polynomial)
    (ambient := ambient))
  /-- The vertical interval retaining the bottom and top horizontal lines. -/ vertical :
    Interval (HorizontalLine.coordinate (polynomial := polynomial)
    (ambient := ambient))

constructive_injectivity Cell

end ClearGrid

namespace ClearGrid.Cell.mk

end ClearGrid.Cell.mk

namespace ClearGrid.Cell.mk

end ClearGrid.Cell.mk

namespace ClearGrid.Cell

variable {polynomial : ClearPath.GaussianPolynomial} {ambient : Box}

/-- Form the rational rectangle bounded by a cell's four retained lines. -/
@[expose] public def box (cell : Cell polynomial ambient) : Box where
  xLower := cell.horizontal.lower.coordinate
  xUpper := cell.horizontal.upper.coordinate
  yLower := cell.vertical.lower.coordinate
  yUpper := cell.vertical.upper.coordinate
  x_valid := cell.horizontal.ordered.le
  y_valid := cell.vertical.ordered.le

/-- Strict endpoint ordering makes the cell rectangle proper. -/
public theorem box_proper (cell : Cell polynomial ambient) : cell.box.Proper :=
  ⟨cell.horizontal.ordered, cell.vertical.ordered⟩

/-- Every cell rectangle lies within its retained ambient box. -/
public theorem box_refines (cell : Cell polynomial ambient) : cell.box.Refines ambient :=
  ⟨cell.horizontal.lower.inside.1, cell.horizontal.upper.inside.2,
    cell.vertical.lower.inside.1, cell.vertical.upper.inside.2⟩

/-- Restrict the original line certificates; their positive numeric bounds
are copied, not rediscovered by polynomial elimination. -/
@[expose] public def boundaryClearance (cell : Cell polynomial ambient) :
  Clearance.Box.Boundary.Basic.BoundaryClearance polynomial cell.box :=
  Clearance.Box.Boundary.Lines.boundaryOfLines
    (cell.horizontal.lower.clearance.restrict cell.box_refines)
    (cell.horizontal.upper.clearance.restrict cell.box_refines)
    (cell.vertical.lower.clearance.restrict cell.box_refines)
    (cell.vertical.upper.clearance.restrict cell.box_refines)

/-- Restrict the four original cell-side line payloads to that SAME cell box.

The two axes remain in their original strict order. Every restricted line
copies its original positive clearance bound; no sort, branch search or
interior-clearance assertion is performed.
-/
public def grid (cell : Cell polynomial ambient) : Grid.ClearGrid polynomial cell.box := by
  let left : VerticalLine polynomial cell.box :=
    ⟨cell.box.xLower, ⟨Fraction.Order.Basic.le_refl _, cell.box.x_valid⟩,
      cell.horizontal.lower.clearance.restrict cell.box_refines⟩
  let right : VerticalLine polynomial cell.box :=
    ⟨cell.box.xUpper, ⟨cell.box.x_valid, Fraction.Order.Basic.le_refl _⟩,
      cell.horizontal.upper.clearance.restrict cell.box_refines⟩
  let bottom : HorizontalLine polynomial cell.box :=
    ⟨cell.box.yLower, ⟨Fraction.Order.Basic.le_refl _, cell.box.y_valid⟩,
      cell.vertical.lower.clearance.restrict cell.box_refines⟩
  let top : HorizontalLine polynomial cell.box :=
    ⟨cell.box.yUpper, ⟨cell.box.y_valid, Fraction.Order.Basic.le_refl _⟩,
      cell.vertical.upper.clearance.restrict cell.box_refines⟩
  refine ⟨[left, right], [bottom, top], ?_, ?_⟩
  · apply List.Pairwise.cons
    · intro entry member
      have same := Purelib.Data.List.Membership.mem_singleton.mp member
      cases same
      exact cell.horizontal.ordered
    · exact List.Pairwise.cons (fun _ member => (List.not_mem_nil member).elim) List.Pairwise.nil
  · apply List.Pairwise.cons
    · intro entry member
      have same := Purelib.Data.List.Membership.mem_singleton.mp member
      cases same
      exact cell.vertical.ordered
    · exact List.Pairwise.cons (fun _ member => (List.not_mem_nil member).elim) List.Pairwise.nil

/-- The local vertical coordinates are the SAME original left and right cell coordinates. -/
public theorem grid_vertical_coordinates (cell : Cell polynomial ambient) :
    cell.grid.vertical.map VerticalLine.coordinate = [cell.box.xLower, cell.box.xUpper] := by rfl

/-- The local horizontal coordinates are the SAME original bottom and top cell coordinates. -/
public theorem grid_horizontal_coordinates (cell : Cell polynomial ambient) :
    cell.grid.horizontal.map HorizontalLine.coordinate = [cell.box.yLower, cell.box.yUpper] := by rfl

/-- Both local vertical payloads retain the original individual clearance bounds. -/
public theorem grid_vertical_bounds (cell : Cell polynomial ambient) :
    cell.grid.vertical.map (fun line => line.clearance.bound) =
      [cell.horizontal.lower.clearance.bound, cell.horizontal.upper.clearance.bound] := by rfl

/-- Both local horizontal payloads retain the original individual clearance bounds. -/
public theorem grid_horizontal_bounds (cell : Cell polynomial ambient) :
    cell.grid.horizontal.map (fun line => line.clearance.bound) =
      [cell.vertical.lower.clearance.bound, cell.vertical.upper.clearance.bound] := by rfl

/-- Ordered horizontal intervals separate two cell interiors. -/
public theorem horizontal_separated (first second : Cell polynomial ambient)
    (before : Interval.Before first.horizontal second.horizontal) : first.box.InteriorSeparated
      second.box :=
  Or.inl before

/-- Ordered vertical intervals separate two cell interiors. -/
public theorem vertical_separated (first second : Cell polynomial ambient)
    (before : Interval.Before first.vertical second.vertical) : first.box.InteriorSeparated
      second.box :=
  Or.inr (Or.inr (Or.inl before))

end ClearGrid.Cell

namespace ClearGrid

variable {polynomial : ClearPath.GaussianPolynomial} {ambient : Box}

/-- Column-major finite cells.  This list is suitable for materializing the
shared geometric triangulation, while each face retains the original lines. -/
@[expose] public def cells (grid : ClearGrid polynomial ambient) : List (Cell
  polynomial ambient) :=
  grid.xIntervals.flatMap fun horizontal => grid.yIntervals.map fun vertical => ⟨horizontal, vertical⟩

end ClearGrid

namespace ClearGrid.Cell

variable {polynomial : ClearPath.GaussianPolynomial} {ambient : Box}

/-- The restricted two-by-two axes have exactly one actual adjacent cell. -/
public theorem grid_cells_length (cell : Cell polynomial ambient) : cell.grid.cells.length = 1 := by rfl

/-- The sole actual retained local cell has the SAME original cell box under a whole grid-factory equation. -/
public theorem cachedCell_box (cell : Cell polynomial ambient) (retained : Grid.ClearGrid polynomial cell.box)
    (factory : retained = cell.grid) (bound : 0 < retained.cells.length) :
    (retained.cells[0]'bound).box = cell.box := by
  cases factory
  rfl

/-- Read the sole actual cell from the SAME retained local grid, keeping its exact membership and original box.

The grid's whole factory law pays the index bound and erased box proof.
The executable lookup consumes the supplied cached grid; no equality
elimination replaces it by another run of the restriction factory.
-/
public def cachedCell (cell : Cell polynomial ambient) (retained : Grid.ClearGrid polynomial cell.box)
    (factory : retained = cell.grid) :
    {value : Cell polynomial cell.box // value ∈ retained.cells ∧ value.box = cell.box} :=
  let count : retained.cells.length = 1 :=
    (congrArg (fun value : Grid.ClearGrid polynomial cell.box => value.cells.length) factory).trans
      cell.grid_cells_length
  let bound : 0 < retained.cells.length := Eq.mpr (congrArg (fun value : Nat => 0 < value) count)
    (of_decide_eq_true rfl : 0 < 1)
  let selected := retained.cells[0]'bound
  ⟨selected, List.getElem_mem bound, cell.cachedCell_box retained factory bound⟩

end ClearGrid.Cell

end Purelib.Polynomial.Geometry.Grid
