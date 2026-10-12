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
public structure VerticalLine (polynomial : Geometry.ClearPath.GaussianPolynomial) (ambient : Box) where
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
public structure HorizontalLine (polynomial : Geometry.ClearPath.GaussianPolynomial) (ambient : Box)
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
@[expose] public def Before (first second : Geometry.Grid.ClearGrid.Interval key) : Prop := key first.upper ≤ key
  second.lower

/-- Actual adjacent entries, retaining their endpoint payloads. -/
@[expose] public def adjacent : (entries : List Alpha) → entries.Pairwise (fun left right => key left < key right) →
  List (Geometry.Grid.ClearGrid.Interval key)
  | [], _ => []
  | [_], _ => []
  | lower :: upper :: remaining, ordered =>
      ⟨lower, upper, (List.pairwise_cons.mp ordered).1 upper List.mem_cons_self⟩ ::
        Purelib.Polynomial.Geometry.Grid.ClearGrid.Interval.adjacent (upper :: remaining) (List.pairwise_cons.mp
          ordered).2

/-- Each adjacent interval retains two entries from the original sorted list.

The head interval retains the first two entries; every later interval retains the corresponding tail occurrences. Both
endpoint membership witnesses refer to the original list. -/
public theorem endpoints_mem (entries : List Alpha) (ordered : entries.Pairwise (fun left right => key left < key
  right))
    {interval : Geometry.Grid.ClearGrid.Interval key} (member : interval ∈ Geometry.Grid.ClearGrid.Interval.adjacent
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
    (Geometry.Grid.ClearGrid.Interval.adjacent entries ordered).Pairwise Before := by
  induction entries with
  | nil => exact List.Pairwise.nil
  | cons lower remaining ih =>
      cases remaining with
      | nil => exact List.Pairwise.nil
      | cons upper rest =>
          have tailOrdered := (List.pairwise_cons.mp ordered).2
          apply List.Pairwise.cons _ (ih tailOrdered)
          intro interval member
          have starts := (Geometry.Grid.ClearGrid.Interval.endpoints_mem (upper :: rest) tailOrdered member).1
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
public structure ClearGrid (polynomial : Geometry.ClearPath.GaussianPolynomial) (ambient : Box) where
  /-- The retained list of vertical line certificates. -/ vertical : List (Geometry.Grid.ClearGrid.VerticalLine
    polynomial ambient)
  /-- The retained list of horizontal line certificates. -/ horizontal : List (Geometry.Grid.ClearGrid.HorizontalLine
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

variable {polynomial : Geometry.ClearPath.GaussianPolynomial} {ambient : Box}

/-- Sort and deduplicate both coordinate lists while retaining line certificates.

The returned axes have strictly increasing rational coordinates and use the original polynomial and ambient box. -/
@[expose] public def build (vertical : List (Geometry.Grid.ClearGrid.VerticalLine polynomial ambient)) (horizontal :
  List (Geometry.Grid.ClearGrid.HorizontalLine polynomial ambient)) :
    ClearGrid polynomial ambient :=
  ⟨Data.List.Sort.RationalKey.Basic.sort Geometry.Grid.ClearGrid.VerticalLine.coordinate vertical,
    Data.List.Sort.RationalKey.Basic.sort Geometry.Grid.ClearGrid.HorizontalLine.coordinate horizontal,
    Data.List.Sort.RationalKey.Basic.pairwise_sort _ _, Data.List.Sort.RationalKey.Basic.pairwise_sort _ _⟩

/-- Grid construction preserves exactly the supplied vertical coordinate values. -/
public theorem build_vertical_coordinates (vertical : List (Geometry.Grid.ClearGrid.VerticalLine polynomial ambient))
    (horizontal : List (Geometry.Grid.ClearGrid.HorizontalLine polynomial ambient)) (coordinate : Fraction.Rational) :
    coordinate ∈ (build vertical horizontal).vertical.map
      Geometry.Grid.ClearGrid.VerticalLine.coordinate ↔
      coordinate ∈ vertical.map VerticalLine.coordinate := Data.List.Sort.RationalKey.Basic.keys_sort _ _ _

/-- Grid construction preserves exactly the supplied horizontal coordinate values. -/
public theorem build_horizontal_coordinates (vertical : List (Geometry.Grid.ClearGrid.VerticalLine polynomial ambient))
    (horizontal : List (Geometry.Grid.ClearGrid.HorizontalLine polynomial ambient)) (coordinate : Fraction.Rational) :
    coordinate ∈ (build vertical horizontal).horizontal.map
      Geometry.Grid.ClearGrid.HorizontalLine.coordinate ↔
      coordinate ∈ horizontal.map HorizontalLine.coordinate := Data.List.Sort.RationalKey.Basic.keys_sort _ _ _

/-- Retain consecutive vertical lines as the grid's horizontal intervals. -/
@[expose] public def xIntervals (grid : ClearGrid polynomial ambient) : List
  (Geometry.Grid.ClearGrid.Interval (Geometry.Grid.ClearGrid.VerticalLine.coordinate (polynomial := polynomial) (ambient
  := ambient))) :=
  Geometry.Grid.ClearGrid.Interval.adjacent grid.vertical grid.vertical_ordered

/-- Retain consecutive horizontal lines as the grid's vertical intervals. -/
@[expose] public def yIntervals (grid : ClearGrid polynomial ambient) : List
  (Geometry.Grid.ClearGrid.Interval (Geometry.Grid.ClearGrid.HorizontalLine.coordinate (polynomial := polynomial)
  (ambient := ambient))) :=
  Geometry.Grid.ClearGrid.Interval.adjacent grid.horizontal grid.horizontal_ordered

end ClearGrid

namespace ClearGrid

set_option genInjectivity false in
/-- One proper face of the grid, with its four cached line certificates.

The horizontal and vertical intervals retain the actual two pairs of line payloads. Their strict key ordering defines a
proper rectangle without replacing any clearance certificate. -/
public structure Cell (polynomial : Geometry.ClearPath.GaussianPolynomial) (ambient : Box) where
  /-- The horizontal interval retaining the left and right vertical lines. -/ horizontal :
    Geometry.Grid.ClearGrid.Interval (Geometry.Grid.ClearGrid.VerticalLine.coordinate (polynomial := polynomial)
    (ambient := ambient))
  /-- The vertical interval retaining the bottom and top horizontal lines. -/ vertical :
    Geometry.Grid.ClearGrid.Interval (Geometry.Grid.ClearGrid.HorizontalLine.coordinate (polynomial := polynomial)
    (ambient := ambient))

constructive_injectivity Cell

end ClearGrid

namespace ClearGrid.Cell.mk

end ClearGrid.Cell.mk

namespace ClearGrid.Cell.mk

end ClearGrid.Cell.mk

namespace ClearGrid.Cell

variable {polynomial : Geometry.ClearPath.GaussianPolynomial} {ambient : Box}

/-- Form the rational rectangle bounded by a cell's four retained lines. -/
@[expose] public def box (cell : Geometry.Grid.ClearGrid.Cell polynomial ambient) : Box where
  xLower := cell.horizontal.lower.coordinate
  xUpper := cell.horizontal.upper.coordinate
  yLower := cell.vertical.lower.coordinate
  yUpper := cell.vertical.upper.coordinate
  x_valid := cell.horizontal.ordered.le
  y_valid := cell.vertical.ordered.le

/-- Strict endpoint ordering makes the cell rectangle proper. -/
public theorem box_proper (cell : Geometry.Grid.ClearGrid.Cell polynomial ambient) : cell.box.Proper :=
  ⟨cell.horizontal.ordered, cell.vertical.ordered⟩

/-- Every cell rectangle lies within its retained ambient box. -/
public theorem box_refines (cell : Geometry.Grid.ClearGrid.Cell polynomial ambient) : cell.box.Refines ambient :=
  ⟨cell.horizontal.lower.inside.1, cell.horizontal.upper.inside.2,
    cell.vertical.lower.inside.1, cell.vertical.upper.inside.2⟩

/-- Restrict the original line certificates; their positive numeric bounds
are copied, not rediscovered by polynomial elimination. -/
@[expose] public def boundaryClearance (cell : Geometry.Grid.ClearGrid.Cell polynomial ambient) :
  Clearance.Box.Boundary.Basic.BoundaryClearance polynomial cell.box :=
  Clearance.Box.Boundary.Lines.boundaryOfLines
    (cell.horizontal.lower.clearance.restrict cell.box_refines)
    (cell.horizontal.upper.clearance.restrict cell.box_refines)
    (cell.vertical.lower.clearance.restrict cell.box_refines)
    (cell.vertical.upper.clearance.restrict cell.box_refines)

/-- Ordered horizontal intervals separate two cell interiors. -/
public theorem horizontal_separated (first second : Geometry.Grid.ClearGrid.Cell polynomial ambient)
    (before : Geometry.Grid.ClearGrid.Interval.Before first.horizontal second.horizontal) : first.box.InteriorSeparated
      second.box :=
  Or.inl before

/-- Ordered vertical intervals separate two cell interiors. -/
public theorem vertical_separated (first second : Geometry.Grid.ClearGrid.Cell polynomial ambient)
    (before : Geometry.Grid.ClearGrid.Interval.Before first.vertical second.vertical) : first.box.InteriorSeparated
      second.box :=
  Or.inr (Or.inr (Or.inl before))

end ClearGrid.Cell

namespace ClearGrid

variable {polynomial : Geometry.ClearPath.GaussianPolynomial} {ambient : Box}

/-- Column-major finite cells.  This list is suitable for materializing the
shared geometric triangulation, while each face retains the original lines. -/
@[expose] public def cells (grid : ClearGrid polynomial ambient) : List (Geometry.Grid.ClearGrid.Cell
  polynomial ambient) :=
  grid.xIntervals.flatMap fun horizontal => grid.yIntervals.map fun vertical => ⟨horizontal, vertical⟩

end ClearGrid

end Purelib.Polynomial.Geometry.Grid
