module
meta import Mathlib.Tactic.Linter.Lint
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.List.Flatten
import Purelib.Data.List.Map
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Polynomial.Geometry.Grid.AxisNeighbors
import Purelib.Polynomial.Geometry.Grid.ClearGrid
public import Purelib.Polynomial.Geometry.Grid.FramedClearGrid
public import Purelib.Polynomial.Geometry.Grid.VertexCellSteps
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.VertexLiftChoices
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Geometry.Grid.VertexStar
import Purelib.Tactic.QuotientFreeOmega

open Purelib.Polynomial.Geometry.Grid.ClearGrid (HorizontalLine Interval VerticalLine)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)

public section

/-!
# One or two retained cells beside each actual grid edge

The fixed-axis neighborhood supplies exact side geometry. A singleton has
both endpoints on the enclosing frame; a pair contains distinct cells.
Reversal reuses the candidates and swaps the endpoint evidence. Root and
branch classification are deliberately left to the cached punctured-grid
consumer, not recomputed by this finite geometric construction.
-/

namespace Purelib

open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib

open Purelib.Data.Gaussian.Components.Basic (point)

variable {polynomial : Geometry.ClearPath.GaussianPolynomial} {ambient : Box} {grid :
  Polynomial.Geometry.Grid.ClearGrid polynomial ambient}

namespace Riemann.Meshes.GridLiftedDualSteps.GridSide

/-- The starting endpoint of an oriented grid side is a corner of its cell. -/
theorem start_corner (side :
  GridSide) (cell : Geometry.Grid.ClearGrid.Cell polynomial ambient) : cell.IsCorner
  (side.start cell.box) := by
  cases side
  · exact ⟨Or.inl rfl, Or.inl rfl⟩
  · exact ⟨Or.inr rfl, Or.inl rfl⟩
  · exact ⟨Or.inr rfl, Or.inr rfl⟩
  · exact ⟨Or.inl rfl, Or.inr rfl⟩

/-- The finishing endpoint of an oriented grid side is a corner of its cell. -/
theorem finish_corner (side :
  GridSide) (cell : Geometry.Grid.ClearGrid.Cell polynomial ambient) : cell.IsCorner
  (side.finish cell.box) :=
  (side.start_next cell.box) ▸ side.next.start_corner cell

end Riemann.Meshes.GridLiftedDualSteps.GridSide

namespace Polynomial.Geometry.Grid.EdgeSides

set_option genInjectivity false in
/-- A cell side with the orientation of the requested grid edge. -/
structure EdgeCell (grid : ClearGrid polynomial ambient) (start finish : Gaussian.Basic.Canonical)
  where
  /-- The cell incident to the retained oriented edge. -/ cell : Geometry.Grid.ClearGrid.Cell polynomial ambient
  /-- The incident cell belongs to the original grid. -/ member : cell ∈ grid.cells
  /-- The original cell side underlying this edge. -/ side : GridSide
  /-- Whether the edge reverses the orientation of its retained cell side. -/ reversed : Bool
  /-- The edge's start is the retained side endpoint selected by its orientation. -/ start_eq : (if reversed then
    side.finish cell.box else side.start cell.box) = start
  /-- The edge's finish is the opposite retained side endpoint. -/ finish_eq : (if reversed then side.start cell.box
    else side.finish cell.box) = finish

constructive_injectivity EdgeCell

end Polynomial.Geometry.Grid.EdgeSides

namespace Polynomial.Geometry.Grid.EdgeSides.EdgeCell

variable {start finish : Gaussian.Basic.Canonical}

/-- Reverse the retained edge orientation while keeping its original cell and side.

Negating the stored Boolean orientation swaps the two certified endpoints.
The same cell, grid membership and original side remain in the reversed record. -/
@[expose] def reverse (edge : EdgeCell grid start finish) : EdgeCell
  grid finish start :=
  ⟨edge.cell, edge.member, edge.side, !edge.reversed,
    by
      have equality := edge.finish_eq
      cases equal : edge.reversed
      · change edge.side.finish edge.cell.box = finish
        change
          (if edge.reversed then edge.side.start edge.cell.box else edge.side.finish edge.cell.box) = finish at equality
        rewrite [equal] at equality
        exact equality
      · change edge.side.start edge.cell.box = finish
        change
          (if edge.reversed then edge.side.start edge.cell.box else edge.side.finish edge.cell.box) = finish at equality
        rewrite [equal] at equality
        exact equality,
    by
      have equality := edge.start_eq
      cases equal : edge.reversed
      · change edge.side.start edge.cell.box = start
        change
          (if edge.reversed then edge.side.finish edge.cell.box else edge.side.start edge.cell.box) = start at equality
        rewrite [equal] at equality
        exact equality
      · change edge.side.finish edge.cell.box = start
        change
          (if edge.reversed then edge.side.finish edge.cell.box else edge.side.start edge.cell.box) = start at equality
        rewrite [equal] at equality
        exact equality⟩

/-- Retain the starting vertex as an incident corner of the edge's cell. -/
@[expose] def first (edge : EdgeCell grid start finish) :
  Geometry.Grid.VertexCellSteps.IncidentCell grid start :=
  ⟨edge.cell, edge.member, by
    apply Eq.mp (congrArg edge.cell.IsCorner edge.start_eq)
    cases edge.reversed
    · exact edge.side.start_corner edge.cell
    · exact edge.side.finish_corner edge.cell⟩

/-- Retain the finishing vertex as an incident corner of the edge's cell. -/
@[expose] def last (edge : EdgeCell grid start finish) :
  Geometry.Grid.VertexCellSteps.IncidentCell grid finish := edge.reverse.first

/-- Retained horizontal and vertical intervals determine a grid cell.

The original grid cells enumerate the same two interval lists. Their supplied
membership certificates identify this exact paired cell in that enumeration. -/
theorem cell_member {cell : Geometry.Grid.ClearGrid.Cell polynomial ambient}
    (horizontal : cell.horizontal ∈ grid.xIntervals) (vertical : cell.vertical ∈ grid.yIntervals) : cell ∈ grid.cells :=
  Data.List.Flatten.mem_flatMap.mpr ⟨cell.horizontal, horizontal,
    Data.List.Map.mem_map.mpr ⟨cell.vertical, vertical, rfl⟩⟩

/-- Attach a left-to-right horizontal edge to its incident cell.

The endpoint flag selects the bottom side or the reversed top side of the retained vertical interval. -/
@[expose] def horizontal
    (interval : Interval (VerticalLine.coordinate (polynomial :=
      polynomial) (ambient := ambient)))
    (member : interval ∈ grid.xIntervals) (y : Fraction.Rational) (upper : Bool)
    (neighbor : Geometry.Grid.AxisNeighbors.AtEndpoint grid.yIntervals y upper) :
    EdgeCell grid (point interval.lower.coordinate y) (point interval.upper.coordinate y) :=
  match upper, neighbor with
  | false, neighbor => ⟨⟨interval, neighbor.interval⟩, cell_member member neighbor.member, .bottom, false,
      congrArg (point interval.lower.coordinate) neighbor.endpoint_eq,
      congrArg (point interval.upper.coordinate) neighbor.endpoint_eq⟩
  | true, neighbor => ⟨⟨interval, neighbor.interval⟩, cell_member member neighbor.member, .top, true,
      congrArg (point interval.lower.coordinate) neighbor.endpoint_eq,
      congrArg (point interval.upper.coordinate) neighbor.endpoint_eq⟩

/-- Attach a bottom-to-top vertical edge to its incident cell.

The endpoint flag selects the right side or the reversed left side of the retained horizontal interval. -/
@[expose] def vertical
    (interval : Interval (HorizontalLine.coordinate (polynomial :=
      polynomial) (ambient := ambient)))
    (member : interval ∈ grid.yIntervals) (x : Fraction.Rational) (upper : Bool)
    (neighbor : Geometry.Grid.AxisNeighbors.AtEndpoint grid.xIntervals x upper) :
    EdgeCell grid (point x interval.lower.coordinate) (point x interval.upper.coordinate) :=
  match upper, neighbor with
  | false, neighbor => ⟨⟨neighbor.interval, interval⟩, cell_member neighbor.member member, .left, true,
      congrArg (fun x => point x interval.lower.coordinate) neighbor.endpoint_eq,
      congrArg (fun x => point x interval.upper.coordinate) neighbor.endpoint_eq⟩
  | true, neighbor => ⟨⟨neighbor.interval, interval⟩, cell_member neighbor.member member, .right, false,
      congrArg (fun x => point x interval.lower.coordinate) neighbor.endpoint_eq,
      congrArg (fun x => point x interval.upper.coordinate) neighbor.endpoint_eq⟩

end Polynomial.Geometry.Grid.EdgeSides.EdgeCell

namespace Polynomial.Geometry.Grid

namespace EdgeSides

/-- One coordinate of the point equals an ambient boundary coordinate. -/
@[expose] def OnFrame (ambient : Box) (point : Gaussian.Basic.Canonical) : Prop :=
  point.re = ambient.xLower ∨ point.re = ambient.xUpper ∨ point.im = ambient.yLower ∨ point.im = ambient.yUpper

end EdgeSides

set_option genInjectivity false in
/-- The incident cells of an oriented grid edge.

A frame edge retains one cell and frame membership of both endpoints; an interior edge retains two distinct incident
cells. -/
inductive EdgeSides (grid : ClearGrid polynomial ambient) (start finish : Gaussian.Basic.Canonical)
  where
  /-- One cell meets the edge and both edge endpoints lie on the ambient frame. -/ | single (cell :
    Geometry.Grid.EdgeSides.EdgeCell grid start finish) (firstFrame : EdgeSides.OnFrame ambient
    start) (lastFrame : EdgeSides.OnFrame ambient finish)
  /-- Two distinct retained cells meet the edge. -/ | pair (first second : Geometry.Grid.EdgeSides.EdgeCell grid start
    finish) (different : first.cell ≠ second.cell)

constructive_injectivity EdgeSides

namespace EdgeSides

variable {start finish : Gaussian.Basic.Canonical}

/-- Reverse an edge while retaining its one or two incident cells. -/
@[expose] def reverse : EdgeSides grid start finish →
  EdgeSides grid finish start
  | .single cell firstFrame lastFrame => .single cell.reverse lastFrame firstFrame
  | .pair first second different => .pair first.reverse second.reverse different

/-- A lone neighboring interval places the coordinate at a proper framed-axis endpoint.

The retained neighbor certificate distinguishes an endpoint from an interior
coordinate with two intervals. The supplied length equality excludes that
interior case without changing the coordinate or original frame bounds. -/
theorem endpoint_of_one {Alpha : Type} {key : Alpha → Fraction.Rational} {entries : List Alpha}
    {ordered : entries.Pairwise (fun first second => key first < key second)} {coordinate lower upper :
      Fraction.Rational}
    (found : Geometry.Grid.AxisNeighbors.Neighbors entries ordered coordinate) (one : found.intervals.length = 1)
    (lowerMember : lower ∈ entries.map key) (upperMember : upper ∈ entries.map key) (proper : lower < upper)
    (bounds : ∀ entry ∈ entries, lower ≤ key entry ∧ key entry ≤ upper) : coordinate = lower ∨ coordinate = upper := by
  rcases found.framed_size_cases lowerMember upperMember proper bounds with ⟨_, boundary⟩ | two
  · exact boundary
  · exact (by omega : False).elim

/-- The neighboring-interval list cannot be empty on a proper framed axis.

The retained lower and upper frame members and their strict ordering force one
or two neighboring intervals. Either original length contradicts the supplied
empty-list length certificate. -/
theorem not_singleton {Alpha : Type} {key : Alpha → Fraction.Rational} {entries : List Alpha}
    {ordered : entries.Pairwise (fun first second => key first < key second)} {coordinate lower upper :
      Fraction.Rational}
    (found : Geometry.Grid.AxisNeighbors.Neighbors entries ordered coordinate) (empty : found.intervals.length = 0)
    (lowerMember : lower ∈ entries.map key) (upperMember : upper ∈ entries.map key) (proper : lower < upper)
    (bounds : ∀ entry ∈ entries, lower ≤ key entry ∧ key entry ≤ upper) : False := by
  rcases found.framed_size_cases lowerMember upperMember proper bounds with ⟨one, _⟩ | two <;> omega

/-- Compute the one or two cells incident to a horizontal grid edge.

The vertical-axis neighbor certificate distinguishes a frame edge from two distinct interior cells. -/
@[expose] def horizontal (frame : FramedClearGrid.AmbientFrame grid) (proper : ambient.Proper)
    (interval : Interval (VerticalLine.coordinate (polynomial :=
      polynomial) (ambient := ambient)))
    (member : interval ∈ grid.xIntervals) (line : HorizontalLine polynomial ambient) (onAxis :
      line ∈ grid.horizontal) :
    EdgeSides grid (point interval.lower.coordinate line.coordinate) (point
      interval.upper.coordinate line.coordinate) :=
  match Geometry.Grid.AxisNeighbors.neighbors line.coordinate grid.horizontal grid.horizontal_ordered
    (Data.List.Map.mem_map_of_mem onAxis) with
  | .first after minimum =>
      let boundary := endpoint_of_one (.first after minimum) rfl frame.yLower frame.yUpper proper.2 (fun line _ =>
        line.inside)
      .single (Geometry.Grid.EdgeSides.EdgeCell.horizontal interval member line.coordinate false after) (Or.inr (Or.inr
        boundary)) (Or.inr (Or.inr boundary))
  | .last before maximum =>
      let boundary := endpoint_of_one (.last before maximum) rfl frame.yLower frame.yUpper proper.2 (fun line _ =>
        line.inside)
      .single (Geometry.Grid.EdgeSides.EdgeCell.horizontal interval member line.coordinate true before) (Or.inr (Or.inr
        boundary)) (Or.inr (Or.inr boundary))
  | .interior before after =>
      .pair (Geometry.Grid.EdgeSides.EdgeCell.horizontal interval member line.coordinate true before)
        (Geometry.Grid.EdgeSides.EdgeCell.horizontal interval member line.coordinate false after) (fun equal => by
          have lowerEq := congrArg (fun cell => cell.box.yLower) equal
          have strict := before.interval.ordered
          change before.interval.lower.coordinate = after.interval.lower.coordinate at lowerEq
          have afterEq : after.interval.lower.coordinate = line.coordinate := after.endpoint_eq
          have beforeEq : before.interval.upper.coordinate = line.coordinate := before.endpoint_eq
          rw [lowerEq, afterEq, beforeEq] at strict
          exact lt_irrefl _ strict)
  | .singleton only => (not_singleton (ordered := grid.horizontal_ordered)
      (.singleton only) rfl frame.yLower frame.yUpper proper.2 (fun line _ => line.inside)).elim

/-- Compute the one or two cells incident to a vertical grid edge.

The horizontal-axis neighbor certificate distinguishes a frame edge from two distinct interior cells. -/
@[expose] def vertical (frame : FramedClearGrid.AmbientFrame grid) (proper : ambient.Proper)
    (interval : Interval (HorizontalLine.coordinate (polynomial :=
      polynomial) (ambient := ambient)))
    (member : interval ∈ grid.yIntervals) (line : VerticalLine polynomial ambient) (onAxis :
      line ∈ grid.vertical) :
    EdgeSides grid (point line.coordinate interval.lower.coordinate) (point line.coordinate
      interval.upper.coordinate) :=
  match Geometry.Grid.AxisNeighbors.neighbors line.coordinate grid.vertical grid.vertical_ordered
    (Data.List.Map.mem_map_of_mem onAxis) with
  | .first after minimum =>
      let boundary := endpoint_of_one (.first after minimum) rfl frame.xLower frame.xUpper proper.1 (fun line _ =>
        line.inside)
      let boundaryPoint : ∀ y, OnFrame ambient (point line.coordinate y) := fun _ =>
        boundary.elim Or.inl (fun equal => Or.inr (Or.inl equal))
      .single (Geometry.Grid.EdgeSides.EdgeCell.vertical interval member line.coordinate false after) (boundaryPoint _)
        (boundaryPoint _)
  | .last before maximum =>
      let boundary := endpoint_of_one (.last before maximum) rfl frame.xLower frame.xUpper proper.1 (fun line _ =>
        line.inside)
      let boundaryPoint : ∀ y, OnFrame ambient (point line.coordinate y) := fun _ =>
        boundary.elim Or.inl (fun equal => Or.inr (Or.inl equal))
      .single (Geometry.Grid.EdgeSides.EdgeCell.vertical interval member line.coordinate true before) (boundaryPoint _)
        (boundaryPoint _)
  | .interior before after =>
      .pair (Geometry.Grid.EdgeSides.EdgeCell.vertical interval member line.coordinate true before)
        (Geometry.Grid.EdgeSides.EdgeCell.vertical interval member line.coordinate false after) (fun equal => by
          have lowerEq := congrArg (fun cell => cell.box.xLower) equal
          have strict := before.interval.ordered
          change before.interval.lower.coordinate = after.interval.lower.coordinate at lowerEq
          have afterEq : after.interval.lower.coordinate = line.coordinate := after.endpoint_eq
          have beforeEq : before.interval.upper.coordinate = line.coordinate := before.endpoint_eq
          rw [lowerEq, afterEq, beforeEq] at strict
          exact lt_irrefl _ strict)
  | .singleton only => (not_singleton (ordered := grid.vertical_ordered)
      (.singleton only) rfl frame.xLower frame.xUpper proper.1 (fun line _ => line.inside)).elim

/-- Compute incident cells for an oriented grid edge of a proper framed grid.

Horizontal and vertical cases use their original neighboring intervals; reversal transports the same retained cells. -/
@[expose] def build (frame : FramedClearGrid.AmbientFrame grid) (proper : ambient.Proper) : {start
  finish : Gaussian.Basic.Canonical} →
    Geometry.Grid.Walks.Edge grid start finish → EdgeSides grid start finish
  | _, _, .horizontal interval adjacent line member => horizontal frame proper interval adjacent line member
  | _, _, .vertical interval adjacent line member => vertical frame proper interval adjacent line member
  | _, _, .reverse edge => (build frame proper edge).reverse

end EdgeSides
end Polynomial.Geometry.Grid

end Purelib

end
