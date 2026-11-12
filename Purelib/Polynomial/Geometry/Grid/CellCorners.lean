module

public import Purelib.Polynomial.Geometry.Grid.CellBoundary
public import Purelib.Polynomial.Geometry.Grid.VertexStar
public import Purelib.Data.List.Search
import Purelib.Polynomial.Geometry.Grid.AxisNeighbors
import Purelib.Data.List.Map
import Purelib.Data.List.Flatten
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Basic

/-! # Actual first cell-corner occurrences on a retained clear grid

The grid's Cartesian cell list is computed metadata. Materialize it once,
retain its whole factory, and select the first actual corner occurrence.
Original axis neighbors prove existence from two distinct axis endpoints;
no root, Point, query or observation is acquired by this finite selection.
-/

public section

namespace Purelib.Polynomial.Geometry.Grid.ClearGrid

open Purelib
open Purelib.Data.List
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry.ClearPath (GaussianPolynomial)
open Purelib.Polynomial.Geometry.Grid

variable {polynomial : GaussianPolynomial} {ambient : Box}

namespace Cell

namespace IsCorner

/-- Corner incidence is exactly membership among the four literal ordered corner points. -/
theorem iff_vertices {cell : Cell polynomial ambient} {point : Canonical} :
    cell.IsCorner point ↔
      point = cell.cornerPoint 0 ∨ point = cell.cornerPoint 1 ∨
        point = cell.cornerPoint 2 ∨ point = cell.cornerPoint 3 := by
  constructor
  · intro corner
    rcases corner with ⟨lower | upper, bottom | top⟩
    · apply Or.inl
      rewrite [cell.cornerPoint_zero]
      exact Basic.ext lower.symm bottom.symm
    · apply Or.inr; apply Or.inr; apply Or.inr
      rewrite [cell.cornerPoint_three]
      exact Basic.ext lower.symm top.symm
    · apply Or.inr; apply Or.inl
      rewrite [cell.cornerPoint_one]
      exact Basic.ext upper.symm bottom.symm
    · apply Or.inr; apply Or.inr; apply Or.inl
      rewrite [cell.cornerPoint_two]
      exact Basic.ext upper.symm top.symm
  · intro corner
    rcases corner with first | second | third | fourth
    · rewrite [first, cell.cornerPoint_zero]
      exact ⟨Or.inl rfl, Or.inl rfl⟩
    · rewrite [second, cell.cornerPoint_one]
      exact ⟨Or.inr rfl, Or.inl rfl⟩
    · rewrite [third, cell.cornerPoint_two]
      exact ⟨Or.inr rfl, Or.inr rfl⟩
    · rewrite [fourth, cell.cornerPoint_three]
      exact ⟨Or.inl rfl, Or.inr rfl⟩

end IsCorner

/-- Decide original corner incidence through the four ordered scalar point comparisons.

The original coordinate predicate is retained. Only the proof payload is
transported; the finite search keeps its original four equality decisions.
-/
def decideCorner (cell : Cell polynomial ambient) (point : Canonical) : Decidable (cell.IsCorner point) :=
  match (inferInstance : Decidable (point = cell.cornerPoint 0 ∨ point = cell.cornerPoint 1 ∨
      point = cell.cornerPoint 2 ∨ point = cell.cornerPoint 3)) with
  | .isTrue accepted => .isTrue (Cell.IsCorner.iff_vertices.mpr accepted)
  | .isFalse rejected => .isFalse (fun accepted => rejected (Cell.IsCorner.iff_vertices.mp accepted))

/-- The corner decision preserves the original ordered-comparison Boolean at every input. -/
theorem decideCorner_readback (cell : Cell polynomial ambient) (point : Canonical) :
    @decide (cell.IsCorner point) (cell.decideCorner point) =
      decide (point = cell.cornerPoint 0 ∨ point = cell.cornerPoint 1 ∨
        point = cell.cornerPoint 2 ∨ point = cell.cornerPoint 3) := by
  by_cases accepted : point = cell.cornerPoint 0 ∨ point = cell.cornerPoint 1 ∨
      point = cell.cornerPoint 2 ∨ point = cell.cornerPoint 3
  · exact (@decide_eq_true (cell.IsCorner point) (cell.decideCorner point)
      (Cell.IsCorner.iff_vertices.mpr accepted)).trans (decide_eq_true accepted).symm
  · exact (@decide_eq_false (cell.IsCorner point) (cell.decideCorner point)
      (fun corner => accepted (Cell.IsCorner.iff_vertices.mp corner))).trans
        (decide_eq_false accepted).symm

/-- Select the first actual corner index using finite scalar decisions.

Only the equality branches decide the returned index. The accepted
geometric disjunction certifies the last branch; it supplies no runtime
witness and no root-owner comparison.
-/
def chooseCorner (cell : Cell polynomial ambient) (point : Canonical) (accepted : cell.IsCorner point) :
    {corner : Fin 4 // point = cell.cornerPoint corner} :=
  if first : point = cell.cornerPoint 0 then ⟨0, first⟩
  else if second : point = cell.cornerPoint 1 then ⟨1, second⟩
  else if third : point = cell.cornerPoint 2 then ⟨2, third⟩
  else ⟨3, (((Cell.IsCorner.iff_vertices.mp accepted).resolve_left first).resolve_left second).resolve_left third⟩

end Cell

section Existence

universe u
variable {Alpha : Type u} {key : Alpha → Rational}

/-- Distinct retained endpoint keys exclude the singleton-neighbor alternative. -/
private theorem endpoint_exists (entries : List Alpha)
    (ordered : entries.Pairwise (fun first last => key first < key last)) (point lower upper : Rational)
    (lowerMember : lower ∈ entries.map key) (upperMember : upper ∈ entries.map key)
    (proper : lower < upper) (member : point ∈ entries.map key) :
    ∃ interval ∈ Interval.adjacent entries ordered, key interval.lower = point ∨ key interval.upper = point := by
  cases AxisNeighbors.neighbors point entries ordered member with
  | first after _ => exact ⟨after.interval, after.member, Or.inl after.endpoint_eq⟩
  | last before _ => exact ⟨before.interval, before.member, Or.inr before.endpoint_eq⟩
  | interior before _ => exact ⟨before.interval, before.member, Or.inr before.endpoint_eq⟩
  | singleton only =>
      obtain ⟨first, firstMember, firstEq⟩ := Map.mem_map.mp lowerMember
      obtain ⟨last, lastMember, lastEq⟩ := Map.mem_map.mp upperMember
      have equal : lower = upper := firstEq.symm.trans
        ((only first firstMember).trans ((only last lastMember).symm.trans lastEq))
      exact (ne_of_lt proper equal).elim

/-- Genuine stored vertex incidence and proper axis endpoints give an actual cell-corner occurrence. -/
private theorem corner_exists (grid : ClearGrid polynomial ambient) (proper : ambient.Proper)
    (bounds : ambient.xLower ∈ grid.vertical.map VerticalLine.coordinate ∧
      ambient.xUpper ∈ grid.vertical.map VerticalLine.coordinate ∧
      ambient.yLower ∈ grid.horizontal.map HorizontalLine.coordinate ∧
      ambient.yUpper ∈ grid.horizontal.map HorizontalLine.coordinate)
    (point : Canonical) (member : FromStates.ContainsVertex grid point) :
    ∃ cell ∈ grid.cells, cell.IsCorner point := by
  obtain ⟨horizontal, horizontalMember, atLeft | atRight⟩ := endpoint_exists
    grid.vertical grid.vertical_ordered point.re ambient.xLower ambient.xUpper
    bounds.1 bounds.2.1 proper.1 member.1
  all_goals
    obtain ⟨vertical, verticalMember, atLower | atUpper⟩ := endpoint_exists
      grid.horizontal grid.horizontal_ordered point.im ambient.yLower ambient.yUpper
      bounds.2.2.1 bounds.2.2.2 proper.2 member.2
  all_goals
    let cell : Cell polynomial ambient := ⟨horizontal, vertical⟩
    have listed : cell ∈ grid.cells := Flatten.mem_flatMap.mpr
      ⟨horizontal, horizontalMember, Map.mem_map.mpr ⟨vertical, verticalMember, rfl⟩⟩
    refine ⟨cell, listed, Cell.IsCorner.iff_vertices.mpr ?_⟩
  · apply Or.inl
    rw [cell.cornerPoint_zero]
    exact Data.Gaussian.Basic.ext atLeft.symm atLower.symm
  · apply Or.inr; apply Or.inr; apply Or.inr
    rw [cell.cornerPoint_three]
    exact Data.Gaussian.Basic.ext atLeft.symm atUpper.symm
  · apply Or.inr; apply Or.inl
    rw [cell.cornerPoint_one]
    exact Data.Gaussian.Basic.ext atRight.symm atLower.symm
  · apply Or.inr; apply Or.inr; apply Or.inl
    rw [cell.cornerPoint_two]
    exact Data.Gaussian.Basic.ext atRight.symm atUpper.symm

end Existence

/-- One pure cell-list materialization, whole first occurrence, corner choice and original prefix.

The cell list is newly computed once, rather than treated as a stored grid
field. All later readers consume this retained list and selected metadata.
The returned walk is the same cell boundary's original ordered prefix.
-/
abbrev CornerLocation (grid : ClearGrid polynomial ambient) (point : Canonical) :=
  Σ cells : {value : List (Cell polynomial ambient) // value = grid.cells},
  Σ selected : {value : Search.Occurrence (fun cell : Cell polynomial ambient => cell.IsCorner point) cells.val //
    Search.firstOccurrence (fun cell => cell.IsCorner point)
      (fun cell => cell.decideCorner point) cells.val = some value},
  Σ corner : {value : {index : Fin 4 // point = selected.val.entry.cornerPoint index} //
    value = selected.val.entry.chooseCorner point selected.val.accepted},
  {walk : (finish : Canonical) × Walks.Walk grid selected.val.entry.box.anchor finish //
    walk = selected.val.entry.cornerPrefix
      (Eq.mp (congrArg (fun values => selected.val.entry ∈ values) cells.property) selected.val.member) corner.val.val}

/-- Materialize one actual cell-list value and retain its first accepted corner occurrence.

Proper retained axis endpoints make success constructive at every actual
stored vertex. No clearance or preparation is missing under these inputs;
all branch decisions concern finite coordinate metadata only.
-/
def locateCorner (grid : ClearGrid polynomial ambient) (proper : ambient.Proper)
    (bounds : ambient.xLower ∈ grid.vertical.map VerticalLine.coordinate ∧
      ambient.xUpper ∈ grid.vertical.map VerticalLine.coordinate ∧
      ambient.yLower ∈ grid.horizontal.map HorizontalLine.coordinate ∧
      ambient.yUpper ∈ grid.horizontal.map HorizontalLine.coordinate)
    (point : Canonical) (member : FromStates.ContainsVertex grid point) : CornerLocation grid point :=
  let cells := grid.cells
  let selected := Search.firstAccepted (fun cell : Cell polynomial ambient => cell.IsCorner point)
    (fun cell => cell.decideCorner point) cells (corner_exists grid proper bounds point member)
  let corner := selected.val.entry.chooseCorner point selected.val.accepted
  let walk := selected.val.entry.cornerPrefix selected.val.member corner.val
  ⟨⟨cells, rfl⟩, selected, ⟨corner, rfl⟩, ⟨walk, rfl⟩⟩

namespace CornerLocation

variable {grid : ClearGrid polynomial ambient} {point : Canonical} (located : CornerLocation grid point)

/-- Read the one newly materialized original Cartesian list. -/
abbrev cells : List (Cell polynomial ambient) := located.1.val

/-- Read the complete original first-match occurrence on that retained list. -/
abbrev selected : Search.Occurrence (fun cell : Cell polynomial ambient => cell.IsCorner point) located.cells :=
  located.2.1.val

/-- Read the SAME selected cell with all four original line payloads. -/
abbrev cell : Cell polynomial ambient := located.selected.entry

/-- Read the whole cached finite choice with its actual point-incidence certificate. -/
abbrev choice : {index : Fin 4 // point = located.cell.cornerPoint index} := located.2.2.1.val

/-- Read the cached finite corner choice. -/
abbrev corner : Fin 4 := located.2.2.1.val.val

/-- Read the complete original ordered prefix result without rerunning its factory. -/
abbrev walk : (finish : Canonical) × Walks.Walk grid located.cell.box.anchor finish := located.2.2.2.val

/-- The retained pure cell list is the whole original Cartesian factory. -/
theorem cells_eq : located.cells = grid.cells := located.1.property

/-- The complete selected occurrence is the actual first-match result on that SAME list. -/
theorem selected_eq : Search.firstOccurrence (fun cell : Cell polynomial ambient => cell.IsCorner point)
    (fun cell => cell.decideCorner point) located.cells = some located.selected := located.2.1.property

/-- The selected whole cell is a genuine member of the original grid-cell family. -/
theorem member : located.cell ∈ grid.cells :=
  Eq.mp (congrArg (fun values => located.cell ∈ values) located.cells_eq) located.selected.member

/-- The selected corner equality is geometric incidence only. -/
theorem point_eq : point = located.cell.cornerPoint located.corner := located.2.2.1.val.property

/-- The complete corner choice is its original finite scalar-decision result. -/
theorem corner_eq : located.choice = located.cell.chooseCorner point located.selected.accepted :=
  located.2.2.1.property

/-- The stored prefix is the original whole ordered corner-prefix factory. -/
theorem walk_eq : located.walk = located.cell.cornerPrefix located.member located.corner := located.2.2.2.property

/-- The SAME prefix finishes at this actual queried geometric point. -/
theorem walk_point : located.walk.1 = point :=
  (congrArg Sigma.fst located.walk_eq).trans
    ((located.cell.cornerPrefix_point located.member located.corner).trans located.point_eq.symm)

end CornerLocation

end Purelib.Polynomial.Geometry.Grid.ClearGrid

end
