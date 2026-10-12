module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.List.Map
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Extension
public import Purelib.Polynomial.Geometry.Grid.FramedClearGrid
import Purelib.Polynomial.Geometry.Grid.Incidence
import Purelib.Polynomial.Geometry.Grid.CellSeparation
public import Purelib.Polynomial.Geometry.Grid.Rectangle.Cuts
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Separation
import Purelib.Polynomial.Geometry.Grid.ClearGridCoverage

/-! Every cell of a coordinate-enlarged grid belongs to exactly one
original cell. The midpoint only locates it; retained axis incidence proves
containment of the entire fine cell, including its boundary. -/

namespace Purelib.Polynomial.Geometry.Grid.Inclusion.CellParents

open Purelib.Data
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.Data.List

variable {polynomial : Geometry.ClearPath.GaussianPolynomial} {ambient : Box} {original fine :
  ClearGrid polynomial ambient}

/-- An interval containing the common point refines a coarser interval whose
endpoints lie outside its interior.

Both outer endpoints lie outside the inner interval interior while containing
its strict interior query. Those inequalities force the displayed endpoint
refinement. -/
private theorem interval_refines {lower upper first last point : Purelib.Data.Rat.Fraction.Rational}
    (inside : lower < point ∧ point < upper) (contains : first ≤ point ∧ point ≤ last)
    (firstOutside : first ≤ lower ∨ upper ≤ first) (lastOutside : last ≤ lower ∨ upper ≤ last) :
    first ≤ lower ∧ upper ≤ last := by
  constructor
  · rcases firstOutside with bound | bound
    · exact bound
    · exact (not_lt_of_ge (bound.trans contains.1) inside.2).elim
  · rcases lastOutside with bound | bound
    · exact (not_lt_of_ge (contains.2.trans bound) inside.1).elim
    · exact bound

/-- An interior point locates the entire fine cell inside its coarse cell.

Inclusion of the coarse axis coordinates prevents any coarse boundary from
crossing the fine cell interior. -/
public theorem refines_of_interior (included : Geometry.Grid.Extension.CoordinateInclusion original fine)
    {small large : Geometry.Grid.ClearGrid.Cell polynomial ambient} (smallMember : small ∈ fine.cells) (largeMember :
      large ∈ original.cells)
    {point : Gaussian.Basic.Canonical} (inside : small.box.StrictContains point) (contains : large.box.Contains point) :
    small.box.Refines large.box := open Purelib in by
  have smallIntervals := Geometry.Grid.CellBoundary.Cell.intervals_mem small smallMember
  have largeIntervals := Geometry.Grid.CellBoundary.Cell.intervals_mem large largeMember
  have x := Geometry.Grid.ClearGrid.Interval.endpoints_mem _ original.vertical_ordered largeIntervals.1
  have y := Geometry.Grid.ClearGrid.Interval.endpoints_mem _ original.horizontal_ordered largeIntervals.2
  have xBounds := Geometry.Grid.Inclusion.CellParents.interval_refines ⟨inside.1, inside.2.1⟩ ⟨contains.1, contains.2.1⟩
    (Geometry.Grid.Incidence.Interval.coordinate_side fine.vertical fine.vertical_ordered smallIntervals.1
      (included.vertical _ (Data.List.Map.mem_map_of_mem x.1)))
    (Geometry.Grid.Incidence.Interval.coordinate_side fine.vertical fine.vertical_ordered smallIntervals.1
      (included.vertical _ (Data.List.Map.mem_map_of_mem x.2)))
  have yBounds := Geometry.Grid.Inclusion.CellParents.interval_refines inside.2.2 contains.2.2
    (Geometry.Grid.Incidence.Interval.coordinate_side fine.horizontal fine.horizontal_ordered smallIntervals.2
      (included.horizontal _ (Data.List.Map.mem_map_of_mem y.1)))
    (Geometry.Grid.Incidence.Interval.coordinate_side fine.horizontal fine.horizontal_ordered smallIntervals.2
      (included.horizontal _ (Data.List.Map.mem_map_of_mem y.2)))
  exact ⟨xBounds.1, xBounds.2, yBounds.1, yBounds.2⟩

set_option genInjectivity false in
/-- A retained coarse-grid parent containing the entire fine cell.

The certificate keeps the original coarse cell, its membership and the exact
box-refinement relation. -/
public structure Parent (original : ClearGrid polynomial ambient) (small :
  Geometry.Grid.ClearGrid.Cell polynomial ambient) where
  /-- The retained coarse-grid cell. -/ cell : Geometry.Grid.ClearGrid.Cell polynomial ambient
  /-- The retained parent belongs to the original coarse grid. -/ member : cell ∈ original.cells
  /-- The fine cell's box refines the retained parent box. -/ refines : small.box.Refines cell.box

constructive_injectivity Parent

/-- Locate a fine cell's center in a proper framed coarse grid and retain its
parent.

The coordinate inclusion and interior center witness certify containment of the
whole fine cell. -/
@[expose] public def parent (included : Geometry.Grid.Extension.CoordinateInclusion original fine) (frame :
  FramedClearGrid.AmbientFrame original) (proper : ambient.Proper)
    (small : Geometry.Grid.ClearGrid.Cell polynomial ambient) (member : small ∈ fine.cells) :
      Geometry.Grid.Inclusion.CellParents.Parent original small :=
  let center := Geometry.Grid.Rectangle.Cuts.center small.box
  let found := frame.locate proper center (small.box_refines.contains (Geometry.Grid.Rectangle.Cuts.center_inside
    small.box_proper))
  ⟨found.cell, found.member, Geometry.Grid.Inclusion.CellParents.refines_of_interior included member found.member
    (Geometry.Grid.Rectangle.Cuts.center_strict small.box_proper) found.contains⟩

/-- Distinct original cells cannot both own a positive-area fine cell. No equality
decision on the proof-bearing cell payloads is needed.

The proper fine cell has the original strict interior center. Refinement places
that same point strictly in one coarse cell and weakly in the other,
contradicting their displayed interior separation. -/
public theorem refinements_disjoint {first last small : Geometry.Grid.ClearGrid.Cell polynomial ambient}
    (separated : first.box.InteriorSeparated last.box)
    (left : small.box.Refines first.box) (right : small.box.Refines last.box) : False := by
  have center := Geometry.Grid.Rectangle.Cuts.center_strict small.box_proper
  have inFirst : first.box.StrictContains (Geometry.Grid.Rectangle.Cuts.center small.box) :=
    ⟨left.1.trans_lt center.1, center.2.1.trans_le left.2.1,
      left.2.2.1.trans_lt center.2.2.1, center.2.2.2.trans_le left.2.2.2⟩
  have inLast := right.contains center.contains
  rcases separated with before | after | below | above
  · exact (lt_irrefl _) (inFirst.2.1.trans_le (before.trans inLast.1))
  · exact (lt_irrefl _) ((inLast.2.1.trans after).trans_lt inFirst.1)
  · exact (lt_irrefl _) (inFirst.2.2.2.trans_le (below.trans inLast.2.2.1))
  · exact (lt_irrefl _) ((inLast.2.2.2.trans above).trans_lt inFirst.2.2.1)

end Purelib.Polynomial.Geometry.Grid.Inclusion.CellParents
