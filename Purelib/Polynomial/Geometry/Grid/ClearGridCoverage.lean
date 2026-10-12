module
import Purelib.Data.List.Membership

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
public import Purelib.Data.List.Flatten
public import Purelib.Data.List.Map
import Purelib.Data.List.Pairwise
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath

public import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Mathlib.Order.Defs.LinearOrder
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Separation
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Coverage and disjoint interiors of the shared clear-line grid

Location follows the stored sorted axes and returns actual adjacent line
payloads.  It neither enumerates the Cartesian product nor extracts an
executable witness from a propositional existence proof.  The resulting
rectangles cover the coordinate hull and have pairwise disjoint interiors.
-/

namespace Purelib.Polynomial.Geometry.Grid.ClearGridCoverage

open Purelib.Data.List

open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Polynomial

universe u

namespace Interval

variable {Alpha : Type u} {key : Alpha → Fraction.Rational}

/-- The query is between two distinct coordinates in the supplied finite
bank.  A singleton axis deliberately cannot satisfy this predicate.

The two membership witnesses and strict endpoint ordering refer to the original axis. Weak bounds include queries on
either endpoint while requiring two distinct keys. -/
@[expose] public def Spanned (entries : List Alpha) (point : Fraction.Rational) : Prop :=
  ∃ lower ∈ entries, ∃ upper ∈ entries, key lower < key upper ∧ key lower ≤ point ∧ point ≤ key upper

set_option genInjectivity false in
/-- An actual adjacent axis interval containing the query coordinate.

The record retains its membership in the original sorted axis and both weak containment inequalities. -/
public structure Located (entries : List Alpha) (ordered : entries.Pairwise (fun left right => key left < key right))
    (point : Fraction.Rational) where
  /-- The original adjacent interval selected by the scan. -/ interval : Geometry.Grid.ClearGrid.Interval key
  /-- The selected interval belongs to the adjacent intervals of the original axis. -/ member : interval ∈
    Geometry.Grid.ClearGrid.Interval.adjacent entries ordered
  /-- The query lies weakly between the selected interval's endpoints. -/ contains : key interval.lower ≤ point ∧ point
    ≤ key interval.upper

constructive_injectivity Located

namespace Located.mk

end Located.mk

namespace Located.mk

end Located.mk

/-- The empty coordinate bank cannot span any query. -/
public theorem not_spanned_nil (point : Fraction.Rational) : ¬Spanned (key := key) [] point := by
  rintro ⟨_, member, _⟩
  exact List.not_mem_nil member

/-- A singleton coordinate bank cannot span a query between distinct coordinates.

Both endpoint membership witnesses identify the sole retained entry. Their required strict ordering would compare that
same rational key with itself. -/
public theorem not_spanned_singleton (entry : Alpha) (point : Fraction.Rational) : ¬Spanned (key := key) [entry] point
  := by
  rintro ⟨lower, lowerMember, upper, upperMember, strict, _⟩
  have lowerEq := Membership.mem_singleton.mp lowerMember
  have upperEq := Membership.mem_singleton.mp upperMember
  subst lower
  subst upper
  exact (lt_irrefl _) strict

/-- The first coordinate of a strictly ordered axis lies at or before any query spanned by that axis.

The lower spanning entry is either the head or a later retained entry. Strict pairwise key ordering in the latter case
composes with its weak query bound. -/
public theorem head_le_query {head : Alpha} {rest : List Alpha} {point : Fraction.Rational}
    (ordered : (head :: rest).Pairwise (fun left right => key left < key right))
    (spanned : Geometry.Grid.ClearGridCoverage.Interval.Spanned (key := key) (head :: rest) point) : key head ≤ point :=
      by
  rcases spanned with ⟨lower, member, _, _, _, lowerBound, _⟩
  rcases Membership.mem_cons.mp member with equal | member
  · rw [equal]
    at lowerBound
    exact lowerBound
  · exact ((List.pairwise_cons.mp ordered).1 lower member).le.trans lowerBound

/-- A spanned query beyond the second coordinate remains spanned after dropping the first axis entry.

The original upper spanning entry cannot be the removed head. The second coordinate and that retained upper entry give
the new span with the same query and strict order. -/
public theorem tail_spanned {lower upper : Alpha} {rest : List Alpha} {point : Fraction.Rational}
    (ordered : (lower :: upper :: rest).Pairwise (fun left right => key left < key right))
    (spanned : Geometry.Grid.ClearGridCoverage.Interval.Spanned (key := key) (lower :: upper :: rest) point) (after :
      key upper < point) :
    Geometry.Grid.ClearGridCoverage.Interval.Spanned (key := key) (upper :: rest) point := by
  rcases spanned with ⟨_, _, last, member, _, _, lastBound⟩
  have lastMember : last ∈ upper :: rest := by
    rcases Membership.mem_cons.mp member with equal | member
    · rw [equal] at lastBound
      have headBefore := (List.pairwise_cons.mp ordered).1 upper List.mem_cons_self
      exact (not_lt_of_ge lastBound (headBefore.trans after)).elim
    · exact member
  exact ⟨upper, List.mem_cons_self, last, lastMember, after.trans_le lastBound, after.le, lastBound⟩

/-- A finite scan of one axis.  All successful comparisons use retained
line data; the proof-only span supplies no runtime choice operation.

The first interval whose upper key bounds the query is retained. Its endpoints, original-axis membership and containment
inequalities certify the selected finite occurrence. -/
@[expose] public def locate : (entries : List Alpha) →
    (ordered : entries.Pairwise (fun left right => key left < key right)) →
    (point : Fraction.Rational) → Geometry.Grid.ClearGridCoverage.Interval.Spanned (key := key) entries point →
      Geometry.Grid.ClearGridCoverage.Interval.Located entries ordered point
  | [], _, point, spanned => (Geometry.Grid.ClearGridCoverage.Interval.not_spanned_nil point spanned).elim
  | [entry], _, point, spanned =>
    (Geometry.Grid.ClearGridCoverage.Interval.not_spanned_singleton entry point spanned).elim
  | lower :: upper :: rest, ordered, point, spanned =>
      if before : point ≤ key upper then
        ⟨⟨lower, upper, (List.pairwise_cons.mp ordered).1 upper List.mem_cons_self⟩,
          List.mem_cons_self, Geometry.Grid.ClearGridCoverage.Interval.head_le_query ordered spanned, before⟩
      else
        let found := Purelib.Polynomial.Geometry.Grid.ClearGridCoverage.Interval.locate (upper :: rest)
          (List.pairwise_cons.mp ordered).2 point
          (Geometry.Grid.ClearGridCoverage.Interval.tail_spanned ordered spanned (lt_of_not_ge before))
        ⟨found.interval, List.mem_cons_of_mem _ found.member, found.contains⟩

end Interval

section Grid

variable {polynomial : Geometry.ClearPath.GaussianPolynomial} {ambient : Box}

/-- Cells sharing one horizontal interval have pairwise disjoint interiors when their vertical intervals are ordered. -/
private theorem column_pairwise
    (horizontal : Geometry.Grid.ClearGrid.Interval (Geometry.Grid.ClearGrid.VerticalLine.coordinate (polynomial :=
      polynomial) (ambient := ambient)))
    (verticals : List (Geometry.Grid.ClearGrid.Interval (Geometry.Grid.ClearGrid.HorizontalLine.coordinate (polynomial
      := polynomial) (ambient := ambient))))
    (ordered : verticals.Pairwise Geometry.Grid.ClearGrid.Interval.Before) :
    (verticals.map (fun vertical => (⟨horizontal, vertical⟩ : Geometry.Grid.ClearGrid.Cell polynomial
      ambient))).Pairwise
      (fun first second => first.box.InteriorSeparated second.box) := open Purelib in by
  induction verticals with
  | nil => exact List.Pairwise.nil
  | cons vertical rest ih =>
      apply List.Pairwise.cons _ (ih (List.pairwise_cons.mp ordered).2)
      intro cell member
      rcases Map.mem_map.mp member with ⟨next, nextMember, equal⟩
      rw [← equal]
      exact Geometry.Grid.ClearGrid.Cell.vertical_separated _ _ ((List.pairwise_cons.mp ordered).1 next nextMember)

/-- The Cartesian cells from two ordered interval lists have pairwise disjoint interiors.

Within a column the vertical intervals separate interiors. Across columns the horizontal interval ordering separates
them, preserving the original column-major cell list. -/
private theorem product_pairwise
    (horizontals : List (Geometry.Grid.ClearGrid.Interval (Geometry.Grid.ClearGrid.VerticalLine.coordinate (polynomial
      := polynomial) (ambient := ambient))))
    (verticals : List (Geometry.Grid.ClearGrid.Interval (Geometry.Grid.ClearGrid.HorizontalLine.coordinate (polynomial
      := polynomial) (ambient := ambient))))
    (horizontalOrdered : horizontals.Pairwise Geometry.Grid.ClearGrid.Interval.Before) (verticalOrdered :
      verticals.Pairwise Geometry.Grid.ClearGrid.Interval.Before) :
    (horizontals.flatMap fun horizontal => verticals.map fun vertical => (⟨horizontal, vertical⟩ :
      Geometry.Grid.ClearGrid.Cell polynomial ambient)).Pairwise
      (fun first second => first.box.InteriorSeparated second.box) := open Purelib in by
  induction horizontals with
  | nil => exact List.Pairwise.nil
  | cons horizontal rest ih =>
      rw [Flatten.flatMap_cons]
      apply Pairwise.pairwise_append (column_pairwise horizontal verticals
        verticalOrdered)
        (ih (List.pairwise_cons.mp horizontalOrdered).2)
      intro first firstMember second secondMember
      rcases Map.mem_map.mp firstMember with ⟨firstVertical, _, firstEq⟩
      rcases Flatten.mem_flatMap.mp secondMember with ⟨secondHorizontal, secondHorizontalMember, secondMember⟩
      rcases Map.mem_map.mp secondMember with ⟨secondVertical, _, secondEq⟩
      rw [← firstEq, ← secondEq]
      exact Geometry.Grid.ClearGrid.Cell.horizontal_separated _ _ ((List.pairwise_cons.mp horizontalOrdered).1
        secondHorizontal secondHorizontalMember)

/-- Shared sides are allowed; no two emitted face interiors overlap. -/
public theorem cells_pairwise (grid : ClearGrid polynomial ambient) :
    grid.cells.Pairwise (fun first second => first.box.InteriorSeparated second.box) :=
  product_pairwise grid.xIntervals grid.yIntervals
    (Geometry.Grid.ClearGrid.Interval.adjacent_pairwise _ _) (Geometry.Grid.ClearGrid.Interval.adjacent_pairwise _ _)

set_option genInjectivity false in
/-- An actual cell of the retained grid containing a displayed Gaussian point.

The result stores the cell, membership in the original Cartesian cell list and all four coordinate inequalities. -/
public structure Located (grid : ClearGrid polynomial ambient) (point : Gaussian.Basic.Canonical)
  where
  /-- The original Cartesian cell selected by the two axis scans. -/ cell : Geometry.Grid.ClearGrid.Cell polynomial
    ambient
  /-- The selected cell belongs to the original grid's cell list. -/ member : cell ∈ grid.cells
  /-- The selected cell contains the displayed query point. -/ contains : cell.box.Contains point

constructive_injectivity Located

namespace Located.mk

end Located.mk

namespace Located.mk

end Located.mk

/-- Locate one actual grid cell using two one-dimensional finite scans. -/
@[expose] public def locate (grid : ClearGrid polynomial ambient) (point : Gaussian.Basic.Canonical)
    (horizontal : Geometry.Grid.ClearGridCoverage.Interval.Spanned (key :=
      Geometry.Grid.ClearGrid.VerticalLine.coordinate) grid.vertical point.re)
    (vertical : Geometry.Grid.ClearGridCoverage.Interval.Spanned (key :=
      Geometry.Grid.ClearGrid.HorizontalLine.coordinate) grid.horizontal point.im) :
      Located grid point :=
  open Purelib in
    let x := Geometry.Grid.ClearGridCoverage.Interval.locate grid.vertical grid.vertical_ordered point.re horizontal
    let y := Geometry.Grid.ClearGridCoverage.Interval.locate grid.horizontal grid.horizontal_ordered point.im vertical
    { cell := ⟨x.interval, y.interval⟩
      member := Flatten.mem_flatMap.mpr ⟨x.interval, x.member, Map.mem_map.mpr ⟨y.interval, y.member, rfl⟩⟩
      contains := ⟨x.contains.1, x.contains.2, y.contains.1, y.contains.2⟩ }

end Grid

end Purelib.Polynomial.Geometry.Grid.ClearGridCoverage
