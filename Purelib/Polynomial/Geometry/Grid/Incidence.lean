module
import Purelib.Data.List.Membership
import Purelib.Data.Rat.Fraction
import Purelib.Data.List.Flatten
import Purelib.Data.List.Map
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath

public import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Refinement

/-!
# Grid faces respect every retained box boundary

No retained coordinate lies strictly inside an adjacent coordinate interval.
Consequently a grid face containing a strict subbox of an original retained
rectangle is wholly contained in that rectangle.  This prevents branch-cell
location from assigning one branch to a face spanning another branch box.
-/

namespace Purelib.Polynomial.Geometry.Grid.Incidence

open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.Data.List

namespace Interval

universe u
variable {Alpha : Type u} {key : Alpha → Fraction.Rational}

/-- Every retained axis entry lies outside the open interior of each adjacent interval.

The adjacent endpoints occur consecutively in the original strictly ordered list. Any selected entry is before the lower
endpoint or after the upper endpoint, allowing equality at either end. -/
public theorem entry_side (entries : List Alpha)
    (ordered : entries.Pairwise (fun left right => key left < key right))
    {interval : Geometry.Grid.ClearGrid.Interval key} (member : interval ∈ Geometry.Grid.ClearGrid.Interval.adjacent
      entries ordered)
    {entry : Alpha} (entryMember : entry ∈ entries) :
    key entry ≤ key interval.lower ∨ key interval.upper ≤ key entry := by
  induction entries with
  | nil => exact (List.not_mem_nil entryMember).elim
  | cons head rest ih =>
      cases rest with
      | nil => exact (List.not_mem_nil member).elim
      | cons next tail =>
          rcases Membership.mem_cons.mp member with equal | member
          · subst interval
            rcases Membership.mem_cons.mp entryMember with equal | entryMember
            · exact Or.inl (by rewrite [equal]; exact Fraction.Order.Basic.le_refl _)
            · rcases Membership.mem_cons.mp entryMember with equal | entryMember
              · exact Or.inr (by rewrite [equal]; exact Fraction.Order.Basic.le_refl _)
              · exact Or.inr (((List.pairwise_cons.mp (List.pairwise_cons.mp ordered).2).1 entry entryMember).le)
          · rcases Membership.mem_cons.mp entryMember with equal | entryMember
            · rw [equal]
              exact Or.inl (((List.pairwise_cons.mp ordered).1 interval.lower
                (Geometry.Grid.ClearGrid.Interval.endpoints_mem _ (List.pairwise_cons.mp ordered).2 member).1).le)
            · exact ih (List.pairwise_cons.mp ordered).2 member entryMember

/-- Every retained axis coordinate lies outside the open interior of each adjacent interval. -/
public theorem coordinate_side (entries : List Alpha)
    (ordered : entries.Pairwise (fun left right => key left < key right))
    {interval : Geometry.Grid.ClearGrid.Interval key} (member : interval ∈ Geometry.Grid.ClearGrid.Interval.adjacent
      entries ordered)
    {coordinate : Fraction.Rational} (coordinateMember : coordinate ∈ entries.map key) :
    coordinate ≤ key interval.lower ∨ key interval.upper ≤ coordinate := open Purelib in by
  rcases Map.mem_map.mp coordinateMember with ⟨entry, entryMember, equal⟩
  rw [← equal]
  exact Geometry.Grid.Incidence.Interval.entry_side entries ordered member entryMember

/-- An adjacent interval containing a strict inner interval lies within the retained outer endpoints.

Both outer endpoints must occur in the original ordered axis, and the inner interval is ordered and contained between
them. -/
public theorem contains_of_strict_inner (entries : List Alpha)
    (ordered : entries.Pairwise (fun left right => key left < key right))
    {interval : Geometry.Grid.ClearGrid.Interval key} (member : interval ∈ Geometry.Grid.ClearGrid.Interval.adjacent
      entries ordered)
    {lower upper innerLower innerUpper : Fraction.Rational}
    (lowerMember : lower ∈ entries.map key) (upperMember : upper ∈ entries.map key)
    (innerOrdered : innerLower ≤ innerUpper) (lowerInside : lower ≤ innerLower) (upperInside : innerUpper ≤ upper)
    (left : key interval.lower < innerLower) (right : innerUpper < key interval.upper) :
    lower ≤ key interval.lower ∧ key interval.upper ≤ upper := by
  constructor
  · rcases coordinate_side entries ordered member lowerMember with before | after
    · exact before
    · exact (not_lt_of_ge (after.trans (lowerInside.trans innerOrdered)) right).elim
  · rcases coordinate_side entries ordered member upperMember with before | after
    · exact (not_lt_of_ge ((innerOrdered.trans upperInside).trans before) left).elim
    · exact after

end Interval

section Grid

variable {polynomial : Geometry.ClearPath.GaussianPolynomial} {ambient : Box}

/-- All four original rectangle boundaries are retained coordinates, so an
adjacent face cannot cross any of them while containing its inner subbox. -/
public theorem cell_refines_of_strict_inner (grid : ClearGrid polynomial ambient) (cell :
  Geometry.Grid.ClearGrid.Cell polynomial ambient)
    (member : cell ∈ grid.cells) {original small : Box}
    (xLower : original.xLower ∈ grid.vertical.map Geometry.Grid.ClearGrid.VerticalLine.coordinate)
    (xUpper : original.xUpper ∈ grid.vertical.map Geometry.Grid.ClearGrid.VerticalLine.coordinate)
    (yLower : original.yLower ∈ grid.horizontal.map Geometry.Grid.ClearGrid.HorizontalLine.coordinate)
    (yUpper : original.yUpper ∈ grid.horizontal.map Geometry.Grid.ClearGrid.HorizontalLine.coordinate)
    (refines : small.Refines original) (strict : small.StrictInterior cell.box) : cell.box.Refines original := open
      Purelib in by
  rcases Flatten.mem_flatMap.mp member with ⟨horizontal, horizontalMember, member⟩
  rcases Map.mem_map.mp member with ⟨vertical, verticalMember, equal⟩
  subst cell
  have x := Geometry.Grid.Incidence.Interval.contains_of_strict_inner _ grid.vertical_ordered horizontalMember xLower
    xUpper
    small.x_valid refines.1 refines.2.1 strict.left strict.right
  have y := Geometry.Grid.Incidence.Interval.contains_of_strict_inner _ grid.horizontal_ordered verticalMember yLower
    yUpper
    small.y_valid refines.2.2.1 refines.2.2.2 strict.bottom strict.top
  exact ⟨x.1, x.2, y.1, y.2⟩

end Grid

end Purelib.Polynomial.Geometry.Grid.Incidence
