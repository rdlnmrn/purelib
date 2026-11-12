module

public import Purelib.Polynomial.Geometry.Grid.AxisNeighbors.Contact
public import Purelib.Polynomial.Geometry.Grid.VertexCellSteps
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Data.Rat.Fraction.Order.Basic

/-! # Shared sides and corners of actual retained grid cells

Two original cell occurrences containing the same point are classified by
their retained horizontal and vertical adjacent intervals. The result keeps
same-cell, true shared-side and corner cases distinct and chooses an actual
side at each nontrivial contact without asserting a signed root relation.
-/

public section

namespace Purelib.Polynomial.Geometry.Grid.ClearGrid.Cell

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Rational (Box)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)

variable {polynomial : ClearPath.GaussianPolynomial} {ambient : Box}
variable {grid : ClearGrid polynomial ambient}

/-- A point lies on the displayed original closed side of a cell.

Containment is retained separately; this predicate fixes the single
coordinate that identifies the original oriented side.
-/
@[expose] def OnSide (cell : Cell polynomial ambient) (point : Canonical) : GridSide → Prop
  | .bottom => point.im = cell.box.yLower
  | .right => point.re = cell.box.xUpper
  | .top => point.im = cell.box.yUpper
  | .left => point.re = cell.box.xLower

/-- Contact on both original axis intervals, retaining their actual payloads. -/
@[expose] def Contacts (first second : Cell polynomial ambient) (point : Canonical) : Type :=
  AxisNeighbors.Contact first.horizontal second.horizontal point.re ×
    AxisNeighbors.Contact first.vertical second.vertical point.im

/-- Classify a common point using only the two retained cell occurrences.

Original cell membership supplies each adjacent-interval membership. No
face classification, coordinate search or root continuation is repeated.
-/
def contactAt (first second : Cell polynomial ambient)
    (firstMember : first ∈ grid.cells) (secondMember : second ∈ grid.cells)
    (point : Canonical) (firstInside : first.box.Contains point) (secondInside : second.box.Contains point) :
    Contacts first second point :=
  let firstIntervals := CellBoundary.Cell.intervals_mem first firstMember
  let secondIntervals := CellBoundary.Cell.intervals_mem second secondMember
  ⟨AxisNeighbors.contactAt grid.vertical_ordered firstIntervals.1 secondIntervals.1 point.re
      ⟨firstInside.1, firstInside.2.1⟩ ⟨secondInside.1, secondInside.2.1⟩,
    AxisNeighbors.contactAt grid.horizontal_ordered firstIntervals.2 secondIntervals.2 point.im
      firstInside.2.2 secondInside.2.2⟩

namespace Contacts

variable {first second : Cell polynomial ambient} {point : Canonical}
variable (contact : Contacts first second point)

/-- Choose opposite sides at a genuine contact, prioritizing the horizontal-axis contact at a corner.

None is reserved for the same original cell. At a corner the selected sides
need not have the same whole span; both original axis flags remain retained
in contact so this case cannot be confused with a shared full side.
-/
@[expose] def sides : Option (GridSide × GridSide) :=
  match contact.1.val, contact.2.val with
  | some false, _ => some (.right, .left)
  | some true, _ => some (.left, .right)
  | none, some false => some (.top, .bottom)
  | none, some true => some (.bottom, .top)
  | none, none => none

/-- Equal retained horizontal and vertical intervals identify the original cells. -/
private theorem cells_eq (horizontal : first.horizontal = second.horizontal)
    (vertical : first.vertical = second.vertical) : first = second := by
  cases first
  cases second
  cases horizontal
  cases vertical
  rfl

/-- The finite choice certifies the same cell or actual incidence on both selected sides. -/
theorem sides_spec :
    match contact.sides with
    | none => first = second
    | some pair => first.OnSide point pair.1 ∧ second.OnSide point pair.2 := by
  unfold sides
  cases horizontal : contact.1.val with
  | none =>
      cases vertical : contact.2.val with
      | none =>
          change first = second
          exact cells_eq (contact.1.same horizontal) (contact.2.same vertical)
      | some direction =>
          cases direction with
          | false =>
              change point.im = first.box.yUpper ∧ point.im = second.box.yLower
              have retained := contact.2.forward vertical
              exact ⟨retained.1.symm, retained.2.symm⟩
          | true =>
              change point.im = first.box.yLower ∧ point.im = second.box.yUpper
              have retained := contact.2.backward vertical
              exact ⟨retained.1.symm, retained.2.symm⟩
  | some direction =>
      cases direction with
      | false =>
          change point.re = first.box.xUpper ∧ point.re = second.box.xLower
          have retained := contact.1.forward horizontal
          exact ⟨retained.1.symm, retained.2.symm⟩
      | true =>
          change point.re = first.box.xLower ∧ point.re = second.box.xUpper
          have retained := contact.1.backward horizontal
          exact ⟨retained.1.symm, retained.2.symm⟩

/-- Contact on both axes makes the same point an actual corner of both original cells. -/
theorem corners (xDirection yDirection : Bool)
    (horizontal : contact.1.val = some xDirection) (vertical : contact.2.val = some yDirection) :
    first.IsCorner point ∧ second.IsCorner point := by
  have x : (first.box.xLower = point.re ∨ first.box.xUpper = point.re) ∧
      (second.box.xLower = point.re ∨ second.box.xUpper = point.re) := by
    cases xDirection with
    | false =>
        have retained := contact.1.forward horizontal
        exact ⟨Or.inr retained.1, Or.inl retained.2⟩
    | true =>
        have retained := contact.1.backward horizontal
        exact ⟨Or.inl retained.1, Or.inr retained.2⟩
  have y : (first.box.yLower = point.im ∨ first.box.yUpper = point.im) ∧
      (second.box.yLower = point.im ∨ second.box.yUpper = point.im) := by
    cases yDirection with
    | false =>
        have retained := contact.2.forward vertical
        exact ⟨Or.inr retained.1, Or.inl retained.2⟩
    | true =>
        have retained := contact.2.backward vertical
        exact ⟨Or.inl retained.1, Or.inr retained.2⟩
  exact ⟨⟨x.1, y.1⟩, ⟨x.2, y.2⟩⟩

/-- A corner case produces the two original incident-cell owners without any coordinate lookup. -/
@[expose] def incidents (firstMember : first ∈ grid.cells) (secondMember : second ∈ grid.cells)
    (xDirection yDirection : Bool)
    (horizontal : contact.1.val = some xDirection) (vertical : contact.2.val = some yDirection) :
    VertexCellSteps.IncidentCell grid point × VertexCellSteps.IncidentCell grid point :=
  let retained := contact.corners xDirection yDirection horizontal vertical
  ⟨⟨first, firstMember, retained.1⟩, ⟨second, secondMember, retained.2⟩⟩

/-- A forward horizontal-axis contact with the same vertical span gives reversed right and left side endpoints. -/
theorem right_left (horizontal : contact.1.val = some false) (vertical : contact.2.val = none) :
    GridSide.left.start second.box = GridSide.right.finish first.box ∧
      GridSide.left.finish second.box = GridSide.right.start first.box := by
  have x := (contact.1.forward horizontal).1.trans (contact.1.forward horizontal).2.symm
  have y := contact.2.same vertical
  constructor
  · apply Data.Gaussian.Basic.ext
    · exact x.symm
    · exact congrArg (fun interval => interval.upper.coordinate) y.symm
  · apply Data.Gaussian.Basic.ext
    · exact x.symm
    · exact congrArg (fun interval => interval.lower.coordinate) y.symm

/-- A reverse horizontal-axis contact with the same vertical span gives reversed left and right side endpoints. -/
theorem left_right (horizontal : contact.1.val = some true) (vertical : contact.2.val = none) :
    GridSide.right.start second.box = GridSide.left.finish first.box ∧
      GridSide.right.finish second.box = GridSide.left.start first.box := by
  have x := (contact.1.backward horizontal).1.trans (contact.1.backward horizontal).2.symm
  have y := contact.2.same vertical
  constructor
  · apply Data.Gaussian.Basic.ext
    · exact x.symm
    · exact congrArg (fun interval => interval.lower.coordinate) y.symm
  · apply Data.Gaussian.Basic.ext
    · exact x.symm
    · exact congrArg (fun interval => interval.upper.coordinate) y.symm

/-- A forward vertical-axis contact with the same horizontal span gives reversed top and bottom side endpoints. -/
theorem top_bottom (horizontal : contact.1.val = none) (vertical : contact.2.val = some false) :
    GridSide.bottom.start second.box = GridSide.top.finish first.box ∧
      GridSide.bottom.finish second.box = GridSide.top.start first.box := by
  have x := contact.1.same horizontal
  have y := (contact.2.forward vertical).1.trans (contact.2.forward vertical).2.symm
  constructor
  · apply Data.Gaussian.Basic.ext
    · exact congrArg (fun interval => interval.lower.coordinate) x.symm
    · exact y.symm
  · apply Data.Gaussian.Basic.ext
    · exact congrArg (fun interval => interval.upper.coordinate) x.symm
    · exact y.symm

/-- A reverse vertical-axis contact with the same horizontal span gives reversed bottom and top side endpoints. -/
theorem bottom_top (horizontal : contact.1.val = none) (vertical : contact.2.val = some true) :
    GridSide.top.start second.box = GridSide.bottom.finish first.box ∧
      GridSide.top.finish second.box = GridSide.bottom.start first.box := by
  have x := contact.1.same horizontal
  have y := (contact.2.backward vertical).1.trans (contact.2.backward vertical).2.symm
  constructor
  · apply Data.Gaussian.Basic.ext
    · exact congrArg (fun interval => interval.upper.coordinate) x.symm
    · exact y.symm
  · apply Data.Gaussian.Basic.ext
    · exact congrArg (fun interval => interval.lower.coordinate) x.symm
    · exact y.symm

end Contacts
end Purelib.Polynomial.Geometry.Grid.ClearGrid.Cell

end
