module
import Purelib.Data.List.Append
import Purelib.Data.List.Membership
import Purelib.Data.Nat.Multiplication
import Purelib.Data.List.Flatten
import Purelib.Data.List.Map

import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
public import Purelib.Riemann.Integration.RectangularOwnedTriangulation
public import Purelib.Geometry.Rectangle.Partition.PreparedBoxTriangulation
import Init.Data.List.Lemmas
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Topology.Mesh.CoordinateTriangulation
meta import Mathlib.Tactic.Linter.Lint

public section

/-!
# Dyadic triangle refinements on a fixed coarse model grid

Only geometric boxes and triangles are refined.  Every descendant retains
its original coarse model owner, so increasing the fine face count does not
increase the model bank or the primitive-offset graph.  The construction is
total and also permits finite subsets of the grid to be triangulated.
-/

namespace Purelib.Geometry.Rectangle.Partition.RectangularMeshRefinement

open Purelib

open Purelib.Data.List

open Purelib.Geometry.Rectangle.Partition

open Purelib.Riemann.Integration

open Purelib.Riemann.Integration.RectangularOwnedTriangulation

open Purelib.Riemann.Normalization

open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions (cells cells_refine cells_length)
open Purelib.Geometry.Rectangle.Partition.PreparedBoxTriangulation (boxTriangles boxTriangles_length lowerTriangle
  upperTriangle)
open Purelib.Topology.Mesh.CoordinateTriangulation (CoordinateTriangle)

namespace ModelTriangle

variable {columns rows : Nat} {geometry : Geometry columns rows}

/-- Attach a refined box's lower triangle to its original coarse model owner.

The refinement certificate supplies containment of all three vertices in that same coarse cell. -/
@[expose] def lowerBox (geometry : Geometry columns rows) (column : Fin (columns + 1)) (row :
  Fin (rows + 1))
    (box : Box) (refines : box.Refines (geometry.box column row)) :
      ModelTriangle geometry where
  column := column
  row := row
  triangle := lowerTriangle box
  firstInside := refines.contains ⟨le_rfl, box.x_valid, le_rfl, box.y_valid⟩
  secondInside := refines.contains ⟨box.x_valid, le_rfl, le_rfl, box.y_valid⟩
  thirdInside := refines.contains ⟨box.x_valid, le_rfl, box.y_valid, le_rfl⟩

/-- Attach a refined box's upper triangle to its original coarse model owner.

The refinement certificate supplies containment of all three vertices in that same coarse cell. -/
@[expose] def upperBox (geometry : Geometry columns rows) (column : Fin (columns + 1)) (row :
  Fin (rows + 1))
    (box : Box) (refines : box.Refines (geometry.box column row)) :
      ModelTriangle geometry where
  column := column
  row := row
  triangle := upperTriangle box
  firstInside := refines.contains ⟨le_rfl, box.x_valid, le_rfl, box.y_valid⟩
  secondInside := refines.contains ⟨box.x_valid, le_rfl, box.y_valid, le_rfl⟩
  thirdInside := refines.contains ⟨le_rfl, box.x_valid, box.y_valid, le_rfl⟩

/-- Convert a list of refining boxes into two owned triangles per box.

Every triangle retains the given coarse cell's indices and the original geometric containment certificate. -/
@[expose] def fromBoxes (geometry : Geometry columns rows)
  (column : Fin (columns + 1)) (row : Fin (rows + 1)) :
    (boxes : List Box) → (∀ box, box ∈ boxes → box.Refines
      (geometry.box column row)) → List (ModelTriangle
      geometry)
  | [], _ => []
  | box :: rest, refines =>
      lowerBox geometry column row box
        (refines box List.mem_cons_self) ::
      upperBox geometry column row box
        (refines box List.mem_cons_self) ::
      ModelTriangle.fromBoxes geometry column row rest
        (fun box member => refines box (List.mem_cons_of_mem _ member))

/-- Every original box-derived triangle keeps its supplied coarse column and row. -/
theorem fromBoxes_cell {columns rows : Nat} (geometry : Geometry columns rows)
    (column : Fin (columns + 1)) (row : Fin (rows + 1)) (boxes : List Box)
    (refines : ∀ box, box ∈ boxes → box.Refines (geometry.box column row))
    {triangle : ModelTriangle geometry} (member : triangle ∈ fromBoxes geometry column row boxes refines) :
    triangle.column = column ∧ triangle.row = row := by
  induction boxes with
  | nil => cases member
  | cons box rest ih =>
      rcases Membership.mem_cons.mp member with equal | member
      · cases equal
        exact ⟨rfl, rfl⟩
      · rcases Membership.mem_cons.mp member with equal | member
        · cases equal
          exact ⟨rfl, rfl⟩
        · exact ih _ member

/-- Forgetting the coarse owners gives exactly the original box-triangle list.

Each original refining box contributes its lower triangle followed by its upper triangle. Scalar list-constructor
transport preserves that exact order and the unchanged refined tail. -/
theorem fromBoxes_coordinates (geometry : Geometry columns rows) (column : Fin (columns + 1))
  (row : Fin (rows + 1))
    (boxes : List Box) (refines : ∀ box, box ∈ boxes → box.Refines (geometry.box column row)) :
    (fromBoxes geometry column row boxes
      refines).map ModelTriangle.triangle = boxTriangles boxes := by
  induction boxes with
  | nil => rfl
  | cons box rest ih =>
      change (lowerBox geometry column row box _).triangle ::
        (upperBox geometry column row box _).triangle ::
        (fromBoxes geometry column row rest _).map ModelTriangle.triangle =
          lowerTriangle box :: upperTriangle box ::
            boxTriangles rest
      exact congrArg (List.cons (lowerTriangle box))
        (congrArg (List.cons (upperTriangle box)) (ih _))

/-- Existing certified quartering supplies all child-containment witnesses. -/
@[expose] def refineCell (geometry : Geometry columns rows) (column : Fin (columns + 1)) (row :
  Fin (rows + 1))
    (depth : Nat) : List (ModelTriangle geometry) :=
  fromBoxes geometry column row
    (cells depth (geometry.box column row))
    (fun _ member => cells_refine depth (geometry.box column row) member)

/-- The refined cell's coordinate faces are exactly the dyadic box triangles. -/
theorem refineCell_coordinates (geometry : Geometry columns rows) (column : Fin (columns + 1))
  (row : Fin (rows + 1))
    (depth : Nat) : (refineCell geometry column row
      depth).map ModelTriangle.triangle =
      boxTriangles (cells depth (geometry.box column row)) :=
        fromBoxes_coordinates ..

/-- Refining one coarse cell to depth n produces two times four to the n faces.

The exact coordinate readback identifies the original dyadic box-triangle list. Its displayed length and the original
quartering count give the same two-times-four-power face count. -/
theorem refineCell_length (geometry : Geometry columns rows) (column : Fin (columns + 1)) (row
  : Fin (rows + 1))
    (depth : Nat) : (refineCell geometry column row
      depth).length = 2 * 4 ^ depth := by
  have lengthEq := congrArg List.length
    (refineCell_coordinates geometry column row
    depth)
  simpa only [Map.length_map, boxTriangles_length, cells_length] using
    lengthEq

/-- Every face of the refined coarse cell has positive oriented area. -/
theorem refineCell_positive (geometry : Geometry columns rows) (column : Fin (columns + 1))
  (row : Fin (rows + 1))
    (depth : Nat) {face : ModelTriangle geometry} (member : face ∈
      refineCell geometry column row depth) :
    0 < PreparedBoxTriangulation.coordinateArea face.triangle := by
  have inCoordinates : face.triangle ∈ (refineCell
    geometry column row depth).map ModelTriangle.triangle :=
    Map.mem_map.mpr ⟨face, member, rfl⟩
  rw [refineCell_coordinates] at inCoordinates
  exact PreparedBoxTriangulation.boxTriangles_positive _
    (fun _ inCells => PreparedBoxPartitions.cells_proper depth (geometry.box_proper column row) inCells) inCoordinates

end ModelTriangle

section Geometry

variable {columns rows : Nat}

/-- A displayed finite selection of coarse cells may describe one patch or several components. No new analytic
certificates are required to refine it. -/
@[expose] def refineSelection (geometry : Geometry columns rows)
    (selection : List (Fin (columns + 1) × Fin (rows + 1))) (depth : Nat) : List
      (ModelTriangle geometry) :=
  selection.flatMap fun cell => ModelTriangle.refineCell geometry
    cell.1 cell.2 depth

/-- The selected-cell face count is the selection length times the per-cell refinement count.

Every selected original coarse cell contributes its same retained refined triangle list. Structural concatenation adds
those exact lengths, including repeated selected occurrences. -/
theorem refineSelection_length (geometry : Geometry columns rows)
    (selection : List (Fin (columns + 1) × Fin (rows + 1))) (depth : Nat) :
    (refineSelection geometry selection depth).length =
      selection.length * (2 * 4 ^ depth) := by
  induction selection with
  | nil => exact (Nat.zero_mul _).symm
  | cons cell rest ih =>
      change ((ModelTriangle.refineCell geometry cell.1 cell.2 depth) ++
        refineSelection geometry rest depth).length = (rest.length + 1) * (2 * 4 ^ depth)
      rw [Append.length_append, ModelTriangle.refineCell_length, ih,
        Data.Nat.Multiplication.right_distrib, Nat.one_mul, Nat.add_comm]

/-- Every face produced from the selected coarse cells has positive oriented area. -/
theorem refineSelection_positive (geometry : Geometry columns rows)
    (selection : List (Fin (columns + 1) × Fin (rows + 1))) (depth : Nat)
    {face : ModelTriangle geometry} (member : face ∈
      refineSelection geometry selection depth) :
    0 < PreparedBoxTriangulation.coordinateArea face.triangle := by
  obtain ⟨cell, _selected, inCell⟩ := Flatten.mem_flatMap.mp member
  exact ModelTriangle.refineCell_positive geometry cell.1 cell.2
    depth inCell

/-- Shared indexing and exact finite incidence for all selected refined triangles. No inverse-root or primitive
polynomials are recomputed. -/
@[expose] def triangulateSelection (geometry : Geometry columns rows)
    (selection : List (Fin (columns + 1) × Fin (rows + 1))) (depth : Nat) :
    OwnedTriangulation
      (refineSelection geometry selection depth) :=
  OwnedTriangulation.build (refineSelection geometry
    selection depth)

end Geometry

end Purelib.Geometry.Rectangle.Partition.RectangularMeshRefinement
