module
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Topology.Polygon.Stokes

import Purelib.Geometry.Rectangle.Partition.PreparedBoxBoundary
public import Purelib.Riemann.Readings.RectangularClippedLocalBoundary
import Purelib.Tactic.Ring

@[expose] public section

/-! Constant primitive offsets retain exact endpoint terms on open sides
and cancel on every closed clipped rectangle. -/
namespace Purelib.Geometry.Rectangle.Partition.PreparedBoxBoundary

open Purelib.Topology.Polygon.Stokes (PrimitivePoint edgeArea)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate Box)
open Purelib.Geometry.Rectangle.Partition.PreparedBoxBoundary (horizontalBoundary verticalBoundary rectangleBoundary)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Riemann.Meshes.RectangularObservationMesh (ObservationPieces)

open Purelib.Geometry
/-- Translating a horizontal primitive boundary adds exactly the difference of its endpoint ribbons. -/
theorem horizontalBoundary_add (values : Gaussian →
  PrimitivePoint) (offset : PrimitivePoint)
    (depth : Nat) (first last height : Coordinate) :
    Rectangle.Partition.PreparedBoxBoundary.horizontalBoundary (fun point => (values point).add offset) depth first last
      height =
      Rectangle.Partition.PreparedBoxBoundary.horizontalBoundary values depth first last height + edgeArea offset
        (values ⟨last, height⟩) -
        edgeArea offset (values ⟨first, height⟩) := by
  induction depth generalizing first last with
  | zero => simp only [Rectangle.Partition.PreparedBoxBoundary.horizontalBoundary, edgeArea, PrimitivePoint.add]; ring1
  | succ depth ih => simp only [Rectangle.Partition.PreparedBoxBoundary.horizontalBoundary, ih]; ring1

/-- Translating a vertical primitive boundary adds exactly the difference of its endpoint ribbons. -/
theorem verticalBoundary_add (values : Gaussian →
  PrimitivePoint) (offset : PrimitivePoint)
    (depth : Nat) (first last horizontal : Coordinate) :
    Rectangle.Partition.PreparedBoxBoundary.verticalBoundary (fun point => (values point).add offset) depth first last
      horizontal =
      Rectangle.Partition.PreparedBoxBoundary.verticalBoundary values depth first last horizontal + edgeArea offset
        (values ⟨horizontal, last⟩) -
        edgeArea offset (values ⟨horizontal, first⟩) := by
  induction depth generalizing first last with
  | zero => simp only [Rectangle.Partition.PreparedBoxBoundary.verticalBoundary, edgeArea, PrimitivePoint.add]; ring1
  | succ depth ih => simp only [Rectangle.Partition.PreparedBoxBoundary.verticalBoundary, ih]; ring1

/-- A constant primitive translation leaves the closed rectangular boundary area unchanged. -/
theorem rectangleBoundary_add (values : Gaussian →
  PrimitivePoint) (offset : PrimitivePoint) (depth : Nat) (box : Box) :
    Rectangle.Partition.PreparedBoxBoundary.rectangleBoundary (fun point => (values point).add offset) depth box =
      Rectangle.Partition.PreparedBoxBoundary.rectangleBoundary values depth box := by
  simp only [Rectangle.Partition.PreparedBoxBoundary.rectangleBoundary,
    Rectangle.Partition.PreparedBoxBoundary.horizontalBoundary_add,
    Rectangle.Partition.PreparedBoxBoundary.verticalBoundary_add]
  ring1

/-- Pointwise equal primitive values have the same actual horizontal dyadic boundary sum.

At each retained subdivision depth the two endpoint values agree, and the same equality applies recursively to both
ordered halves. -/
theorem horizontalBoundary_congr {first last : Gaussian
  → PrimitivePoint} (equal : ∀ point, first point = last point)
    (depth : Nat) (lower upper height : Coordinate) :
    Rectangle.Partition.PreparedBoxBoundary.horizontalBoundary first depth lower upper height =
      Rectangle.Partition.PreparedBoxBoundary.horizontalBoundary last depth lower upper height := by
  induction depth generalizing lower upper with
  | zero =>
      simp only [Rectangle.Partition.PreparedBoxBoundary.horizontalBoundary, equal, -eq_self, -iff_self]
      rfl
  | succ depth ih =>
      simp only [Rectangle.Partition.PreparedBoxBoundary.horizontalBoundary, ih, -eq_self, -iff_self]
      rfl

/-- Pointwise equal primitive values have the same actual vertical dyadic boundary sum.

At each retained subdivision depth the two endpoint values agree, and the same equality applies recursively to both
ordered halves. -/
theorem verticalBoundary_congr {first last : Gaussian →
  PrimitivePoint} (equal : ∀ point, first point = last point)
    (depth : Nat) (lower upper horizontal : Coordinate) :
    Rectangle.Partition.PreparedBoxBoundary.verticalBoundary first depth lower upper horizontal =
      Rectangle.Partition.PreparedBoxBoundary.verticalBoundary last depth lower upper horizontal := by
  induction depth generalizing lower upper with
  | zero =>
      simp only [Rectangle.Partition.PreparedBoxBoundary.verticalBoundary, equal, -eq_self, -iff_self]
      rfl
  | succ depth ih =>
      simp only [Rectangle.Partition.PreparedBoxBoundary.verticalBoundary, ih, -eq_self, -iff_self]
      rfl

/-- Pointwise equal primitive values have the same closed dyadic rectangle boundary sum.

The four original oriented side sums agree at the retained depth and rectangle coordinates. -/
theorem rectangleBoundary_congr {first last : Gaussian →
  PrimitivePoint} (equal : ∀ point, first point = last point)
    (depth : Nat) (box : Box) : Rectangle.Partition.PreparedBoxBoundary.rectangleBoundary first depth box =
      Rectangle.Partition.PreparedBoxBoundary.rectangleBoundary last depth box := by
  simp only [Rectangle.Partition.PreparedBoxBoundary.rectangleBoundary,
    Rectangle.Partition.PreparedBoxBoundary.horizontalBoundary_congr equal,
    Rectangle.Partition.PreparedBoxBoundary.verticalBoundary_congr equal, -eq_self, -iff_self]
  rfl

end Purelib.Geometry.Rectangle.Partition.PreparedBoxBoundary

namespace Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationPieces

open Purelib.Riemann.Normalization.InverseRootPolynomial (Box Gaussian)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint edgeArea)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate Box)
open Purelib.Geometry.Rectangle.Partition.PreparedBoxBoundary (horizontalBoundary verticalBoundary rectangleBoundary)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Riemann.Meshes.RectangularObservationMesh (ObservationPieces)

variable {columns rows : Nat} {geometry : Geometry columns rows}

open Purelib.Riemann in
open Purelib.Geometry in
/-- Independent constant owner translations preserve the total local clipped boundary area.

Each retained closed rectangle cancels its own translation ribbons, preserving the original piece list and owner
assignments. -/
theorem localBoundary_eq_of_translation
  {boxes : List Box} (pieces : ObservationPieces geometry boxes)
    (values translated : Fin (columns + 1) → Fin (rows + 1) → Gaussian → PrimitivePoint)
    (offsets : Fin (columns + 1) → Fin (rows + 1) → PrimitivePoint)
    (equal : ∀ column row point, translated column row point = (values column row point).add (offsets column row))
    (depth : Nat) : pieces.localBoundary translated depth = pieces.localBoundary values depth := by
  induction pieces with
  | nil => rfl
  | cons column row refines tail ih =>
      rw [Meshes.RectangularObservationMesh.ObservationPieces.localBoundary,
        Meshes.RectangularObservationMesh.ObservationPieces.localBoundary,
        Rectangle.Partition.PreparedBoxBoundary.rectangleBoundary_congr (equal column row),
        Rectangle.Partition.PreparedBoxBoundary.rectangleBoundary_add, ih]

end Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationPieces
