module
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.LinearAlgebra.Grid.Offsets
import Purelib.Riemann.Readings.RectangularPairedEndpointReadings
import Purelib.Riemann.Integration.RectangularPrimitiveMagnitude
import Purelib.Integration.Path.SuccessiveMagnitude
import Purelib.Tactic.Ring
public import Purelib.Riemann.Readings.RectangularSeamBounds
public import Purelib.Riemann.Readings.RectangularPointReadings

public section

/-! Endpoint owners need not lie in one model cell. Bound their primitive
increments along the exact spanning tree of retained corner anchors. -/
namespace Purelib.Riemann.Integration.RectangularEndpointMagnitude

open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib
open Purelib.Data.Rat
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (RegionClearance PrimitiveOverlapBounds)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry Bank)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives)
open Purelib.Riemann.Integration.RectangularPrimitiveGluing (PrimitiveAnchors)
open Purelib.Riemann.Integration.RectangularOwnedTriangulation (OwnedVertex)
open Purelib.Riemann.Readings.RectangularSeamBounds (boundarySlope)
open Purelib.Riemann.Readings.RectangularPointReadings (PointReadings)

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Rat.Fraction.Order.Arithmetic (mul_nonneg_direct mul_le_mul_of_nonneg_left_direct)

variable {polynomial numerator : Polynomial} {ambient : Box} {clearance : RegionClearance polynomial ambient}
    {columns rows : Nat} {geometry : Geometry columns rows} {models : Bank polynomial geometry}
    {primitives : Primitives models numerator}

open Purelib.Data in
/-- The original primitive boundary slope bound is nonnegative. -/
private theorem slope_nonnegative (bounds : PrimitiveOverlapBounds clearance numerator) : 0 ≤ boundarySlope bounds :=
  Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
    (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct bounds.numeratorUpper_nonnegative bounds.inverseUpper_positive.le))
      ambient.diagonalSq_nonneg

open Purelib.Riemann in
open Purelib.Integration in
open Purelib.Data in
open Purelib.LinearAlgebra in
/-- Bound a retained owner's translated primitive value relative to the original lower-left anchor.

The exact anchor spanning tree supplies horizontal and first-column increments, followed by one local owner-cell
increment. -/
private theorem origin_magnitude (anchors : PrimitiveAnchors primitives) (offsets : LinearAlgebra.Grid.Offsets
  anchors.edges)
    (bounds : PrimitiveOverlapBounds clearance numerator)
    (refines : ∀ column row, (geometry.box column row).Refines ambient) (owner : OwnedVertex geometry) :
    Gaussian.Basic.Canonical.normSq (anchors.alignedValue offsets owner.column owner.row owner.point -
      anchors.alignedValue offsets 0 0 (geometry.vertex 0 0)) ≤
      2 * (boundarySlope bounds + 2 * ((columns : Coordinate)^2 * boundarySlope bounds +
        (rows : Coordinate)^2 * boundarySlope bounds)) := by
  let lower := fun column row => anchors.alignedValue offsets column row (geometry.vertex column.castSucc row.castSucc)
  have horizontal (column : Fin columns) (row : Fin (rows + 1)) :
      Gaussian.Basic.Canonical.normSq (lower column.succ row - lower column.castSucc row) ≤ boundarySlope bounds := by
    have equal : lower column.succ row - lower column.castSucc row =
        primitives.value column.castSucc row (geometry.vertex column.castSucc.succ row.castSucc) -
          primitives.value column.castSucc row (geometry.vertex column.castSucc.castSucc row.castSucc) := by
      dsimp only [lower, PrimitiveAnchors.alignedValue]
      rw [offsets.horizontal, anchors.horizontal_spec]
      change _ + _ + primitives.value column.succ row (geometry.vertex column.castSucc.succ row.castSucc) - _ = _
      ring1
    rw [equal]
    exact Integration.RectangularPrimitiveModels.Primitives.local_increment_bound primitives bounds refines _ _
      (geometry.lowerLeft_mem _ _) (geometry.lowerRight_mem _ _)
  have vertical (row : Fin rows) : Gaussian.Basic.Canonical.normSq (lower 0 row.succ - lower 0 row.castSucc) ≤
    boundarySlope bounds := by
    have equal : lower 0 row.succ - lower 0 row.castSucc =
        primitives.value 0 row.castSucc (geometry.vertex 0 row.castSucc.succ) -
          primitives.value 0 row.castSucc (geometry.vertex 0 row.castSucc.castSucc) := by
      dsimp only [lower, PrimitiveAnchors.alignedValue]
      rw [offsets.firstVertical, anchors.vertical_spec]
      have zeroCast : (0 : Fin (columns + 1)).castSucc = (0 : Fin (columns + 1 + 1)) := rfl
      rw [zeroCast]
      change _ + _ + primitives.value 0 row.succ (geometry.vertex 0 row.castSucc.succ) - _ = _
      ring1
    rw [equal]
    exact Integration.RectangularPrimitiveModels.Primitives.local_increment_bound primitives bounds refines _ _
      (geometry.lowerLeft_mem _ _) (geometry.upperLeft_mem _ _)
  have alongRow := Path.SuccessiveMagnitude.successive_magnitude (fun column => lower column owner.row)
    (slope_nonnegative bounds) (fun column => by
      have scalar := horizontal column owner.row
      simpa only [Gaussian.Norm.Basic.normSq_eq_canonical, -eq_self, -iff_self] using scalar) owner.column
  have alongColumn := Path.SuccessiveMagnitude.successive_magnitude (lower 0)
    (slope_nonnegative bounds) (fun row => by
      have scalar := vertical row
      simpa only [Gaussian.Norm.Basic.normSq_eq_canonical, -eq_self, -iff_self] using scalar) owner.row
  simp only [Gaussian.Norm.Basic.normSq_eq_canonical, -eq_self, -iff_self] at alongRow alongColumn
  have corner := (Gaussian.Norm.Bounds.normSq_add_le_two (lower owner.column owner.row - lower 0 owner.row)
    (lower 0 owner.row - lower 0 0))
  simp only [Gaussian.Norm.Basic.normSq_eq_canonical, -eq_self, -iff_self] at corner
  have corner := corner.trans
    (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Rat.Fraction.Order.Arithmetic.add_le_add_direct
      alongRow alongColumn) (by decide))
  have localBound : Gaussian.Basic.Canonical.normSq (anchors.alignedValue offsets owner.column owner.row owner.point -
    lower owner.column owner.row) ≤
      boundarySlope bounds := by
    dsimp only [lower, PrimitiveAnchors.alignedValue]
    have cancel (offset first second : Gaussian.Basic.Canonical) :
        (offset + first) - (offset + second) = first - second := by ring1
    rw [cancel]
    exact Integration.RectangularPrimitiveModels.Primitives.local_increment_bound primitives bounds refines _ _
      (geometry.lowerLeft_mem _ _) owner.contains
  have cancel (a b c : Gaussian) : (a - b) + (b - c) = a - c := by ring1
  rw [cancel] at corner
  have estimate := (Gaussian.Norm.Bounds.normSq_add_le_two
    (anchors.alignedValue offsets owner.column owner.row owner.point - lower owner.column owner.row)
    (lower owner.column owner.row - lower 0 0))
  simp only [Gaussian.Norm.Basic.normSq_eq_canonical, -eq_self, -iff_self] at estimate
  have estimate := estimate.trans
    (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Rat.Fraction.Order.Arithmetic.add_le_add_direct
      localBound corner) (by decide))
  rw [cancel] at estimate
  exact estimate

/-- A uniform primitive endpoint-difference ceiling from the original grid dimensions and boundary slope.

The exact tree translations give eight times the local slope plus twice the row and column squared-count contributions,
independently of numerical stage. -/
@[expose] def endpointMagnitude (columns rows : Nat) (slope : Coordinate) : Coordinate :=
  8 * (slope + 2 * ((columns : Coordinate)^2 * slope + (rows : Coordinate)^2 * slope))

open Purelib.Data in
/-- A nonnegative boundary slope gives a nonnegative endpoint-difference ceiling. -/
theorem endpointMagnitude_nonnegative (columns rows : Nat) {slope : Coordinate} (nonnegative : 0 ≤ slope) :
    0 ≤ endpointMagnitude columns rows slope :=
  Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg nonnegative
    (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
    (add_nonneg (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (Rat.Fraction.Order.Arithmetic.sq_nonneg_direct _)
      nonnegative)
      (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (Rat.Fraction.Order.Arithmetic.sq_nonneg_direct _)
        nonnegative))))

open Purelib.Data in
open Purelib.LinearAlgebra in
/-- Any two retained point readings satisfy the original grid's endpoint-difference ceiling.

Their owners may differ; both cached readings are compared through the same exact spanning-tree anchor. -/
theorem endpoint_readings_magnitude (anchors : PrimitiveAnchors primitives) (offsets : LinearAlgebra.Grid.Offsets
  anchors.edges)
    (bounds : PrimitiveOverlapBounds clearance numerator)
    (refines : ∀ column row, (geometry.box column row).Refines ambient)
    {count : Nat} {points : Fin count → Gaussian} (readings : PointReadings anchors offsets points) (first last : Fin
      count) :
    Gaussian.Basic.Canonical.normSq (readings.values last - readings.values first) ≤ endpointMagnitude columns rows
      (boundarySlope bounds) := by
  rw [readings.value_eq, readings.value_eq]
  have estimate := (Gaussian.Norm.Bounds.normSq_sub_le_two
    (anchors.alignedValue offsets (readings.owners last).column (readings.owners last).row (readings.owners last).point
      -
      anchors.alignedValue offsets 0 0 (geometry.vertex 0 0))
    (anchors.alignedValue offsets (readings.owners first).column (readings.owners first).row (readings.owners
      first).point -
      anchors.alignedValue offsets 0 0 (geometry.vertex 0 0)))
  simp only [Gaussian.Norm.Basic.normSq_eq_canonical, -eq_self, -iff_self] at estimate
  have estimate := estimate.trans
    (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Rat.Fraction.Order.Arithmetic.add_le_add_direct
      (origin_magnitude anchors offsets bounds refines (readings.owners last))
      (origin_magnitude anchors offsets bounds refines (readings.owners first))) (by decide))
  have cancel : (anchors.alignedValue offsets (readings.owners last).column (readings.owners last).row (readings.owners
    last).point -
      anchors.alignedValue offsets 0 0 (geometry.vertex 0 0)) -
      (anchors.alignedValue offsets (readings.owners first).column (readings.owners first).row (readings.owners
        first).point -
        anchors.alignedValue offsets 0 0 (geometry.vertex 0 0)) =
      anchors.alignedValue offsets (readings.owners last).column (readings.owners last).row (readings.owners last).point
        -
        anchors.alignedValue offsets (readings.owners first).column (readings.owners first).row (readings.owners
          first).point := by ring1
  rw [cancel] at estimate
  exact estimate.trans_eq (by unfold endpointMagnitude; ring1)

end Purelib.Riemann.Integration.RectangularEndpointMagnitude
