module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Vector.Basic

public import Purelib.Riemann.Integration.RectangularPrimitiveModels
public import Purelib.LinearAlgebra.Grid.Offsets
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Data.Rat.Fraction.Field
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

@[expose] public section

/-!
# Finite grid gluing of local primitive polynomials

Cache the four primitive corner readings once per cell, then construct all
edge anchors and spanning-tree translations from those readings.  A square
defect is the difference of two already bounded edge drifts.  Finite-sum
Cauchy controls the accumulated mismatch on every non-tree edge.
-/

namespace Purelib.Riemann.Integration.RectangularPrimitiveGluing

open Purelib.Riemann.Integration.RectangularPrimitiveModels
open Purelib.LinearAlgebra.Grid.Offsets (Edges Gaussian Coordinate)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry Bank Transitions)
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (RegionClearance PrimitiveOverlapBounds DensePrimitive)
open Purelib.Riemann.Branches.RectangularSheetGauge
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison

open Purelib.Riemann.Normalization.InverseRootPolynomial (Polynomial Model)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)

open Purelib in
set_option genInjectivity false in
/-- The four ordered Gaussian corner values of an original rectangular cell. -/
structure CornerValues where
  /-- The original lower-left corner value. -/ lowerLeft : LinearAlgebra.Grid.Offsets.Gaussian
  /-- The original lower-right corner value. -/ lowerRight : LinearAlgebra.Grid.Offsets.Gaussian
  /-- The original upper-left corner value. -/ upperLeft : LinearAlgebra.Grid.Offsets.Gaussian
  /-- The original upper-right corner value. -/ upperRight : LinearAlgebra.Grid.Offsets.Gaussian

constructive_injectivity CornerValues

open Purelib.Data in
set_option genInjectivity false in
/-- Cached primitive values at all four original corners of each retained cell.

Each readback equation refers to the same original primitive and exact geometric column and row indices. -/
structure PrimitiveCorners {polynomial numerator : Polynomial} {columns rows : Nat} {geometry : Geometry columns rows}
    {models : Bank polynomial geometry} (primitives : Primitives models numerator) where
  /-- The retained corner-value vector indexed by original column and row. -/ values : Data.Vector
    (Data.Vector CornerValues (rows + 1)) (columns + 1)
  /-- The lower-left cache equals the original primitive at that exact geometric corner. -/ lowerLeft_eq : ∀ column row,
    (values column row).lowerLeft = primitives.value column row (geometry.vertex column.castSucc row.castSucc)
  /-- The lower-right cache equals the original primitive at that exact geometric corner. -/ lowerRight_eq : ∀ column
    row, (values column row).lowerRight = primitives.value column row (geometry.vertex column.succ row.castSucc)
  /-- The upper-left cache equals the original primitive at that exact geometric corner. -/ upperLeft_eq : ∀ column row,
    (values column row).upperLeft = primitives.value column row (geometry.vertex column.castSucc row.succ)
  /-- The upper-right cache equals the original primitive at that exact geometric corner. -/ upperRight_eq : ∀ column
    row, (values column row).upperRight = primitives.value column row (geometry.vertex column.succ row.succ)

constructive_injectivity PrimitiveCorners

namespace PrimitiveCorners

variable {polynomial numerator : Polynomial} {columns rows : Nat} {geometry : Geometry columns rows}
    {models : Bank polynomial geometry} {primitives : Primitives models numerator}

open Purelib.Data in
/-- Cache the original primitives' values at their four geometric cell corners. -/
def build (primitives : Primitives models numerator) : PrimitiveCorners primitives where
  values := Vector.Basic.vectorOfFn fun column => Vector.Basic.vectorOfFn fun row =>
    ⟨primitives.value column row (geometry.vertex column.castSucc row.castSucc),
      primitives.value column row (geometry.vertex column.succ row.castSucc),
      primitives.value column row (geometry.vertex column.castSucc row.succ),
      primitives.value column row (geometry.vertex column.succ row.succ)⟩
  lowerLeft_eq := fun column row => by rw [Vector.Basic.vectorOfFn_apply, Vector.Basic.vectorOfFn_apply]
  lowerRight_eq := fun column row => by rw [Vector.Basic.vectorOfFn_apply, Vector.Basic.vectorOfFn_apply]
  upperLeft_eq := fun column row => by rw [Vector.Basic.vectorOfFn_apply, Vector.Basic.vectorOfFn_apply]
  upperRight_eq := fun column row => by rw [Vector.Basic.vectorOfFn_apply, Vector.Basic.vectorOfFn_apply]

end PrimitiveCorners

open Purelib in
set_option genInjectivity false in
/-- Retained corner caches and exact adjacent-cell primitive offsets at common edge starts.

Both offset vectors are computed from those exact cached values and retain their original horizontal and vertical
adjacency indices. -/
structure PrimitiveAnchors {polynomial numerator : Polynomial} {columns rows : Nat} {geometry : Geometry columns rows}
    {models : Bank polynomial geometry} (primitives : Primitives models numerator) where
  /-- The original retained four-corner primitive caches. -/ corners : PrimitiveCorners primitives
  /-- The retained adjacent-cell anchor-offset vectors. -/ edges : LinearAlgebra.Grid.Offsets.Edges columns rows
  /-- Each horizontal offset is the exact difference of the retained common-edge starting corner values. -/
    horizontal_eq : ∀ column row,
    edges.horizontal column row = (corners.values column.castSucc row).lowerRight - (corners.values column.succ
      row).lowerLeft
  /-- Each vertical offset is the exact difference of the retained common-edge starting corner values. -/ vertical_eq :
    ∀ column row,
    edges.vertical column row = (corners.values column row.castSucc).upperLeft - (corners.values column
      row.succ).lowerLeft

constructive_injectivity PrimitiveAnchors

namespace PrimitiveAnchors

variable {polynomial numerator : Polynomial} {columns rows : Nat} {geometry : Geometry columns rows}
    {models : Bank polynomial geometry} {primitives : Primitives models numerator}

open Purelib.Data in
/-- Compute original adjacent-cell offsets from the exact retained primitive corner caches. -/
def ofCorners (corners : PrimitiveCorners primitives) : PrimitiveAnchors primitives where
  corners := corners
  edges :=
    { horizontal := Vector.Basic.vectorOfFn fun column => Vector.Basic.vectorOfFn fun row =>
        (corners.values column.castSucc row).lowerRight - (corners.values column.succ row).lowerLeft
      vertical := Vector.Basic.vectorOfFn fun column => Vector.Basic.vectorOfFn fun row =>
        (corners.values column row.castSucc).upperLeft - (corners.values column row.succ).lowerLeft }
  horizontal_eq := fun column row => by rw [Vector.Basic.vectorOfFn_apply, Vector.Basic.vectorOfFn_apply]
  vertical_eq := fun column row => by rw [Vector.Basic.vectorOfFn_apply, Vector.Basic.vectorOfFn_apply]

/-- Cache the original primitives' corner values and construct their exact adjacent-cell anchor offsets. -/
def build (primitives : Primitives models numerator) : PrimitiveAnchors primitives := ofCorners (.build primitives)

/-- The retained horizontal offset equals the original primitive difference at the common edge's starting vertex. -/
theorem horizontal_spec (anchors : PrimitiveAnchors primitives) (column : Fin columns) (row : Fin (rows + 1)) :
    anchors.edges.horizontal column row =
      primitives.value column.castSucc row (geometry.vertex column.castSucc.succ row.castSucc) -
        primitives.value column.succ row (geometry.vertex column.castSucc.succ row.castSucc) := by
  rw [anchors.horizontal_eq, anchors.corners.lowerRight_eq, anchors.corners.lowerLeft_eq]
  rfl

/-- The retained vertical offset equals the original primitive difference at the common edge's starting vertex. -/
theorem vertical_spec (anchors : PrimitiveAnchors primitives) (column : Fin (columns + 1)) (row : Fin rows) :
    anchors.edges.vertical column row =
      primitives.value column row.castSucc (geometry.vertex column.castSucc row.castSucc.succ) -
        primitives.value column row.succ (geometry.vertex column.castSucc row.castSucc.succ) := by
  rw [anchors.vertical_eq, anchors.corners.upperLeft_eq, anchors.corners.lowerLeft_eq]
  rfl

section
open Purelib
/-- The original adjacent-column primitive difference minus its retained edge-start offset. -/
def horizontalDrift (anchors : PrimitiveAnchors primitives) (column : Fin columns) (row : Fin (rows + 1)) (point :
  LinearAlgebra.Grid.Offsets.Gaussian) : Gaussian :=
  primitives.value column.castSucc row point - primitives.value column.succ row point - anchors.edges.horizontal column
    row

/-- The original adjacent-row primitive difference minus its retained edge-start offset. -/
def verticalDrift (anchors : PrimitiveAnchors primitives) (column : Fin (columns + 1)) (row : Fin rows) (point :
  LinearAlgebra.Grid.Offsets.Gaussian) : Gaussian :=
  primitives.value column row.castSucc point - primitives.value column row.succ point - anchors.edges.vertical column
    row

/-- The original offset-square defect equals the two retained edge drifts at the shared vertex. -/
theorem square_eq_drifts (anchors : PrimitiveAnchors primitives) (column : Fin columns) (row : Fin rows) :
    anchors.edges.square column row =
      anchors.verticalDrift column.castSucc row (geometry.vertex column.castSucc.succ row.castSucc.succ) -
        anchors.horizontalDrift column row.castSucc (geometry.vertex column.castSucc.succ row.castSucc.succ) := by
  rw [LinearAlgebra.Grid.Offsets.Edges.square, anchors.vertical_spec column.succ row, anchors.horizontal_spec column
    row.succ]
  simp only [horizontalDrift, verticalDrift, Fin.castSucc_succ]
  ring1

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- A common bound on original endpoint drifts bounds each offset-square defect by four times that bound. -/
theorem square_bound (anchors : PrimitiveAnchors primitives) (bound : LinearAlgebra.Grid.Offsets.Coordinate)
    (horizontal : ∀ column row, normSq (anchors.horizontalDrift column row (geometry.vertex column.castSucc.succ
      row.succ)) ≤ bound)
    (vertical : ∀ column row, normSq (anchors.verticalDrift column row (geometry.vertex column.succ row.castSucc.succ))
      ≤ bound)
    (column : Fin columns) (row : Fin rows) : normSq (anchors.edges.square column row) ≤ 4 * bound := by
  rw [anchors.square_eq_drifts]
  have scalarBound : normSq ((anchors.verticalDrift column.castSucc row (geometry.vertex column.castSucc.succ
    row.castSucc.succ)) - (anchors.horizontalDrift column row.castSucc (geometry.vertex column.castSucc.succ
    row.castSucc.succ))) ≤
      2 * (normSq (anchors.verticalDrift column.castSucc row (geometry.vertex column.castSucc.succ row.castSucc.succ)) +
        normSq (anchors.horizontalDrift column row.castSucc (geometry.vertex column.castSucc.succ row.castSucc.succ)))
        := by
    simpa only [Norm.Basic.normSq_eq_canonical] using
      Norm.Bounds.normSq_sub_le_two (anchors.verticalDrift column.castSucc row (geometry.vertex column.castSucc.succ
        row.castSucc.succ)) (anchors.horizontalDrift column row.castSucc (geometry.vertex column.castSucc.succ
        row.castSucc.succ))
  exact scalarBound.trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (add_le_add (vertical column.castSucc row) (horizontal column row.castSucc)) (by decide)).trans_eq (by ring1))

/-- Construct the original primitive-offset grid with the retained initial additive value. -/
def offsets (anchors : PrimitiveAnchors primitives) (initial : Gaussian := 0) : LinearAlgebra.Grid.Offsets
  anchors.edges :=
  .build anchors.edges initial

/-- Add the retained cell offset to the exact original primitive value. -/
def alignedValue (anchors : PrimitiveAnchors primitives) (offsets : LinearAlgebra.Grid.Offsets anchors.edges)
    (column : Fin (columns + 1)) (row : Fin (rows + 1)) (point : LinearAlgebra.Grid.Offsets.Gaussian) : Gaussian :=
  offsets.values column row + primitives.value column row point

/-- The horizontally aligned primitive difference equals the original horizontal edge drift. -/
theorem horizontal_difference (anchors : PrimitiveAnchors primitives) (offsets : LinearAlgebra.Grid.Offsets
  anchors.edges)
    (column : Fin columns) (row : Fin (rows + 1)) (point : LinearAlgebra.Grid.Offsets.Gaussian) :
    anchors.alignedValue offsets column.castSucc row point - anchors.alignedValue offsets column.succ row point =
      anchors.horizontalDrift column row point := by
  simp only [alignedValue, offsets.horizontal, horizontalDrift]
  ring1

/-- The vertically aligned primitive difference equals the original vertical drift minus the retained offset gap. -/
theorem vertical_difference (anchors : PrimitiveAnchors primitives) (offsets : LinearAlgebra.Grid.Offsets
  anchors.edges)
    (column : Fin (columns + 1)) (row : Fin rows) (point : LinearAlgebra.Grid.Offsets.Gaussian) :
    anchors.alignedValue offsets column row.castSucc point - anchors.alignedValue offsets column row.succ point =
      anchors.verticalDrift column row point - offsets.verticalGap column row := by
  simp only [alignedValue, verticalDrift, LinearAlgebra.Grid.Offsets.verticalGap]
  ring1

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- The original vertically aligned primitive gap is bounded by the retained drift bound and grid width.

The exact offset-square defects control accumulated vertical gaps, preserving the original cell indices and local point
bound. -/
theorem vertical_difference_bound (anchors : PrimitiveAnchors primitives) (offsets : LinearAlgebra.Grid.Offsets
  anchors.edges)
    (bound : LinearAlgebra.Grid.Offsets.Coordinate) (nonnegative : 0 ≤ bound)
    (horizontal : ∀ column row, normSq (anchors.horizontalDrift column row (geometry.vertex column.castSucc.succ
      row.succ)) ≤ bound)
    (vertical : ∀ column row, normSq (anchors.verticalDrift column row (geometry.vertex column.succ row.castSucc.succ))
      ≤ bound)
    (column : Fin (columns + 1)) (row : Fin rows) (point : LinearAlgebra.Grid.Offsets.Gaussian)
    (localBound : normSq (anchors.verticalDrift column row point) ≤ bound) :
    normSq (anchors.alignedValue offsets column row.castSucc point - anchors.alignedValue offsets column row.succ point)
      ≤
      (8 * (columns : LinearAlgebra.Grid.Offsets.Coordinate) ^ 2 + 2) * bound := by
  have squares : ∀ column row, Data.Gaussian.Norm.Basic.normSq (anchors.edges.square column row) ≤ 4 * bound := fun
    column
    row => by
    rw [Norm.Basic.normSq_eq_canonical]; exact anchors.square_bound bound horizontal vertical column row
  have gap := offsets.verticalGap_width_bound (4 * bound)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) nonnegative)
    squares column row
  rw [Norm.Basic.normSq_eq_canonical] at gap
  rw [anchors.vertical_difference]
  have scalarBound : normSq ((anchors.verticalDrift column row point) - (offsets.verticalGap column row)) ≤
      2 * (normSq (anchors.verticalDrift column row point) + normSq (offsets.verticalGap column row)) := by
    simpa only [Norm.Basic.normSq_eq_canonical] using
      Norm.Bounds.normSq_sub_le_two (anchors.verticalDrift column row point) (offsets.verticalGap column row)
  exact scalarBound.trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add localBound gap) (by decide)).trans_eq (by
      ring1))

end

end PrimitiveAnchors

end Purelib.Riemann.Integration.RectangularPrimitiveGluing
