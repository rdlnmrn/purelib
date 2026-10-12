module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Vector.Basic
import Purelib.Riemann.Branches.RectangularSheetGauge

import Purelib.LinearAlgebra.Grid.Offsets
import Purelib.Topology.Grid.Signs
public import Purelib.Integration.Polynomial.Rectangle.Boundary.Corners
import Purelib.Riemann.Integration.RectangularPrimitiveOverlap
import Purelib.Tactic.Ring
public import Purelib.Riemann.Integration.RectangularPrimitiveAccuracy

@[expose] public section

/-!
# Cached corner corrections of the actual translated primitive grid

Read each old corner cache and spanning-tree translation once.  The resulting
corner polygons are the endpoint corrections of those very local primitive
models.  Their bounds use the computed grid mismatch; no separate corner
smallness certificate or primitive-value ceiling is requested.
-/

namespace Purelib.Riemann.Integration.RectangularPrimitiveCorners

open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (RegionClearance PrimitiveOverlapBounds)
open Purelib.Riemann.Normalization.RectangularInverseModels (Transitions)

open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry Bank)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives)
open Purelib.Riemann.Integration.RectangularPrimitiveGluing (PrimitiveAnchors CornerValues)
open Purelib.Riemann.Integration.RectangularPrimitiveAccuracy (GridPrimitiveAccuracy)

open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)

open Purelib.Integration in
open Purelib.Data in
open Purelib.LinearAlgebra in
set_option genInjectivity false in
/-- Translated primitive corner values with cached junction and endpoint corrections.

Every corner agrees with the same anchored primitive and retained grid offset. Structural caches retain the interior
corner areas and their exact aggregate identities. -/
structure AlignedCorners {polynomial numerator : Polynomial} {columns rows : Nat} {geometry : Geometry columns rows}
    {models : Bank polynomial geometry} {primitives : Primitives models numerator}
    (anchors : PrimitiveAnchors primitives) (offsets : LinearAlgebra.Grid.Offsets anchors.edges) where
  /-- The retained translated values at each rectangle's four corners. -/ values :
    Polynomial.Rectangle.Boundary.Corners.Values columns rows
  /-- The lower-left cache equals the aligned primitive at that geometric vertex. -/ lowerLeft_eq : ∀ column row,
    (values column row).lowerLeft = anchors.alignedValue offsets column row (geometry.vertex column.castSucc
    row.castSucc)
  /-- The lower-right cache equals the aligned primitive at that geometric vertex. -/ lowerRight_eq : ∀ column row,
    (values column row).lowerRight = anchors.alignedValue offsets column row (geometry.vertex column.succ row.castSucc)
  /-- The upper-left cache equals the aligned primitive at that geometric vertex. -/ upperLeft_eq : ∀ column row,
    (values column row).upperLeft = anchors.alignedValue offsets column row (geometry.vertex column.castSucc row.succ)
  /-- The upper-right cache equals the aligned primitive at that geometric vertex. -/ upperRight_eq : ∀ column row,
    (values column row).upperRight = anchors.alignedValue offsets column row (geometry.vertex column.succ row.succ)
  /-- The structural grid of cached interior corner corrections. -/ cornerAreas : Data.Vector
    (Data.Vector Gaussian rows) columns
  /-- Each cached correction equals the corner polygon area of the retained values. -/ cornerAreas_eq : ∀ column row,
    cornerAreas column row = Polynomial.Rectangle.Boundary.Corners.interiorCorner values column row
  /-- The cached exterior joining correction. -/ exteriorJoins : Gaussian
  /-- The joining cache equals the exterior correction of the retained values. -/ exteriorJoins_eq : exteriorJoins =
    Polynomial.Rectangle.Boundary.Corners.exteriorJoins values
  /-- The cached total endpoint correction. -/ endpointTotal : Gaussian
  /-- The endpoint cache equals the endpoint sum of the retained values. -/ endpointTotal_eq : endpointTotal =
    Polynomial.Rectangle.Boundary.Corners.endpointSum values
  /-- The cached sum of all interior corner corrections. -/ cornerTotal : Gaussian
  /-- The corner cache equals the corner sum of the retained values. -/ cornerTotal_eq : cornerTotal =
    Polynomial.Rectangle.Boundary.Corners.cornerSum values

constructive_injectivity AlignedCorners

namespace AlignedCorners

variable {polynomial numerator : Polynomial} {columns rows : Nat} {geometry : Geometry columns rows}
    {models : Bank polynomial geometry} {primitives : Primitives models numerator}
    {anchors : PrimitiveAnchors primitives} {offsets : LinearAlgebra.Grid.Offsets anchors.edges}

open Purelib.Algebra in
open Purelib.Integration in
open Purelib.Data in
open Purelib.LinearAlgebra in
/-- Translate cached primitive corner readings and retain all corner corrections.

Reuse each existing corner value and grid offset without reevaluating a polynomial, then sum the cached interior areas.
-/
def build (anchors : PrimitiveAnchors primitives) (offsets : LinearAlgebra.Grid.Offsets anchors.edges) : AlignedCorners
  anchors offsets :=
  let values := Vector.Basic.vectorOfFn fun column => Vector.Basic.vectorOfFn fun row =>
    let old := anchors.corners.values column row
    let shift := offsets.values column row
    (⟨shift + old.lowerLeft, shift + old.lowerRight, shift + old.upperLeft, shift + old.upperRight⟩ : CornerValues)
  let cornerAreas := Vector.Basic.vectorOfFn fun column => Vector.Basic.vectorOfFn fun row =>
    Polynomial.Rectangle.Boundary.Corners.interiorCorner values column row
  { values := values
    lowerLeft_eq := fun column row => by
      dsimp only [values]
      rw [Vector.Basic.vectorOfFn_apply, Vector.Basic.vectorOfFn_apply]
      exact congrArg (offsets.values column row + ·) (anchors.corners.lowerLeft_eq column row)
    lowerRight_eq := fun column row => by
      dsimp only [values]
      rw [Vector.Basic.vectorOfFn_apply, Vector.Basic.vectorOfFn_apply]
      exact congrArg (offsets.values column row + ·) (anchors.corners.lowerRight_eq column row)
    upperLeft_eq := fun column row => by
      dsimp only [values]
      rw [Vector.Basic.vectorOfFn_apply, Vector.Basic.vectorOfFn_apply]
      exact congrArg (offsets.values column row + ·) (anchors.corners.upperLeft_eq column row)
    upperRight_eq := fun column row => by
      dsimp only [values]
      rw [Vector.Basic.vectorOfFn_apply, Vector.Basic.vectorOfFn_apply]
      exact congrArg (offsets.values column row + ·) (anchors.corners.upperRight_eq column row)
    cornerAreas := cornerAreas
    cornerAreas_eq := fun column row => by dsimp only [cornerAreas]; rw [Vector.Basic.vectorOfFn_apply,
      Vector.Basic.vectorOfFn_apply]
    exteriorJoins := Polynomial.Rectangle.Boundary.Corners.exteriorJoins values
    exteriorJoins_eq := rfl
    endpointTotal := Polynomial.Rectangle.Boundary.Corners.endpointSum values
    endpointTotal_eq := rfl
    cornerTotal := FiniteSum.Fin.sumFin fun column => FiniteSum.Fin.sumFin fun row => cornerAreas column row
    cornerTotal_eq := by
      apply FiniteSum.Fin.sumFin_congr
      intro column
      apply FiniteSum.Fin.sumFin_congr
      intro row
      dsimp only [cornerAreas]
      rw [Vector.Basic.vectorOfFn_apply, Vector.Basic.vectorOfFn_apply] }

open Purelib.Integration in
/-- The endpoint correction splits into exterior joins and interior corner corrections. -/
theorem endpoint_decomposition (corners : AlignedCorners anchors offsets) :
    corners.endpointTotal = corners.exteriorJoins + corners.cornerTotal := by
  rw [corners.endpointTotal_eq, corners.exteriorJoins_eq, corners.cornerTotal_eq]
  exact Polynomial.Rectangle.Boundary.Corners.endpointSum_eq corners.values

open Purelib.Algebra in
/-- Read the total corner correction as the double sum of its structural area cache. -/
theorem cornerTotal_eq_sum (corners : AlignedCorners anchors offsets) :
    corners.cornerTotal = FiniteSum.Fin.sumFin
      (fun column => FiniteSum.Fin.sumFin (fun row => corners.cornerAreas column row)) := by
  rw [corners.cornerTotal_eq]
  apply FiniteSum.Fin.sumFin_congr
  intro column
  apply FiniteSum.Fin.sumFin_congr
  intro row
  exact (corners.cornerAreas_eq column row).symm

end AlignedCorners

namespace GridPrimitiveAccuracy

variable {polynomial numerator : Polynomial} {ambient : Box} {clearance : RegionClearance polynomial ambient}
    {bounds : PrimitiveOverlapBounds clearance numerator} {columns rows : Nat} {target : Coordinate}
    {geometry : Geometry columns rows} {bank : Bank polynomial geometry}

open Purelib.Riemann in
open Purelib.Integration in
open Purelib.Topology in
open Purelib.Data in
open Purelib.LinearAlgebra in
/-- Bound one cached corner correction by sixty-four times the squared global overlap bound.

Every model box refines the common ambient box; adjacent and diagonal overlap estimates apply to the same aligned corner
readings. -/
theorem corner_bound (request : GridPrimitiveAccuracy bounds columns target)
    {transitions : Transitions (bank.refine request.index)} {gauge : Grid.Signs.Gauge transitions.flatGrid}
    {primitives : Primitives (Branches.RectangularSheetGauge.Transitions.oriented transitions gauge) numerator} {anchors
      : PrimitiveAnchors primitives}
    {offsets : LinearAlgebra.Grid.Offsets anchors.edges} (corners : AlignedCorners anchors offsets)
    (refines : ∀ column row, (geometry.box column row).Refines ambient) (column : Fin columns) (row : Fin rows) :
    normSq (corners.cornerAreas column row) ≤ 64 * request.globalBound ^ 2 := by
  have nonnegative := request.edgeBound_nonnegative.trans request.edgeBound_le_globalBound
  have north := Integration.RectangularPrimitiveOverlap.GridPrimitiveAccuracy.same_column_bound request anchors offsets
    refines column.castSucc row.succ row.castSucc
    (geometry.lowerRight_mem column.castSucc row.succ) (geometry.upperRight_mem column.castSucc row.castSucc)
  have east := Integration.RectangularPrimitiveOverlap.GridPrimitiveAccuracy.same_row_bound request anchors offsets
    refines column.succ column.castSucc row.castSucc
    (geometry.upperLeft_mem column.succ row.castSucc) (geometry.upperRight_mem column.castSucc row.castSucc)
  have diagonal := Integration.RectangularPrimitiveAccuracy.GridPrimitiveAccuracy.overlap_bound request anchors offsets
    refines column.succ column.castSucc row.succ row.castSucc
    (geometry.lowerLeft_mem column.succ row.succ) (geometry.upperRight_mem column.castSucc row.castSucc)
  rw [← Gaussian.Norm.Basic.normSq_eq_canonical] at north diagonal east
  rw [corners.cornerAreas_eq, Polynomial.Rectangle.Boundary.Corners.interiorCorner,
    corners.upperRight_eq, corners.lowerRight_eq, corners.lowerLeft_eq, corners.upperLeft_eq]
  have scalarBound := Polynomial.Rectangle.Boundary.Corners.cornerArea_bound nonnegative
    (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) nonnegative) north diagonal east
  rw [Gaussian.Norm.Basic.normSq_eq_canonical] at scalarBound
  exact scalarBound.trans_eq (by ring1)

open Purelib.Algebra in
open Purelib.Riemann in
open Purelib.Topology in
open Purelib.Data in
open Purelib.LinearAlgebra in
/-- Bound the total corner correction using only the coarse grid size and overlap bound.

Its squared norm is at most sixty-four times the squared junction count times the squared global mismatch bound. -/
theorem cornerTotal_bound (request : GridPrimitiveAccuracy bounds columns target)
    {transitions : Transitions (bank.refine request.index)} {gauge : Grid.Signs.Gauge transitions.flatGrid}
    {primitives : Primitives (Branches.RectangularSheetGauge.Transitions.oriented transitions gauge) numerator} {anchors
      : PrimitiveAnchors primitives}
    {offsets : LinearAlgebra.Grid.Offsets anchors.edges} (corners : AlignedCorners anchors offsets)
    (refines : ∀ column row, (geometry.box column row).Refines ambient) :
    normSq corners.cornerTotal ≤ 64 * ((columns : Coordinate) * (rows : Coordinate)) ^ 2 * request.globalBound ^ 2 := by
  rw [corners.cornerTotal_eq_sum]
  have rowBound (column : Fin columns) :
      Data.Gaussian.Norm.Basic.normSq (FiniteSum.Fin.sumFin (fun row => corners.cornerAreas column row)) ≤
        (rows : Coordinate) ^ 2 * (64 * request.globalBound ^ 2) := by
    apply Gaussian.Norm.Sum.Indexed.normSq_sumFin_le
    intro row
    have scalar := corner_bound request corners refines column row
    simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using scalar
  have estimate := Gaussian.Norm.Sum.Indexed.normSq_sumFin_le
    (fun column => FiniteSum.Fin.sumFin (fun row => corners.cornerAreas column row))
    ((rows : Coordinate) ^ 2 * (64 * request.globalBound ^ 2)) rowBound
  rw [Gaussian.Norm.Basic.normSq_eq_canonical] at estimate
  exact estimate.trans_eq (by ring1)

end GridPrimitiveAccuracy

end Purelib.Riemann.Integration.RectangularPrimitiveCorners
