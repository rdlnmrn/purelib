module
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
import Purelib.Riemann.Normalization.InverseModelEdgeTransition
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
public import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Affine
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.RectangularPrimitiveModels

import Purelib.LinearAlgebra.Grid.Offsets
import Purelib.Topology.Grid.Signs
public import Purelib.Riemann.Integration.RectangularPrimitiveGluing
public import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Data.Rat.Fraction.Order

@[expose] public section

/-!
# Requested accuracy for an entire glued regular grid patch

The refinement index is computed before constructing the larger primitive
polynomials.  It pays both local drift and the quadratic grid-width factor
for non-tree offsets.  The bounds use the fixed ambient clearance, not a
Taylor ceiling that grows with the refined polynomial degree.
-/

namespace Purelib.Riemann.Integration.RectangularPrimitiveAccuracy

variable {pairs : Nat}

open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (RegionClearance PrimitiveOverlapBounds)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry Bank Transitions)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives)
open Purelib.Riemann.Integration.RectangularPrimitiveGluing (PrimitiveAnchors)
open Purelib.Riemann.Integration.RectangularRefinementSigns (SheetCache)
open Purelib.Riemann.Normalization.InverseModelEdgeTransition (line_one)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius quarterRadius_eq_mul_pow)

open Purelib.Approximation.Rational in
set_option genInjectivity false in
/-- A paid rectangular primitive-gluing request retaining edge scale, grid scale and exact refinement depth.

The cached local and global bounds retain their exact geometric formulas, and the global bound is strictly below the
original target. -/
structure GridPrimitiveAccuracy {polynomial numerator : Polynomial} {ambient : Box}
    {clearance : RegionClearance polynomial ambient} (bounds : PrimitiveOverlapBounds clearance numerator)
    (columns : Nat) (target : Coordinate) (pairs : optParam Nat 0) where
  /-- The cached original ambient edge-error scale. -/ edgeScale : Coordinate
  /-- The edge-scale cache equals the original coefficient bound times ambient diagonal formula. -/ edgeScale_eq :
    edgeScale = 24 * (1 / 256) * bounds.weight pairs * ambient.diagonalSq
  /-- The cached original width-dependent global scale. -/ scale : Coordinate
  /-- The global scale equals the original gluing factor times the exact edge scale. -/ scale_eq : scale = (8 * (columns
    : Coordinate) ^ 2 + 2) * edgeScale
  /-- The retained common inverse-model refinement depth. -/ index : Nat
  /-- The cached original edge bound at the retained depth. -/ edgeBound : Coordinate
  /-- The edge bound equals the exact quarter-radius refinement of its retained scale. -/ edgeBound_eq : edgeBound =
    quarterRadius edgeScale index
  /-- The cached original width-dependent global bound. -/ globalBound : Coordinate
  /-- The global bound equals the original gluing factor times the retained edge bound. -/ globalBound_eq : globalBound
    = (8 * (columns : Coordinate) ^ 2 + 2) * edgeBound
  /-- The exact retained global bound is strictly below the original target. -/ accurate : globalBound < target

constructive_injectivity GridPrimitiveAccuracy

namespace GridPrimitiveAccuracy

variable {polynomial numerator : Polynomial} {ambient : Normalization.InverseRootPolynomial.Box}
  {clearance : RegionClearance polynomial ambient}
    {bounds : PrimitiveOverlapBounds clearance numerator} {columns : Nat} {target : Coordinate}

section
open Purelib.Data.Rat
/-- The original column-dependent gluing factor is at least one. -/
public theorem factor_one_le (columns : Nat) : (1 : Coordinate) ≤ 8 * (columns : Coordinate) ^ 2 + 2 :=
  (show (1 : Coordinate) ≤ 2 by decide).trans
    (le_add_of_nonneg_left (Arithmetic.mul_nonneg_direct (by decide)
      (Arithmetic.sq_nonneg_direct _)))

/-- The retained original odd-power overlap weight is nonnegative. -/
public theorem product_nonnegative (bounds : PrimitiveOverlapBounds clearance numerator)
    (pairs : optParam Nat 0) : 0 ≤ bounds.weight pairs := bounds.weight_nonnegative pairs

/-- The original ambient diagonal and coefficient bounds give a nonnegative edge scale. -/
public theorem edgeScale_nonneg (bounds : PrimitiveOverlapBounds clearance numerator)
    (pairs : optParam Nat 0) :
    0 ≤ 24 * (1 / 256 : Coordinate) * bounds.weight pairs * ambient.diagonalSq :=
  Arithmetic.mul_nonneg_direct
    (Arithmetic.mul_nonneg_direct (by decide +kernel) (product_nonnegative bounds pairs))
      ambient.diagonalSq_nonneg

end

open Purelib.Approximation.Rational in
open Purelib.Data.Rat in
/-- Choose and cache the first geometric refinement depth paying the original global gluing target.

The exact edge scale and column-dependent factor determine one shared search; its retained edge and global bounds
preserve that same depth and payment. -/
def build (bounds : PrimitiveOverlapBounds clearance numerator) (columns : Nat) (target : Coordinate)
    (positive : 0 < target) (pairs : optParam Nat 0) : GridPrimitiveAccuracy bounds columns target pairs :=
  let edgeScale := 24 * (1 / 256) * bounds.weight pairs * ambient.diagonalSq
  let factor := 8 * Budget.Aggregate.countCoordinate columns ^ 2 + 2
  have factorEq : factor = 8 * (columns : Coordinate) ^ 2 + 2 := by
    dsimp only [factor]
    rw [Budget.Aggregate.countCoordinate_eq]
  let scale := factor * edgeScale
  have scaleNonnegative : 0 ≤ scale := Arithmetic.mul_nonneg_direct
    ((show (0 : Coordinate) ≤ 1 by decide).trans ((factor_one_le columns).trans_eq factorEq.symm))
      (edgeScale_nonneg bounds pairs)
  let index := Geometric.Search.firstQuarterBelow scale 0 target
  let edgeBound := quarterRadius edgeScale index
  let globalBound := factor * edgeBound
  have equal : globalBound = quarterRadius scale index := by
    simp only [globalBound, edgeBound, scale, quarterRadius_eq_mul_pow]
    ring1
  { edgeScale := edgeScale
    edgeScale_eq := rfl
    scale := scale
    scale_eq := by dsimp only [scale]; rw [factorEq]
    index := index
    edgeBound := edgeBound
    edgeBound_eq := rfl
    globalBound := globalBound
    globalBound_eq := by dsimp only [globalBound]; rw [factorEq]
    accurate := equal.trans_lt (Geometric.Search.firstQuarterBelow_accurate scale scaleNonnegative 0 target positive) }

open Purelib.Approximation.Rational in
/-- The retained original edge bound is nonnegative. -/
theorem edgeBound_nonnegative (request : GridPrimitiveAccuracy bounds columns target pairs) :
    0 ≤ request.edgeBound := by
  rw [request.edgeBound_eq]
  exact Geometric.Basic.quarterRadius_nonneg
    ((edgeScale_nonneg bounds pairs).trans_eq request.edgeScale_eq.symm) request.index

open Purelib.Data.Rat in
/-- The retained original edge bound is at most its corresponding global bound. -/
theorem edgeBound_le_globalBound (request : GridPrimitiveAccuracy bounds columns target pairs) : request.edgeBound ≤
  request.globalBound := by
  rw [request.globalBound_eq]
  exact (by ring1 : request.edgeBound = 1 * request.edgeBound).trans_le
    (Arithmetic.mul_le_mul_of_nonneg_right_direct (factor_one_le columns)
      request.edgeBound_nonnegative)

section
open Purelib.Approximation.Rational
open Purelib.Data.Rat
/-- The original refined local increment scale, including the unit parameter square, is bounded by the retained edge
allowance. -/
private theorem local_scale_le (request : GridPrimitiveAccuracy bounds columns target pairs)
    {left right length parameter : Coordinate}
    (leftBound : left ≤ quarterRadius (1 / 256) request.index)
    (rightBound : right ≤ quarterRadius (1 / 256) request.index)
    (lengthNonnegative : 0 ≤ length) (lengthBound : length ≤ ambient.diagonalSq)
    (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
    12 * (left + right) * bounds.weight pairs * length * parameter ^ 2 ≤ request.edgeBound :=
      by
  have residualNonnegative := Geometric.Basic.quarterRadius_nonneg (by decide +kernel : (0 : Coordinate) ≤ 1 / 256)
    request.index
  have productNonnegative := product_nonnegative bounds pairs
  have squared := Arithmetic.pow_le_pow_direct inside.1 inside.2 2
  have parameterBound : parameter ^ 2 ≤ (1 : Coordinate) := squared.trans_eq (by ring1)
  have baseNonnegative : 0 ≤ 12 * (quarterRadius (1 / 256) request.index + quarterRadius
    (1 / 256) request.index) *
      bounds.weight pairs := Arithmetic.mul_nonneg_direct
    (Arithmetic.mul_nonneg_direct (by decide) (add_nonneg residualNonnegative residualNonnegative))
      productNonnegative
  calc
    _ ≤ 12 * (quarterRadius (1 / 256) request.index + quarterRadius (1 / 256)
      request.index) *
        bounds.weight pairs * length * parameter ^ 2 :=
      Arithmetic.mul_le_mul_of_nonneg_right_direct
        (Arithmetic.mul_le_mul_of_nonneg_right_direct
          (Arithmetic.mul_le_mul_of_nonneg_right_direct
            (Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add leftBound rightBound) (by decide))
            productNonnegative) lengthNonnegative) (Arithmetic.sq_nonneg_direct _)
    _ ≤ 12 * (quarterRadius (1 / 256) request.index + quarterRadius (1 / 256)
      request.index) *
        bounds.weight pairs * ambient.diagonalSq * 1 :=
      Arithmetic.mul_le_mul_direct
        (Arithmetic.mul_le_mul_of_nonneg_left_direct lengthBound baseNonnegative) parameterBound
        (Arithmetic.sq_nonneg_direct _) (Arithmetic.mul_nonneg_direct baseNonnegative
          ambient.diagonalSq_nonneg)
    _ = request.edgeBound := by
      rw [request.edgeBound_eq, request.edgeScale_eq]
      simp only [quarterRadius_eq_mul_pow]
      ring1

/-- The original refined full-edge increment scale is bounded by the retained edge allowance. -/
theorem local_scale_bound (request : GridPrimitiveAccuracy bounds columns target pairs)
    {left right length : Coordinate}
    (leftBound : left ≤ quarterRadius (1 / 256) request.index)
    (rightBound : right ≤ quarterRadius (1 / 256) request.index)
    (lengthNonnegative : 0 ≤ length) (lengthBound : length ≤ ambient.diagonalSq) :
    12 * (left + right) * bounds.weight pairs * length ≤ request.edgeBound := by
  have estimate := request.local_scale_le leftBound rightBound lengthNonnegative lengthBound
    (parameter := 1) ⟨by decide, le_rfl⟩
  simpa only [one_pow, Fraction.Field.mul_one_direct] using estimate

end

section
open Purelib
open Purelib.Data.Gaussian
open Purelib.Geometry.Rational
open Purelib.Riemann.Branches
/-- The original adjacent-column primitive drift meets the retained edge bound along the common segment. -/
theorem horizontal_drift_bound (request : GridPrimitiveAccuracy bounds columns target pairs)
    {rows : Nat} {geometry : Geometry columns rows} {bank : Bank polynomial geometry}
    {transitions : Transitions (bank.refine request.index)} {gauge : Topology.Grid.Signs.Gauge transitions.flatGrid}
    {primitives : Primitives (RectangularSheetGauge.Transitions.oriented transitions gauge) numerator pairs} (anchors :
      PrimitiveAnchors primitives)
    (refines : ∀ column row, (geometry.box column row).Refines ambient)
    (column : Fin columns) (row : Fin (rows + 1)) {parameter : Coordinate} (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
    normSq (anchors.horizontalDrift column row
      (Affine.line (geometry.vertex column.castSucc.succ row.castSucc)
        (geometry.vertex column.castSucc.succ row.succ - geometry.vertex column.castSucc.succ row.castSucc) parameter))
          ≤ request.edgeBound := by
  rw [PrimitiveAnchors.horizontalDrift, anchors.horizontal_spec]
  have incrementBound := primitives.horizontal_increment_le bounds refines column row inside
  have lengthBound := Box.normSq_sub_le_diagonalSq
    ((refines column.castSucc row).contains (geometry.upperRight_mem column.castSucc row))
    ((refines column.castSucc row).contains (geometry.lowerRight_mem column.castSucc row))
  rw [Norm.Basic.normSq_eq_canonical] at lengthBound
  have scaleBound := request.local_scale_le
    (bank.refine_uniform_bound request.index column.castSucc row)
    (bank.refine_uniform_bound request.index column.succ row)
    (normSq_nonneg (geometry.vertex column.castSucc.succ row.succ - geometry.vertex column.castSucc.succ
      row.castSucc))
    lengthBound inside
  exact incrementBound.trans scaleBound

/-- The original adjacent-row primitive drift meets the retained edge bound along the common segment. -/
theorem vertical_drift_bound (request : GridPrimitiveAccuracy bounds columns target pairs)
    {rows : Nat} {geometry : Geometry columns rows} {bank : Bank polynomial geometry}
    {transitions : Transitions (bank.refine request.index)} {gauge : Topology.Grid.Signs.Gauge transitions.flatGrid}
    {primitives : Primitives (RectangularSheetGauge.Transitions.oriented transitions gauge) numerator pairs} (anchors :
      PrimitiveAnchors primitives)
    (refines : ∀ column row, (geometry.box column row).Refines ambient)
    (column : Fin (columns + 1)) (row : Fin rows) {parameter : Coordinate} (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
    normSq (anchors.verticalDrift column row
      (Affine.line (geometry.vertex column.castSucc row.castSucc.succ)
        (geometry.vertex column.succ row.castSucc.succ - geometry.vertex column.castSucc row.castSucc.succ) parameter))
          ≤ request.edgeBound := by
  rw [PrimitiveAnchors.verticalDrift, anchors.vertical_spec]
  have incrementBound := primitives.vertical_increment_le bounds refines column row inside
  have lengthBound := Box.normSq_sub_le_diagonalSq
    ((refines column row.castSucc).contains (geometry.upperRight_mem column row.castSucc))
    ((refines column row.castSucc).contains (geometry.upperLeft_mem column row.castSucc))
  rw [Norm.Basic.normSq_eq_canonical] at lengthBound
  have scaleBound := request.local_scale_le
    (bank.refine_uniform_bound request.index column row.castSucc)
    (bank.refine_uniform_bound request.index column row.succ)
    (normSq_nonneg (geometry.vertex column.succ row.castSucc.succ - geometry.vertex column.castSucc
      row.castSucc.succ))
    lengthBound inside
  exact incrementBound.trans scaleBound

end

open Purelib
open Purelib.Geometry.Rational
open Purelib.Riemann.Branches
/-- The original horizontally aligned primitive gap meets the retained global bound along the common segment. -/
theorem horizontal_bound (request : GridPrimitiveAccuracy bounds columns target pairs)
    {rows : Nat} {geometry : Geometry columns rows} {bank : Bank polynomial geometry}
    {transitions : Transitions (bank.refine request.index)} {gauge : Topology.Grid.Signs.Gauge transitions.flatGrid}
    {primitives : Primitives (RectangularSheetGauge.Transitions.oriented transitions gauge) numerator pairs} (anchors :
      PrimitiveAnchors primitives)
    (offsets : LinearAlgebra.Grid.Offsets anchors.edges)
    (refines : ∀ column row, (geometry.box column row).Refines ambient)
    (column : Fin columns) (row : Fin (rows + 1)) {parameter : Coordinate} (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
    let point := Affine.line (geometry.vertex column.castSucc.succ row.castSucc)
      (geometry.vertex column.castSucc.succ row.succ - geometry.vertex column.castSucc.succ row.castSucc) parameter
    normSq (anchors.alignedValue offsets column.castSucc row point - anchors.alignedValue offsets column.succ row point)
      ≤ request.globalBound := by
  dsimp only
  rw [anchors.horizontal_difference]
  exact (request.horizontal_drift_bound anchors refines column row inside).trans request.edgeBound_le_globalBound

/-- The original vertically aligned primitive gap meets the retained global bound along the common segment. -/
theorem vertical_bound (request : GridPrimitiveAccuracy bounds columns target pairs)
    {rows : Nat} {geometry : Geometry columns rows} {bank : Bank polynomial geometry}
    {transitions : Transitions (bank.refine request.index)} {gauge : Topology.Grid.Signs.Gauge transitions.flatGrid}
    {primitives : Primitives (RectangularSheetGauge.Transitions.oriented transitions gauge) numerator pairs} (anchors :
      PrimitiveAnchors primitives)
    (offsets : LinearAlgebra.Grid.Offsets anchors.edges)
    (refines : ∀ column row, (geometry.box column row).Refines ambient)
    (column : Fin (columns + 1)) (row : Fin rows) {parameter : Coordinate} (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
    let point := Affine.line (geometry.vertex column.castSucc row.castSucc.succ)
      (geometry.vertex column.succ row.castSucc.succ - geometry.vertex column.castSucc row.castSucc.succ) parameter
    normSq (anchors.alignedValue offsets column row.castSucc point - anchors.alignedValue offsets column row.succ point)
      ≤ request.globalBound := by
  have horizontal (column : Fin columns) (row : Fin (rows + 1)) :
      normSq (anchors.horizontalDrift column row (geometry.vertex column.castSucc.succ row.succ)) ≤ request.edgeBound :=
        by
    have bound := request.horizontal_drift_bound anchors refines column row (parameter := 1) ⟨by decide, le_rfl⟩
    rw [line_one] at bound
    exact bound
  have vertical (column : Fin (columns + 1)) (row : Fin rows) :
      normSq (anchors.verticalDrift column row (geometry.vertex column.succ row.castSucc.succ)) ≤ request.edgeBound :=
        by
    have bound := request.vertical_drift_bound anchors refines column row (parameter := 1) ⟨by decide, le_rfl⟩
    rw [line_one] at bound
    exact bound
  have estimate := anchors.vertical_difference_bound offsets request.edgeBound request.edgeBound_nonnegative horizontal
    vertical
    column row _ (request.vertical_drift_bound anchors refines column row inside)
  rw [← request.globalBound_eq] at estimate
  exact estimate

/-- The original horizontally aligned primitive gap is strictly below the requested target. -/
theorem horizontal_accurate (request : GridPrimitiveAccuracy bounds columns target pairs)
    {rows : Nat} {geometry : Geometry columns rows} {bank : Bank polynomial geometry}
    {transitions : Transitions (bank.refine request.index)} {gauge : Topology.Grid.Signs.Gauge transitions.flatGrid}
    {primitives : Primitives (RectangularSheetGauge.Transitions.oriented transitions gauge) numerator pairs} (anchors :
      PrimitiveAnchors primitives)
    (offsets : LinearAlgebra.Grid.Offsets anchors.edges)
    (refines : ∀ column row, (geometry.box column row).Refines ambient)
    (column : Fin columns) (row : Fin (rows + 1)) {parameter : Coordinate} (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
    let point := Affine.line (geometry.vertex column.castSucc.succ row.castSucc)
      (geometry.vertex column.castSucc.succ row.succ - geometry.vertex column.castSucc.succ row.castSucc) parameter
    normSq (anchors.alignedValue offsets column.castSucc row point - anchors.alignedValue offsets column.succ row point)
      < target :=
  (request.horizontal_bound anchors offsets refines column row inside).trans_lt request.accurate

/-- The original vertically aligned primitive gap is strictly below the requested target. -/
theorem vertical_accurate (request : GridPrimitiveAccuracy bounds columns target pairs)
    {rows : Nat} {geometry : Geometry columns rows} {bank : Bank polynomial geometry}
    {transitions : Transitions (bank.refine request.index)} {gauge : Topology.Grid.Signs.Gauge transitions.flatGrid}
    {primitives : Primitives (RectangularSheetGauge.Transitions.oriented transitions gauge) numerator pairs} (anchors :
      PrimitiveAnchors primitives)
    (offsets : LinearAlgebra.Grid.Offsets anchors.edges)
    (refines : ∀ column row, (geometry.box column row).Refines ambient)
    (column : Fin (columns + 1)) (row : Fin rows) {parameter : Coordinate} (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
    let point := Affine.line (geometry.vertex column.castSucc row.castSucc.succ)
      (geometry.vertex column.succ row.castSucc.succ - geometry.vertex column.castSucc row.castSucc.succ) parameter
    normSq (anchors.alignedValue offsets column row.castSucc point - anchors.alignedValue offsets column row.succ point)
      < target :=
  (request.vertical_bound anchors offsets refines column row inside).trans_lt request.accurate

end GridPrimitiveAccuracy

open Purelib in
open Purelib.Riemann.Branches in
set_option genInjectivity false in
/-- Original transition and gauge caches with their exact oriented primitives, anchors and additive offsets.

Each retained stage is indexed by the preceding original cache, preserving the sheet choices and primitive ownership
throughout the construction. -/
structure GluedPrimitives {polynomial : Polynomial} {columns rows : Nat} {geometry : Geometry columns rows}
    (bank : Bank polynomial geometry) (numerator : Polynomial) (pairs : optParam Nat 0) where
  /-- The retained original bank's exact transition-sign cache. -/ transitions : Transitions bank
  /-- The retained gauge on those exact original transitions. -/ gauge : Topology.Grid.Signs.Gauge transitions.flatGrid
  /-- The cached primitives for the exact gauge-oriented original model bank. -/ primitives : Primitives
    (RectangularSheetGauge.Transitions.oriented transitions gauge) numerator pairs
  /-- The retained original primitive corner and edge-anchor caches. -/ anchors : PrimitiveAnchors primitives
  /-- The retained additive offsets indexed by the exact original anchors. -/ offsets :
    LinearAlgebra.Grid.Offsets anchors.edges

constructive_injectivity GluedPrimitives

open Purelib.Riemann.Branches in
open Purelib.Riemann.Integration in
/-- Construct original oriented primitives, anchors and offsets from the exact retained sheet cache. -/
def GluedPrimitives.ofSheets {polynomial : Polynomial} {columns rows : Nat} {geometry : Geometry columns rows}
    {bank : Bank polynomial geometry} (sheets : SheetCache bank) (numerator : Polynomial) (pairs : optParam Nat 0) :
    GluedPrimitives bank numerator pairs :=
  let transitions := sheets.transitions
  let gauge := sheets.gauge
  let oriented := RectangularSheetGauge.Transitions.oriented transitions gauge
  let primitives := Primitives.build oriented numerator pairs
  let anchors := PrimitiveAnchors.build primitives
  ⟨transitions, gauge, primitives, anchors, anchors.offsets⟩

/-- Refine the original sheet cache at the paid depth and construct its exact glued primitives. -/
def GridPrimitiveAccuracy.prepare {polynomial numerator : Polynomial} {ambient : Box}
    {clearance : RegionClearance polynomial ambient} {bounds : PrimitiveOverlapBounds clearance numerator}
    {columns rows : Nat} {target : Coordinate} {geometry : Geometry columns rows}
    {bank : Bank polynomial geometry} (request : GridPrimitiveAccuracy bounds columns target pairs)
    (sheets : SheetCache bank) : GluedPrimitives (bank.refine request.index) numerator pairs :=
  GluedPrimitives.ofSheets (sheets.refine request.index) numerator pairs

end Purelib.Riemann.Integration.RectangularPrimitiveAccuracy

end

public section

namespace Purelib.Riemann.Integration.RectangularPrimitiveAccuracy.GridPrimitiveAccuracy

open Purelib
open Purelib.Approximation.Rational
open Purelib.Data.Rat
open Purelib.Riemann.Integration

open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (RegionClearance PrimitiveOverlapBounds)
open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Data.Rat.Fraction.Order
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius_antitone)

variable {polynomial numerator : Polynomial} {ambient : Box} {clearance : RegionClearance polynomial ambient}
    {bounds : PrimitiveOverlapBounds clearance numerator} {columns pairs : Nat} {target : Coordinate}

/-- The retained grid primitive accuracy scale is nonnegative.

The retained grid scale is a product of the original nonnegative factors.
Its displayed square, count factors and ambient squared diagonal preserve
nonnegativity. -/
theorem scale_nonnegative (request : GridPrimitiveAccuracy bounds columns target pairs) : 0 ≤
  request.scale := by
  rw [request.scale_eq, request.edgeScale_eq]
  exact Arithmetic.mul_nonneg_direct
    (add_nonneg (Arithmetic.mul_nonneg_direct (by decide)
      (Arithmetic.sq_nonneg_direct _)) (by decide))
    (Arithmetic.mul_nonneg_direct
      (Arithmetic.mul_nonneg_direct (by decide +kernel)
        (product_nonnegative bounds pairs)) ambient.diagonalSq_nonneg)

/-- The retained grid global bound equals its scale times the quarter-radius decay at its index.

The global bound and scale use the same retained grid index. Their defining
scalar equations identify the original quarter-radius decay exactly. -/
theorem globalBound_eq_quarter (request : GridPrimitiveAccuracy bounds columns target pairs) :
    request.globalBound = Geometric.Basic.quarterRadius request.scale request.index := by
  rw [request.globalBound_eq, request.edgeBound_eq, request.scale_eq]
  simp only [Geometric.Basic.quarterRadius_eq_mul_pow]
  ring1

/-- Raise a grid accuracy request to the maximum of its original index and the supplied minimum.

The original scales are retained, and the edge and global bounds are recomputed at the new index with their accuracy
certificates. -/
@[expose] def atLeast (request : GridPrimitiveAccuracy bounds columns target pairs) (minimum :
  Nat) :
    GridPrimitiveAccuracy bounds columns target pairs :=
  let index := max minimum request.index
  { edgeScale := request.edgeScale, edgeScale_eq := request.edgeScale_eq
    scale := request.scale, scale_eq := request.scale_eq
    index := index
    edgeBound := Geometric.Basic.quarterRadius request.edgeScale index, edgeBound_eq := rfl
    globalBound := Geometric.Basic.quarterRadius request.scale index
    globalBound_eq := by rw [request.scale_eq]; simp only [Geometric.Basic.quarterRadius_eq_mul_pow]; ring1
    accurate := (quarterRadius_antitone
      (scale_nonnegative request)
      (Data.Nat.Order.le_max_right _ _)).trans_lt
      ((globalBound_eq_quarter
        request).symm.trans_lt request.accurate) }

/-- The raised grid accuracy index is at least the requested minimum. -/
theorem atLeast_index_ge (request : GridPrimitiveAccuracy bounds columns target pairs) (minimum :
  Nat) :
    minimum ≤ (atLeast request minimum).index
      := Data.Nat.Order.le_max_left _ _

open Purelib.Riemann.Normalization.InverseRootPolynomial (Polynomial Box Coordinate)
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (RegionClearance PrimitiveOverlapBounds)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)

/-- Equal retained indices give the same global bound on the same clearance, numerator bounds and column count.

The requested tolerances may differ. The defining edge-scale and global-bound
certificates identify only these scalar readings, without identifying the
whole independent accuracy requests.
-/
theorem globalBound_eq_of_index_eq {polynomial numerator : Polynomial} {ambient : Box}
    {clearance : RegionClearance polynomial ambient} {bounds : PrimitiveOverlapBounds clearance numerator}
    {columns pairs : Nat} {firstTarget lastTarget : Coordinate}
    (first : GridPrimitiveAccuracy bounds columns firstTarget pairs)
    (last : GridPrimitiveAccuracy bounds columns lastTarget pairs) (same : first.index = last.index) :
    first.globalBound = last.globalBound := by
  have scales := first.edgeScale_eq.trans last.edgeScale_eq.symm
  have edges := first.edgeBound_eq.trans
    ((congrArg₂ quarterRadius scales same).trans last.edgeBound_eq.symm)
  exact first.globalBound_eq.trans
    ((congrArg (fun value : Coordinate => (8 * (columns : Coordinate) ^ 2 + 2) * value) edges).trans
      last.globalBound_eq.symm)

end Purelib.Riemann.Integration.RectangularPrimitiveAccuracy.GridPrimitiveAccuracy

end
