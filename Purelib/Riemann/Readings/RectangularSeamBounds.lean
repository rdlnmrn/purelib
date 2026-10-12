module
import Purelib.Data.Gaussian.Basic
import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
import Purelib.Riemann.Integration.RectangularPrimitiveAccuracy
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Riemann.Integration.RectangularPrimitiveModels
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Geometry.Rational.Affine
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.RectangularPrimitiveCorners

import Purelib.Integration.Path.Dyadic.DyadicBoundaryRibbon
import Purelib.LinearAlgebra.Grid.Offsets
import Purelib.Topology.Grid.Signs
public import Purelib.Riemann.Readings.RectangularBoundaryAssembly
import Purelib.Polynomial.Dense.Gaussian.Primitive.Segment.Bounds
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Data.Vector.Basic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction.Cast

open Purelib.Data.Rat

@[expose] public section

/-!
# Subdivision-independent seams of the actual translated primitive grid

Both tree and non-tree edges use the already computed grid mismatch.  The
increment bound is independent of all primitive constants and Newton degrees.
Thus a whole corrected seam is paid before choosing the fine mesh depth.
-/

namespace Purelib.Riemann.Readings.RectangularSeamBounds

open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Integration.Path.Dyadic.DyadicBoundaryRibbon (dyadicDifference dyadicDifference_bound)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (RegionClearance PrimitiveOverlapBounds DensePrimitive)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry Bank Transitions)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives ambient_numerator_inverse_le)
open Purelib.Riemann.Integration.RectangularPrimitiveGluing (PrimitiveAnchors)
open Purelib.Riemann.Integration.RectangularPrimitiveAccuracy (GridPrimitiveAccuracy)
open Purelib.Riemann.Readings.RectangularBoundaryAssembly (BoundaryAssembly)

open Purelib.Data.Rat in
/-- The original primitive boundary slope from numerator, inverse and ambient diameter bounds. -/
def boundarySlope {polynomial numerator : Polynomial} {ambient : Purelib.Geometry.Rational.Box} {clearance :
  RegionClearance polynomial ambient}
    (bounds : PrimitiveOverlapBounds clearance numerator) : Fraction.Rational :=
  2 * (bounds.numeratorUpper * bounds.inverseUpper) * ambient.diagonalSq

section
open Purelib.Data.Gaussian
/-- Applying the same fixed translations preserves the original value gap. -/
private theorem translated_gap (a b c d x y : Basic.Canonical) :
    ((x + a) - (y + b)) - ((x + c) - (y + d)) = (a - b) - (c - d) := by ring1

/-- Reversing the ordered gap negates its value. -/
private theorem reversed_gap (a b c d : Basic.Canonical) : (a - b) - (c - d) = -((b - a) - (d - c)) := by ring1

/-- Swapping the two Gaussian endpoints preserves squared distance. -/
private theorem normSq_sub_swap (a b : Basic.Canonical) : normSq (a - b) = normSq (b - a) := by
  rw [show a - b = -(b - a) by ring1]
  rw [← Norm.Basic.normSq_eq_canonical, Norm.Basic.normSq_neg, Norm.Basic.normSq_eq_canonical]

end

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
open Purelib.Polynomial.Dense.Gaussian in
/-- Bound a translated primitive increment along its original contained segment.

The coefficient ceiling and segment-length bound give twice their product times the squared parameter increment on the
unit interval. -/
private theorem translated_increment_le {coefficient : Polynomial} {box : Purelib.Geometry.Rational.Box}
    (primitive : DensePrimitive coefficient box) (shift start finish : Basic.Canonical) (ceiling diameter : Coordinate)
    (ceilingNonnegative : 0 ≤ ceiling)
    (inside : ∀ parameter, 0 ≤ parameter ∧ parameter ≤ 1 → box.Contains (Affine.line start (finish - start) parameter))
    (coefficientBound : ∀ parameter, 0 ≤ parameter ∧ parameter ≤ 1 →
      normSq (coefficient.eval (Affine.line start (finish - start) parameter)) ≤ ceiling)
    (lengthBound : normSq (finish - start) ≤ diameter)
    {first last : Coordinate} (firstInside : 0 ≤ first ∧ first ≤ 1) (lastInside : 0 ≤ last ∧ last ≤ 1) :
    normSq ((shift + primitive.value.eval (Affine.line start (finish - start) last)) -
      (shift + primitive.value.eval (Affine.line start (finish - start) first))) ≤
      2 * ceiling * diameter * (last - first) ^ 2 := by
  rw [show (shift + primitive.value.eval (Affine.line start (finish - start) last)) -
      (shift + primitive.value.eval (Affine.line start (finish - start) first)) =
        primitive.value.eval (Affine.line start (finish - start) last) -
          primitive.value.eval (Affine.line start (finish - start) first) by ring1]
  have coefficientAdapter (parameter : Coordinate) (insideParameter : 0 ≤ parameter ∧ parameter ≤ 1) :
      Data.Gaussian.Norm.Basic.normSq (coefficient.eval (Affine.line start (finish - start) parameter)) ≤ ceiling := by
    rw [Norm.Basic.normSq_eq_canonical]
    exact coefficientBound parameter insideParameter
  have lengthAdapter := lengthBound
  rw [← Norm.Basic.normSq_eq_canonical] at lengthAdapter
  have estimate := Primitive.Segment.Bounds.DensePrimitive.segment_increment_le primitive start (finish - start) (⟨0, 1,
    by decide⟩ : Data.Rat.Interval.Bounds)
    inside ceiling coefficientAdapter lastInside firstInside
  rw [Norm.Basic.normSq_eq_canonical] at estimate
  exact estimate.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct lengthAdapter
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) ceilingNonnegative))
        (Fraction.Order.Arithmetic.sq_nonneg_direct _))

namespace GridPrimitiveAccuracy

variable {polynomial numerator : Polynomial} {ambient : Purelib.Riemann.Normalization.InverseRootPolynomial.Box}
  {clearance : RegionClearance polynomial ambient}
    {bounds : PrimitiveOverlapBounds clearance numerator} {columns rows : Nat} {target : Coordinate}
    {geometry : Geometry columns rows} {bank : Bank polynomial geometry}

section
open Purelib
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Integration.Path.Dyadic
open Purelib.Riemann.Branches
/-- Bound the original adjacent-column dyadic primitive difference by the retained request allowance.

The exact grid containments, original gauge and refinement index give eight global bounds times four boundary slopes
plus edge bound. -/
theorem horizontal_dyadic_bound (request : GridPrimitiveAccuracy bounds columns target)
    {transitions : Transitions (bank.refine request.index)} {gauge : Topology.Grid.Signs.Gauge transitions.flatGrid}
    {primitives : Primitives (RectangularSheetGauge.Transitions.oriented transitions gauge) numerator} (anchors :
      PrimitiveAnchors primitives)
    (offsets : LinearAlgebra.Grid.Offsets anchors.edges) (refines : ∀ column row, (geometry.box column
      row).Refines ambient)
    (column : Fin columns) (row : Fin (rows + 1)) (depth : Nat) :
    let start := geometry.vertex column.castSucc.succ row.castSucc
    let finish := geometry.vertex column.castSucc.succ row.succ
    let point := fun parameter => Affine.line start (finish - start) parameter
    normSq (DyadicBoundaryRibbon.dyadicDifference (fun parameter => anchors.alignedValue offsets column.castSucc row
      (point parameter))
      (fun parameter => anchors.alignedValue offsets column.succ row (point parameter)) depth 0 1) ≤
      8 * request.globalBound * (4 * boundarySlope bounds + request.edgeBound) := by
  let edge := (RectangularSheetGauge.Transitions.oriented transitions gauge).horizontalEdge column row
  let start := geometry.vertex column.castSucc.succ row.castSucc
  let finish := geometry.vertex column.castSucc.succ row.succ
  let point := fun parameter => Affine.line start (finish - start) parameter
  have lengthBound : normSq (finish - start) ≤ ambient.diagonalSq := by
    have scalar := Box.normSq_sub_le_diagonalSq
      ((refines column.castSucc row).contains (geometry.upperRight_mem column.castSucc row))
      ((refines column.castSucc row).contains (geometry.lowerRight_mem column.castSucc row))
    rw [Norm.Basic.normSq_eq_canonical] at scalar
    exact scalar
  have rightLe (first last : Coordinate) (firstInside : 0 ≤ first ∧ first ≤ 1) (lastInside : 0 ≤ last ∧ last ≤ 1) :
      normSq (anchors.alignedValue offsets column.succ row (point last) - anchors.alignedValue offsets column.succ row
        (point first)) ≤
        boundarySlope bounds * (last - first) ^ 2 := by
    apply translated_increment_le (primitives.dense column.succ row) (offsets.values column.succ row) start finish
      (bounds.numeratorUpper * bounds.inverseUpper) ambient.diagonalSq
      (Fraction.Order.Arithmetic.mul_nonneg_direct bounds.numeratorUpper_nonnegative bounds.inverseUpper_positive.le)
      (fun _ inside => edge.right_contains_at inside) ?_ lengthBound firstInside lastInside
    intro parameter inside
    rw [primitives.coefficient_eq]
    exact ambient_numerator_inverse_le bounds ((RectangularSheetGauge.Transitions.oriented transitions gauge).ready
      column.succ row).model
      (refines column.succ row) (edge.right_contains_at inside)
  have driftLe (first last : Coordinate) (firstInside : 0 ≤ first ∧ first ≤ 1) (lastInside : 0 ≤ last ∧ last ≤ 1) :
      normSq ((anchors.alignedValue offsets column.castSucc row (point last) - anchors.alignedValue offsets column.succ
        row (point last)) -
        (anchors.alignedValue offsets column.castSucc row (point first) - anchors.alignedValue offsets column.succ row
          (point first))) ≤
          request.edgeBound * (last - first) ^ 2 := by
    simp only [PrimitiveAnchors.alignedValue, translated_gap]
    have estimate := primitives.horizontal_gap_increment_le bounds refines column row firstInside lastInside
    exact estimate.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (request.local_scale_bound (bank.refine_uniform_bound request.index column.castSucc row)
        (bank.refine_uniform_bound request.index column.succ row) (Basic.Canonical.normSq_nonneg _) lengthBound)
      (Fraction.Order.Arithmetic.sq_nonneg_direct _))
  have estimate := DyadicBoundaryRibbon.dyadicDifference_bound
    (fun parameter => anchors.alignedValue offsets column.castSucc row (point parameter))
    (fun parameter => anchors.alignedValue offsets column.succ row (point parameter))
    (request.edgeBound_nonnegative.trans request.edgeBound_le_globalBound)
    (fun parameter inside => by
      rw [Norm.Basic.normSq_eq_canonical]
      exact request.horizontal_bound anchors offsets refines column row inside)
    (fun first last firstInside lastInside => by
      rw [Norm.Basic.normSq_eq_canonical]
      exact rightLe first last firstInside lastInside)
    (fun first last firstInside lastInside => by
      rw [Norm.Basic.normSq_eq_canonical]
      exact driftLe first last firstInside lastInside) depth
    (show (0 : Coordinate) ≤ 0 ∧ 0 ≤ 1 from ⟨le_rfl, by decide⟩)
    (show (0 : Coordinate) ≤ 1 ∧ 1 ≤ 1 from ⟨by decide, le_rfl⟩) (show (0 : Coordinate) ≤ 1 by decide)
  rw [Norm.Basic.normSq_eq_canonical] at estimate
  simpa only [(show (1 : Fraction.Rational) - 0 = 1 from by decide), one_pow, Fraction.Field.mul_one_direct] using
    estimate

/-- Bound the original upper/lower dyadic primitive difference by the retained request allowance.

The original reversed edge orientation and exact ambient containment retain the same quantitative slope and edge-bound
factors. -/
theorem vertical_dyadic_bound (request : GridPrimitiveAccuracy bounds columns target)
    {transitions : Transitions (bank.refine request.index)} {gauge : Topology.Grid.Signs.Gauge transitions.flatGrid}
    {primitives : Primitives (RectangularSheetGauge.Transitions.oriented transitions gauge) numerator} (anchors :
      PrimitiveAnchors primitives)
    (offsets : LinearAlgebra.Grid.Offsets anchors.edges) (refines : ∀ column row, (geometry.box column
      row).Refines ambient)
    (column : Fin (columns + 1)) (row : Fin rows) (depth : Nat) :
    let start := geometry.vertex column.castSucc row.castSucc.succ
    let finish := geometry.vertex column.succ row.castSucc.succ
    let point := fun parameter => Affine.line start (finish - start) parameter
    normSq (DyadicBoundaryRibbon.dyadicDifference (fun parameter => anchors.alignedValue offsets column row.succ (point
      parameter))
      (fun parameter => anchors.alignedValue offsets column row.castSucc (point parameter)) depth 0 1) ≤
      8 * request.globalBound * (4 * boundarySlope bounds + request.edgeBound) := by
  let edge := (RectangularSheetGauge.Transitions.oriented transitions gauge).verticalEdge column row
  let start := geometry.vertex column.castSucc row.castSucc.succ
  let finish := geometry.vertex column.succ row.castSucc.succ
  let point := fun parameter => Affine.line start (finish - start) parameter
  have lengthBound : normSq (finish - start) ≤ ambient.diagonalSq := by
    have scalar := Box.normSq_sub_le_diagonalSq
      ((refines column row.castSucc).contains (geometry.upperRight_mem column row.castSucc))
      ((refines column row.castSucc).contains (geometry.upperLeft_mem column row.castSucc))
    rw [Norm.Basic.normSq_eq_canonical] at scalar
    exact scalar
  have rightLe (first last : Coordinate) (firstInside : 0 ≤ first ∧ first ≤ 1) (lastInside : 0 ≤ last ∧ last ≤ 1) :
      normSq (anchors.alignedValue offsets column row.castSucc (point last) - anchors.alignedValue offsets column
        row.castSucc (point first)) ≤
        boundarySlope bounds * (last - first) ^ 2 := by
    apply translated_increment_le (primitives.dense column row.castSucc) (offsets.values column row.castSucc) start
      finish
      (bounds.numeratorUpper * bounds.inverseUpper) ambient.diagonalSq
      (Fraction.Order.Arithmetic.mul_nonneg_direct bounds.numeratorUpper_nonnegative bounds.inverseUpper_positive.le)
      (fun _ inside => edge.left_contains_at inside) ?_ lengthBound firstInside lastInside
    intro parameter inside
    rw [primitives.coefficient_eq]
    exact ambient_numerator_inverse_le bounds ((RectangularSheetGauge.Transitions.oriented transitions gauge).ready
      column row.castSucc).model
      (refines column row.castSucc) (edge.left_contains_at inside)
  have errorLe (parameter : Coordinate) (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
      normSq (anchors.alignedValue offsets column row.succ (point parameter) - anchors.alignedValue offsets column
        row.castSucc (point parameter)) ≤ request.globalBound := by
    rw [normSq_sub_swap]
    exact request.vertical_bound anchors offsets refines column row inside
  have driftLe (first last : Coordinate) (firstInside : 0 ≤ first ∧ first ≤ 1) (lastInside : 0 ≤ last ∧ last ≤ 1) :
      normSq ((anchors.alignedValue offsets column row.succ (point last) - anchors.alignedValue offsets column
        row.castSucc (point last)) -
        (anchors.alignedValue offsets column row.succ (point first) - anchors.alignedValue offsets column row.castSucc
          (point first))) ≤
          request.edgeBound * (last - first) ^ 2 := by
    simp only [PrimitiveAnchors.alignedValue, translated_gap]
    rw [reversed_gap]
    rw [← Norm.Basic.normSq_eq_canonical, Norm.Basic.normSq_neg, Norm.Basic.normSq_eq_canonical]
    have estimate := primitives.vertical_gap_increment_le bounds refines column row firstInside lastInside
    exact estimate.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (request.local_scale_bound (bank.refine_uniform_bound request.index column row.castSucc)
        (bank.refine_uniform_bound request.index column row.succ) (Basic.Canonical.normSq_nonneg _) lengthBound)
      (Fraction.Order.Arithmetic.sq_nonneg_direct _))
  have estimate := DyadicBoundaryRibbon.dyadicDifference_bound
    (fun parameter => anchors.alignedValue offsets column row.succ (point parameter))
    (fun parameter => anchors.alignedValue offsets column row.castSucc (point parameter))
    (request.edgeBound_nonnegative.trans request.edgeBound_le_globalBound)
    (fun parameter inside => by
      rw [Norm.Basic.normSq_eq_canonical]
      exact errorLe parameter inside)
    (fun first last firstInside lastInside => by
      rw [Norm.Basic.normSq_eq_canonical]
      exact rightLe first last firstInside lastInside)
    (fun first last firstInside lastInside => by
      rw [Norm.Basic.normSq_eq_canonical]
      exact driftLe first last firstInside lastInside) depth
    (show (0 : Coordinate) ≤ 0 ∧ 0 ≤ 1 from ⟨le_rfl, by decide⟩)
    (show (0 : Coordinate) ≤ 1 ∧ 1 ≤ 1 from ⟨by decide, le_rfl⟩) (show (0 : Coordinate) ≤ 1 by decide)
  rw [Norm.Basic.normSq_eq_canonical] at estimate
  simpa only [(show (1 : Fraction.Rational) - 0 = 1 from by decide), one_pow, Fraction.Field.mul_one_direct] using
    estimate

end

section
open Purelib
open Purelib.Riemann.Branches
/-- The cached horizontal seam correction satisfies its original dyadic comparison bound. -/
theorem horizontalCorrection_bound (request : GridPrimitiveAccuracy bounds columns target)
    {transitions : Transitions (bank.refine request.index)} {gauge : Topology.Grid.Signs.Gauge transitions.flatGrid}
    {primitives : Primitives (RectangularSheetGauge.Transitions.oriented transitions gauge) numerator} {anchors :
      PrimitiveAnchors primitives}
    {offsets : LinearAlgebra.Grid.Offsets anchors.edges} {depth : Nat} (assembly : BoundaryAssembly anchors
      offsets depth)
    (refines : ∀ column row, (geometry.box column row).Refines ambient) (column : Fin columns) (row : Fin (rows + 1)) :
    normSq (assembly.horizontalCorrections column row) ≤ 8 * request.globalBound * (4 * boundarySlope bounds +
      request.edgeBound) := by
  rw [assembly.horizontalCorrection_eq_dyadic]
  exact horizontal_dyadic_bound request anchors offsets refines column row depth

/-- The cached vertical seam correction satisfies its original dyadic comparison bound. -/
theorem verticalCorrection_bound (request : GridPrimitiveAccuracy bounds columns target)
    {transitions : Transitions (bank.refine request.index)} {gauge : Topology.Grid.Signs.Gauge transitions.flatGrid}
    {primitives : Primitives (RectangularSheetGauge.Transitions.oriented transitions gauge) numerator} {anchors :
      PrimitiveAnchors primitives}
    {offsets : LinearAlgebra.Grid.Offsets anchors.edges} {depth : Nat} (assembly : BoundaryAssembly anchors
      offsets depth)
    (refines : ∀ column row, (geometry.box column row).Refines ambient) (column : Fin (columns + 1)) (row : Fin rows) :
    normSq (assembly.verticalCorrections column row) ≤ 8 * request.globalBound * (4 * boundarySlope bounds +
      request.edgeBound) := by
  rw [assembly.verticalCorrection_eq_dyadic]
  exact vertical_dyadic_bound request anchors offsets refines column row depth

end

open Purelib in
open Purelib.Algebra in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Riemann.Branches in
/-- Bound the retained seam sum by its original horizontal and vertical correction counts.

The squared adjacency counts multiply the same retained request allowance; both finite correction families remain
explicit. -/
theorem seamTotal_bound (request : GridPrimitiveAccuracy bounds columns target)
    {transitions : Transitions (bank.refine request.index)} {gauge : Topology.Grid.Signs.Gauge transitions.flatGrid}
    {primitives : Primitives (RectangularSheetGauge.Transitions.oriented transitions gauge) numerator} {anchors :
      PrimitiveAnchors primitives}
    {offsets : LinearAlgebra.Grid.Offsets anchors.edges} {depth : Nat} (assembly : BoundaryAssembly anchors
      offsets depth)
    (refines : ∀ column row, (geometry.box column row).Refines ambient) :
    normSq assembly.seamTotal ≤
      2 * (((columns : Coordinate) * ((rows : Coordinate) + 1)) ^ 2 + (((columns : Coordinate) + 1) * (rows :
        Coordinate)) ^ 2) *
        (8 * request.globalBound * (4 * boundarySlope bounds + request.edgeBound)) := by
  let allowance := 8 * request.globalBound * (4 * boundarySlope bounds + request.edgeBound)
  have horizontal := Norm.Sum.Indexed.normSq_sumFin_le
    (fun column => FiniteSum.Fin.sumFin (fun row => assembly.horizontalCorrections column row))
    (((rows + 1 : Nat) : Coordinate) ^ 2 * allowance)
    (fun column => Norm.Sum.Indexed.normSq_sumFin_le (fun row => assembly.horizontalCorrections column row)
      allowance (fun row => by
        have scalar := horizontalCorrection_bound request assembly refines column row
        rw [← Norm.Basic.normSq_eq_canonical] at scalar
        exact scalar))
  have vertical := Norm.Sum.Indexed.normSq_sumFin_le
    (fun column => FiniteSum.Fin.sumFin (fun row => assembly.verticalCorrections column row))
    ((rows : Coordinate) ^ 2 * allowance)
    (fun column => Norm.Sum.Indexed.normSq_sumFin_le (fun row => assembly.verticalCorrections column row)
      allowance (fun row => by
        have scalar := verticalCorrection_bound request assembly refines column row
        rw [← Norm.Basic.normSq_eq_canonical] at scalar
        exact scalar))
  rw [← Norm.Basic.normSq_eq_canonical, assembly.seamTotal_eq_sum]
  exact (Norm.Bounds.normSq_add_le_two _ _).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add horizontal vertical) (by decide)).trans_eq
      (by
      rw [Fraction.Cast.natCast_add_direct, Fraction.Cast.natCast_add_direct, Nat.cast_one]
      dsimp only [allowance]
      ring1))

open Purelib in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Riemann.Branches in
open Purelib.Riemann.Integration in
/-- Bound the original local-minus-exterior primitive boundary using its seams and corners.

The retained grid dimensions, global request bound, primitive slope and edge bound supply the separate seam and corner
payments. -/
theorem boundaryDiscrepancy_bound (request : GridPrimitiveAccuracy bounds columns target)
    {transitions : Transitions (bank.refine request.index)} {gauge : Topology.Grid.Signs.Gauge transitions.flatGrid}
    {primitives : Primitives (RectangularSheetGauge.Transitions.oriented transitions gauge) numerator} {anchors :
      PrimitiveAnchors primitives}
    {offsets : LinearAlgebra.Grid.Offsets anchors.edges} {depth : Nat} (assembly : BoundaryAssembly anchors
      offsets depth)
    (refines : ∀ column row, (geometry.box column row).Refines ambient) :
    normSq (assembly.localTotal - assembly.exterior) ≤
      32 * (((columns : Coordinate) * ((rows : Coordinate) + 1)) ^ 2 + (((columns : Coordinate) + 1) * (rows :
        Coordinate)) ^ 2) *
        request.globalBound * (4 * boundarySlope bounds + request.edgeBound) +
      128 * ((columns : Coordinate) * (rows : Coordinate)) ^ 2 * request.globalBound ^ 2 := by
  have seamScalar := seamTotal_bound request assembly refines
  rw [← Norm.Basic.normSq_eq_canonical] at seamScalar
  have cornerScalar := RectangularPrimitiveCorners.GridPrimitiveAccuracy.cornerTotal_bound request assembly.corners
    refines
  rw [← Norm.Basic.normSq_eq_canonical] at cornerScalar
  rw [← Norm.Basic.normSq_eq_canonical, assembly.decomposition]
  exact (Norm.Bounds.normSq_add_le_two _ _).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (add_le_add seamScalar cornerScalar) (by decide)).trans_eq (by ring1))

end GridPrimitiveAccuracy

end Purelib.Riemann.Readings.RectangularSeamBounds
