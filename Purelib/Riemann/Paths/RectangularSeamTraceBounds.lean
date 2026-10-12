module
import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
import Purelib.Riemann.Integration.RectangularPrimitiveAccuracy
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Riemann.Integration.RectangularPrimitiveModels
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Geometry.Rational.Affine
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Primitive.Segment.Bounds
import Purelib.Riemann.Branches.RectangularSheetGauge

import Purelib.LinearAlgebra.Grid.Offsets
import Purelib.Topology.Grid.Signs
public import Purelib.Riemann.Readings.RectangularSeamBounds
public import Purelib.Riemann.Periods.DyadicBilinearBoundaryRibbon
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Topology.Polygon.Stokes
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

public section

/-! Actual scalar model bounds retained for paired seam comparisons. -/

namespace Purelib.Riemann.Paths.RectangularSeamTraceBounds

open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (RegionClearance PrimitiveOverlapBounds DensePrimitive)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry Bank Transitions)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives ambient_numerator_inverse_le)
open Purelib.Riemann.Integration.RectangularPrimitiveGluing (PrimitiveAnchors)
open Purelib.Riemann.Integration.RectangularPrimitiveAccuracy (GridPrimitiveAccuracy)
open Purelib.Riemann.Readings.RectangularSeamBounds (boundarySlope)
open Purelib.Data.Rat in
/-- The rational coordinate carrier of the retained trace bounds. -/
private abbrev Coordinate := Fraction.Rational
open Purelib.Data.Gaussian in
/-- The canonical Gaussian rational carrier of the compared traces. -/
private abbrev Gaussian := Basic.Canonical
open Purelib.Polynomial.Dense.Gaussian in
/-- The original dense Gaussian primitive polynomial carrier. -/
private abbrev Polynomial := Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial
/-- The retained rational box carrier of the trace geometry. -/
private abbrev Box := Purelib.Geometry.Rational.Box

/-- Pointwise, increment and drift bounds for two original unit-interval traces.

The separate error, slope and drift constants control the original ordered functions and their difference, retaining
both parameter endpoints. -/
structure SeamTraceBounds (left right : Coordinate → Gaussian) (error slope drift : Coordinate) : Prop where
  /-- The original pointwise squared trace gap is bounded by the retained error. -/ errors : ∀ parameter, 0 ≤ parameter
    ∧ parameter ≤ 1 → normSq (left parameter - right parameter) ≤ error
  /-- The original right-trace increments satisfy the retained quadratic slope bound. -/ increments : ∀ first last, 0 ≤
    first ∧ first ≤ 1 → 0 ≤ last ∧ last ≤ 1 →
    normSq (right last - right first) ≤ slope * (last - first) ^ 2
  /-- The original trace-gap increments satisfy the retained quadratic drift bound. -/ drifts : ∀ first last, 0 ≤ first
    ∧ first ≤ 1 → 0 ≤ last ∧ last ≤ 1 →
    normSq ((left last - right last) - (left first - right first)) ≤ drift * (last - first) ^ 2

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Riemann.Periods in
/-- Bound the paired bilinear dyadic difference of two independently controlled trace pairs.

The same original depth and trace order are retained; eight times the maximum error multiplies four maximum slopes plus
maximum drifts. -/
theorem SeamTraceBounds.paired_dyadic_bound
    {leftFirst rightFirst leftSecond rightSecond : Coordinate → Gaussian}
    {firstError firstSlope firstDrift secondError secondSlope secondDrift : Coordinate}
    (first : SeamTraceBounds leftFirst rightFirst firstError firstSlope firstDrift)
    (second : SeamTraceBounds leftSecond rightSecond secondError secondSlope secondDrift) (depth : Nat) :
    normSq (DyadicBilinearBoundaryRibbon.dyadicDifference
      (fun parameter => ⟨leftFirst parameter, leftSecond parameter⟩)
      (fun parameter => ⟨rightFirst parameter, rightSecond parameter⟩) depth 0 1) ≤
      8 * max firstError secondError * (4 * max firstSlope secondSlope + max firstDrift secondDrift) := by
  have bound := DyadicBilinearBoundaryRibbon.dyadicDifference_bound
    (fun parameter => ⟨leftFirst parameter, leftSecond parameter⟩)
    (fun parameter => ⟨rightFirst parameter, rightSecond parameter⟩)
    (error := max firstError secondError) (slope := max firstSlope secondSlope) (drift := max firstDrift secondDrift)
    (fun parameter inside => ⟨(first.errors parameter inside).trans (Fraction.Order.Basic.le_max_left _ _),
      (second.errors parameter inside).trans (Fraction.Order.Basic.le_max_right _ _)⟩)
    (fun start finish startInside finishInside =>
      ⟨(first.increments start finish startInside finishInside).trans
          (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (Fraction.Order.Basic.le_max_left _ _)
            (Fraction.Order.Arithmetic.sq_nonneg_direct _)),
        (second.increments start finish startInside finishInside).trans
          (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (Fraction.Order.Basic.le_max_right _ _)
            (Fraction.Order.Arithmetic.sq_nonneg_direct _))⟩)
    (fun start finish startInside finishInside =>
      ⟨(first.drifts start finish startInside finishInside).trans
          (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (Fraction.Order.Basic.le_max_left _ _)
            (Fraction.Order.Arithmetic.sq_nonneg_direct _)),
        (second.drifts start finish startInside finishInside).trans
          (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (Fraction.Order.Basic.le_max_right _ _)
            (Fraction.Order.Arithmetic.sq_nonneg_direct _))⟩)
    depth (show (0 : Coordinate) ≤ 0 ∧ 0 ≤ 1 from ⟨le_rfl, by decide⟩)
    (show (0 : Coordinate) ≤ 1 ∧ 1 ≤ 1 from ⟨by decide, le_rfl⟩) (by decide : (0 : Coordinate) ≤ 1)
  rw [Norm.Basic.normSq_eq_canonical] at bound
  rw [show (1 : Coordinate) - 0 = 1 by ring1, one_pow, Fraction.Field.mul_one_direct] at bound
  exact bound

/-- Applying the same fixed translations preserves the original trace gap. -/
private theorem translated_gap (a b c d x y : Gaussian) :
    ((x + a) - (y + b)) - ((x + c) - (y + d)) = (a - b) - (c - d) := by ring1

/-- Reversing the original ordered trace gap negates it. -/
private theorem reversed_gap (a b c d : Gaussian) : (a - b) - (c - d) = -((b - a) - (d - c)) := by ring1

open Purelib.Data.Gaussian in
/-- Swapping original Gaussian endpoints preserves squared distance. -/
private theorem normSq_sub_swap (a b : Gaussian) : normSq (a - b) = normSq (b - a) := by
  rw [show a - b = -(b - a) by ring1]
  rw [← Norm.Basic.normSq_eq_canonical, Norm.Basic.normSq_neg, Norm.Basic.normSq_eq_canonical]

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
open Purelib.Polynomial.Dense.Gaussian in
/-- Bound the translated original primitive increment on a contained unit-parameter segment.

The retained coefficient ceiling and segment diameter determine the quadratic parameter-increment bound. -/
private theorem translated_increment_le {coefficient : Polynomial} {box : Box}
    (primitive : DensePrimitive coefficient box) (shift start finish : Gaussian) (ceiling diameter : Coordinate)
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

open Purelib
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Riemann.Branches
/-- Construct the original adjacent-column trace bounds from retained grid primitive accuracy.

The original aligned primitives, gauge and refinement index give the global error, boundary slope and edge drift bounds.
-/
theorem horizontal_trace_bounds (request : GridPrimitiveAccuracy bounds columns target)
    {transitions : Transitions (bank.refine request.index)} {gauge : Topology.Grid.Signs.Gauge transitions.flatGrid}
    {primitives : Primitives (RectangularSheetGauge.Transitions.oriented transitions gauge) numerator} (anchors :
      PrimitiveAnchors primitives)
    (offsets : LinearAlgebra.Grid.Offsets anchors.edges) (refines : ∀ column row, (geometry.box column
      row).Refines ambient)
    (column : Fin columns) (row : Fin (rows + 1)) :
    let start := geometry.vertex column.castSucc.succ row.castSucc
    let finish := geometry.vertex column.castSucc.succ row.succ
    let point := fun parameter => Affine.line start (finish - start) parameter
    SeamTraceBounds (fun parameter => anchors.alignedValue offsets column.castSucc row (point parameter))
      (fun parameter => anchors.alignedValue offsets column.succ row (point parameter)) request.globalBound
        (boundarySlope bounds) request.edgeBound := by
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
  exact ⟨(fun _ inside => request.horizontal_bound anchors offsets refines column row inside), rightLe, driftLe⟩

/-- Construct the original upper/lower trace bounds from retained grid primitive accuracy.

The exact reversed vertical orientation, aligned offsets and original refinement index determine the retained three
bounds. -/
theorem vertical_trace_bounds (request : GridPrimitiveAccuracy bounds columns target)
    {transitions : Transitions (bank.refine request.index)} {gauge : Topology.Grid.Signs.Gauge transitions.flatGrid}
    {primitives : Primitives (RectangularSheetGauge.Transitions.oriented transitions gauge) numerator} (anchors :
      PrimitiveAnchors primitives)
    (offsets : LinearAlgebra.Grid.Offsets anchors.edges) (refines : ∀ column row, (geometry.box column
      row).Refines ambient)
    (column : Fin (columns + 1)) (row : Fin rows) :
    let start := geometry.vertex column.castSucc row.castSucc.succ
    let finish := geometry.vertex column.succ row.castSucc.succ
    let point := fun parameter => Affine.line start (finish - start) parameter
    SeamTraceBounds (fun parameter => anchors.alignedValue offsets column row.succ (point parameter))
      (fun parameter => anchors.alignedValue offsets column row.castSucc (point parameter)) request.globalBound
        (boundarySlope bounds) request.edgeBound := by
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
  exact ⟨errorLe, rightLe, driftLe⟩

end GridPrimitiveAccuracy
end Purelib.Riemann.Paths.RectangularSeamTraceBounds
