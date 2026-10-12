module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Polynomial.Dense.Gaussian.Primitive.Segment.Comparison
import Purelib.Riemann.Normalization.InverseModelEdgeTransition
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Affine
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Polynomial.Dense.Multiplication

import Purelib.Polynomial.Dense.Gaussian.GCD
import Purelib.Topology.Grid.Signs
public import Purelib.Riemann.Branches.RectangularSheetGauge
public import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction
import Purelib.Riemann.Normalization.InverseModelOverlapCocycle
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Data.Rat.Fraction.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

@[expose] public section

/-!
# Cached primitives on consistently oriented rectangular model banks

Each coefficient product, antiderivative and Taylor bound is retained once.
The interface also accepts generated caches checked by semantic polynomial
identities.  A fixed ambient clearance supplies a coefficient ceiling that
does not grow with the Newton degree.
-/

namespace Purelib.Riemann.Integration.RectangularPrimitiveModels

open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry Bank Transitions)
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (RegionClearance PrimitiveOverlapBounds DensePrimitive)

open Purelib.Riemann.Branches.RectangularSheetGauge
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison

open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Polynomial.Dense.Basic.DensePolynomial
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)

open Purelib.Data.Rat in
open Purelib.Polynomial.Dense.Gaussian in
set_option genInjectivity false in
/-- A retained polynomial primitive with its exact derivative and nonnegative remainder bound.

The cached coefficient and value polynomial keep their original derivative readback, while the scalar ceiling retains
its nonnegative certificate. -/
structure PrimitiveCell where
  /-- The retained original coefficient polynomial. -/ coefficient : Polynomial
  /-- The cached original primitive polynomial. -/ value : Polynomial
  /-- The cached primitive's derivative evaluates to its exact retained coefficient. -/ derivative_eq : ∀ point,
    (GCD.derivative value).eval point = coefficient.eval point
  /-- The retained nonnegative primitive-increment remainder bound. -/ remainderBound : Fraction.Rational
  /-- The retained remainder bound is nonnegative. -/ remainderBound_nonnegative : 0 ≤ remainderBound

constructive_injectivity PrimitiveCell

set_option genInjectivity false in
open Purelib.Data in
/-- An indexed primitive bank for the original inverse-root models and numerator polynomial.

Each coefficient equals the same numerator times its original cell model, and the retained remainder bounds control
increments inside that exact cell box. -/
structure Primitives {polynomial : Polynomial} {columns rows : Nat} {geometry : Geometry columns rows}
    (models : Bank polynomial geometry) (numerator : Polynomial) where
  /-- The cached primitive cells at the original column and row indices. -/ cells : Data.Vector
    (Data.Vector PrimitiveCell (rows + 1)) (columns + 1)
  /-- Each retained coefficient evaluates to the original numerator times its exact inverse-root model. -/
    coefficient_eq : ∀ column row point,
    (cells column row).coefficient.eval point = numerator.eval point * (models.ready column row).model.value.eval point
  /-- The original cell primitive's linearization remainder obeys its retained bound inside the same cell box. -/
    increment_bound : ∀ column row {start finish : Gaussian},
    (geometry.box column row).Contains start → (geometry.box column row).Contains finish →
    normSq ((cells column row).value.eval finish - (cells column row).value.eval start -
      (cells column row).coefficient.eval start * (finish - start)) ≤
        (cells column row).remainderBound * normSq (finish - start) ^ 2

constructive_injectivity Primitives

namespace Primitives

variable {polynomial numerator : Polynomial} {columns rows : Nat} {geometry : Geometry columns rows}
    {models : Bank polynomial geometry}

open Purelib.Data in
open Purelib.Data.Gaussian in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
/-- Construct and cache the original cellwise polynomial primitives and remainder certificates.

Each coefficient uses the exact stored inverse-root model and common numerator; its original dense primitive supplies
the cached value and bound. -/
def build (models : Bank polynomial geometry) (numerator : Polynomial) : Primitives models numerator :=
  let cells := Vector.Basic.vectorOfFn fun column => Vector.Basic.vectorOfFn fun row =>
    let coefficient := numerator * (models.ready column row).model.value
    let primitive := Primitive.Certificate.DensePrimitive.ofPolynomial coefficient (geometry.box column row)
    (⟨coefficient, primitive.value, primitive.derivative_eq, primitive.remainderBound,
      primitive.remainderBound_nonnegative⟩ : PrimitiveCell)
  { cells := cells
    coefficient_eq := fun column row point => by
      dsimp only [cells]
      rw [Vector.Basic.vectorOfFn_apply, Vector.Basic.vectorOfFn_apply]
      exact Dense.Basic.DensePolynomial.eval_mul _ _ _
    increment_bound := fun column row _ _ startInside finishInside => by
      dsimp only [cells]
      rw [Vector.Basic.vectorOfFn_apply, Vector.Basic.vectorOfFn_apply]
      simpa only [Norm.Basic.normSq_eq_canonical] using (Primitive.Certificate.DensePrimitive.ofPolynomial _
        _).increment_bound startInside finishInside }

open Purelib.Data.Gaussian in
/-- Read the exact retained primitive cell as a dense primitive on its original cell box. -/
def dense (primitives : Primitives models numerator) (column : Fin (columns + 1)) (row : Fin (rows + 1)) :
    DensePrimitive (primitives.cells column row).coefficient (geometry.box column row) :=
  { value := (primitives.cells column row).value
    derivative_eq := (primitives.cells column row).derivative_eq
    remainderBound := (primitives.cells column row).remainderBound
    remainderBound_nonnegative := (primitives.cells column row).remainderBound_nonnegative
    increment_bound := fun startInside finishInside => by
      simpa only [Norm.Basic.normSq_eq_canonical] using primitives.increment_bound column row startInside finishInside }

/-- Evaluate the original cached primitive polynomial at the given point in its retained cell index. -/
def value (primitives : Primitives models numerator) (column : Fin (columns + 1)) (row : Fin (rows + 1)) (point :
  Gaussian) : Gaussian :=
  (primitives.cells column row).value.eval point

end Primitives

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Polynomial.Dense.Gaussian in
/-- The original ambient clearance bounds the numerator times inverse model on every refining cell. -/
theorem ambient_numerator_inverse_le {polynomial numerator : Polynomial} {ambient inner : Purelib.Geometry.Rational.Box}
    {clearance : RegionClearance polynomial ambient} (bounds : PrimitiveOverlapBounds clearance numerator)
    (model : Model polynomial inner) (refines : inner.Refines ambient) {point : Gaussian} (inside : inner.Contains
      point) :
    normSq (numerator.eval point * model.value.eval point) ≤ bounds.numeratorUpper * bounds.inverseUpper := by
  have inverse := (PrimitiveOverlapBounds.build (clearance.restrict refines) numerator).inverse_norm_le model inside
  change normSq (model.value.eval point) ≤ 1 + 4 / clearance.bound at inverse
  rw [← bounds.inverseUpper_eq] at inverse
  rw [Basic.Canonical.normSq_mul]
  have scalar := Bounds.Box.normSq_eval_le_denseEvalNormBound numerator (refines.contains inside)
  rw [Norm.Basic.normSq_eq_canonical] at scalar
  exact Fraction.Order.Arithmetic.mul_le_mul_direct
    (scalar.trans_eq bounds.numeratorUpper_eq.symm)
    inverse (Basic.Canonical.normSq_nonneg _) bounds.numeratorUpper_nonnegative

namespace Primitives

variable {polynomial numerator : Polynomial} {columns rows : Nat} {geometry : Geometry columns rows}
    {bank : Bank polynomial geometry} {transitions : Transitions bank}
    {gauge : Purelib.Topology.Grid.Signs.Gauge transitions.flatGrid}
    {ambient : Purelib.Riemann.Normalization.InverseRootPolynomial.Box} {clearance : RegionClearance polynomial ambient}

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
open Purelib.Polynomial.Dense.Gaussian in
/-- A uniform coefficient gap bounds primitive-difference increments along the same contained segment.

The exact starting and ending parameters remain in the unit interval, and the bound retains their squared separation and
original segment movement. -/
private theorem increment_of_gap {leftCoefficient rightCoefficient : Polynomial} {leftBox rightBox :
  Purelib.Geometry.Rational.Box}
    (left : DensePrimitive leftCoefficient leftBox) (right : DensePrimitive rightCoefficient rightBox)
    (start finish : Gaussian) (bound : Fraction.Rational)
    (leftInside : ∀ parameter, 0 ≤ parameter ∧ parameter ≤ 1 → leftBox.Contains (Affine.line start (finish - start)
      parameter))
    (rightInside : ∀ parameter, 0 ≤ parameter ∧ parameter ≤ 1 → rightBox.Contains (Affine.line start (finish - start)
      parameter))
    (gap : ∀ parameter, 0 ≤ parameter ∧ parameter ≤ 1 →
      normSq (leftCoefficient.eval (Affine.line start (finish - start) parameter) -
        rightCoefficient.eval (Affine.line start (finish - start) parameter)) ≤ bound)
    {first last : Fraction.Rational} (firstInside : 0 ≤ first ∧ first ≤ 1) (lastInside : 0 ≤ last ∧ last ≤ 1) :
    normSq ((left.value.eval (Affine.line start (finish - start) last) -
      right.value.eval (Affine.line start (finish - start) last)) -
        (left.value.eval (Affine.line start (finish - start) first) -
          right.value.eval (Affine.line start (finish - start) first))) ≤
      2 * bound * normSq (finish - start) * (last - first) ^ 2 := by
  have estimate := Primitive.Segment.Comparison.DensePrimitive.difference_increment_le left right 1 start (finish -
    start) (Norm.Basic.normSq_one)
    (⟨0, 1, by decide⟩ : Data.Rat.Interval.Bounds) leftInside rightInside bound
    (fun parameter inside => by
      rw [Basic.one_mul]; simpa only [Norm.Basic.normSq_eq_canonical] using gap parameter inside) lastInside firstInside
  rw [Basic.one_mul, Norm.Basic.normSq_eq_canonical, Norm.Basic.normSq_eq_canonical] at estimate
  have identity : (left.value.eval (Affine.line start (finish - start) last) -
      right.value.eval (Affine.line start (finish - start) last)) -
        (left.value.eval (Affine.line start (finish - start) first) -
          right.value.eval (Affine.line start (finish - start) first)) =
    (left.value.eval (Affine.line start (finish - start) last) - left.value.eval (Affine.line start (finish - start)
      first)) -
      (right.value.eval (Affine.line start (finish - start) last) - right.value.eval (Affine.line start (finish - start)
        first)) := by ring1
  rw [identity]
  exact estimate.trans_eq (by ring1)

/-- Multiplying a Gaussian difference equals the difference of the two original products. -/
private theorem distribute_difference (numerator left right : Gaussian) :
    numerator * left - numerator * right = numerator * (left - right) := by ring1

section
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Riemann.Branches
/-- The adjacent-column primitive gap has a controlled increment between any two points on the original common edge. -/
theorem horizontal_gap_increment_le (primitives : Primitives (RectangularSheetGauge.Transitions.oriented transitions
  gauge) numerator)
    (bounds : PrimitiveOverlapBounds clearance numerator)
    (refines : ∀ column row, (geometry.box column row).Refines ambient)
    (column : Fin columns) (row : Fin (rows + 1)) {first last : Fraction.Rational}
    (firstInside : 0 ≤ first ∧ first ≤ 1) (lastInside : 0 ≤ last ∧ last ≤ 1) :
    let start := geometry.vertex column.castSucc.succ row.castSucc
    let finish := geometry.vertex column.castSucc.succ row.succ
    let firstPoint := Affine.line start (finish - start) first
    let lastPoint := Affine.line start (finish - start) last
    normSq ((primitives.value column.castSucc row lastPoint - primitives.value column.succ row lastPoint) -
      (primitives.value column.castSucc row firstPoint - primitives.value column.succ row firstPoint)) ≤
      12 * ((bank.ready column.castSucc row).model.bound + (bank.ready column.succ row).model.bound) *
        (bounds.numeratorUpper * bounds.inverseUpper) * normSq (finish - start) * (last - first) ^ 2 := by
  let edge := (RectangularSheetGauge.Transitions.oriented transitions gauge).horizontalEdge column row
  let start := geometry.vertex column.castSucc.succ row.castSucc
  let finish := geometry.vertex column.castSucc.succ row.succ
  have gap (parameter : Fraction.Rational) (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
      normSq ((primitives.cells column.castSucc row).coefficient.eval (Affine.line start (finish - start) parameter) -
        (primitives.cells column.succ row).coefficient.eval (Affine.line start (finish - start) parameter)) ≤
      6 * ((bank.ready column.castSucc row).model.bound + (bank.ready column.succ row).model.bound) *
        (bounds.numeratorUpper * bounds.inverseUpper) := by
    rw [primitives.coefficient_eq, primitives.coefficient_eq]
    rw [distribute_difference]
    have estimate := RectangularSheetGauge.Transitions.horizontal_distance_le transitions gauge column row inside
      (numerator.eval (Affine.line start (finish - start) parameter))
    simp only [RectangularSheetGauge.Transitions.oriented, RectangularSheetGauge.Bank.orient_bound] at estimate
    exact estimate.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (ambient_numerator_inverse_le bounds ((RectangularSheetGauge.Transitions.oriented transitions gauge).ready
        column.castSucc row).model
        (refines column.castSucc row) (edge.left_contains_at inside))
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        (add_nonneg (bank.ready column.castSucc row).model.bound_nonnegative (bank.ready column.succ
          row).model.bound_nonnegative)))
  exact (increment_of_gap (primitives.dense column.castSucc row) (primitives.dense column.succ row) _ _ _
    (fun _ inside => edge.left_contains_at inside) (fun _ inside => edge.right_contains_at inside) gap firstInside
      lastInside).trans_eq (by ring1)

/-- The adjacent-row primitive gap has a controlled increment between any two points on the original common edge. -/
theorem vertical_gap_increment_le (primitives : Primitives (RectangularSheetGauge.Transitions.oriented transitions
  gauge) numerator)
    (bounds : PrimitiveOverlapBounds clearance numerator)
    (refines : ∀ column row, (geometry.box column row).Refines ambient)
    (column : Fin (columns + 1)) (row : Fin rows) {first last : Fraction.Rational}
    (firstInside : 0 ≤ first ∧ first ≤ 1) (lastInside : 0 ≤ last ∧ last ≤ 1) :
    let start := geometry.vertex column.castSucc row.castSucc.succ
    let finish := geometry.vertex column.succ row.castSucc.succ
    let firstPoint := Affine.line start (finish - start) first
    let lastPoint := Affine.line start (finish - start) last
    normSq ((primitives.value column row.castSucc lastPoint - primitives.value column row.succ lastPoint) -
      (primitives.value column row.castSucc firstPoint - primitives.value column row.succ firstPoint)) ≤
      12 * ((bank.ready column row.castSucc).model.bound + (bank.ready column row.succ).model.bound) *
        (bounds.numeratorUpper * bounds.inverseUpper) * normSq (finish - start) * (last - first) ^ 2 := by
  let edge := (RectangularSheetGauge.Transitions.oriented transitions gauge).verticalEdge column row
  let start := geometry.vertex column.castSucc row.castSucc.succ
  let finish := geometry.vertex column.succ row.castSucc.succ
  have gap (parameter : Fraction.Rational) (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
      normSq ((primitives.cells column row.castSucc).coefficient.eval (Affine.line start (finish - start) parameter) -
        (primitives.cells column row.succ).coefficient.eval (Affine.line start (finish - start) parameter)) ≤
      6 * ((bank.ready column row.castSucc).model.bound + (bank.ready column row.succ).model.bound) *
        (bounds.numeratorUpper * bounds.inverseUpper) := by
    rw [primitives.coefficient_eq, primitives.coefficient_eq]
    rw [distribute_difference]
    have estimate := RectangularSheetGauge.Transitions.vertical_distance_le transitions gauge column row inside
      (numerator.eval (Affine.line start (finish - start) parameter))
    simp only [RectangularSheetGauge.Transitions.oriented, RectangularSheetGauge.Bank.orient_bound] at estimate
    exact estimate.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (ambient_numerator_inverse_le bounds ((RectangularSheetGauge.Transitions.oriented transitions gauge).ready column
        row.castSucc).model
        (refines column row.castSucc) (edge.left_contains_at inside))
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        (add_nonneg (bank.ready column row.castSucc).model.bound_nonnegative (bank.ready column
          row.succ).model.bound_nonnegative)))
  exact (increment_of_gap (primitives.dense column row.castSucc) (primitives.dense column row.succ) _ _ _
    (fun _ inside => edge.left_contains_at inside) (fun _ inside => edge.right_contains_at inside) gap firstInside
      lastInside).trans_eq (by ring1)

open Purelib.Riemann.Normalization
/-- The adjacent-column primitive gap differs from its original edge-start value by the retained quadratic bound.

The original common-edge parameter is measured from zero, with both cached cell primitives and the same numerator and
error ceilings retained. -/
theorem horizontal_increment_le (primitives : Primitives (RectangularSheetGauge.Transitions.oriented transitions gauge)
  numerator)
    (bounds : PrimitiveOverlapBounds clearance numerator)
    (refines : ∀ column row, (geometry.box column row).Refines ambient)
    (column : Fin columns) (row : Fin (rows + 1)) {parameter : Fraction.Rational} (inside : 0 ≤ parameter ∧ parameter ≤
      1) :
    let start := geometry.vertex column.castSucc.succ row.castSucc
    let finish := geometry.vertex column.castSucc.succ row.succ
    let point := Affine.line start (finish - start) parameter
    normSq ((primitives.value column.castSucc row point - primitives.value column.succ row point) -
      (primitives.value column.castSucc row start - primitives.value column.succ row start)) ≤
      12 * ((bank.ready column.castSucc row).model.bound + (bank.ready column.succ row).model.bound) *
        (bounds.numeratorUpper * bounds.inverseUpper) * normSq (finish - start) * parameter ^ 2 := by
  have bound := primitives.horizontal_gap_increment_le bounds refines column row (first := 0) ⟨le_rfl, by decide⟩ inside
  have parameterZero : parameter - 0 = parameter := by ring1
  simpa only [InverseModelEdgeTransition.line_zero, parameterZero] using bound

/-- The adjacent-row primitive gap differs from its original edge-start value by the retained quadratic bound.

The original common-edge parameter is measured from zero, with both cached cell primitives and the same numerator and
error ceilings retained. -/
theorem vertical_increment_le (primitives : Primitives (RectangularSheetGauge.Transitions.oriented transitions gauge)
  numerator)
    (bounds : PrimitiveOverlapBounds clearance numerator)
    (refines : ∀ column row, (geometry.box column row).Refines ambient)
    (column : Fin (columns + 1)) (row : Fin rows) {parameter : Fraction.Rational} (inside : 0 ≤ parameter ∧ parameter ≤
      1) :
    let start := geometry.vertex column.castSucc row.castSucc.succ
    let finish := geometry.vertex column.succ row.castSucc.succ
    let point := Affine.line start (finish - start) parameter
    normSq ((primitives.value column row.castSucc point - primitives.value column row.succ point) -
      (primitives.value column row.castSucc start - primitives.value column row.succ start)) ≤
      12 * ((bank.ready column row.castSucc).model.bound + (bank.ready column row.succ).model.bound) *
        (bounds.numeratorUpper * bounds.inverseUpper) * normSq (finish - start) * parameter ^ 2 := by
  have bound := primitives.vertical_gap_increment_le bounds refines column row (first := 0) ⟨le_rfl, by decide⟩ inside
  have parameterZero : parameter - 0 = parameter := by ring1
  simpa only [InverseModelEdgeTransition.line_zero, parameterZero] using bound

end

end Primitives

end Purelib.Riemann.Integration.RectangularPrimitiveModels
