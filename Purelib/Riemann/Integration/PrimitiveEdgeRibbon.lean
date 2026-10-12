module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
import Purelib.Riemann.Normalization.InverseModelEdgeTransition
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Affine

import Purelib.Integration.Path.BoundaryRibbon
public import Purelib.Riemann.Integration.PrimitiveEdgeControl
public import Purelib.Integration.Path.Dyadic.UniformParameters
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

@[expose] public section

namespace Purelib.Riemann.Integration

open Purelib.Riemann.Integration.PrimitiveEdgeControl
open Purelib.Integration.Path.Dyadic.UniformParameters
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison
open Purelib.Riemann.Normalization.InverseModelEdgeTransition (EdgeTransition)

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian Polynomial Box half correction
  residualStep correction_residual residualStep_contracts Model)

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open Purelib.Integration.Path.BoundaryRibbon (Ribbon)

namespace PrimitiveEdgeRibbon

open Purelib.Data in
/-- The finite vector carrier of the retained edge samples. -/
abbrev EdgeVector := Data.Vector

end PrimitiveEdgeRibbon

set_option genInjectivity false in
open Purelib.Geometry.Rational in
open Purelib.Integration.Path in
open Purelib.Integration.Path.Dyadic in
/-- A sampled ribbon comparing the original anchored value and edge primitive.

The original edge control and unit partition index cached affine points and both trace rows, with exact readbacks to
their mathematical values. -/
structure PrimitiveEdgeRibbon {polynomial numerator leftCoefficient rightCoefficient : Polynomial}
    {leftBox rightBox : Purelib.Geometry.Rational.Box} {clearance : RegionClearance polynomial leftBox}
    (bounds : PrimitiveOverlapBounds clearance numerator) {left : Model polynomial leftBox} {right : Model polynomial
      rightBox}
    {start finish : Gaussian} (edge : EdgeTransition left right start finish)
    (leftPrimitive : DensePrimitive leftCoefficient leftBox) (rightPrimitive : DensePrimitive rightCoefficient rightBox)
    (anchor : PrimitiveEdgeAnchor edge leftPrimitive.value rightPrimitive.value) {count : Nat} (partition :
      UniformParameters.UnitPartition count)
    extends PrimitiveEdgeControl bounds edge leftPrimitive rightPrimitive anchor where
  /-- The cached affine sample points in original partition order. -/
  points : PrimitiveEdgeRibbon.EdgeVector Gaussian (count + 1)
  /-- Each cached point is the original endpoint interpolation at its partition parameter. -/ points_eq : ∀ vertex,
    points vertex = Affine.line start (finish - start) (partition.parameters vertex)
  /-- The retained ribbon built from the two cached sample rows. -/ trace : BoundaryRibbon.Ribbon count
  /-- The left trace reads the original anchored value at each cached point. -/ left_eq : ∀ vertex, trace.left vertex =
    anchor.alignedValue (points vertex)
  /-- The right trace reads the original primitive model at each cached point. -/ right_eq : ∀ vertex, trace.right
    vertex = leftPrimitive.value.eval (points vertex)

constructive_injectivity PrimitiveEdgeRibbon

namespace PrimitiveEdgeRibbon

variable {polynomial numerator leftCoefficient rightCoefficient : Polynomial} {leftBox rightBox :
  Purelib.Riemann.Normalization.InverseRootPolynomial.Box}
    {clearance : RegionClearance polynomial leftBox} {bounds : PrimitiveOverlapBounds clearance numerator}
    {left : Model polynomial leftBox} {right : Model polynomial rightBox} {start finish : Gaussian}
    {edge : EdgeTransition left right start finish} {leftPrimitive : DensePrimitive leftCoefficient leftBox}
    {rightPrimitive : DensePrimitive rightCoefficient rightBox}
    {anchor : PrimitiveEdgeAnchor edge leftPrimitive.value rightPrimitive.value} {count : Nat} {partition :
      Purelib.Integration.Path.Dyadic.UniformParameters.UnitPartition count}

open Purelib.Data in
open Purelib.Geometry.Rational in
open Purelib.Integration.Path in
open Purelib.Integration.Path.Dyadic in
/-- Build the original edge ribbon from cached affine points and their two value rows.

The original partition, primitive bounds and edge control determine the same ordered samples and certified trace. -/
def build (bounds : PrimitiveOverlapBounds clearance numerator) (edge : EdgeTransition left right start finish)
    (leftPrimitive : DensePrimitive leftCoefficient leftBox) (rightPrimitive : DensePrimitive rightCoefficient rightBox)
    (anchor : PrimitiveEdgeAnchor edge leftPrimitive.value rightPrimitive.value) (partition :
      UniformParameters.UnitPartition count)
    (leftCoefficient_eq : ∀ point, leftCoefficient.eval point = numerator.eval point * left.value.eval point)
    (rightCoefficient_eq : ∀ point, rightCoefficient.eval point = numerator.eval point * right.value.eval point) :
    PrimitiveEdgeRibbon bounds edge leftPrimitive rightPrimitive anchor partition :=
  let points := Vector.Basic.vectorOfFn fun vertex => Affine.line start (finish - start) (partition.parameters vertex)
  let leftValues := Vector.Basic.vectorOfFn fun vertex => anchor.alignedValue (points vertex)
  let rightValues := Vector.Basic.vectorOfFn fun vertex => leftPrimitive.value.eval (points vertex)
  { toPrimitiveEdgeControl :=
      PrimitiveEdgeControl.build bounds edge leftPrimitive rightPrimitive anchor
        leftCoefficient_eq rightCoefficient_eq
    points := points
    points_eq := fun vertex => Vector.Basic.vectorOfFn_apply _ vertex
    trace := BoundaryRibbon.Ribbon.build leftValues rightValues
    left_eq := fun vertex => by
      change leftValues vertex = _
      exact Vector.Basic.vectorOfFn_apply _ vertex
    right_eq := fun vertex => by
      change rightValues vertex = _
      exact Vector.Basic.vectorOfFn_apply _ vertex }

/-- The original ribbon's pointwise squared errors are bounded by its retained drift. -/
theorem error_bound (ribbon : PrimitiveEdgeRibbon bounds edge leftPrimitive rightPrimitive anchor partition)
    (vertex : Fin (count + 1)) : normSq (ribbon.trace.errors vertex) ≤ ribbon.drift := by
  rw [ribbon.trace.errors_eq, ribbon.left_eq, ribbon.right_eq, ribbon.points_eq]
  exact ribbon.toPrimitiveEdgeControl.error_bound (partition.inside vertex)

/-- The primitive trace increments are bounded by slope times squared partition step. -/
theorem right_increment_bound (ribbon : PrimitiveEdgeRibbon bounds edge leftPrimitive rightPrimitive anchor partition)
    (segment : Fin count) : normSq (ribbon.trace.right segment.succ - ribbon.trace.right segment.castSucc) ≤
      ribbon.slope * partition.step ^ 2 := by
  rw [ribbon.right_eq, ribbon.right_eq, ribbon.points_eq, ribbon.points_eq]
  have estimate := ribbon.toPrimitiveEdgeControl.right_increment_bound (partition.inside segment.castSucc)
    (partition.inside segment.succ)
  rw [partition.increment_eq] at estimate
  exact estimate

/-- The original error increments are bounded by drift times squared partition step. -/
theorem drift_increment_bound (ribbon : PrimitiveEdgeRibbon bounds edge leftPrimitive rightPrimitive anchor partition)
    (segment : Fin count) : normSq (ribbon.trace.errors segment.succ - ribbon.trace.errors segment.castSucc) ≤
      ribbon.drift * partition.step ^ 2 := by
  rw [ribbon.trace.errors_eq, ribbon.trace.errors_eq, ribbon.left_eq, ribbon.left_eq,
    ribbon.right_eq, ribbon.right_eq, ribbon.points_eq, ribbon.points_eq]
  have estimate := ribbon.toPrimitiveEdgeControl.drift_increment_bound (partition.inside segment.castSucc)
    (partition.inside segment.succ)
  rw [partition.increment_eq] at estimate
  exact estimate

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- The original ribbon difference has squared norm at most eight times drift times four slopes plus drift. -/
theorem difference_bound (ribbon : PrimitiveEdgeRibbon bounds edge leftPrimitive rightPrimitive anchor partition) :
    normSq ribbon.trace.difference ≤ 8 * ribbon.drift * (4 * ribbon.slope + ribbon.drift) := by
  have errors : ∀ vertex, Data.Gaussian.Norm.Basic.normSq (ribbon.trace.errors vertex) ≤ ribbon.drift := fun vertex =>
    by
    rw [Norm.Basic.normSq_eq_canonical]; exact ribbon.error_bound vertex
  have right : ∀ segment : Fin count, Data.Gaussian.Norm.Basic.normSq (ribbon.trace.right segment.succ -
    ribbon.trace.right
    segment.castSucc) ≤ ribbon.slope * partition.step ^ 2 := fun segment => by
    rw [Norm.Basic.normSq_eq_canonical]; exact ribbon.right_increment_bound segment
  have drift : ∀ segment : Fin count, Data.Gaussian.Norm.Basic.normSq (ribbon.trace.errors segment.succ -
    ribbon.trace.errors
    segment.castSucc) ≤ ribbon.drift * partition.step ^ 2 := fun segment => by
    rw [Norm.Basic.normSq_eq_canonical]; exact ribbon.drift_increment_bound segment
  have estimate := ribbon.trace.difference_bound ribbon.toPrimitiveEdgeControl.drift_nonnegative errors right drift
  rw [Norm.Basic.normSq_eq_canonical] at estimate
  rw [partition.span_eq, one_pow, Fraction.Field.mul_one_direct] at estimate
  exact estimate

end PrimitiveEdgeRibbon

namespace PrimitiveEdgeRibbon

set_option genInjectivity false in
/-- A positive tolerance paying the original edge-ribbon target.

The retained slope, denominator and edge request keep the original primitive bounds and endpoints, with explicit
positivity, unit cap and payment proofs. -/
structure PrimitiveRibbonAccuracy {polynomial numerator : Polynomial} {leftBox rightBox : Purelib.Geometry.Rational.Box}
    {clearance : RegionClearance polynomial leftBox} (bounds : PrimitiveOverlapBounds clearance numerator)
    (left : Model polynomial leftBox) (right : Model polynomial rightBox)
    (start finish : Gaussian) (target : Coordinate) where
  /-- The retained original primitive increment slope. -/ slope : Coordinate
  /-- The slope is exactly twice the numerator/inverse bound product times endpoint distance squared. -/ slope_eq :
    slope = 2 * (bounds.numeratorUpper * bounds.inverseUpper) * normSq (finish - start)
  /-- The retained slope is nonnegative. -/ slope_nonnegative : 0 ≤ slope
  /-- The positive denominator used to allocate the original ribbon tolerance. -/ denominator : Coordinate
  /-- The denominator is exactly eight times four slopes plus one. -/ denominator_eq : denominator = 8 * (4 * slope + 1)
  /-- The retained allocation denominator is strictly positive. -/ denominator_positive : 0 < denominator
  /-- The retained positive edge tolerance. -/ tolerance : Coordinate
  /-- The retained tolerance is strictly positive. -/ positive : 0 < tolerance
  /-- The retained tolerance is at most one. -/ le_one : tolerance ≤ 1
  /-- The denominator times tolerance is paid by the original target. -/ paid : denominator * tolerance ≤ target
  /-- The original endpoint-indexed edge accuracy request at this tolerance. -/ edgeRequest : PrimitiveEdgeAccuracy
    bounds left right start finish tolerance

constructive_injectivity PrimitiveRibbonAccuracy

end PrimitiveEdgeRibbon

namespace PrimitiveEdgeRibbon.PrimitiveRibbonAccuracy

variable {polynomial numerator : Polynomial} {leftBox rightBox :
  Purelib.Riemann.Normalization.InverseRootPolynomial.Box}
    {clearance : RegionClearance polynomial leftBox} {bounds : PrimitiveOverlapBounds clearance numerator}
    {left : Model polynomial leftBox} {right : Model polynomial rightBox} {start finish : Gaussian} {target :
      Coordinate}

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- Allocate a positive ribbon tolerance from the original target and slope denominator.

The executable choice is target divided by denominator plus target; its retained payment and unit cap index the original
endpoint edge request. -/
def build (bounds : PrimitiveOverlapBounds clearance numerator)
    (left : Model polynomial leftBox) (right : Model polynomial rightBox)
    (start finish : Gaussian) (target : Coordinate) (targetPositive : 0 < target) :
    PrimitiveRibbonAccuracy bounds left right start finish target :=
  let slope := 2 * (bounds.numeratorUpper * bounds.inverseUpper) * normSq (finish - start)
  have slopeNonnegative : 0 ≤ slope := Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (Fraction.Order.Arithmetic.mul_nonneg_direct bounds.numeratorUpper_nonnegative bounds.inverseUpper_positive.le))
        (Basic.Canonical.normSq_nonneg _)
  let denominator := 8 * (4 * slope + 1)
  have denominatorPositive : 0 < denominator := Fraction.Order.Arithmetic.mul_pos_direct (by decide)
    (Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      slopeNonnegative) (by decide))
  have totalPositive : 0 < denominator + target := Fraction.Order.Arithmetic.add_pos_of_pos_of_nonneg_direct
    denominatorPositive targetPositive.le
  let tolerance := target / (denominator + target)
  have positive : 0 < tolerance := Fraction.Order.Field.div_pos_direct targetPositive totalPositive
  have cancel : (denominator + target) * tolerance = target := by
    rw [Fraction.Field.mul_comm]
    exact Fraction.Field.div_mul_cancel_of_ne _ _ totalPositive.ne'
  { slope := slope
    slope_eq := rfl
    slope_nonnegative := slopeNonnegative
    denominator := denominator
    denominator_eq := rfl
    denominator_positive := denominatorPositive
    tolerance := tolerance
    positive := positive
    le_one := (Fraction.Order.Field.div_le_iff_pos totalPositive).2 (by
      rw [Fraction.Field.one_mul]
      exact le_add_of_nonneg_left denominatorPositive.le)
    paid := (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (le_add_of_nonneg_right targetPositive.le) positive.le).trans_eq cancel
    edgeRequest := PrimitiveEdgeAccuracy.build bounds left right start finish tolerance positive }

open Purelib.Data.Rat in
/-- The selected original edge accuracy makes the ribbon allowance strictly smaller than the target. -/
theorem allowance_lt (request : PrimitiveRibbonAccuracy bounds left right start finish target)
    {edge : EdgeTransition (left.refine request.edgeRequest.index) (right.refine request.edgeRequest.index) start
      finish}
    {leftCoefficient rightCoefficient : Polynomial} {leftPrimitive : DensePrimitive leftCoefficient leftBox}
    {rightPrimitive : DensePrimitive rightCoefficient rightBox}
    {anchor : PrimitiveEdgeAnchor edge leftPrimitive.value rightPrimitive.value}
    (control : PrimitiveEdgeControl bounds edge leftPrimitive rightPrimitive anchor) :
    8 * control.drift * (4 * control.slope + control.drift) < target := by
  let ribbon := control
  have driftLt : ribbon.drift < request.tolerance := ribbon.drift_eq.trans_lt request.edgeRequest.refined_scale_lt
  have driftLe : ribbon.drift ≤ 1 := driftLt.le.trans request.le_one
  have slopeEq : ribbon.slope = request.slope := ribbon.slope_eq.trans request.slope_eq.symm
  calc
    _ ≤ 8 * ribbon.drift * (4 * ribbon.slope + 1) := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (add_le_add le_rfl driftLe) (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) ribbon.drift_nonnegative)
    _ = request.denominator * ribbon.drift := by rw [slopeEq, request.denominator_eq]; ring1
    _ < request.denominator * request.tolerance := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
      request.denominator_positive driftLt
    _ ≤ target := request.paid

open Purelib.Integration.Path.Dyadic in
/-- The ribbon at the retained original edge request meets its strict target bound. -/
theorem accurate (request : PrimitiveRibbonAccuracy bounds left right start finish target)
    {edge : EdgeTransition (left.refine request.edgeRequest.index) (right.refine request.edgeRequest.index) start
      finish}
    {leftCoefficient rightCoefficient : Polynomial} {leftPrimitive : DensePrimitive leftCoefficient leftBox}
    {rightPrimitive : DensePrimitive rightCoefficient rightBox}
    {anchor : PrimitiveEdgeAnchor edge leftPrimitive.value rightPrimitive.value} {count : Nat} {partition :
      UniformParameters.UnitPartition count}
    (ribbon : PrimitiveEdgeRibbon bounds edge leftPrimitive rightPrimitive anchor partition) : normSq
      ribbon.trace.difference < target :=
  ribbon.difference_bound.trans_lt (request.allowance_lt ribbon.toPrimitiveEdgeControl)

end PrimitiveEdgeRibbon.PrimitiveRibbonAccuracy

end Purelib.Riemann.Integration
