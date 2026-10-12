module
import Purelib.Data.Nat.Order
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.List.Membership
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Reciprocal.Bounds

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CoordinatePolynomial
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularCoordinatePolynomial
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartCoordinateSteps
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartEdges
import Purelib.Riemann.Normalization.ReciprocalDiskCoordinateOrientation
import Mathlib.Algebra.Ring.Defs
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Integration.Path.Dyadic.DyadicTrace
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.InverseModelRootChannels
import Purelib.Riemann.Normalization.InverseModelRootSamples
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Tactic.Ring

public section

/-! Even-chart sheet variation on the actual cached common-cover readings.
The inverse-model index and endpoint-reading tolerance remain separate. -/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartSteps

open Purelib.Approximation
open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry
open Purelib.Riemann
open Purelib

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)

open Purelib.Data.Rat.Fraction.Compatibility

variable {genus count otherCount depth floor index : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
  {differential other : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent}
  {otherPatch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch
    (Integration.PreparedEdgeRecasting.recastCenteredEdge other parent)}
  {data : Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count} {otherData :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data otherPatch otherCount}
  {cover : Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover data} {otherCover :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover otherData}
  {interval : Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover.CommonInterval cover otherCover} {regular :
    Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}
  {geometry : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPaths.ChartGeometry (cap := cap) interval depth} {target
    requested : Normalization.InverseRootPolynomial.Coordinate}
  {prepared : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest regular geometry target floor}
  {box otherBox : Rational.Box}
  {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {otherSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other index otherBox}
  {firstComparison : Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Data regular interval.first.cell}
  {secondComparison : Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Data regular interval.second.cell}
  {first : Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Sample firstComparison sample}
  {second : Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Sample secondComparison otherSample}

/-- This consumes the retained coordinate polynomial and both cached endpoint
comparisons; it neither samples a new root nor identifies the sheet readings. -/
theorem Evaluation.regular_coordinate_step (evaluated :
  Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest.Evaluation prepared first second requested)
    (modelLater : prepared.index ≤ index) (coordinate :
      Disk.CoordinatePolynomial first)
    (unramified : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 0)
    (a b : Fin (geometry.tail.length + 1)) :
    Data.Gaussian.Norm.Basic.normSq ((evaluated.area.evaluated.readings.get b).first.coordinate -
      (evaluated.area.evaluated.readings.get a).first.coordinate) <
      2 * (Hyperelliptic.Charts.Reciprocal.ReciprocalRegularCoordinatePolynomial.regularSlope firstComparison index *
        (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest.Parameter (geometry := geometry) b -
        Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest.Parameter (geometry := geometry) a)^2
        + 4 * target) := by
  let va := coordinate.value.eval (parent.edge.point
    (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest.Parameter (geometry := geometry) a))⁻¹
  let vb := coordinate.value.eval (parent.edge.point
    (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest.Parameter (geometry := geometry) b))⁻¹
  let ca := (evaluated.area.evaluated.readings.get a).first.coordinate
  let cb := (evaluated.area.evaluated.readings.get b).first.coordinate
  have firstError :=
    Hyperelliptic.Charts.Reciprocal.Disk.CommonChartCoordinateSteps.SourceChartRequest.Evaluation.coordinate_accurate
    evaluated modelLater coordinate a
  have lastError :=
    Hyperelliptic.Charts.Reciprocal.Disk.CommonChartCoordinateSteps.SourceChartRequest.Evaluation.coordinate_accurate
    evaluated modelLater coordinate b
  have errors : Data.Gaussian.Norm.Basic.normSq ((vb - cb) - (va - ca)) < 4 * target :=
    (Gaussian.Norm.Bounds.normSq_sub_le_two _ _).trans_lt
      ((Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide) (Fraction.Order.Arithmetic.add_lt_add_direct
        lastError firstError)).trans_eq (by ring1))
  have increment :=
    Hyperelliptic.Charts.Reciprocal.ReciprocalRegularCoordinatePolynomial.CoordinatePolynomial.regular_increment_bound
    coordinate unramified
    (geometry.vertices.get a).first.root.between (geometry.vertices.get b).first.root.between
  have total := (Gaussian.Norm.Bounds.normSq_sub_le_two (vb - va) ((vb - cb) - (va - ca))).trans_lt
    (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide)
      ((Fraction.Order.Arithmetic.add_lt_add_left_direct errors (Data.Gaussian.Norm.Basic.normSq (vb -
        va))).trans_le (Fraction.Order.Arithmetic.add_le_add_direct increment le_rfl)))
  have identity : cb - ca = (vb - va) - ((vb - cb) - (va - ca)) := by ring1
  rw [identity]
  exact total

/-- The computed model threshold serves every retained vertex pair and all
later inverse samples, independently of the final dyadic vertex count. -/
theorem Evaluation.regular_coordinate_requested (evaluated :
  Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest.Evaluation prepared first second requested)
    (unramified : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 0)
    (slopeTarget : Normalization.InverseRootPolynomial.Coordinate) (positive : 0 < slopeTarget) (minimum : Nat)
    (later : max prepared.index
      (Hyperelliptic.Charts.Reciprocal.ReciprocalRegularCoordinatePolynomial.regularSlopeRequest firstComparison
        slopeTarget positive minimum).val ≤ index)
    (a b : Fin (geometry.tail.length + 1)) :
    Data.Gaussian.Norm.Basic.normSq ((evaluated.area.evaluated.readings.get b).first.coordinate -
      (evaluated.area.evaluated.readings.get a).first.coordinate) <
      2 * (slopeTarget * (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest.Parameter (geometry
        := geometry) b - Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest.Parameter (geometry
        := geometry) a)^2 + 4 * target) := by
  have bound := Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartSteps.Evaluation.regular_coordinate_step evaluated
    ((Data.Nat.Order.le_max_left _ _).trans later)
    (Disk.CoordinatePolynomial.build first) unramified a b
  have slope := (Hyperelliptic.Charts.Reciprocal.ReciprocalRegularCoordinatePolynomial.regularSlopeRequest
    firstComparison slopeTarget positive minimum).property.2
    index ((Data.Nat.Order.le_max_right _ _).trans later)
  have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct slope.le
    (Fraction.Order.Arithmetic.sq_nonneg_direct
      (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest.Parameter (geometry := geometry) b -
      Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest.Parameter (geometry := geometry) a))
  exact bound.trans_le (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.add_le_add_direct scaled le_rfl) (by decide))

/-- The squared difference of two unit-interval rational parameters is at most one. -/
private theorem unit_step_square {a b : Normalization.InverseRootPolynomial.Coordinate} (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b
  ∧ b ≤ 1) :
    (b - a)^2 ≤ 1 := by
  have ordered {x y : Normalization.InverseRootPolynomial.Coordinate} (hx : 0 ≤ x) (hy : y ≤ 1) (order : x ≤ y) : (y -
    x)^2 ≤ 1 := by
    have bound := Fraction.Order.Arithmetic.pow_le_pow_direct (Fraction.Order.Arithmetic.sub_nonneg_direct order)
      (((Fraction.Order.Arithmetic.sub_le_sub_direct (Fraction.Order.Basic.le_refl y) hx).trans_eq (by ring1)).trans hy)
      2
    simpa only [one_pow, -eq_self, -iff_self] using bound
  by_cases order : a ≤ b
  · exact ordered ha.1 hb.2 order
  · have bound := ordered hb.1 ha.2 (le_of_lt (lt_of_not_ge order))
    exact (by ring1 : (b - a)^2 = (a - b)^2).trans_le bound

/-- Every cached vertex pair meets the same requested squared-error bound.
The model threshold is computed before the final dyadic vertex count is used. -/
theorem Evaluation.regular_coordinates_small (evaluated :
  Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest.Evaluation prepared first second requested)
    (unramified : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 0) (positive : 0 < target)
      (minimum : Nat)
    (later : max prepared.index
      (Hyperelliptic.Charts.Reciprocal.ReciprocalRegularCoordinatePolynomial.regularSlopeRequest firstComparison (4 *
        target)
        (Fraction.Order.Arithmetic.mul_pos_direct (by decide) positive) minimum).val ≤ index)
    (a b : Fin (geometry.tail.length + 1)) :
    Data.Gaussian.Norm.Basic.normSq ((evaluated.area.evaluated.readings.get b).first.coordinate -
      (evaluated.area.evaluated.readings.get a).first.coordinate) < 16 * target := by
  have bound := Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartSteps.Evaluation.regular_coordinate_requested
    evaluated unramified (4 * target)
    (Fraction.Order.Arithmetic.mul_pos_direct (by decide) positive) minimum later a b
  have inside (i : Fin (geometry.tail.length + 1)) :
      0 ≤ Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest.Parameter (geometry := geometry) i
        ∧ Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest.Parameter (geometry := geometry) i
        ≤ 1 :=
    ⟨interval.first.owner.left.inside.1.trans (geometry.vertices.get i).first.root.between.1,
      (geometry.vertices.get i).first.root.between.2.trans interval.first.owner.right.inside.2⟩
  have step := Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartSteps.unit_step_square (inside a) (inside b)
  have paid := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct step
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 4)
    positive.le)
  have total := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct
    paid (le_refl (4 * target)))
    (by decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 2)
  exact bound.trans_le (total.trans_eq (by ring1))

/-- The paired original cap-polynomial values at the inverse of one retained chart vertex. -/
@[expose] def regularPolynomialPoint (sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential
  index box)
    (otherSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other index otherBox)
    (i : Fin (geometry.tail.length + 1)) : Topology.Polygon.Stokes.PrimitivePoint :=
  ⟨sample.primitive.value.eval (parent.edge.point
    (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest.Parameter (geometry := geometry) i))⁻¹,
   otherSample.primitive.value.eval (parent.edge.point
     (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest.Parameter (geometry := geometry) i))⁻¹⟩

/-- An unramified original cap primitive is bounded by the retained regular factor ceiling throughout the reciprocal
disk. -/
private theorem regular_primitive_bound {numerator : Hyperelliptic.Differentials.Basic.Differential genus} {domain :
  Rational.Box}
    (sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap numerator index domain)
    (unramified : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 0) {point :
      Normalization.InverseRootPolynomial.Gaussian}
    (inside : Purelib.Polynomial.Dense.Gaussian.Reciprocal.Bounds.InDisk curve.polynomial point) :
    Data.Gaussian.Norm.Basic.normSq (sample.primitive.value.eval point) ≤ regular.factorUpper := open
      Purelib.Polynomial in by
  rw [sample.primitive_factor, Hyperelliptic.Charts.Reciprocal.Cap.Primitives.point,
    Hyperelliptic.Charts.Reciprocal.Cap.Primitives.degree,
    unramified, Nat.zero_add, pow_one, Gaussian.Norm.Basic.normSq_mul]
  have bound := Fraction.Order.Arithmetic.mul_le_mul_direct (Dense.Gaussian.Reciprocal.Bounds.disk_unit_bound inside)
    (regular.factor_bound sample inside) (Gaussian.Norm.Basic.normSq_nonneg _) (by
        decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 1)
  exact bound.trans_eq (Fraction.Field.one_mul _)

/-- Both coordinates of the original paired cap-polynomial point satisfy the retained regular factor ceiling. -/
theorem regularPolynomialPoint_bounded (unramified : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder
  curve = 0)
    (i : Fin (geometry.tail.length + 1)) :
    Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded
      (Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartSteps.regularPolynomialPoint (geometry := geometry) sample
      otherSample i) regular.factorUpper := by
  have inside := Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.inverse_inDisk curve (data.boundary.point
    ⟨interval.first.owner.left.inside.1.trans (geometry.vertices.get i).first.root.between.1,
      (geometry.vertices.get i).first.root.between.2.trans interval.first.owner.right.inside.2⟩)
  have firstScalar := regular_primitive_bound (regular := regular) sample unramified inside
  have secondScalar := Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartSteps.regular_primitive_bound (regular :=
    regular) otherSample unramified inside
  rw [Gaussian.Norm.Basic.normSq_eq_canonical] at firstScalar secondScalar
  exact ⟨firstScalar, secondScalar⟩

/-- Each actual unramified chart coordinate has squared norm at most two under the original reading tolerance. -/
private theorem regular_coordinate_bound (evaluated :
  Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest.Evaluation prepared first second requested)
    (unramified : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 0) (i : Fin
      (geometry.tail.length + 1)) :
    Data.Gaussian.Norm.Basic.normSq (evaluated.area.evaluated.readings.get i).first.coordinate ≤ 2 := by
  have small : evaluated.area.budget.tolerance ≤ 1 := by
    rw [evaluated.area.budget.tolerance_eq]
    exact (Fraction.Order.Basic.min_le_left _ _).trans (by
        decide : (1 / 16 : Normalization.InverseRootPolynomial.Coordinate) ≤ 1)
  have squareScalar := Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartEdges.Evaluation.regular_square
    (evaluated.area.evaluated.readings.get i) unramified
  rw [Gaussian.Norm.Basic.normSq_eq_canonical] at squareScalar
  have scalar := Normalization.ReciprocalDiskCoordinateOrientation.coordinate_norm_upper
    (root := (evaluated.area.evaluated.readings.get i).first.coordinate) (point := (1 : Gaussian.Basic.Canonical))
    (by decide : Gaussian.Basic.Canonical.normSq (1 : Gaussian.Basic.Canonical) ≤ 1) small squareScalar
  rw [← Gaussian.Norm.Basic.normSq_eq_canonical] at scalar
  exact scalar

/-- The combined positive coordinate and chart-reading error factor is nonnegative. -/
private theorem edge_factor_nonnegative (target tolerance : Normalization.InverseRootPolynomial.Coordinate) (positive :
  0 < target)
    (tolerancePositive : 0 < tolerance) : 0 ≤ 2 * (32 * target + tolerance) :=
  Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct (by
    decide +kernel) positive.le) tolerancePositive.le)

/-- Uniform edge control uses only fixed cap bounds and allocated tolerances,
not the coefficient size of either sampled primitive polynomial. -/
theorem Evaluation.regular_edge_uniform (evaluated :
  Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest.Evaluation prepared first second requested)
    (unramified : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 0) (positive : 0 < target)
      (minimum : Nat)
    (later : max prepared.index
      (Hyperelliptic.Charts.Reciprocal.ReciprocalRegularCoordinatePolynomial.regularSlopeRequest firstComparison (4 *
        target)
        (Fraction.Order.Arithmetic.mul_pos_direct (by decide) positive) minimum).val ≤ index)
    (a b : Fin (geometry.tail.length + 1)) :
    let readings := evaluated.area.evaluated.readings
    let polynomial := Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartSteps.regularPolynomialPoint (geometry :=
      geometry) sample otherSample
    Data.Gaussian.Norm.Basic.normSq (Topology.Polygon.Stokes.edgeArea (readings.get a).chartPoint (readings.get
      b).chartPoint -
      Topology.Polygon.Stokes.edgeArea (polynomial a) (polynomial b)) ≤
      (2 * (32 * target + evaluated.area.budget.tolerance)) * (4 * regular.factorUpper * regular.factorUpper) := by
  intro readings polynomial
  have step := Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartSteps.Evaluation.regular_coordinates_small
    evaluated unramified positive minimum later a b
  have root := Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartSteps.regular_coordinate_bound evaluated unramified
    a
  have product := Fraction.Order.Arithmetic.mul_le_mul_direct root step.le (Gaussian.Norm.Basic.normSq_nonneg _)
    (by decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 2)
  have factor := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.add_le_add_direct (product.trans_eq (by ring1 : 2 * (16 * target) = 32 * target))
      (le_refl evaluated.area.budget.tolerance)) (by decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 2)
  have firstBound : Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded (polynomial a) regular.factorUpper :=
    Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartSteps.regularPolynomialPoint_bounded unramified a
  have lastBound : Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded (polynomial b) regular.factorUpper :=
    Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartSteps.regularPolynomialPoint_bounded unramified b
  have area := Readings.PrimitiveAreaBounds.PrimitivePoint.area_bound firstBound lastBound
  rw [← Gaussian.Norm.Basic.normSq_eq_canonical] at area
  have tolerancePositive : (0 : Normalization.InverseRootPolynomial.Coordinate) < evaluated.area.budget.tolerance :=
    evaluated.area.budget.positive
  have nonnegative : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 2 * (32 * target +
    evaluated.area.budget.tolerance) :=
    Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartSteps.edge_factor_nonnegative target
      evaluated.area.budget.tolerance positive tolerancePositive
  exact (Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartEdges.Evaluation.regular_edge_bound (readings.get a)
    (readings.get b) unramified).trans
    (Fraction.Order.Arithmetic.mul_le_mul_direct factor area (Gaussian.Norm.Basic.normSq_nonneg _) nonnegative)

/-- The actual edge-error ceiling retaining the coordinate norm, model slope, source-reading tolerance and paired
polynomial edge area. -/
@[expose] def Evaluation.regularEdgeError (evaluated :
  Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest.Evaluation prepared first second requested)
    (a b : Fin (geometry.tail.length + 1)) : Coordinate :=
  let readings := evaluated.area.evaluated.readings
  let polynomial := Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartSteps.regularPolynomialPoint (geometry :=
    geometry) sample otherSample
  (2 * (Data.Gaussian.Norm.Basic.normSq (readings.get a).first.coordinate *
    (2 * (Hyperelliptic.Charts.Reciprocal.ReciprocalRegularCoordinatePolynomial.regularSlope firstComparison index *
      (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest.Parameter (geometry := geometry) b -
      Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest.Parameter (geometry := geometry) a)^2 +
      4 * target)) +
    evaluated.area.budget.tolerance)) * Data.Gaussian.Norm.Basic.normSq (Topology.Polygon.Stokes.edgeArea
      (polynomial a) (polynomial b))

/-- Pay the actual chart edge using the decreasing sheet slope, the source
coordinate tolerance and the separately allocated chart-square tolerance. -/
theorem Evaluation.regular_edge_accurate (evaluated :
  Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest.Evaluation prepared first second requested)
    (modelLater : prepared.index ≤ index) (coordinate :
      Disk.CoordinatePolynomial first)
    (unramified : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 0)
    (a b : Fin (geometry.tail.length + 1)) :
    let readings := evaluated.area.evaluated.readings
    let polynomial := Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartSteps.regularPolynomialPoint (geometry :=
      geometry) sample otherSample
    Data.Gaussian.Norm.Basic.normSq (Topology.Polygon.Stokes.edgeArea (readings.get a).chartPoint (readings.get
      b).chartPoint -
      Topology.Polygon.Stokes.edgeArea (polynomial a) (polynomial b)) ≤
      Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartSteps.Evaluation.regularEdgeError evaluated a b := by
  intro readings polynomial
  have step := Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartSteps.Evaluation.regular_coordinate_step evaluated
    modelLater coordinate unramified a b
  have edge := Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartEdges.Evaluation.regular_edge_bound (readings.get
    a) (readings.get b) unramified
  have factor := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct step.le
    (Gaussian.Norm.Basic.normSq_nonneg (readings.get a).first.coordinate)
  have enlarged := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.add_le_add_direct factor (le_refl evaluated.area.budget.tolerance))
    (by decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 2)
  exact edge.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct enlarged
    (Gaussian.Norm.Basic.normSq_nonneg _))

/-- The maximum of a finite rational list together with zero. -/
@[expose] def maximum : List Normalization.InverseRootPolynomial.Coordinate →
  Normalization.InverseRootPolynomial.Coordinate
  | [] => 0
  | head :: tail => max head (Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartSteps.maximum tail)

/-- Every retained list entry is at most the finite maximum with zero. -/
private theorem le_maximum {values : List Normalization.InverseRootPolynomial.Coordinate} {value :
  Normalization.InverseRootPolynomial.Coordinate} (member : value ∈ values) :
    value ≤ Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartSteps.maximum values := by
  induction values with
  | nil => exact (List.not_mem_nil member).elim
  | cons head tail ih =>
      rcases Data.List.Membership.mem_cons.mp member with rfl | member
      · exact Fraction.Order.Basic.le_max_left _ _
      · exact (ih member).trans (Fraction.Order.Basic.le_max_right _ _)

/-- The original chart edge count squared times the largest retained edge-error ceiling. -/
@[expose] def Evaluation.regularAreaError (evaluated :
  Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest.Evaluation prepared first second requested)
  : Coordinate :=
  (geometry.tail.length : Normalization.InverseRootPolynomial.Coordinate)^2 *
    Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartSteps.maximum
    (List.ofFn (fun edge : Fin geometry.tail.length =>
      Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartSteps.Evaluation.regularEdgeError evaluated edge.castSucc
      edge.succ))

/-- Aggregate every retained edge of the full uncentered path. In particular,
this does not silently drop its endpoint term or replace it by a single chord. -/
theorem Evaluation.regular_area_accurate (evaluated :
  Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest.Evaluation prepared first second requested)
    (modelLater : prepared.index ≤ index) (coordinate :
      Disk.CoordinatePolynomial first)
    (unramified : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 0) :
    Data.Gaussian.Norm.Basic.normSq (evaluated.area.evaluated.chart.originalArea -
      Periods.CenteredBilinearPath.area
        (Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartSteps.regularPolynomialPoint (geometry := geometry)
        sample otherSample)) ≤
      Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartSteps.Evaluation.regularAreaError evaluated := open
        Purelib.Algebra in by
  let polynomial := Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartSteps.regularPolynomialPoint (geometry :=
    geometry) sample otherSample
  let readings := evaluated.area.evaluated.readings
  let errors := List.ofFn (fun edge : Fin geometry.tail.length =>
    Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartSteps.Evaluation.regularEdgeError evaluated edge.castSucc
    edge.succ)
  have each (edge : Fin geometry.tail.length) :
      Data.Gaussian.Norm.Basic.normSq (Topology.Polygon.Stokes.edgeArea (readings.get edge.castSucc).chartPoint
        (readings.get edge.succ).chartPoint -
        Topology.Polygon.Stokes.edgeArea (polynomial edge.castSucc) (polynomial edge.succ)) ≤
          Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartSteps.maximum errors :=
    (Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartSteps.Evaluation.regular_edge_accurate evaluated modelLater
      coordinate unramified edge.castSucc edge.succ).trans
      (Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartSteps.le_maximum (Data.List.OfFn.Basic.mem_ofFn.mpr ⟨edge,
        rfl⟩))
  have bound := Gaussian.Norm.Sum.Indexed.normSq_sumFin_le _
    (Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartSteps.maximum errors) each
  rw [FiniteSum.Fin.sumFin_sub] at bound
  rw [evaluated.area.evaluated.chart.originalArea_eq]
  exact bound

/-- Half of a nonnegative rational value is at most that value. -/
private theorem half_le (value : Normalization.InverseRootPolynomial.Coordinate) (nonnegative : 0 ≤ value) : value / 2 ≤
  value := by
  apply (Fraction.Order.Field.div_le_iff_pos (by decide : (0 : Normalization.InverseRootPolynomial.Coordinate) < 2)).mpr
  exact (by ring1 : value = 1 * value).trans_le
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (by
        decide : (1 : Normalization.InverseRootPolynomial.Coordinate) ≤ 2) nonnegative).trans_eq (by ring1))

/-- A pre-sample rate for the complete regular chart path. Both source and
chart comparisons use the same tolerance, and the actual edge count is paid. -/
theorem Evaluation.regular_area_uniform (evaluated :
  Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest.Evaluation prepared first second target)
    (unramified : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 0) (positive : 0 < target)
      (minimum : Nat)
    (later : max prepared.index
      (Hyperelliptic.Charts.Reciprocal.ReciprocalRegularCoordinatePolynomial.regularSlopeRequest firstComparison (4 *
        target)
        (Fraction.Order.Arithmetic.mul_pos_direct (by decide) positive) minimum).val ≤ index) :
    Data.Gaussian.Norm.Basic.normSq (evaluated.area.evaluated.chart.originalArea -
      Periods.CenteredBilinearPath.area
        (Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartSteps.regularPolynomialPoint (geometry := geometry)
        sample otherSample)) ≤
      (geometry.tail.length : Normalization.InverseRootPolynomial.Coordinate)^2 * (264 * regular.factorUpper^2 * target)
        := open Purelib.Algebra in by
  have magnitude : 0 ≤ evaluated.area.magnitude :=
    evaluated.area.magnitude_eq.symm ▸ evaluated.request.magnitude_nonnegative
  have tolerance := (evaluated.area.budget.tolerance_le magnitude positive).trans
    (Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartSteps.half_le target positive.le)
  have scalar (factor tolerance : Normalization.InverseRootPolynomial.Coordinate) (bound : tolerance ≤ target)
    (nonnegative : 0 ≤ factor) :
      (2 * (32 * target + tolerance)) * (4 * factor * factor) ≤ 264 * factor^2 * target := by
    have estimate := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct (le_refl
        (32 * target)) bound) (by decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 2))
      (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by
          decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 4) nonnegative) nonnegative)
    exact estimate.trans_eq (by ring1)
  let polynomial := Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartSteps.regularPolynomialPoint (geometry :=
    geometry) sample otherSample
  let readings := evaluated.area.evaluated.readings
  have each (edge : Fin geometry.tail.length) :
      Data.Gaussian.Norm.Basic.normSq (Topology.Polygon.Stokes.edgeArea (readings.get edge.castSucc).chartPoint
        (readings.get edge.succ).chartPoint -
        Topology.Polygon.Stokes.edgeArea (polynomial edge.castSucc) (polynomial edge.succ)) ≤ 264 *
          regular.factorUpper^2 * target :=
    (Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartSteps.Evaluation.regular_edge_uniform evaluated unramified
      positive minimum later edge.castSucc edge.succ).trans
      (scalar regular.factorUpper evaluated.area.budget.tolerance tolerance regular.factorUpper_nonnegative)
  have bound := Gaussian.Norm.Sum.Indexed.normSq_sumFin_le _ (264 * regular.factorUpper^2 * target) each
  rw [FiniteSum.Fin.sumFin_sub] at bound
  rw [evaluated.area.evaluated.chart.originalArea_eq]
  exact bound

/-- Uniform edge control with the retained chart's own target separated from
the requested area error. The model threshold uses the chart target; the
resulting bound uses the larger requested error. -/
theorem Evaluation.regular_area_uniform_requested {requested : Normalization.InverseRootPolynomial.Coordinate}
    (evaluated : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest.Evaluation prepared first
      second requested)
    (unramified : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 0) (positive : 0 < target)
    (requestedPositive : 0 < requested) (targetLe : target ≤ requested) (minimum : Nat)
    (later : max prepared.index
      (Hyperelliptic.Charts.Reciprocal.ReciprocalRegularCoordinatePolynomial.regularSlopeRequest firstComparison (4 *
        target)
        (Fraction.Order.Arithmetic.mul_pos_direct (by decide) positive) minimum).val ≤ index) :
    Data.Gaussian.Norm.Basic.normSq (evaluated.area.evaluated.chart.originalArea -
      Periods.CenteredBilinearPath.area
        (Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartSteps.regularPolynomialPoint (geometry := geometry)
        sample otherSample)) ≤
      (geometry.tail.length : Normalization.InverseRootPolynomial.Coordinate)^2 * (264 * regular.factorUpper^2 *
        requested) := open Purelib.Algebra in by
  have magnitude : 0 ≤ evaluated.area.magnitude :=
    evaluated.area.magnitude_eq.symm ▸ evaluated.request.magnitude_nonnegative
  have tolerance := (evaluated.area.budget.tolerance_le magnitude requestedPositive).trans
    (Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartSteps.half_le requested requestedPositive.le)
  have scalar (factor tolerance : Normalization.InverseRootPolynomial.Coordinate) (bound : tolerance ≤ requested)
    (nonnegative : 0 ≤ factor) :
      (2 * (32 * requested + tolerance)) * (4 * factor * factor) ≤ 264 * factor^2 * requested := by
    have estimate := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct (le_refl
        (32 * requested)) bound) (by decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 2))
      (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by
          decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 4) nonnegative) nonnegative)
    exact estimate.trans_eq (by ring1)
  let polynomial := Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartSteps.regularPolynomialPoint (geometry :=
    geometry) sample otherSample
  let readings := evaluated.area.evaluated.readings
  have each (edge : Fin geometry.tail.length) :
      Data.Gaussian.Norm.Basic.normSq (Topology.Polygon.Stokes.edgeArea (readings.get edge.castSucc).chartPoint
        (readings.get edge.succ).chartPoint -
        Topology.Polygon.Stokes.edgeArea (polynomial edge.castSucc) (polynomial edge.succ)) ≤
        264 * regular.factorUpper^2 * requested := by
    have edgeBound := Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartSteps.Evaluation.regular_edge_uniform
      evaluated unramified positive minimum later edge.castSucc edge.succ
    have le32 : 32 * target ≤ 32 * requested :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct targetLe (by
          decide +kernel : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 32)
    have combined : 2 * (32 * target + evaluated.area.budget.tolerance) ≤
        2 * (32 * requested + evaluated.area.budget.tolerance) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct le32
        (le_refl _)) (by decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 2)
    have factor := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct combined
      (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by
          decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 4) regular.factorUpper_nonnegative)
        regular.factorUpper_nonnegative)
    exact edgeBound.trans (factor.trans
      (scalar regular.factorUpper evaluated.area.budget.tolerance tolerance regular.factorUpper_nonnegative))
  have bound := Gaussian.Norm.Sum.Indexed.normSq_sumFin_le _ (264 * regular.factorUpper^2 * requested) each
  rw [FiniteSum.Fin.sumFin_sub] at bound
  rw [evaluated.area.evaluated.chart.originalArea_eq]
  exact bound

/-- The original edge-count-squared regular area rate is nonnegative. -/
theorem regular_area_rate_nonnegative (count : Nat) (factor : Normalization.InverseRootPolynomial.Coordinate) :
    0 ≤ (count : Normalization.InverseRootPolynomial.Coordinate)^2 * (264 * factor^2) :=
  Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.sq_nonneg_direct _)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) (Fraction.Order.Arithmetic.sq_nonneg_direct _))

/-- Allocate the tolerance and model threshold before sampling. The existing
source request retains all vertex owners; every later model sample and its
cached full chart path satisfy the requested discrepancy bound. -/
theorem regular_area_requested (original : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest
  regular geometry target floor)
    (unramified : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 0)
    (error : Normalization.InverseRootPolynomial.Coordinate) (positive : 0 < error) (minimum : Nat) :
    let rate := (geometry.tail.length : Normalization.InverseRootPolynomial.Coordinate)^2 * (264 *
      regular.factorUpper^2)
    let tolerance := Rational.Budget.Weighted.allowance error rate
    let tolerancePositive := Rational.Budget.Weighted.allowance_positive positive
      (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartSteps.regular_area_rate_nonnegative
        geometry.tail.length regular.factorUpper)
    let source := Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.withTarget original tolerance
      tolerancePositive
    let threshold := max source.index
      (Hyperelliptic.Charts.Reciprocal.ReciprocalRegularCoordinatePolynomial.regularSlopeRequest firstComparison (4 *
        tolerance)
        (Fraction.Order.Arithmetic.mul_pos_direct (by decide) tolerancePositive) minimum).val
    ∀ (evaluated : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest.Evaluation source first
      second tolerance), threshold ≤ index →
      Data.Gaussian.Norm.Basic.normSq (evaluated.area.evaluated.chart.originalArea -
        Periods.CenteredBilinearPath.area
          (Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartSteps.regularPolynomialPoint (geometry := geometry)
          sample otherSample)) ≤ error := by
  intro rate tolerance tolerancePositive source threshold evaluated later
  have bound := Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartSteps.Evaluation.regular_area_uniform evaluated
    unramified tolerancePositive minimum later
  have algebra (count factor tolerance : Normalization.InverseRootPolynomial.Coordinate) :
      count^2 * (264 * factor^2 * tolerance) = (count^2 * (264 * factor^2)) * tolerance := by ring1
  exact bound.trans ((algebra _ _ _).trans_le
    (Rational.Budget.Weighted.mul_allowance_le positive.le
      (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartSteps.regular_area_rate_nonnegative
        geometry.tail.length regular.factorUpper)))

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartSteps
