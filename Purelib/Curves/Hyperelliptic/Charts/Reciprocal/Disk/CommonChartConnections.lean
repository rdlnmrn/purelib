module
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Integration.Path.Dyadic.RadialTriangles
import Purelib.Topology.Polygon.Stokes

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPreparation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Riemann.RootContinuation.RootRadialGeometry
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank
import Init.Data.Fin.Basic
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartJunctions
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedDisk
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedRootGeometry
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Path.Dyadic.DyadicTrace
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.InverseModelRootChannels
import Purelib.Riemann.Normalization.InverseModelRootSamples
import Purelib.Riemann.Normalization.ReciprocalDiskCommonSourceCharts
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Tactic.Ring
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedRadialRibbon

public section

/-! Complete-bank junction bounds consume the original cached chart readings. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartConnections

open Purelib
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk
open Purelib.Data.Rat
open Purelib.Data.Vector
open Purelib.Integration.Path.Dyadic
open Purelib.Riemann.Normalization
open Purelib.Riemann.Readings.PrimitiveAreaBounds
open Purelib.Topology.Polygon
open Purelib.Topology.Polygon.Stokes
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels (Data)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover (CommonCover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank (ChartRequest junctionLeft junctionRight
  junctionWeight)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank.ChartRequest (Evaluation)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPreparation (IntervalAt)
open Purelib.Riemann.RootContinuation
open Purelib.Data.Rat.Fraction.Compatibility
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
variable {genus count otherCount depth floor index : Nat} {curve : HyperellipticCurve
  genus}
  {differential other : Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : PreparedPatch parent}
  {otherPatch : PreparedPatch
    (Purelib.Riemann.Integration.PreparedEdgeRecasting.recastCenteredEdge other parent)}
  {data : Data patch count} {otherData :
    Data otherPatch otherCount}
  {cover : Cover data} {otherCover :
    Cover otherData}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {common :
    CommonCover cover otherCover}
  {target : Coordinate} {request :
    ChartRequest regular common depth target floor}

/-- Every actual retained adjacent-chart junction is paid at the complete bank's reading floor. -/
theorem junction_le_readingFloor (i : Fin (common.intervals.length - 1)) :
    (request.junctions.get i).index ≤ request.readingFloor :=
  (DependentVector.get_le_maximum (CommonChartBank.junctionWeight regular common request.plans) request.junctions
    i).trans
    ((Data.Nat.Order.le_max_right _ _).trans_eq request.readingFloor_eq.symm)

namespace Evaluation
variable (evaluated : Evaluation
  request index)

/-- Read the actual first paired chart point already cached for the selected original interval. -/
@[expose] def firstChartPoint (i : Fin common.intervals.length) : Stokes.PrimitivePoint :=
  ((evaluated.entries.get i).evaluated.chart.retained.area.evaluated.readings.get 0).chartPoint

/-- Read the actual last paired chart point already cached for that same original interval. -/
@[expose] def lastChartPoint (i : Fin common.intervals.length) : Stokes.PrimitivePoint :=
  ((evaluated.entries.get i).evaluated.chart.retained.area.evaluated.readings.get
    (Fin.last (request.plans.get i).geometry.tail.length)).chartPoint

/-- The actual next-first minus previous-last paired chart connector at the retained junction. -/
@[expose] def junctionGap (i : Fin (common.intervals.length - 1)) : Stokes.PrimitivePoint :=
  (firstChartPoint evaluated
    (CommonChartBank.junctionRight common i)).sub
    (lastChartPoint evaluated
    (CommonChartBank.junctionLeft common i))

/-- Read the local chart-area tolerance already retained by this actual interval evaluation. -/
@[expose] def chartTolerance (i : Fin common.intervals.length) : Coordinate :=
  (evaluated.entries.get i).evaluated.chart.retained.area.budget.tolerance

/-- The actual local chart tolerance is at most one thirty-second of its original interval tolerance. -/
theorem chartTolerance_prepared (i : Fin common.intervals.length) :
    chartTolerance evaluated i ≤
      (request.plans.get i).budget.tolerance / 32 := by
  let entry := evaluated.entries.get i
  let area := entry.evaluated.chart.retained.area
  have nonnegative : 0 ≤ area.magnitude := area.magnitude_eq.symm ▸
    entry.evaluated.chart.retained.request.magnitude_nonnegative
  have positive : 0 < ((request.plans.get i).budget.tolerance / 4) / 4 :=
    Fraction.Order.Field.div_pos_direct (Fraction.Order.Field.div_pos_direct (request.plans.get i).budget.positive (by
      decide)) (by decide)
  have bound := area.budget.tolerance_le nonnegative positive
  have scalar (value : InverseRootPolynomial.Coordinate) : ((value / 4) / 4) / 2 = value / 32 := by
    calc
      _ = value * ((4 : InverseRootPolynomial.Coordinate)⁻¹ * 4⁻¹ * 2⁻¹) := by
        simp only [Fraction.Field.div_eq_mul_inv_direct, -eq_self, -iff_self];
        ring1
      _ = value * (32 : InverseRootPolynomial.Coordinate)⁻¹ := congrArg (fun coefficient => value * coefficient) (by
        decide +kernel)
  exact bound.trans_eq (scalar _)

/-- The actual local chart tolerance is at most one thirty-second of the original complete-bank allowance. -/
theorem chartTolerance_le (i : Fin common.intervals.length) :
    chartTolerance evaluated i ≤
      request.allowance / 32 :=
  (chartTolerance_prepared evaluated
    i).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (request.plans.get i).budget.bounded
      (by decide +kernel : (0 : InverseRootPolynomial.Coordinate) ≤ (32 : InverseRootPolynomial.Coordinate)⁻¹))

/-- The actual retained chart tolerance satisfies the original padded root-square clearance. -/
theorem chartTolerance_padded (i : Fin common.intervals.length) :
    chartTolerance evaluated i ≤
      regular.padded.squareTolerance := by
  have shrink := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (by decide +kernel : (32 : InverseRootPolynomial.Coordinate)⁻¹ ≤ 1) (request.plans.get i).budget.positive.le
  exact (chartTolerance_prepared evaluated
    i).trans
    ((shrink.trans_eq (mul_one _)).trans (request.plans.get i).budget.padded_paid)

/-- Read the shared first-component root coordinate already cached at the original chart vertex. -/
@[expose] def chartCoordinate (i : Fin common.intervals.length)
    (vertex : Fin ((request.plans.get i).geometry.tail.length + 1)) : InverseRootPolynomial.Gaussian :=
  ((evaluated.entries.get i).evaluated.chart.retained.area.evaluated.readings.get vertex).first.coordinate

/-- Both components use this same retained coordinate, not two independently chosen roots. This is the readback needed
for the paired radial polynomial. -/
theorem chartPoint_readback (branch : HyperellipticReciprocal.originOrder curve = 1)
    (i : Fin common.intervals.length) (vertex : Fin ((request.plans.get i).geometry.tail.length + 1)) :
    ((evaluated.entries.get i).evaluated.chart.retained.area.evaluated.readings.get vertex).chartPoint =
      ⟨evaluated.samples.firstCap.primitive.value.eval
        (chartCoordinate evaluated i
        vertex),
        evaluated.samples.otherCap.primitive.value.eval
          (chartCoordinate evaluated i
          vertex)⟩ := by
  let reading := (evaluated.entries.get i).evaluated.chart.retained.area.evaluated.readings.get vertex
  apply congrArg₂ PrimitivePoint.mk
  · change reading.firstChart.value = evaluated.samples.firstCap.primitive.value.eval reading.first.coordinate
    have value := reading.firstChart.value_eq
    rw [branch, if_neg (by decide : (1 : Nat) ≠ 0)] at value
    exact value
  · have value := reading.otherChart.value_eq
    rw [branch, if_neg (by decide : (1 : Nat) ≠ 0), ← reading.coordinate_eq] at value
    exact value

/-- The geometric clearance was paid before either primitive polynomial or root coordinate was sampled. Every retained
paired chart vertex is covered. -/
theorem chart_square_inside (branch : HyperellipticReciprocal.originOrder curve = 1)
    (i : Fin common.intervals.length) (vertex : Fin ((request.plans.get i).geometry.tail.length + 1)) :
    regular.padded.Contains
      (chartCoordinate evaluated i vertex
      * chartCoordinate evaluated i
      vertex) := by
  let owner := ((request.plans.get i).geometry.vertices.get vertex).first
  let reading := (evaluated.entries.get i).evaluated.chart.retained.area.evaluated.readings.get vertex
  have square := reading.firstChart.square_accurate
  rw [branch, pow_one, Data.Gaussian.Norm.Basic.normSq_eq_canonical] at square
  exact regular.padded.contains_square
    (ReciprocalExteriorCollar.inverse_inDisk curve (data.boundary.point
      ⟨(CommonChartPreparation.IntervalAt common i).first.owner.left.inside.1.trans owner.root.between.1,
        owner.root.between.2.trans (CommonChartPreparation.IntervalAt common i).first.owner.right.inside.2⟩))
    (square.le.trans
      (chartTolerance_padded evaluated i))

/-- This includes the entire radial fan, not merely its sampled boundary. No orientation of an independently rounded
root chord is presumed. -/
theorem radial_chord_inside (branch : HyperellipticReciprocal.originOrder curve = 1)
    (i : Fin common.intervals.length) (first last : Fin ((request.plans.get i).geometry.tail.length + 1))
    {parameter : InverseRootPolynomial.Gaussian} (unit : RadialTriangles.unitBox.Contains parameter) :
    regular.padded.Contains
      (RootRadialGeometry.point
        (chartCoordinate evaluated i
        first) (chartCoordinate evaluated
        i last) parameter *
        RootRadialGeometry.point
          (chartCoordinate evaluated i
          first) (chartCoordinate
          evaluated i last) parameter) :=
  regular.padded.radial_square
    (regular.padded.chord_square
      (chart_square_inside evaluated
      branch i first)
      (chart_square_inside evaluated
        branch i last) unit.2.2) ⟨unit.1, unit.2.1⟩

/-- Both local area searches retain the preselected complete-bank junction floor, even when they finish at different
stages. -/
theorem junction_coordinate_accurate (i : Fin (common.intervals.length - 1)) :
    Data.Gaussian.Norm.Basic.normSq (((evaluated.entries.get (CommonChartBank.junctionRight common
      i)).evaluated.chart.retained.area.evaluated.readings.get 0).first.coordinate -
      ((evaluated.entries.get (CommonChartBank.junctionLeft common
        i)).evaluated.chart.retained.area.evaluated.readings.get
        (Fin.last (request.plans.get (CommonChartBank.junctionLeft common i)).geometry.tail.length)).first.coordinate) <
      collar.coordinateBound / 64 := by
  let left := evaluated.entries.get (CommonChartBank.junctionLeft common i)
  let right := evaluated.entries.get (CommonChartBank.junctionRight common i)
  exact (request.junctions.get i).coordinate_accurate
    (left.evaluated.chart.retained.area.evaluated.readings.get (Fin.last (request.plans.get
      (CommonChartBank.junctionLeft common i)).geometry.tail.length))
    (right.evaluated.chart.retained.area.evaluated.readings.get 0)
    ((Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartConnections.junction_le_readingFloor i).trans
      left.readingLater)
    ((Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartConnections.junction_le_readingFloor i).trans
      right.readingLater)

/-- The bank's original allowance pays the actual paired chart connector, including the two chart-reading errors. No
roots or polynomials are reread. -/
theorem junction_bounded (i : Fin (common.intervals.length - 1)) :
    PrimitivePoint.Bounded
      (junctionGap evaluated i)
        request.allowance := by
  let left := evaluated.entries.get (CommonChartBank.junctionLeft common i)
  let right := evaluated.entries.get (CommonChartBank.junctionRight common i)
  have bounded := (request.junctions.get i).chart_accurate
    (left.evaluated.chart.retained.area.evaluated.readings.get (Fin.last (request.plans.get
      (CommonChartBank.junctionLeft common i)).geometry.tail.length))
    (right.evaluated.chart.retained.area.evaluated.readings.get 0)
    ((Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartConnections.junction_le_readingFloor i).trans
      left.readingLater)
    ((Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartConnections.junction_le_readingFloor i).trans
      right.readingLater)
  have leftBound := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (chartTolerance_le evaluated
    (CommonChartBank.junctionLeft common i)) (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 4)
  have rightBound := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (chartTolerance_le evaluated
    (CommonChartBank.junctionRight common i)) (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 4)
  have paid := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.add_le_add_direct rightBound (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.add_le_add_direct (le_refl (request.allowance / 16)) leftBound) (by
          decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2)))
    (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2)
  have scalar : 2 * (4 * (request.allowance / 32) + 2 * (request.allowance / 16 + 4 * (request.allowance / 32))) =
      request.allowance := by
    calc
      _ = request.allowance * (24 * (32 : InverseRootPolynomial.Coordinate)⁻¹ + 4 * (16 :
        InverseRootPolynomial.Coordinate)⁻¹) := by
        simp only [Fraction.Field.div_eq_mul_inv_direct, -eq_self, -iff_self]; ring1
      _ = request.allowance * 1 := congrArg (fun coefficient => request.allowance * coefficient) (by decide +kernel)
      _ = request.allowance := mul_one _
  exact ⟨bounded.1.trans (paid.trans_eq scalar), bounded.2.trans (paid.trans_eq scalar)⟩

end Evaluation
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartConnections
