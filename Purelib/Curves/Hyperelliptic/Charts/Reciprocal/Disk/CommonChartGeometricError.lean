module
import Purelib.Approximation.Rational.Geometric.DyadicCount
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Algebra.FiniteSum.Fin.Rational
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Vector.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartArcComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartFanBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartJoinedFans
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPreparation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartCoordinateSteps
import Purelib.Integration.Path.Dyadic.DyadicSteps
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartFans
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CoordinatePolynomial
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.ReciprocalDiskCommonSourceCharts
import Purelib.Tactic.Ring

public section

/-! The actual chart edge count cancels one power of the dyadic squared
width. The remaining arc error has an explicit quarter-power ceiling. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartGeometricError

open Purelib.Algebra
open Purelib.Approximation
open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Riemann
open Purelib

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)

open Purelib.Data.Rat.Fraction.Compatibility

open Purelib.Riemann.Periods.CenteredBilinearPath hiding Coordinate

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
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {common :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover.CommonCover cover otherCover}
  {target : Coordinate} {request : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank.ChartRequest regular common
    depth target floor}
  (evaluated : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank.ChartRequest.Evaluation request index)

/-- The squared finite dyadic edge count cancels the unit quarter-power radius exactly. -/
private theorem count_cancel (depth : Nat) : (((2^depth : Nat) : Coordinate)^2) * Rational.Geometric.Basic.quarterRadius
  1 depth = 1 := by
  calc
    _ = ((2^depth : Nat) : Coordinate) *
        (((2^depth : Nat) : Coordinate) * Rational.Geometric.Basic.quarterRadius 1 depth) := by ring1
    _ = 1 := Rational.Geometric.DyadicCount.dyadic_count_cancel 1 depth

/-- Each original common interval retains exactly the requested dyadic number of chart edges. -/
theorem chartEdgeCount (i : Fin common.intervals.length) : (request.plans.get i).geometry.tail.length = 2^depth := open
  Purelib.Integration in by
  rw [(request.plans.get i).geometry.tail_eq, Path.Dyadic.DyadicSteps.tail_length]

/-- Each retained chart edge has squared parameter width equal to the original interval width squared times the dyadic
quarter-power factor. -/
theorem chartWidthSquare (i : Fin common.intervals.length) (edge : Fin (request.plans.get i).geometry.tail.length) :
    (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest.Parameter (geometry :=
      (request.plans.get i).geometry) edge.succ -
      Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest.Parameter (geometry :=
        (request.plans.get i).geometry) edge.castSucc)^2 =
    Rational.Geometric.Basic.quarterRadius 1 depth *
      ((Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPreparation.IntervalAt common i).edge.right.parameter -
      (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPreparation.IntervalAt common i).edge.left.parameter)^2 := open
      Purelib.Integration in by
  have steps : Path.Dyadic.DyadicSteps.Steps (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPreparation.IntervalAt
    common i).edge.left.parameter (request.plans.get i).geometry.tail
      (((Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPreparation.IntervalAt common i).edge.right.parameter -
        (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPreparation.IntervalAt common i).edge.left.parameter) * (1 /
        2)^depth) := by
    rw [(request.plans.get i).geometry.tail_eq]
    exact Path.Dyadic.DyadicSteps.tail_steps _ _ _
  exact steps.width_square edge

/-- The original allocated coordinate tolerance is bounded by the unit quarter-power radius at the retained depth. -/
theorem coordinateTolerance_mesh (i : Fin common.intervals.length) :
    Hyperelliptic.Charts.Reciprocal.Disk.CommonChartCoordinateSteps.Evaluation.coordinateTolerance (request := request)
      i ≤ Rational.Geometric.Basic.quarterRadius 1 depth := by
  let plan := request.plans.get i
  let budget := plan.request.chart.budget
  have magnitude : 0 ≤ plan.request.chart.magnitude :=
    plan.request.chart.magnitude_eq.symm ▸
      Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceChartRequest.magnitude_nonnegative plan.prepared
  have coefficient : (1 : Coordinate) ≤ 32 * (4 * plan.request.chart.magnitude + 1) * 16 := by
    have lower : (1 : Coordinate) ≤ 4 * plan.request.chart.magnitude + 1 := le_add_of_nonneg_left
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) magnitude)
    have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct lower (by decide +kernel : (0 : Coordinate) ≤ 32))
      (by decide +kernel : (0 : Coordinate) ≤ 16)
    exact (by decide +kernel : (1 : Coordinate) ≤ 32 * 1 * 16).trans scaled
  have toleranceCount : ((plan.geometry.tail.length : Coordinate)^2) * budget.tolerance < (plan.budget.tolerance / 4) /
    4 := by
    have multiplied := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct coefficient budget.positive.le)
        (Fraction.Order.Arithmetic.sq_nonneg_direct (plan.geometry.tail.length : Coordinate))
    exact (show (plan.geometry.tail.length : Coordinate)^2 * budget.tolerance =
      (plan.geometry.tail.length : Coordinate)^2 * (1 * budget.tolerance) by ring1).trans_le multiplied |>.trans_lt
      ((by ring1 : (plan.geometry.tail.length : Coordinate)^2 *
          (32 * (4 * plan.request.chart.magnitude + 1) * 16 * budget.tolerance) =
        (plan.geometry.tail.length : Coordinate)^2 * (32 * (4 * plan.request.chart.magnitude + 1) * (16 *
          budget.tolerance))).trans_lt budget.paid)
  have small : (plan.budget.tolerance / 4) / 4 ≤ 1 :=
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct plan.budget.small (by
          decide : (0 : Coordinate) ≤ (4 : Coordinate)⁻¹))
      (by decide : (0 : Coordinate) ≤ (4 : Coordinate)⁻¹)).trans (by decide)
  have counted : (((2^depth : Nat) : Coordinate)^2) *
    Hyperelliptic.Charts.Reciprocal.Disk.CommonChartCoordinateSteps.Evaluation.coordinateTolerance (request := request)
    i ≤ 1 := by
    have bound := (toleranceCount.trans_le small).le
    change ((request.plans.get i).geometry.tail.length : Coordinate)^2 *
      Hyperelliptic.Charts.Reciprocal.Disk.CommonChartCoordinateSteps.Evaluation.coordinateTolerance (request :=
      request) i ≤ 1 at bound
    rw [Hyperelliptic.Charts.Reciprocal.Disk.CommonChartGeometricError.chartEdgeCount] at bound
    exact bound
  have multiplied := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct counted
    (Rational.Geometric.Basic.quarterRadius_nonneg (by decide : (0 : Coordinate) ≤ 1) depth)
  exact (show Hyperelliptic.Charts.Reciprocal.Disk.CommonChartCoordinateSteps.Evaluation.coordinateTolerance (request :=
    request) i =
      ((((2^depth : Nat) : Coordinate)^2) *
        Hyperelliptic.Charts.Reciprocal.Disk.CommonChartCoordinateSteps.Evaluation.coordinateTolerance (request :=
        request) i) * Rational.Geometric.Basic.quarterRadius 1 depth by
        rw [show ((((2^depth : Nat) : Coordinate)^2) *
          Hyperelliptic.Charts.Reciprocal.Disk.CommonChartCoordinateSteps.Evaluation.coordinateTolerance (request :=
          request) i) * Rational.Geometric.Basic.quarterRadius 1 depth =
          ((((2^depth : Nat) : Coordinate)^2) * Rational.Geometric.Basic.quarterRadius 1 depth) *
            Hyperelliptic.Charts.Reciprocal.Disk.CommonChartCoordinateSteps.Evaluation.coordinateTolerance (request :=
            request) i by ring1,
          Hyperelliptic.Charts.Reciprocal.Disk.CommonChartGeometricError.count_cancel]; ring1).trans_le
            (multiplied.trans_eq (Fraction.Field.one_mul _))

/-- Each original coordinate-step ceiling is bounded by the retained slope-plus-four factor times the dyadic
quarter-power radius. -/
theorem coordinateStep_geometric (i : Fin common.intervals.length) {slope : Coordinate} (nonnegative : 0 ≤ slope)
    (edge : Fin (request.plans.get i).geometry.tail.length) :
    Hyperelliptic.Charts.Reciprocal.Disk.CommonChartCoordinateSteps.Evaluation.CoordinateStep (request := request) i
      slope edge ≤ 2 * (slope + 4) * Rational.Geometric.Basic.quarterRadius 1 depth := by
  have width : ((Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPreparation.IntervalAt common i).edge.right.parameter -
    (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPreparation.IntervalAt common i).edge.left.parameter)^2 ≤ 1 :=
    (Fraction.Order.Arithmetic.pow_le_pow_direct (Fraction.Order.Arithmetic.sub_nonneg_direct
      (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPreparation.IntervalAt common i).ordered)
      ((Fraction.Order.Arithmetic.sub_le_sub_direct
        (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPreparation.IntervalAt common i).edge.right.inside.2
        (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPreparation.IntervalAt common i).edge.left.inside.1).trans_eq
        (by decide : (1 : Coordinate) - 0 = 1)) 2).trans_eq (by decide)
  unfold Hyperelliptic.Charts.Reciprocal.Disk.CommonChartCoordinateSteps.Evaluation.CoordinateStep
  rw [Hyperelliptic.Charts.Reciprocal.Disk.CommonChartGeometricError.chartWidthSquare]
  have main := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct width (Rational.Geometric.Basic.quarterRadius_nonneg (by
      decide : (0 : Coordinate) ≤ 1) depth)) nonnegative
  have reading := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartGeometricError.coordinateTolerance_mesh (request := request) i) (by
    decide : (0 : Coordinate) ≤ 4)
  exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct main
    reading) (by decide)).trans_eq (by ring1)

/-- The cached original interval arc ceiling has an explicit quarter-geometric bound after cancellation of the actual
edge count. -/
theorem preparedInterval_geometric {scale : Coordinate} (scaleNonnegative : 0 ≤ scale)
    (controls : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartCoordinateSteps.Evaluation.CoordinateControls evaluated)
      (i : Fin common.intervals.length) :
    Hyperelliptic.Charts.Reciprocal.Disk.CommonChartCoordinateSteps.Evaluation.PreparedIntervalArcBound (evaluated :=
      evaluated) scale controls i ≤
      Rational.Geometric.Basic.quarterRadius (4 * scale * ((controls.get i).bounds.slope + 4)^2) depth := by
  let slope := (controls.get i).bounds.slope
  have slopeNonnegative : 0 ≤ slope := (controls.get i).bounds.slope_nonnegative
  have stepNonnegative (edge : Fin (request.plans.get i).geometry.tail.length) :
      0 ≤ Hyperelliptic.Charts.Reciprocal.Disk.CommonChartCoordinateSteps.Evaluation.CoordinateStep (request := request)
        i slope edge :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct
      slopeNonnegative (Fraction.Order.Arithmetic.sq_nonneg_direct _))
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (request.plans.get i).request.chart.budget.positive.le))
  have terms := FiniteSum.Rational.Order.Positivity.sumFin_mono
    (fun edge => scale * (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartCoordinateSteps.Evaluation.CoordinateStep
      (request := request) i slope edge)^2)
    (fun _ => scale * (2 * (slope + 4) * Rational.Geometric.Basic.quarterRadius 1 depth)^2)
    (fun edge => Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.pow_le_pow_direct (stepNonnegative edge)
        (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartGeometricError.coordinateStep_geometric (request := request) i
        slopeNonnegative edge) 2) scaleNonnegative)
  rw [FiniteSum.Fin.Rational.sum_constant] at terms
  have counted := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct terms
    (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le (request.plans.get i).geometry.tail.length))
  change Hyperelliptic.Charts.Reciprocal.Disk.CommonChartCoordinateSteps.Evaluation.PreparedIntervalArcBound (evaluated
    := evaluated) scale controls i ≤ _ at counted
  apply counted.trans_eq
  rw [Hyperelliptic.Charts.Reciprocal.Disk.CommonChartGeometricError.chartEdgeCount]
  calc
    _ = ((((2^depth : Nat) : Coordinate)^2) * Rational.Geometric.Basic.quarterRadius 1 depth) *
        (4 * scale * (slope + 4)^2 * Rational.Geometric.Basic.quarterRadius 1 depth) := by ring1
    _ = _ := by
      rw [Hyperelliptic.Charts.Reciprocal.Disk.CommonChartGeometricError.count_cancel];
      simp only [Rational.Geometric.Basic.quarterRadius_eq_mul_pow, -eq_self, -iff_self];
      dsimp only [slope, -eq_self, -iff_self];
      ring1

/-- The interval-count-weighted sum of the original coordinate-controlled geometric arc scales. -/
@[expose] def GeometricArcScale (scale : Coordinate) (controls :
  Hyperelliptic.Charts.Reciprocal.Disk.CommonChartCoordinateSteps.Evaluation.CoordinateControls evaluated) : Coordinate
  :=
  (common.intervals.length : Coordinate) * FiniteSum.Fin.sumFin (fun i => 4 * scale * ((controls.get i).bounds.slope +
    4)^2)

/-- The geometric scale from the retained controls equals the original request preparation's cached scale. -/
theorem geometricArcScale_preparation (controls :
  Hyperelliptic.Charts.Reciprocal.Disk.CommonChartCoordinateSteps.Evaluation.CoordinateControls evaluated) :
    Hyperelliptic.Charts.Reciprocal.Disk.CommonChartGeometricError.GeometricArcScale (evaluated := evaluated)
      request.preparation.arcScale controls = request.preparation.scale := by
  rw [request.preparation.scale_eq]
  apply congrArg (fun value => (common.intervals.length : Coordinate) * value)
  exact FiniteSum.Fin.sumFin_congr (fun i => congrArg (fun slope => 4 * request.preparation.arcScale * (slope + 4)^2)
    (controls.get i).slope_eq)

set_option genInjectivity false in
/-- A cached quarter-geometric ceiling for the actual prepared arc comparison.

The scale retains its exact coordinate-control readback and dominates the already computed original arc bound. -/
structure GeometricArcBound
    {prepared : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartArcComparison.ArcComparisonPreparation (differential :=
      differential) (other := other) (regular := regular)}
    {comparison : prepared.Comparison (evaluated := evaluated)} (ceiling :
      Hyperelliptic.Charts.Reciprocal.Disk.CommonChartCoordinateSteps.Evaluation.PreparedArcBound (evaluated :=
      evaluated) comparison) where
  /-- The cached aggregate geometric scale of the original interval controls. -/ scale : Coordinate
  /-- The scale equals the interval-count-weighted sum of the retained local scales. -/ scale_eq : scale =
    Hyperelliptic.Charts.Reciprocal.Disk.CommonChartGeometricError.GeometricArcScale (evaluated := evaluated)
    prepared.scale ceiling.controls
  /-- The retained geometric scale is nonnegative. -/ nonnegative : 0 ≤ scale
  /-- The cached quarter-geometric error ceiling at the original depth. -/ bound : Coordinate
  /-- The ceiling equals the quarter-power radius of the retained scale. -/ bound_eq : bound =
    Rational.Geometric.Basic.quarterRadius scale depth
  /-- The geometric ceiling dominates the original prepared arc bound. -/ dominates : ceiling.bound ≤ bound

constructive_injectivity GeometricArcBound

/-- Reuse the prepared coordinate controls. The finite interval count is
paid in the cached scale, and the original edge count has cancelled. -/
@[expose] def geometricArcBound
    {prepared : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartArcComparison.ArcComparisonPreparation (differential :=
      differential) (other := other) (regular := regular)}
    {comparison : prepared.Comparison (evaluated := evaluated)} (ceiling :
      Hyperelliptic.Charts.Reciprocal.Disk.CommonChartCoordinateSteps.Evaluation.PreparedArcBound (evaluated :=
      evaluated) comparison) :
    Hyperelliptic.Charts.Reciprocal.Disk.CommonChartGeometricError.GeometricArcBound (evaluated := evaluated) ceiling :=
      open Purelib in by
  let scale := Hyperelliptic.Charts.Reciprocal.Disk.CommonChartGeometricError.GeometricArcScale (evaluated := evaluated)
    prepared.scale ceiling.controls
  have preparedNonnegative : 0 ≤ prepared.scale := prepared.scale_eq.symm ▸
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) (Fraction.Order.Arithmetic.sq_nonneg_direct _)
  have nonnegative : 0 ≤ scale := Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Cast.Order.natCast_le_direct
    (Nat.zero_le _))
    (FiniteSum.Rational.Order.weight_sum_nonnegative _ (fun _ => Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) preparedNonnegative)
      (Fraction.Order.Arithmetic.sq_nonneg_direct _)))
  refine ⟨scale, rfl, nonnegative, Rational.Geometric.Basic.quarterRadius scale depth, rfl, ?_⟩
  rw [ceiling.bound_eq]
  have localBounds := FiniteSum.Rational.Order.Positivity.sumFin_mono
    (fun i => Data.Vector.get ceiling.intervals i)
    (fun i => Rational.Geometric.Basic.quarterRadius (4 * prepared.scale * ((ceiling.controls.get i).bounds.slope +
      4)^2) depth)
    (fun i => (ceiling.intervals_eq i).trans_le
      (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartGeometricError.preparedInterval_geometric (evaluated :=
      evaluated) preparedNonnegative ceiling.controls i))
  apply (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct localBounds (Fraction.Cast.Order.natCast_le_direct
    (Nat.zero_le _))).trans_eq
  have expanded := FiniteSum.Fin.sumFin_congr (fun i => Rational.Geometric.Basic.quarterRadius_eq_mul_pow
    (4 * prepared.scale * ((ceiling.controls.get i).bounds.slope + 4)^2) depth)
  rw [expanded, FiniteSum.Fin.sumFin_mul_right, Rational.Geometric.Basic.quarterRadius_eq_mul_pow]
  dsimp only [scale, Hyperelliptic.Charts.Reciprocal.Disk.CommonChartGeometricError.GeometricArcScale, -eq_self,
    -iff_self]
  ring1

/-- Matching the original local scale identifies the retained aggregate geometric scale with the request preparation's
cached scale. -/
theorem GeometricArcBound.preparation_scale
    {prepared : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartArcComparison.ArcComparisonPreparation (differential :=
      differential) (other := other) (regular := regular)}
    {comparison : prepared.Comparison (evaluated := evaluated)} {ceiling :
      Hyperelliptic.Charts.Reciprocal.Disk.CommonChartCoordinateSteps.Evaluation.PreparedArcBound (evaluated :=
      evaluated) comparison}
    (geometric : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartGeometricError.GeometricArcBound (evaluated :=
      evaluated) ceiling) (owned : prepared.scale = request.preparation.arcScale) :
    geometric.scale = request.preparation.scale := by
  rw [geometric.scale_eq, owned]
  exact Hyperelliptic.Charts.Reciprocal.Disk.CommonChartGeometricError.geometricArcScale_preparation (evaluated :=
    evaluated) ceiling.controls

/-- The actual joined source boundary satisfies the retained geometric arc ceiling with the original request and chart
errors. -/
theorem FanBankRequest.Joined.geometric_source_boundary_bound {requested : Coordinate} {minimum : Nat}
    {planned : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartFanBank.FanBankRequest evaluated requested minimum} {bank
      : planned.Bank} (joined : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartJoinedFans.FanBankRequest.Joined planned
      bank)
    {prepared : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartArcComparison.ArcComparisonPreparation (differential :=
      differential) (other := other) (regular := regular)}
    {comparison : prepared.Comparison (evaluated := evaluated)} {ceiling :
      Hyperelliptic.Charts.Reciprocal.Disk.CommonChartCoordinateSteps.Evaluation.PreparedArcBound (evaluated :=
      evaluated) comparison}
    (geometric : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartGeometricError.GeometricArcBound (evaluated :=
      evaluated) ceiling) :
    Data.Gaussian.Norm.Basic.normSq
      (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartArcComparison.sourceOpenBoundary evaluated planned.fan.depth) <
      2 * (target + 2 * (2 * (requested + target) + geometric.bound)) :=

    (CommonChartCoordinateSteps.Evaluation.FanBankRequest.Joined.prepared_source_boundary_bound
    evaluated joined ceiling).trans_le
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.add_le_add_direct le_rfl (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Fraction.Order.Arithmetic.add_le_add_direct le_rfl geometric.dominates) (by decide))) (by decide))

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartGeometricError
