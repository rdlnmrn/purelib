module
import Purelib.Algebra.FiniteSum.Rational.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartConnections
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartFanBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartJoinedFans
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPreparation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources
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
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartArcComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CoordinatePolynomial
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Basic
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartFans
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Path.Dyadic.DyadicTrace
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.InverseModelRootChannels
import Purelib.Riemann.Normalization.InverseModelRootSamples
import Purelib.Riemann.Normalization.ReciprocalDiskCommonSourceCharts
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Tactic.Ring

public section

/-! Prepared polynomial control of the original paired chart coordinates.
The source endpoint requests already pay the unweighted coordinate error,
even for a vanishing differential. No new root samples are acquired. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartCoordinateSteps.SourceChartRequest

open Purelib.Algebra
open Purelib.Curves
open Purelib.Data
open Purelib
open Purelib.Geometry
open Purelib.Riemann
open Purelib.Data.Rat

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)

open Purelib.Data.Rat.Fraction.Compatibility

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest (Evaluation)

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank.ChartRequest (Evaluation)

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

/-- The retained source coordinate reading approximates its original polynomial value within the requested coordinate
tolerance. -/
theorem Evaluation.coordinate_accurate (evaluated : Evaluation prepared first second requested)
    (modelLater : prepared.index ≤ index) (coordinate :
      CoordinatePolynomial first)
    (i : Fin (geometry.tail.length + 1)) :
    Data.Gaussian.Norm.Basic.normSq (coordinate.value.eval (parent.edge.point
      (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest.Parameter (geometry := geometry) i))⁻¹
      -
      (evaluated.area.evaluated.readings.get i).first.coordinate) < target := by
  let vertex := prepared.vertices.get i
  have modelBound : max vertex.first.index vertex.second.index ≤ index :=
    (Data.Vector.DependentVector.get_le_maximum
      (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.sourceModelWeight regular geometry) prepared.vertices
      i).trans
      (prepared.index_eq.symm.trans_le modelLater)
  have readingLater : prepared.readingIndex ≤ evaluated.area.refined.stage :=
    (Data.Nat.Order.le_max_left _ _).trans evaluated.area.refined.floor_le
  have readingBound : max vertex.first.coordinate.rightIndex vertex.second.coordinate.rightIndex ≤
    evaluated.area.refined.stage :=
    (Data.Vector.DependentVector.get_le_maximum
      (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.sourceReadingWeight regular geometry) prepared.vertices
      i).trans
      (prepared.readingIndex_eq.symm.trans_le readingLater)
  have bound := vertex.first.coordinate_accurate first ((Data.Nat.Order.le_max_left _ _).trans modelBound)
    ((Data.Nat.Order.le_max_left _ _).trans readingBound)
  rw [coordinate.eval, (evaluated.area.evaluated.readings.get i).first.coordinate_eq]
  rw [vertex.firstBounds.radicand_eq] at bound
  exact bound

/-- Two retained coordinate readings differ by the original polynomial slope bound plus both requested reading errors.
-/
theorem Evaluation.coordinate_step (evaluated : Evaluation prepared first second requested)
    (modelLater : prepared.index ≤ index) (coordinate :
      CoordinatePolynomial first)
    (bounds : Hyperelliptic.Charts.Reciprocal.Disk.CoordinatePolynomial.CoordinateBounds firstComparison) (branch :
      Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1)
    (a b : Fin (geometry.tail.length + 1)) :
    Data.Gaussian.Norm.Basic.normSq ((evaluated.area.evaluated.readings.get b).first.coordinate -
      (evaluated.area.evaluated.readings.get a).first.coordinate) <
      2 * (bounds.slope * (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest.Parameter
        (geometry := geometry) b - Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest.Parameter
        (geometry := geometry) a)^2 + 4 * target) := open Purelib.Data.Rat in by
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
  have increment := bounds.increment_bound coordinate branch
    (geometry.vertices.get a).first.root.between (geometry.vertices.get b).first.root.between
  have total := (Gaussian.Norm.Bounds.normSq_sub_le_two (vb - va) ((vb - cb) - (va - ca))).trans_lt
    (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide)
      ((Fraction.Order.Arithmetic.add_lt_add_left_direct errors (Data.Gaussian.Norm.Basic.normSq (vb -
        va))).trans_le (Fraction.Order.Arithmetic.add_le_add_direct increment le_rfl)))
  have identity : cb - ca = (vb - va) - ((vb - cb) - (va - ca)) := by ring1
  rw [identity]
  exact total

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartCoordinateSteps.SourceChartRequest

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartCoordinateSteps.Evaluation

open Purelib.Algebra
open Purelib.Curves
open Purelib.Data
open Purelib
open Purelib.Geometry
open Purelib.Riemann
open Purelib.Data.Rat

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)

open Purelib.Data.Rat.Fraction.Compatibility

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest (Evaluation)

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank.ChartRequest (Evaluation)

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
  {target : Normalization.InverseRootPolynomial.Coordinate} {request :
    Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank.ChartRequest regular common depth target floor}
  (evaluated : Evaluation request index)

/-- The original interval coordinate bound selected by its retained interval index. -/
@[expose] def CoordinateBoundAt (i : Fin common.intervals.length) :=
  Hyperelliptic.Charts.Reciprocal.Disk.CoordinatePolynomial.CoordinateBounds (request.plans.get i).request.first
/-- The original coordinate polynomial on the retained interval and its requested model stage. -/
@[expose] def CoordinatePolynomialAt (i : Fin common.intervals.length) :=
  CoordinatePolynomial (evaluated.entries.get i).first

/-- The local coordinate error allowance of the original chart request. -/
@[expose] def coordinateTolerance (i : Fin common.intervals.length) : Coordinate :=
  (request.plans.get i).request.chart.budget.tolerance

/-- The explicit squared coordinate-step ceiling from the original slope and local reading tolerance. -/
@[expose] def CoordinateStep (i : Fin common.intervals.length) (slope : Normalization.InverseRootPolynomial.Coordinate)
    (edge : Fin (request.plans.get i).geometry.tail.length) : Coordinate :=
  2 * (slope *
    (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest.Parameter (geometry :=
      (request.plans.get i).geometry) edge.succ -
      Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest.Parameter (geometry :=
        (request.plans.get i).geometry) edge.castSucc)^2 +
    4 * Hyperelliptic.Charts.Reciprocal.Disk.CommonChartCoordinateSteps.Evaluation.coordinateTolerance (request :=
      request) i)

set_option genInjectivity false in
/-- One original interval's coordinate polynomial and bounds with a certified ceiling for every actual retained edge.

The polynomial retains its original slope identity and is compared against the same sampled source coordinates. -/
structure CoordinateControl (i : Fin common.intervals.length) where
  /-- The original retained coordinate bounds for this interval. -/ bounds :
    Hyperelliptic.Charts.Reciprocal.Disk.CommonChartCoordinateSteps.Evaluation.CoordinateBoundAt (request := request) i
  /-- The coordinate polynomial on the same interval and retained model stage. -/ polynomial :
    Hyperelliptic.Charts.Reciprocal.Disk.CommonChartCoordinateSteps.Evaluation.CoordinatePolynomialAt evaluated i
  /-- The polynomial slope is exactly the original retained coordinate slope. -/ slope_eq : bounds.slope =
    (request.preparation.entries.get i).coordinates.slope
  /-- Every actual original interval edge satisfies the retained coordinate-step ceiling. -/ bounded :
    Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1 → ∀ edge : Fin (request.plans.get
    i).geometry.tail.length,
    Data.Gaussian.Norm.Basic.normSq
      (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartConnections.Evaluation.chartCoordinate evaluated i edge.succ -
      Hyperelliptic.Charts.Reciprocal.Disk.CommonChartConnections.Evaluation.chartCoordinate evaluated i edge.castSucc)
      <
      Hyperelliptic.Charts.Reciprocal.Disk.CommonChartCoordinateSteps.Evaluation.CoordinateStep (request := request) i
        bounds.slope edge

constructive_injectivity CoordinateControl

/-- One coordinate polynomial per retained interval; all edges reuse its
prepared derivative ceiling and the original source-reading certificates. -/
@[expose] def coordinateControl (i : Fin common.intervals.length) :
  Hyperelliptic.Charts.Reciprocal.Disk.CommonChartCoordinateSteps.Evaluation.CoordinateControl evaluated i := by
  let entry := evaluated.entries.get i
  let bounds : Hyperelliptic.Charts.Reciprocal.Disk.CoordinatePolynomial.CoordinateBounds (request.plans.get
    i).request.first :=
    (request.comparisons_eq i).1.symm ▸ (request.preparation.entries.get i).coordinates
  let polynomial := CoordinatePolynomial.build entry.first
  have transport (left right : Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Data regular
    (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPreparation.IntervalAt common i).first.cell)
      (same : left = right) (coordinates : Hyperelliptic.Charts.Reciprocal.Disk.CoordinatePolynomial.CoordinateBounds
        right) :
      (same.symm ▸ coordinates).slope = coordinates.slope := by cases same; rfl
  have slopeEq : bounds.slope = (request.preparation.entries.get i).coordinates.slope :=
    transport _ _ (request.comparisons_eq i).1 _
  have later : (request.plans.get i).request.chart.refined.index ≤ index :=
    (Data.Nat.Order.le_max_right _ _).trans ((Data.Nat.Order.le_max_left _ _).trans
      ((request.plans.get i).request.index_eq.symm.trans_le entry.evaluated.later))
  exact ⟨bounds, polynomial, slopeEq, fun branch edge =>
    Hyperelliptic.Charts.Reciprocal.Disk.CommonChartCoordinateSteps.SourceChartRequest.Evaluation.coordinate_step
      entry.evaluated.chart.retained later polynomial bounds branch edge.castSucc edge.succ⟩

/-- The actual coordinate-controlled arc edge satisfies the retained area scale times the squared coordinate-step bound.
-/
theorem CoordinateControl.arc_edge_bound {i : Fin common.intervals.length}
    (control : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartCoordinateSteps.Evaluation.CoordinateControl evaluated i)
    (prepared : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartArcComparison.ArcComparisonPreparation (differential :=
      differential) (other := other) (regular := regular))
    (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1) (edge : Fin
      (request.plans.get i).geometry.tail.length) :
    prepared.EdgeBound (evaluated := evaluated) i edge ≤
      prepared.scale * (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartCoordinateSteps.Evaluation.CoordinateStep
        (request := request) i control.bounds.slope edge)^2 := open Purelib.Data.Rat in by
  have scaleNonnegative : 0 ≤ prepared.scale := prepared.scale_eq.symm ▸
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) (Fraction.Order.Arithmetic.sq_nonneg_direct _)
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.pow_le_pow_direct (Gaussian.Norm.Basic.normSq_nonneg _) (control.bounded branch edge).le
      2) scaleNonnegative

/-- The dependent vector of coordinate controls for all original retained intervals. -/
@[expose] def CoordinateControls := Data.Vector.DependentVector
  (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartCoordinateSteps.Evaluation.CoordinateControl evaluated)

/-- The original interval edge count times the finite sum of its retained coordinate-step area ceilings. -/
@[expose] def PreparedIntervalArcBound (scale : Normalization.InverseRootPolynomial.Coordinate) (controls :
  Hyperelliptic.Charts.Reciprocal.Disk.CommonChartCoordinateSteps.Evaluation.CoordinateControls evaluated)
    (i : Fin common.intervals.length) : Coordinate :=
  ((request.plans.get i).geometry.tail.length : Normalization.InverseRootPolynomial.Coordinate) * FiniteSum.Fin.sumFin
    (fun edge =>
    scale * (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartCoordinateSteps.Evaluation.CoordinateStep (request :=
      request) i (controls.get i).bounds.slope edge)^2)

/-- The dependent vector of explicit arc-bound values on the original retained intervals. -/
@[expose] def PreparedIntervalArcBounds := Data.Vector Normalization.InverseRootPolynomial.Coordinate
  common.intervals.length

set_option genInjectivity false in
/-- Cached original interval controls and arc ceilings with a certified bound on the actual shared arc comparison.

The interval values and their total retain exact readback equations, so the proof uses the same computed bounds. -/
structure PreparedArcBound
    {prepared : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartArcComparison.ArcComparisonPreparation (differential :=
      differential) (other := other) (regular := regular)}
    (comparison : prepared.Comparison (evaluated := evaluated)) where
  /-- The retained coordinate controls for the exact original intervals. -/ controls :
    Hyperelliptic.Charts.Reciprocal.Disk.CommonChartCoordinateSteps.Evaluation.CoordinateControls evaluated
  /-- The cached explicit arc bounds of the original intervals. -/ intervals :
    Hyperelliptic.Charts.Reciprocal.Disk.CommonChartCoordinateSteps.Evaluation.PreparedIntervalArcBounds (common :=
    common)
  /-- Each cached interval value equals its original coordinate-controlled arc bound. -/ intervals_eq : ∀ i,
    Data.Vector.get intervals i =
    Hyperelliptic.Charts.Reciprocal.Disk.CommonChartCoordinateSteps.Evaluation.PreparedIntervalArcBound (evaluated :=
      evaluated) prepared.scale controls i
  /-- The cached total original arc ceiling. -/ bound : Normalization.InverseRootPolynomial.Coordinate
  /-- The total is exactly the finite sum of the retained interval bounds. -/ bound_eq : bound =
    (common.intervals.length : Normalization.InverseRootPolynomial.Coordinate) *
    FiniteSum.Fin.sumFin (fun i => Data.Vector.get intervals i)
  /-- The cached bound dominates the actual original shared arc comparison. -/ dominates : comparison.bound ≤ bound

constructive_injectivity PreparedArcBound

/-- The ceiling uses parameter widths and the source request's tolerance,
not the observed coordinate distances. Cache each polynomial and each
interval total once; the original arc-comparison data remains the owner. -/
@[expose] def prepareArcBound
    {prepared : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartArcComparison.ArcComparisonPreparation (differential :=
      differential) (other := other) (regular := regular)}
    (comparison : prepared.Comparison (evaluated := evaluated))
    (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1) :
      Hyperelliptic.Charts.Reciprocal.Disk.CommonChartCoordinateSteps.Evaluation.PreparedArcBound (evaluated :=
      evaluated) comparison := open Purelib.Data.Rat in by
  let controls := Data.Vector.DependentVector.ofFn
    (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartCoordinateSteps.Evaluation.coordinateControl (evaluated :=
    evaluated))
  let intervals := Data.Vector.Basic.vectorOfFn
    (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartCoordinateSteps.Evaluation.PreparedIntervalArcBound (evaluated :=
    evaluated) prepared.scale controls)
  have readback := Data.Vector.Basic.vectorOfFn_apply
    (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartCoordinateSteps.Evaluation.PreparedIntervalArcBound (evaluated :=
    evaluated) prepared.scale controls)
  refine ⟨controls, intervals, readback, (common.intervals.length : Normalization.InverseRootPolynomial.Coordinate) *
    FiniteSum.Fin.sumFin (fun i => intervals i), rfl, ?_⟩
  rw [comparison.bound_eq]
  apply Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct _ (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le
    _))
  apply FiniteSum.Rational.Order.Positivity.sumFin_mono
  intro i
  rw [(comparison.intervals.get i).bound_eq, readback]
  apply Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct _ (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le
    _))
  apply FiniteSum.Rational.Order.Positivity.sumFin_mono
  intro edge
  rw [(comparison.intervals.get i).edges_eq]
  exact Hyperelliptic.Charts.Reciprocal.Disk.CommonChartCoordinateSteps.Evaluation.CoordinateControl.arc_edge_bound
    evaluated (controls.get i) prepared branch edge

/-- The original joined source boundary satisfies the retained prepared arc ceiling with its explicit remaining boundary
terms. -/
theorem FanBankRequest.Joined.prepared_source_boundary_bound {requested :
  Normalization.InverseRootPolynomial.Coordinate} {minimum : Nat}
    {planned : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartFanBank.FanBankRequest evaluated requested minimum} {bank
      : planned.Bank} (joined : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartJoinedFans.FanBankRequest.Joined planned
      bank)
    {prepared : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartArcComparison.ArcComparisonPreparation (differential :=
      differential) (other := other) (regular := regular)}
    {comparison : prepared.Comparison (evaluated := evaluated)} (ceiling :
      Hyperelliptic.Charts.Reciprocal.Disk.CommonChartCoordinateSteps.Evaluation.PreparedArcBound (evaluated :=
      evaluated) comparison) :
    Data.Gaussian.Norm.Basic.normSq
      (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartArcComparison.sourceOpenBoundary evaluated planned.fan.depth) <
      2 * (target + 2 * (2 * (requested + target) + ceiling.bound)) :=
  open Purelib.Data.Rat in
    (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartArcComparison.FanBankRequest.Joined.source_boundary_bound evaluated
    joined comparison).trans_le
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.add_le_add_direct le_rfl (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Fraction.Order.Arithmetic.add_le_add_direct le_rfl ceiling.dominates) (by decide))) (by decide))

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartCoordinateSteps.Evaluation
