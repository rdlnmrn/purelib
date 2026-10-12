module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Vector.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartConnections
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartFanBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPreparation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartRadialJunctions
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.RootContinuation.RootRadialPairedArcs
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartJoinedFans
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedPairedArcArea
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartFans
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartPaths
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Path.Dyadic.DyadicTrace
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Normalization.ReciprocalDiskCommonSourceCharts
import Purelib.Tactic.Ring

public section

/-! The retained source chart polygons versus the curved paired fan arcs.
The executable bound reports the actual mesh; it does not assert that an
arbitrary original chart depth has already met a requested tolerance. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartArcComparison

open Purelib.Algebra
open Purelib.Curves
open Purelib.Data
open Purelib
open Purelib.Riemann
open Purelib.Data.Rat

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

open Purelib.Data.Rat.Fraction.Compatibility

/-- The finite indexed Gaussian sum equals the sum of its original list-of-function readback. -/
private theorem sum_readback {n : Nat} (values : Fin n → Gaussian.Basic.Canonical) : FiniteSum.Fin.sumFin values =
  Data.Gaussian.Norm.Sum.Basic.gaussianSum (List.ofFn values) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [FiniteSum.Fin.sumFin_succ, Data.List.OfFn.Basic.ofFn_succ, Data.Gaussian.Norm.Sum.Basic.gaussianSum, ih]

/-- Pointwise squared-norm bounds sum to a bound on the original indexed list of values. -/
private theorem norm_sum_bound {n : Nat} (values : Fin n → Gaussian.Basic.Canonical) (bounds : Fin n →
  Normalization.InverseRootPolynomial.Coordinate)
    (bounded : ∀ i, Data.Gaussian.Norm.Basic.normSq (values i) ≤ bounds i) :
      Purelib.Data.Gaussian.Norm.Sum.Basic.gaussianNormSqSum (List.ofFn values) ≤ FiniteSum.Fin.sumFin bounds := open
      Purelib.Data.Rat in by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
      rw [Data.List.OfFn.Basic.ofFn_succ, Gaussian.Norm.Sum.Basic.gaussianNormSqSum, FiniteSum.Fin.sumFin_succ]
      have firstScalar := bounded 0
      rw [Gaussian.Norm.Basic.normSq_eq_canonical] at firstScalar
      exact Fraction.Order.Arithmetic.add_le_add_direct firstScalar (ih _ _ (fun i => bounded i.succ))

/-- The squared norm of the original finite sum is bounded by its count times the sum of the supplied pointwise bounds.
-/
theorem weighted_bound {n : Nat} (values : Fin n → Gaussian.Basic.Canonical) (bounds : Fin n →
  Normalization.InverseRootPolynomial.Coordinate)
    (bounded : ∀ i, Data.Gaussian.Norm.Basic.normSq (values i) ≤ bounds i) : Data.Gaussian.Norm.Basic.normSq
      (FiniteSum.Fin.sumFin values) ≤ (n : Normalization.InverseRootPolynomial.Coordinate) * FiniteSum.Fin.sumFin bounds
      := open Purelib.Data.Rat in by
  rw [Hyperelliptic.Charts.Reciprocal.Disk.CommonChartArcComparison.sum_readback]
  have bound := Gaussian.Norm.Sum.Basic.normSq_gaussianSum_le (List.ofFn values)
  rw [Data.List.OfFn.Basic.length_ofFn] at bound
  rw [← Gaussian.Norm.Basic.normSq_eq_canonical] at bound
  exact bound.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartArcComparison.norm_sum_bound values bounds bounded)
    (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le n)))

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
  (evaluated : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank.ChartRequest.Evaluation request index)

set_option genInjectivity false in
/-- The original uniform reciprocal bounds and retained coefficient scale for comparing chart chords with paired radial
arcs. -/
structure ArcComparisonPreparation where
  /-- The original padded reciprocal uniform bounds. -/ bounds :
    Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse.UniformBounds regular.padded
  /-- The retained coefficient scale for the paired arc comparison. -/ scale :
    Normalization.InverseRootPolynomial.Coordinate
  /-- The scale equals sixteen times the square of the maximum original coefficient bound. -/ scale_eq : scale = 16 *
    (max (bounds.coefficientUpper differential) (bounds.coefficientUpper other))^2

constructive_injectivity ArcComparisonPreparation

namespace ArcComparisonPreparation
variable {evaluated}

/-- Retain the original common-chart preparation's uniform bounds and exact arc scale. -/
@[expose] def build (preparation : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPreparation.ChartPreparation regular
  common) :
    Hyperelliptic.Charts.Reciprocal.Disk.CommonChartArcComparison.ArcComparisonPreparation (differential :=
      differential) (other := other) (regular := regular) :=
  ⟨preparation.bounds, preparation.arcScale, preparation.arcScale_eq⟩

variable (prepared :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartArcComparison.ArcComparisonPreparation (differential :=
  differential) (other := other) (regular := regular))

/-- The original coefficient scale times the fourth power of the distance between the actual adjacent chart coordinates.
-/
@[expose] def EdgeBound (i : Fin common.intervals.length) (edge : Fin (request.plans.get i).geometry.tail.length) :
  Coordinate :=
  prepared.scale * Data.Gaussian.Norm.Basic.normSq
    (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartConnections.Evaluation.chartCoordinate evaluated i edge.succ -
    Hyperelliptic.Charts.Reciprocal.Disk.CommonChartConnections.Evaluation.chartCoordinate evaluated i edge.castSucc)^2

/-- The cached scalar bounds indexed by the original chart interval's retained edges. -/
@[expose] def EdgeBounds (i : Fin common.intervals.length) :=
  Data.Vector Normalization.InverseRootPolynomial.Coordinate (request.plans.get i).geometry.tail.length

set_option genInjectivity false in
/-- The actual retained edge bounds and their certified aggregate comparison for one original common-cover interval. -/
structure Interval (i : Fin common.intervals.length) where
  /-- The cached bounds for the original interval edges. -/ edges :
    Hyperelliptic.Charts.Reciprocal.Disk.CommonChartArcComparison.ArcComparisonPreparation.EdgeBounds (request :=
    request) i
  /-- Each cached entry is exactly the original coordinate-distance bound. -/ edges_eq : ∀ edge,
    Data.Vector.get edges edge = prepared.EdgeBound (evaluated := evaluated) i edge
  /-- The cached aggregate interval comparison bound. -/ bound : Normalization.InverseRootPolynomial.Coordinate
  /-- The aggregate is the original edge count times the sum of retained edge bounds. -/ bound_eq : bound =
    ((request.plans.get i).geometry.tail.length : Normalization.InverseRootPolynomial.Coordinate) *
    FiniteSum.Fin.sumFin (fun edge => Data.Vector.get edges edge)
  /-- Every radial depth satisfies the bound against the original retained chart area. -/ bounded : ∀ radialDepth,
    Data.Gaussian.Norm.Basic.normSq (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartFanBank.FanBankRequest.ArcArea
    (evaluated := evaluated) radialDepth i -
    (evaluated.entries.get i).evaluated.chart.retained.area.evaluated.chart.originalArea) ≤ bound

constructive_injectivity Interval

/-- Each actual paired radial arc differs from its original retained chart wedge within the coordinate-distance bound.
-/
theorem edge_bound (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1)
    (i : Fin common.intervals.length) (edge : Fin (request.plans.get i).geometry.tail.length) (radialDepth : Nat) :
    Data.Gaussian.Norm.Basic.normSq (RootContinuation.RootRadialPairedArcs.Bilinear.arcArea
      (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartRadialJunctions.radialValues evaluated) radialDepth
      (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartConnections.Evaluation.chartCoordinate evaluated i edge.castSucc)
        (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartConnections.Evaluation.chartCoordinate evaluated i edge.succ) -
      Topology.Polygon.Stokes.edgeArea
        ((evaluated.entries.get i).evaluated.chart.retained.area.evaluated.readings.get edge.castSucc).chartPoint
        ((evaluated.entries.get i).evaluated.chart.retained.area.evaluated.readings.get edge.succ).chartPoint) ≤
      prepared.EdgeBound (evaluated := evaluated) i edge := by
  rw [Hyperelliptic.Charts.Reciprocal.Disk.CommonChartConnections.Evaluation.chartPoint_readback evaluated branch,
    Hyperelliptic.Charts.Reciprocal.Disk.CommonChartConnections.Evaluation.chartPoint_readback evaluated branch]
  have bound := Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedPairedArcArea.paired_arc_refinement prepared.bounds
    evaluated.samples.firstCap evaluated.samples.otherCap branch
    (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartConnections.Evaluation.chart_square_inside evaluated branch i
      edge.castSucc) (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartConnections.Evaluation.chart_square_inside
      evaluated branch i edge.succ) radialDepth
  exact bound.trans_eq (congrArg (fun scale => scale * Data.Gaussian.Norm.Basic.normSq
    (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartConnections.Evaluation.chartCoordinate evaluated i edge.succ -
      Hyperelliptic.Charts.Reciprocal.Disk.CommonChartConnections.Evaluation.chartCoordinate evaluated i
      edge.castSucc)^2) prepared.scale_eq.symm)

/-- Cache the actual coordinate-distance bound for every original interval edge and certify its aggregate at every
radial depth. -/
@[expose] def acquireInterval (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1)
    (i : Fin common.intervals.length) : prepared.Interval (evaluated := evaluated) i := by
  let edges := Data.Vector.Basic.vectorOfFn (prepared.EdgeBound (evaluated := evaluated) i)
  have readback := Data.Vector.Basic.vectorOfFn_apply (prepared.EdgeBound (evaluated := evaluated) i)
  refine ⟨edges, readback, ((request.plans.get i).geometry.tail.length : Normalization.InverseRootPolynomial.Coordinate)
    * FiniteSum.Fin.sumFin (fun edge => edges edge), rfl, ?_⟩
  intro radialDepth
  rw [(evaluated.entries.get i).evaluated.chart.retained.area.evaluated.chart.originalArea_eq]
  unfold Hyperelliptic.Charts.Reciprocal.Disk.CommonChartFanBank.FanBankRequest.ArcArea
    Periods.CenteredBilinearPath.area
  rw [← FiniteSum.Fin.sumFin_sub]
  exact Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartArcComparison.weighted_bound _ _ (fun edge =>
    (prepared.edge_bound branch i edge radialDepth).trans_eq (readback edge).symm)

/-- The retained arc-comparison certificate for each original common-cover interval. -/
@[expose] def Intervals := Data.Vector.DependentVector (prepared.Interval (evaluated := evaluated))

set_option genInjectivity false in
/-- The cached comparison bound between the original chart area and actual paired radial arcs at every radial depth. -/
structure Comparison where
  /-- The actual retained interval certificates. -/ intervals : prepared.Intervals (evaluated := evaluated)
  /-- The cached whole-bank arc-comparison bound. -/ bound : Normalization.InverseRootPolynomial.Coordinate
  /-- The bound is the original interval count times the sum of retained interval bounds. -/ bound_eq : bound =
    (common.intervals.length : Normalization.InverseRootPolynomial.Coordinate) * FiniteSum.Fin.sumFin (fun i =>
    (intervals.get i).bound)
  /-- Every radial depth satisfies the bound against the original cached chart area. -/ bounded : ∀ radialDepth,
    Data.Gaussian.Norm.Basic.normSq (FiniteSum.Fin.sumFin
    (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartFanBank.FanBankRequest.ArcArea (evaluated := evaluated)
    radialDepth) - evaluated.chartArea) ≤ bound

constructive_injectivity Comparison

/-- Only root-coordinate squared distances are newly calculated. The chart
area and all polynomial values remain the original retained caches. -/
@[expose] def acquire (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1) :
  prepared.Comparison (evaluated := evaluated) := by
  let intervals := Data.Vector.DependentVector.ofFn (fun i => prepared.acquireInterval (evaluated := evaluated) branch
    i)
  refine ⟨intervals, (common.intervals.length : Normalization.InverseRootPolynomial.Coordinate) * FiniteSum.Fin.sumFin
    (fun i => (intervals.get i).bound), rfl, ?_⟩
  intro radialDepth
  rw [evaluated.chartArea_eq, ← FiniteSum.Fin.sumFin_sub]
  exact Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartArcComparison.weighted_bound _ _ (fun i => (intervals.get
    i).bounded radialDepth)

end ArcComparisonPreparation

/-- The source quantity keeps the origin correction, all chart connectors,
and the actual open radial endpoint term. None is declared zero. -/
@[expose] def sourceOpenBoundary (radialDepth : Nat) : Gaussian :=
  evaluated.sourceArea - evaluated.correction + FiniteSum.Fin.sumFin
    (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartJoinedFans.FanBankRequest.ConnectorArea (evaluated := evaluated)) +
    Hyperelliptic.Charts.Reciprocal.Disk.CommonChartJoinedFans.FanBankRequest.OuterRadialBoundary (evaluated :=
      evaluated) radialDepth

/-- The retained source boundary, including all connectors and outer radial ends, satisfies the combined chart,
joined-fan and actual mesh-comparison bound. -/
theorem FanBankRequest.Joined.source_boundary_bound {requested : Normalization.InverseRootPolynomial.Coordinate}
  {minimum : Nat}
    {planned : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartFanBank.FanBankRequest evaluated requested minimum} {bank
      : planned.Bank} (joined : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartJoinedFans.FanBankRequest.Joined planned
      bank)
    {prepared : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartArcComparison.ArcComparisonPreparation (differential :=
      differential) (other := other) (regular := regular)}
    (comparison : prepared.Comparison (evaluated := evaluated)) :
    Data.Gaussian.Norm.Basic.normSq
      (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartArcComparison.sourceOpenBoundary evaluated planned.fan.depth) <
      2 * (target + 2 * (2 * (requested + target) + comparison.bound)) := open Purelib.Data.Rat in by
  have arc := comparison.bounded planned.fan.depth
  have reversed : Data.Gaussian.Norm.Basic.normSq (evaluated.chartArea - FiniteSum.Fin.sumFin
    (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartFanBank.FanBankRequest.ArcArea (evaluated := evaluated)
    planned.fan.depth)) ≤ comparison.bound := by
    rw [show evaluated.chartArea - FiniteSum.Fin.sumFin
      (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartFanBank.FanBankRequest.ArcArea (evaluated := evaluated)
      planned.fan.depth) =
      -(FiniteSum.Fin.sumFin (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartFanBank.FanBankRequest.ArcArea (evaluated
        := evaluated) planned.fan.depth) - evaluated.chartArea) by ring1, Gaussian.Norm.Basic.normSq_neg]
    exact arc
  have joinedPlus := (Fraction.Order.Arithmetic.add_lt_add_right_direct joined.bounded
    (Data.Gaussian.Norm.Basic.normSq (evaluated.chartArea - FiniteSum.Fin.sumFin
      (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartFanBank.FanBankRequest.ArcArea (evaluated := evaluated)
      planned.fan.depth)))).trans_le
      (Fraction.Order.Arithmetic.add_le_add_direct le_rfl reversed)
  have polygon := (Gaussian.Norm.Bounds.normSq_add_le_two joined.area
    (evaluated.chartArea - FiniteSum.Fin.sumFin
      (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartFanBank.FanBankRequest.ArcArea (evaluated := evaluated)
      planned.fan.depth))).trans_lt
      (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide) joinedPlus)
  have full := (Gaussian.Norm.Bounds.normSq_add_le_two (evaluated.sourceArea - evaluated.chartArea -
    evaluated.correction)
    (joined.area + (evaluated.chartArea - FiniteSum.Fin.sumFin
      (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartFanBank.FanBankRequest.ArcArea (evaluated := evaluated)
      planned.fan.depth)))).trans_lt
      (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide) (Fraction.Order.Arithmetic.add_lt_add_direct
        evaluated.bounded polygon))
  have identity : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartArcComparison.sourceOpenBoundary evaluated
    planned.fan.depth =
      (evaluated.sourceArea - evaluated.chartArea - evaluated.correction) +
        (joined.area + (evaluated.chartArea - FiniteSum.Fin.sumFin
          (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartFanBank.FanBankRequest.ArcArea (evaluated := evaluated)
          planned.fan.depth))) := by
    rw [joined.boundary_eq]
    unfold Hyperelliptic.Charts.Reciprocal.Disk.CommonChartArcComparison.sourceOpenBoundary
      Hyperelliptic.Charts.Reciprocal.Disk.CommonChartJoinedFans.FanBankRequest.JoinedBoundary
    ring1
  rw [identity]
  exact full

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartArcComparison
